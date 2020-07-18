#![allow(dead_code)]

use clang::*;
use linked_hash_map::LinkedHashMap;
use linked_hash_set::LinkedHashSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::hash::Hash;
use std::iter::once;
use std::iter::IntoIterator;
use std::vec;

type CallbackIndex<'tu> = HashMap<Entity<'tu>, String>;

fn get_single_base_class(e: Entity) -> Option<Entity> {
  let mut it = e
    .get_children()
    .into_iter()
    .filter(|c| c.get_kind() == EntityKind::BaseSpecifier)
    .filter_map(|c| c.get_type())
    .filter_map(|t| t.get_declaration())
    .filter_map(|b| b.get_definition());
  match it.next() {
    Some(base) if it.next().is_none() => Some(base),
    _ => None, // Return None if there are 0 or 2+ base classes.
  }
}

fn get_direct_subclasses(e: Entity) -> Option<Vec<Entity>> {
  let t = e.get_type()?;
  let mut subclasses = Vec::<Entity>::new();
  e.get_translation_unit()
    .get_entity()
    .visit_children(|e2, p2| {
      use EntityKind::*;
      if e2.get_kind() == BaseSpecifier
        && e2.get_type().map(|t2| t2 == t).unwrap()
      {
        assert!(p2.get_kind() == ClassDecl || p2.get_kind() == StructDecl);
        assert!(p2.is_definition());
        subclasses.push(p2);
      }
      EntityVisitResult::Recurse
    });
  Some(subclasses)
}

// Note: a TranslationUnit is also a named entity.
fn get_named_semantic_parent(e: Entity) -> Option<Entity> {
  let p = e.get_semantic_parent()?;
  match p.get_name() {
    Some(_) => Some(p),
    None => get_named_semantic_parent(p),
  }
}

fn is_v8_ns(e: Entity) -> bool {
  e.get_kind() == EntityKind::Namespace
    && e.get_name().map(|n| n == "v8").unwrap_or(false)
    && get_named_semantic_parent(e)
      .map(|p| p.get_kind() == EntityKind::TranslationUnit)
      .unwrap_or(false)
}

fn is_v8_top_level_class(e: Entity, class_name: &str) -> bool {
  e.get_kind() == EntityKind::ClassDecl
    && e.get_name().map(|n| n == class_name).unwrap_or(false)
    && e.get_semantic_parent().map(is_v8_ns).unwrap_or(false)
}

// This function also returns `true` if `e` itself has name `v8::{class_name}`.
fn has_base_class_in_v8_ns(e: Entity, class_name: &'static str) -> bool {
  is_v8_top_level_class(e, class_name)
    || get_single_base_class(e)
      .map(|b| has_base_class_in_v8_ns(b, class_name))
      .unwrap_or(false)
}

fn type_has_base_class_in_v8_ns(ty: &Type, class_name: &'static str) -> bool {
  ty.get_declaration()
    .map(|e| has_base_class_in_v8_ns(e, class_name))
    .unwrap_or(false)
}

fn get_flat_name_for_callback_type(e: Entity) -> String {
  let mut name = e.get_name().unwrap();
  let mut parent = e;
  loop {
    parent = parent.get_semantic_parent().unwrap();
    if parent.get_kind() == EntityKind::Namespace
      || is_v8_top_level_class(parent, "Isolate")
      || is_v8_top_level_class(parent, "Context")
      || (is_v8_top_level_class(parent, "Module") && name.contains("Module"))
    {
      break;
    } else if let Some(parent_name) = parent.get_name() {
      name = format!("{}{}", parent_name, name);
    }
  }
  name
    .replace("CallbackFunction", "Fn")
    .replace("CallbackCallback", "Callback")
    .replace("CallbackInfoCallback", "Callback")
}

fn to_snake_case(s: impl AsRef<str>) -> String {
  let mut words = vec![];
  for part in s.as_ref().split('_') {
    let mut last_upper = false;
    let mut buf = String::new();
    if part.is_empty() {
      continue;
    }
    for ch in part.chars() {
      if !buf.is_empty() && buf != "'" && ch.is_uppercase() && !last_upper {
        words.push(buf);
        buf = String::new();
      }
      last_upper = ch.is_uppercase();
      buf.extend(ch.to_lowercase());
    }
    words.push(buf);
  }
  words.join("_")
}

fn replace_suffix(
  s: &str,
  old_suffix: &str,
  new_suffix: &str,
) -> Option<String> {
  if !s.ends_with(old_suffix) {
    None
  } else {
    Some(format!(
      "{}{}",
      &s[0..s.len() - old_suffix.len()],
      new_suffix
    ))
  }
}

fn is_type_used(translation_unit: &TranslationUnit, ty: Type) -> bool {
  let can_ty = ty.get_canonical_type();
  let root = translation_unit.get_entity();
  root.visit_children(|e, _| {
    if e.get_storage_class().is_some()
      && e
        .get_type()
        .map(|var_ty| var_ty.get_canonical_type() == can_ty)
        .unwrap_or(false)
    {
      EntityVisitResult::Break
    } else {
      EntityVisitResult::Recurse
    }
  })
}

enum TypeParams<'tu> {
  Zero,
  One(Type<'tu>),
  Two(Type<'tu>, Type<'tu>),
}

fn is_v8_type<'tu>(ty: Type<'tu>, name: &str) -> Option<Type<'tu>> {
  let _def = ty
    .get_declaration()
    .filter(|d| d.get_name().map(|n| n == name).unwrap_or(false))
    .filter(|d| d.get_semantic_parent().map(is_v8_ns).unwrap_or(false))?;
  Some(ty)
}

fn is_v8_type_pointee<'tu>(ty: Type<'tu>, name: &str) -> Option<Type<'tu>> {
  ty.get_pointee_type().and_then(|ty| is_v8_type(ty, name))
}

fn is_void_type<'tu>(ty: Type<'tu>) -> bool {
  ty.get_kind() == TypeKind::Void
}

fn get_type_name<'tu>(ty: Type<'tu>) -> Option<String> {
  match ty.get_declaration() {
    Some(d) => d.get_name(),
    None if is_void_type(ty) => Some("void".to_owned()),
    None => None,
  }
}

fn get_type_params<'tu>(ty: Type<'tu>) -> Option<TypeParams<'tu>> {
  let mut ptys = ty.get_template_argument_types()?.into_iter();
  let pty1 = ptys.next();
  let pty2 = pty1.and_then(|_| ptys.next());
  let pty3 = pty2.and_then(|_| ptys.next());
  let info = match (pty1, pty2, pty3) {
    (None, _, _) => TypeParams::Zero,
    (Some(p), None, _) => TypeParams::One(p?),
    (Some(p), Some(q), None) => TypeParams::Two(p?, q?),
    _ => panic!("More than 2 type parameters"),
  };
  Some(info)
}

fn is_std_ns(e: Entity) -> bool {
  e.get_kind() == EntityKind::Namespace
    && e.get_name().map(|n| n == "std").unwrap_or(false)
    && get_named_semantic_parent(e)
      .map(|p| p.get_kind() == EntityKind::TranslationUnit)
      .unwrap_or(false)
}

fn is_std_type<'tu>(ty: Type<'tu>, name: &str) -> bool {
  ty.get_declaration()
    .filter(|d| d.get_name().map(|n| n == name).unwrap_or(false))
    .filter(|d| {
      get_named_semantic_parent(*d)
        .map(|p| is_std_ns(p) || p.get_kind() == EntityKind::TranslationUnit)
        .unwrap_or(false)
    })
    .is_some()
}

#[derive(Debug, Clone)]
struct Sig<'tu> {
  pub id: SigIdent,
  pub ty: SigType<'tu>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum SigIdent {
  Return,
  Param(Option<String>),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
enum Disposition {
  Const,
  Mut,
  Owned,
}

impl Disposition {
  pub fn new_ptr(pointee_ty: Type<'_>) -> Self {
    if pointee_ty.is_const_qualified() {
      Self::Const
    } else {
      Self::Mut
    }
  }

  pub fn is_ptr(self) -> bool {
    match self {
      Self::Const | Self::Mut => true,
      Self::Owned => false,
    }
  }
}

impl Display for Disposition {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let raw = f.alternate();
    match self {
      Self::Const if raw => write!(f, "*const "),
      Self::Mut if raw => write!(f, "*mut "),
      Self::Const => write!(f, "&"),
      Self::Mut => write!(f, "&mut "),
      Self::Owned => Ok(()),
    }
  }
}

#[derive(Debug, Clone)]
enum SigType<'tu> {
  Void {
    disposition: Disposition,
  },
  Bool,
  Int {
    signed: bool,
  },
  IntFixedSize {
    bits: u8,
    signed: bool,
  },
  IntPtrSize {
    signed: bool,
  },
  Double,
  Isolate {
    disposition: Disposition,
  },
  CallbackScope {
    param: String,
  },
  StartupData,
  Local {
    inner_ty: Type<'tu>,
    inner_ty_name: String,
  },
  MaybeLocal {
    inner_ty_name: String,
  },
  PromiseRejectMessage,
  PropertyDescriptor {
    disposition: Disposition,
  },
  CallbackInfo {
    ty_name: String,
    ret_ty_name: Option<String>,
  },
  CallbackArguments {
    ty_name: String,
    info_ty_name: String,
    info_var_name: String,
  },
  CallbackReturnValue {
    ret_ty_name: String,
    info_ty_name: String,
    info_var_name: String,
  },
  Enum {
    ty_name: String,
  },
  Unknown(Type<'tu>),
}

impl<'tu> Display for SigType<'tu> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let raw = f.alternate();
    match self {
      Self::Void {
        disposition: Disposition::Owned,
      } => write!(f, "()"),
      Self::Void { disposition } => write!(f, "{:#}c_void", disposition),
      Self::Bool => write!(f, "bool"),
      Self::Int { signed: true } if raw => write!(f, "c_int"),
      Self::Int { signed: false } if raw => write!(f, "c_uint"),
      Self::Int { signed } => Self::IntFixedSize {
        bits: 32,
        signed: *signed,
      }
      .fmt(f),
      Self::IntFixedSize { bits, signed: true } => write!(f, "i{}", bits),
      Self::IntFixedSize {
        bits,
        signed: false,
      } => write!(f, "u{}", bits),
      Self::IntPtrSize { signed: true } => write!(f, "isize"),
      Self::IntPtrSize { signed: false } => write!(f, "usize"),
      Self::Double if raw => write!(f, "c_double"),
      Self::Double => write!(f, "f64"),
      Self::Isolate { disposition } => {
        disposition.fmt(f)?;
        write!(f, "Isolate")
      }
      Self::CallbackScope { .. } => write!(f, "&mut HandleScope<'s>"),
      Self::Local { inner_ty_name, .. } => {
        write!(f, "Local<'s, {}>", inner_ty_name)
      }
      Self::MaybeLocal { inner_ty_name } => {
        write!(f, "Option<Local<'s, {}>>", inner_ty_name)
      }
      Self::PromiseRejectMessage => write!(f, "PromiseRejectMessage<'s>"),
      Self::PropertyDescriptor { disposition } => {
        disposition.fmt(f)?;
        write!(f, "PropertyDescriptor")
      }
      Self::StartupData => write!(f, "StartupData"),
      Self::CallbackInfo { ty_name, .. } => {
        write!(f, "{:#}{}", Disposition::Const, ty_name)
      }
      Self::CallbackArguments { ty_name, .. } => write!(f, "{}<'s>", ty_name),
      Self::CallbackReturnValue { ret_ty_name, .. } => {
        write!(f, "ReturnValue<'s, {}>", ret_ty_name)
      }
      Self::Enum { ty_name } => write!(f, "{}", ty_name),
      Self::Unknown(mut uty) => {
        eprint!("XX ?? {:?}", uty);
        while let Some(pty) = uty.get_pointee_type() {
          Disposition::new_ptr(pty).fmt(f)?;
          uty = pty;
        }
        eprintln!("  sizeof={:?}  sz[]={:?}", uty.get_sizeof(), uty.get_size());
        write!(
          f,
          "{}??",
          get_type_name(uty).unwrap_or_else(|| uty.get_display_name())
        )
      }
    }
  }
}

impl<'tu> From<(Option<String>, Type<'tu>)> for Sig<'tu> {
  fn from((id, ty): (Option<String>, Type<'tu>)) -> Self {
    Self {
      id: id.into(),
      ty: ty.into(),
    }
  }
}

impl<'tu> Sig<'tu> {
  fn new_return(ret_ty: Type<'tu>) -> Self {
    Self {
      id: SigIdent::Return,
      ty: ret_ty.into(),
    }
  }

  fn gather_lifetimes(
    &self,
    mut rest: impl Iterator<Item = Sig<'tu>>,
    lifetimes: &mut LinkedHashMap<String, LinkedHashSet<String>>,
    raw: bool,
    for_macro: bool,
  ) {
    match self.ty {
      SigType::CallbackScope { .. }
      | SigType::Local { .. }
      | SigType::MaybeLocal { .. }
      | SigType::PromiseRejectMessage
      | SigType::CallbackArguments { .. }
      | SigType::CallbackReturnValue { .. } => {
        let lifetime = if for_macro { "'__s" } else { "'s" };
        if !lifetimes.contains_key(lifetime) {
          lifetimes.insert(lifetime.to_owned(), Default::default());
        }
      }
      _ => {}
    }
    if let Some(next) = rest.next() {
      next.gather_lifetimes(rest, lifetimes, raw, for_macro);
    }
  }

  fn gather_type_params(
    &self,
    mut rest: impl Iterator<Item = Sig<'tu>>,
    type_params: &mut LinkedHashMap<String, LinkedHashSet<String>>,
    raw: bool,
  ) {
    match self.ty {
      _ => {}
    }
    if let Some(next) = rest.next() {
      next.gather_type_params(rest, type_params, raw);
    }
  }

  pub fn is_return_value_that_requires_win64_stack_return_fix(&self) -> bool {
    match self {
      Sig {
        id: SigIdent::Return,
        ty: SigType::Local { .. },
      }
      | Sig {
        id: SigIdent::Return,
        ty: SigType::MaybeLocal { .. },
      } => true,
      _ => false,
    }
  }

  pub fn generate_call_signature<R>(
    &self,
    rest: R,
    raw: bool,
    win64_stack_return_fix: bool,
    with_types: bool,
    with_names: bool,
    closure_style: bool,
    used_inputs: Option<&HashSet<String>>,
  ) -> String
  where
    R: Iterator<Item = Sig<'tu>>,
  {
    let gen_rest = |mut rest: R| {
      let next = rest.next();
      next
        .map(|n| {
          n.generate_call_signature(
            rest,
            raw,
            win64_stack_return_fix,
            with_types,
            with_names,
            closure_style,
            used_inputs,
          )
        })
        .unwrap_or_default()
    };
    let fmt_separator = || if with_names && with_types { ": " } else { "" };
    let fmt_name_prefix = |v| {
      if used_inputs.map(|ui| !ui.contains(v)).unwrap_or_default() {
        "_"
      } else if v == "type" {
        "r#"
      } else {
        ""
      }
    };
    let fmt_name = |v| {
      if with_names {
        if raw {
          format!("{}{:#}", fmt_name_prefix(v), v)
        } else {
          format!("{}{}", fmt_name_prefix(v), v)
        }
      } else {
        Default::default()
      }
    };
    let fmt_type = |v| {
      if with_types {
        if raw {
          format!("{:#}", v)
        } else {
          format!("{}", v)
        }
      } else {
        Default::default()
      }
    };
    use SigIdent as I;
    match self {
      Sig { id: I::Return, .. } if !with_types && !closure_style => {
        format!("({})", gen_rest(rest))
      }
      Sig { id: I::Return, .. } if !with_types && closure_style => {
        format!("|{}|", gen_rest(rest))
      }
      Sig { id: I::Return, ty }
        if raw && !with_names && win64_stack_return_fix =>
      {
        format!(
          "(\n  *mut {:#},\n{}) -> *mut {:#}\n",
          ty,
          gen_rest(rest),
          ty
        )
      }
      Sig { id: I::Return, ty }
        if raw && with_names && win64_stack_return_fix =>
      {
        format!(
          "(\n  return_value: *mut {:#},\n{}) -> *mut {:#}\n",
          ty,
          gen_rest(rest),
          ty
        )
      }
      Sig { id: I::Return, ty } if ty.is_void() => {
        format!("(\n{})", gen_rest(rest))
      }
      Sig { id: I::Return, ty } => {
        format!("(\n{}    ) -> {}\n", gen_rest(rest), fmt_type(ty))
      }
      Sig {
        id: I::Param(Some(name)),
        ty,
      } => format!(
        "      {}{}{},\n{}",
        fmt_name(name),
        fmt_separator(),
        fmt_type(ty),
        gen_rest(rest)
      ),
      _ => unreachable!(),
    }
  }

  fn gather_raw_to_native_conversion_used_inputs<R>(
    self,
    mut rest: R,
    used_inputs: &mut HashSet<String>,
  ) where
    R: Iterator<Item = Sig<'tu>>,
  {
    match self {
      Sig {
        ty: SigType::CallbackScope { param },
        ..
      } => {
        used_inputs.insert(param);
      }
      Sig {
        ty: SigType::CallbackArguments { info_var_name, .. },
        ..
      }
      | Sig {
        ty: SigType::CallbackReturnValue { info_var_name, .. },
        ..
      } => {
        used_inputs.insert(info_var_name);
      }
      Sig {
        id: SigIdent::Param(Some(name)),
        ..
      } => {
        used_inputs.insert(name);
      }
      _ => {}
    }
    if let Some(next) = rest.next() {
      next.gather_raw_to_native_conversion_used_inputs(rest, used_inputs);
    }
  }

  fn gather_raw_to_native_conversions<R>(&self, rest: R) -> String
  where
    R: Iterator<Item = Sig<'tu>>,
  {
    let gen_rest = |mut rest: R| {
      let next = rest.next();
      next
        .map(|n| n.gather_raw_to_native_conversions(rest))
        .unwrap_or_default()
    };
    match self {
      Sig {
        id: SigIdent::Param(Some(name)),
        ty: SigType::Isolate { disposition },
      }
      | Sig {
        id: SigIdent::Param(Some(name)),
        ty: SigType::PropertyDescriptor { disposition },
      } => {
        assert_ne!(disposition, &Disposition::Owned);
        format!(
          "  let {} = unsafe {{ {}*{} }};\n{}",
          name,
          disposition,
          name,
          gen_rest(rest)
        )
      }
      Sig {
        id: SigIdent::Param(Some(name)),
        ty: SigType::CallbackScope { param },
      } => format!(
        "  let {} = &mut unsafe {{ CallbackScope::new({}) }};\n{}",
        name,
        param,
        gen_rest(rest)
      ),
      Sig {
        id: SigIdent::Param(Some(name)),
        ty:
          SigType::CallbackArguments {
            ty_name,
            info_ty_name,
            info_var_name,
          },
      } => format!(
        "  let {} = {}::from_{}({});\n{}",
        name,
        ty_name,
        to_snake_case(info_ty_name),
        info_var_name,
        gen_rest(rest)
      ),
      Sig {
        id: SigIdent::Param(Some(name)),
        ty:
          SigType::CallbackReturnValue {
            ret_ty_name,
            info_ty_name,
            info_var_name,
          },
      } => format!(
        "  let {} = ReturnValue::<{}>::from_{}({});\n{}",
        name,
        ret_ty_name,
        to_snake_case(info_ty_name),
        info_var_name,
        gen_rest(rest)
      ),
      _ => gen_rest(rest),
    }
  }
}

impl From<Option<String>> for SigIdent {
  fn from(name: Option<String>) -> SigIdent {
    Self::Param(name)
  }
}

impl<'a> From<&'a str> for SigIdent {
  fn from(name: &str) -> SigIdent {
    Self::Param(Some(name.to_owned()))
  }
}

impl<'tu> From<Type<'tu>> for SigType<'tu> {
  fn from(ty: Type<'tu>) -> Self {
    use SigType as M;
    use TypeKind as K;

    if ty.get_kind() == K::Void {
      M::Void {
        disposition: Disposition::Owned,
      }
    } else if let Some(pty) =
      ty.get_pointee_type().filter(|&pty| is_void_type(pty))
    {
      M::Void {
        disposition: Disposition::new_ptr(pty),
      }
    } else if ty.get_kind() == K::Bool {
      M::Bool
    } else if ty.get_kind() == K::Int {
      M::Int { signed: true }
    } else if is_std_type(ty, "int32_t") {
      M::IntFixedSize {
        bits: 32,
        signed: true,
      }
    } else if is_std_type(ty, "int64_t") {
      M::IntFixedSize {
        bits: 64,
        signed: true,
      }
    } else if is_std_type(ty, "uint32_t") {
      M::IntFixedSize {
        bits: 32,
        signed: false,
      }
    } else if is_std_type(ty, "uint64_t") {
      M::IntFixedSize {
        bits: 64,
        signed: false,
      }
    } else if is_std_type(ty, "ssize_t") || is_std_type(ty, "intptr_t") {
      M::IntPtrSize { signed: true }
    } else if is_std_type(ty, "size_t") || is_std_type(ty, "uintptr_t") {
      M::IntPtrSize { signed: false }
    } else if ty.get_kind() == K::Double {
      M::Double
    } else if let Some(TypeParams::One(inner_ty)) =
      is_v8_type(ty, "Local").and_then(get_type_params)
    {
      M::Local {
        inner_ty,
        inner_ty_name: get_type_name(inner_ty).unwrap(),
      }
    } else if let Some(TypeParams::One(inner_ty)) =
      is_v8_type(ty, "MaybeLocal").and_then(get_type_params)
    {
      M::MaybeLocal {
        inner_ty_name: get_type_name(inner_ty).unwrap(),
      }
    } else if let Some(pty) = is_v8_type_pointee(ty, "Isolate") {
      M::Isolate {
        disposition: Disposition::new_ptr(pty),
      }
    } else if let Some(ty2) = is_v8_type_pointee(ty, "FunctionCallbackInfo")
      .or_else(|| is_v8_type_pointee(ty, "PropertyCallbackInfo"))
    {
      let ty_name = get_type_name(ty2).unwrap();
      let ret_ty_name = get_type_params(ty2)
        .and_then(|ps| match ps {
          TypeParams::One(p) if p.get_kind() != TypeKind::Void => Some(p),
          TypeParams::One(_) | TypeParams::Zero => None,
          _ => panic!(),
        })
        .and_then(get_type_name);
      M::CallbackInfo {
        ty_name,
        ret_ty_name,
      }
    } else if let Some(_ty) = is_v8_type(ty, "StartupData") {
      M::StartupData
    } else if let Some(_ty) = is_v8_type(ty, "PromiseRejectMessage") {
      M::PromiseRejectMessage
    } else if let Some(pty) = is_v8_type_pointee(ty, "PropertyDescriptor") {
      M::PropertyDescriptor {
        disposition: Disposition::new_ptr(pty),
      }
    } else if ty.get_kind() == TypeKind::Enum && ty.get_sizeof().unwrap() == 4 {
      M::Enum {
        ty_name: get_type_name(ty).unwrap(),
      }
    } else {
      M::Unknown(ty)
    }
  }
}

impl<'tu> SigType<'tu> {
  fn is_unknown(&self) -> bool {
    match self {
      Self::Unknown(..) => true,
      _ => false,
    }
  }

  fn is_void(&self) -> bool {
    match self {
      Self::Void {
        disposition: Disposition::Owned,
      } => true,
      _ => false,
    }
  }

  fn is_void_ptr(&self) -> bool {
    match self {
      Self::Void { disposition } => disposition.is_ptr(),
      _ => false,
    }
  }
}

fn gather_recursively_with<
  'tu,
  F: FnOnce(Sig<'tu>, vec::IntoIter<Sig<'tu>>) -> R,
  R: Default,
>(
  sigs: Vec<Sig<'tu>>,
  f: F,
) -> R {
  let mut rest = sigs.into_iter();
  if let Some(first) = rest.next() {
    f(first, rest)
  } else {
    Default::default()
  }
}

fn add_angle_bracket_param<N, I>(
  map: &mut LinkedHashMap<String, LinkedHashSet<String>>,
  name: N,
  constraints: I,
) where
  N: AsRef<str>,
  I: IntoIterator,
  I::Item: AsRef<str>,
{
  let name = name.as_ref();
  if !map.contains_key(name) {
    let r = map.insert(name.to_owned(), Default::default());
    assert!(r.is_none());
  }
  let val = map.get_mut(name).unwrap();
  for c in constraints {
    let c = c.as_ref();
    if !val.contains(c) {
      let r = val.insert(c.to_owned());
      assert!(!r);
    }
  }
}

fn generate_angle_bracket_params<'tu>(
  sigs: &[Sig<'tu>],
  raw: bool,
  with_lifetimes: bool,
  with_type_params: bool,
  include_unconstrained: bool,
  include_constraints: bool,
  for_macro: bool,
  wrap_fn: impl Fn(String) -> String,
) -> String {
  let mut map = LinkedHashMap::<String, LinkedHashSet<String>>::new();
  if with_lifetimes {
    gather_recursively_with(sigs.to_owned(), |first, rest| {
      first.gather_lifetimes(rest, &mut map, raw, for_macro)
    });
  }
  if with_type_params {
    gather_recursively_with(sigs.to_owned(), |first, rest| {
      first.gather_type_params(rest, &mut map, raw)
    });
  }
  let s = if !include_constraints {
    assert!(include_unconstrained);
    map
      .into_iter()
      .map(|(k, _)| k)
      .collect::<Vec<_>>()
      .join(", ")
  } else {
    map
      .into_iter()
      .filter(|(_, v)| !v.is_empty() || include_unconstrained)
      .map(|(k, v)| {
        if v.is_empty() {
          k
        } else {
          format!("{}: {}", k, v.into_iter().collect::<Vec<_>>().join(" + "))
        }
      })
      .collect::<Vec<_>>()
      .join(", ")
  };
  if !s.is_empty() {
    wrap_fn(s)
  } else {
    s
  }
}

fn generate_call_params<'tu>(
  sigs: &[Sig<'tu>],
  raw: bool,
  win64_stack_return_fix: bool,
  with_types: bool,
  with_names: bool,
  closure_style: bool,
  for_macro: bool,
  used_inputs: Option<&HashSet<String>>,
) -> String {
  let mut call_params =
    gather_recursively_with(sigs.to_owned(), |first, rest| {
      first.generate_call_signature(
        rest,
        raw,
        win64_stack_return_fix,
        with_types,
        with_names,
        closure_style,
        used_inputs,
      )
    });
  // BLERGH! ugly hack!
  if for_macro {
    call_params = call_params.replace("'", "'__");
  }
  call_params
}

fn contains_unknown_cxx_types<'tu>(sigs: &[Sig<'tu>]) -> bool {
  sigs
    .iter()
    .find(|sig| match sig {
      Sig {
        ty: SigType::Unknown(_),
        ..
      } => true,
      _ => false,
    })
    .is_some()
}

fn gather_raw_to_native_conversions<'tu>(sigs: &[Sig<'tu>]) -> String {
  gather_recursively_with(sigs.to_owned(), |first, rest| {
    first.gather_raw_to_native_conversions(rest)
  })
}

fn gather_used_inputs<'tu>(sigs_native: &[Sig<'tu>]) -> HashSet<String> {
  gather_recursively_with(sigs_native.to_owned(), |first, rest| {
    let mut used_inputs = HashSet::<String>::new();
    first.gather_raw_to_native_conversion_used_inputs(rest, &mut used_inputs);
    used_inputs
  })
}

fn give_all_signature_params_a_name(sigs: Vec<Sig>) -> Vec<Sig> {
  sigs
    .into_iter()
    .map(|sig| match sig {
      Sig {
        id: SigIdent::Return,
        ..
      } => sig,
      Sig {
        id: SigIdent::Param(Some(..)),
        ..
      } => sig,
      Sig {
        id: SigIdent::Param(None),
        ty,
      } => Sig {
        id: match ty {
          SigType::Isolate { .. } => "isolate",
          SigType::CallbackInfo { .. } => "info",
          SigType::Void { .. } => "callback_data",
          _ => "«?»",
        }
        .into(),
        ty,
      },
    })
    .collect()
}

fn convert_raw_signature_to_native<'tu>(sigs: &[Sig<'tu>]) -> Vec<Sig<'tu>> {
  // Prefer to create Scope from Local<Context> over other options.
  let mut scope_param = sigs
    .iter()
    .find_map(|sig| match sig {
      Sig {
        ty: SigType::Local { inner_ty, .. },
        id: SigIdent::Param(name),
      } if type_has_base_class_in_v8_ns(inner_ty, "Context") => name.clone(),
      _ => None,
    })
    // If no Local<Context> found, look for other options.
    .or_else(|| {
      sigs.iter().find_map(|sig| match sig {
        Sig {
          ty: SigType::Local { inner_ty, .. },
          id: SigIdent::Param(name),
        } if type_has_base_class_in_v8_ns(inner_ty, "Object")
          || type_has_base_class_in_v8_ns(inner_ty, "Message") =>
        {
          name.clone()
        }
        Sig {
          ty: SigType::PromiseRejectMessage,
          id: SigIdent::Param(Some(name)),
        } => Some(format!("&{}", &name)),
        Sig {
          ty: SigType::CallbackInfo { .. },
          id: SigIdent::Param(Some(name)),
        } => Some(format!("&*{}", &name)),
        _ => None,
      })
    })
    .map(|param| Sig {
      ty: SigType::CallbackScope { param },
      id: "scope".into(),
    });

  let has_scope = scope_param.is_some();

  sigs
    .iter()
    .cloned()
    .flat_map(move |sig| match sig {
      // Keep the return type at the beginning of the list.
      // Insert the CallbackScope (if any) right after the return type.
      Sig {
        id: SigIdent::Return,
        ..
      } => once(sig).chain(scope_param.take().into_iter()),
      _ => once(sig).chain(None.into_iter()),
    })
    .filter(
      |sig| match sig {
        // Remove any `Isolate` and `Local<Context>` parameters if we are passing
        // a scope.
        Sig {
          ty: SigType::Isolate { .. },
          ..
        } => false,
        Sig {
          ty: SigType::Local { inner_ty, .. },
          id: SigIdent::Param(..),
        } if type_has_base_class_in_v8_ns(inner_ty, "Context") => false,
        _ => true,
      } || !has_scope
    )
    .flat_map(|sig| match sig {
      // Split Function/PropertyCallbackInfo into 'arguments' and, if
      // the return type is not `void`, a 'return_value' object.
      Sig {
        ty:
          SigType::CallbackInfo {
            ty_name: info_ty_name,
            ret_ty_name,
          },
        id: SigIdent::Param(Some(info_var_name)),
      } => {
        let args_ty_name =
          replace_suffix(&info_ty_name, "Info", "Arguments").unwrap();
        let args_var_name = info_var_name.replace("info", "arguments");
        once(Sig {
          ty: SigType::CallbackArguments {
            ty_name: args_ty_name,
            info_ty_name: info_ty_name.clone(),
            info_var_name: info_var_name.clone(),
          },
          id: SigIdent::Param(Some(args_var_name)),
        })
        .chain(
          ret_ty_name
            .map(|ret_ty_name| Sig {
              ty: SigType::CallbackReturnValue {
                ret_ty_name,
                info_ty_name,
                info_var_name,
              },
              id: "return_value".into(),
            })
            .into_iter(),
        )
      }
      _ => once(sig).chain(None.into_iter()),
    })
    .collect::<Vec<_>>()
}

fn return_value_requires_win64_stack_return_fix<'tu>(
  sigs: &[Sig<'tu>],
) -> bool {
  sigs
    .iter()
    .find(|sig| sig.is_return_value_that_requires_win64_stack_return_fix())
    .is_some()
}

fn format_comment(comment: &str) -> String {
  let delims: &[_] = &['/', '*', ' ', '\n'];
  comment
    .trim_start_matches(delims)
    .trim_end_matches(delims)
    .replacen("", "/// ", 1)
    .replace("\n  ", "\n")
    .replace("\n  ", "\n") // Yes, two times in a row.
    .replace("\n * ", "\n/// ")
    .replace("\n *\n", "\n///\n")
    .replace("\\code", "```ignore")
    .replace("\\endcode", "```")
    .replace(".  ", ". ")
}

fn render_callback_definition<'tu>(
  cb_name: &str,
  cb_comment: Option<&str>,
  sigs_native: &[Sig<'tu>],
  sigs_raw: &[Sig<'tu>],
  used_inputs: HashSet<String>,
  use_win64fix: bool,
) -> String {
  let cb_name_uc = cb_name;
  let cb_name_lc = to_snake_case(&cb_name);
  let cb_comment = cb_comment
    .map(format_comment)
    .unwrap_or_else(|| format!("// === {} ===\n", &cb_name_uc));
  let for_lifetimes_native = generate_angle_bracket_params(
    sigs_native,
    false,
    true,
    false,
    true,
    false,
    false,
    |s| format!("for<{}> ", s),
  );
  let for_lifetimes_native_for_macro = generate_angle_bracket_params(
    sigs_native,
    false,
    true,
    false,
    true,
    false,
    true,
    |s| format!("for<{}> ", s),
  );
  let lifetimes_native = generate_angle_bracket_params(
    sigs_native,
    false,
    true,
    false,
    true,
    false,
    false,
    |s| s,
  );
  let for_lifetimes_raw = generate_angle_bracket_params(
    sigs_raw,
    true,
    true,
    false,
    true,
    false,
    false,
    |s| format!("for<{}> ", s),
  );
  let lifetimes_raw_comma = generate_angle_bracket_params(
    sigs_raw,
    true,
    true,
    false,
    true,
    false,
    false,
    |s| format!("{}, ", s),
  );
  let call_param_types_native = generate_call_params(
    sigs_native,
    false,
    false,
    true,
    false,
    false,
    false,
    None,
  );
  let call_param_types_native_for_macro = generate_call_params(
    sigs_native,
    false,
    false,
    true,
    false,
    false,
    true,
    None,
  );
  let call_param_types_raw = generate_call_params(
    sigs_raw, true, false, true, false, false, false, None,
  );
  let call_param_types_raw_win64fix =
    generate_call_params(sigs_raw, true, true, true, false, false, false, None);
  let call_param_names_native = generate_call_params(
    sigs_native,
    false,
    false,
    false,
    true,
    false,
    false,
    None,
  );
  let call_param_names_native_closure_notused = generate_call_params(
    sigs_native,
    false,
    false,
    false,
    true,
    true,
    false,
    Some(&Default::default()),
  );
  let call_param_names_raw = generate_call_params(
    sigs_raw,
    true,
    false,
    false,
    true,
    false,
    false,
    Some(&used_inputs),
  );
  let call_params_full_native_notused = generate_call_params(
    sigs_native,
    false,
    false,
    true,
    true,
    false,
    false,
    Some(&Default::default()),
  );
  let call_params_full_raw = generate_call_params(
    sigs_raw,
    true,
    false,
    true,
    true,
    false,
    false,
    Some(&used_inputs),
  );
  let call_params_full_raw_win64fix = generate_call_params(
    sigs_raw,
    true,
    true,
    true,
    true,
    false,
    false,
    Some(&used_inputs),
  );
  let raw_to_native_conversions = gather_raw_to_native_conversions(sigs_native);

  let common_code = format!(
    r#"
{cb_comment}
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct {cb_name_uc}(Raw{cb_name_uc});

pub trait Into{cb_name_uc}:
  UnitType
  + Into<{cb_name_uc}>
  + {for_lifetimes_native}FnOnce{call_param_types_native}
{{ }}

impl<F> Into{cb_name_uc} for F where
  F: UnitType
    + Into<{cb_name_uc}>
    + {for_lifetimes_native}FnOnce{call_param_types_native}
{{ }}

#[macro_export]
macro_rules! impl_into_{cb_name_lc} {{
  () => {{
    impl $crate::support::UnitType
    + Into<{cb_name_uc}>
    + {for_lifetimes_native_for_macro}FnOnce{call_param_types_native_for_macro}  }};
}}
"#,
    cb_name_uc = cb_name_uc,
    cb_name_lc = cb_name_lc,
    cb_comment = cb_comment,
    for_lifetimes_native = for_lifetimes_native,
    for_lifetimes_native_for_macro = for_lifetimes_native_for_macro,
    call_param_types_native = call_param_types_native,
    call_param_types_native_for_macro = call_param_types_native_for_macro,
  );

  let abi_specific_code = if !use_win64fix {
    format!(
      r#"
type Raw{cb_name_uc} = {for_lifetimes_raw}extern "C" fn{call_param_types_raw};

impl<F> From<F> for {cb_name_uc}
where 
  F: UnitType
    + {for_lifetimes_native}FnOnce{call_param_types_native}
{{
  fn from(_: F) -> Self {{
    #[inline(always)]
    extern "C" fn adapter<{lifetimes_raw_comma}F: Into{cb_name_uc}>{call_params_full_raw} {{
      {raw_to_native_conversions}
      (F::get()){call_param_names_native}
    }}

    Self(adapter::<F>)
  }}
}}
"#,
      cb_name_uc = cb_name_uc,
      for_lifetimes_native = for_lifetimes_native,
      for_lifetimes_raw = for_lifetimes_raw,
      lifetimes_raw_comma = lifetimes_raw_comma,
      call_param_types_native = call_param_types_native,
      call_param_types_raw = call_param_types_raw,
      call_param_names_native = call_param_names_native,
      call_params_full_raw = call_params_full_raw,
      raw_to_native_conversions = raw_to_native_conversions,
    )
  } else {
    format!(
      r#"
#[cfg(target_family = "unix")]
type Raw{cb_name_uc} = {for_lifetimes_raw}extern "C" fn{call_param_types_raw};

#[cfg(all(target_family = "windows", target_arch = "x86_64"))]
type Raw{cb_name_uc} = {for_lifetimes_raw}extern "C" fn{call_param_types_raw_win64fix};

impl<F> From<F> for {cb_name_uc}
  where 
    F: UnitType
      + {for_lifetimes_native}FnOnce{call_param_types_native}
{{
  fn from(_: F) -> Self {{
    #[inline(always)]
    fn signature_adapter<{lifetimes_raw_comma}F: Into{cb_name_uc}>{call_params_full_raw} {{
      {raw_to_native_conversions}
      (F::get()){call_param_names_native}
    }}

    #[cfg(target_family = "unix")]
    #[inline(always)]
    extern "C" fn abi_adapter<{lifetimes_raw_comma}F: Into{cb_name_uc}>{call_params_full_raw} {{
      signature_adapter::<F>{call_param_names_raw}
    }}

    #[cfg(all(target_family = "windows", target_arch = "x86_64"))]
    #[inline(always)]
    extern "C" fn abi_adapter<{lifetimes_raw_comma}F: Into{cb_name_uc}>{call_params_full_raw_win64fix} {{
      unsafe {{
        std::ptr::write(return_value, signature_adapter::<F>{call_param_names_raw});
        return_value
      }}
    }}

    Self(abi_adapter::<F>)
  }}
}}
"#,
      cb_name_uc = cb_name_uc,
      for_lifetimes_native = for_lifetimes_native,
      for_lifetimes_raw = for_lifetimes_raw,
      lifetimes_raw_comma = lifetimes_raw_comma,
      call_param_types_native = call_param_types_native,
      call_param_types_raw = call_param_types_raw,
      call_param_types_raw_win64fix = call_param_types_raw_win64fix,
      call_param_names_native = call_param_names_native,
      call_param_names_raw = call_param_names_raw,
      call_params_full_raw = call_params_full_raw,
      call_params_full_raw_win64fix = call_params_full_raw_win64fix,
      raw_to_native_conversions = raw_to_native_conversions,
    )
  };

  let test_code = format!(
    r#"
#[cfg(test)]
fn mock_{cb_name_lc}<{lifetimes_native}>{call_params_full_native_notused} {{
  unimplemented!()
}}

#[test]
fn {cb_name_lc}_type_param() {{
  fn pass_by_type_param<F: Into{cb_name_uc}>(_: F) -> {cb_name_uc} {{
    F::get().into()
  }} 
  let _ = pass_by_type_param(mock_{cb_name_lc});
}}

#[test]
fn {cb_name_lc}_impl_into_trait() {{
  fn pass_by_impl_into_trait(f: impl Into<{cb_name_uc}>) -> {cb_name_uc} {{
    f.into()
  }}
  let _ = pass_by_impl_into_trait(mock_{cb_name_lc});
}}

#[test]
fn {cb_name_lc}_impl_into_macro() {{
  fn pass_by_impl_into_macro(f: impl_into_{cb_name_lc}!()) -> {cb_name_uc} {{
    f.into()
  }}
  let _ = pass_by_impl_into_macro(mock_{cb_name_lc});
  let _ = pass_by_impl_into_macro({call_param_names_native_closure_notused} unimplemented!());
}}
"#,
    cb_name_uc = cb_name_uc,
    cb_name_lc = cb_name_lc,
    lifetimes_native = lifetimes_native,
    call_param_names_native_closure_notused =
      call_param_names_native_closure_notused,
    call_params_full_native_notused = call_params_full_native_notused
  );

  let code = format!(
    "{common_code}\n{abi_specific_code}\n{test_code}",
    common_code = common_code,
    abi_specific_code = abi_specific_code,
    test_code = test_code,
  );

  code
}

#[allow(dead_code)]
fn comment_out(code: String) -> String {
  code
    .lines()
    .map(|s| format!("// {}\n", s))
    .collect::<String>()
}

fn visit_callback_definition<'tu>(
  e: Entity<'tu>,   // The typedef definition node.
  fn_ty: Type<'tu>, // The callback function prototype.
) -> Option<()> {
  let cb_name = get_flat_name_for_callback_type(e);
  let cb_comment = e.get_comment();
  let ret_ty = fn_ty.get_result_type()?;
  let arg_names = e
    .get_children()
    .into_iter()
    .filter(|c| c.get_kind() == EntityKind::ParmDecl)
    .map(|c| c.get_name());
  let arg_tys = fn_ty.get_argument_types()?;
  let sigs_raw = once(Sig::new_return(ret_ty))
    .chain(arg_names.zip(arg_tys).map(Sig::from))
    .collect();
  let sigs_raw = give_all_signature_params_a_name(sigs_raw);
  let sigs_native = convert_raw_signature_to_native(&sigs_raw);
  let used_inputs = gather_used_inputs(&sigs_native);
  let use_win64fix = return_value_requires_win64_stack_return_fix(&sigs_raw);
  let code = render_callback_definition(
    &cb_name,
    cb_comment.as_deref(),
    &sigs_native,
    &sigs_raw,
    used_inputs,
    use_win64fix,
  );
  if contains_unknown_cxx_types(&sigs_raw) {
    // println!("{}", comment_out(code));
  } else {
    println!("{}", code);
  }
  Some(())
}

fn visit_declaration<'tu>(
  _index: &mut CallbackIndex<'tu>,
  e: Entity<'tu>,
) -> Option<()> {
  if e.is_definition() {
    if let Some(ty) = e.get_typedef_underlying_type() {
      if ty.get_kind() == TypeKind::Pointer {
        if let Some(pointee_ty) = ty.get_pointee_type() {
          if pointee_ty.get_kind() == TypeKind::FunctionPrototype
            && is_type_used(e.get_translation_unit(), ty)
          {
            visit_callback_definition(e, pointee_ty);
          }
        }
      }
    }
  }
  Some(())
}

fn visit_v8_ns<'tu>(index: &mut CallbackIndex<'tu>, ns: Entity<'tu>) {
  ns.visit_children(|e, _| {
    if e.is_declaration() {
      visit_declaration(index, e);
      EntityVisitResult::Recurse
    } else {
      EntityVisitResult::Continue
    }
  });
}

fn visit_translation_unit<'tu>(translation_unit: &'tu TranslationUnit<'tu>) {
  let root = translation_unit.get_entity();
  let mut index = CallbackIndex::new();
  root.visit_children(|e, _| {
    if e.get_kind() == EntityKind::Namespace {
      if is_v8_ns(e) {
        visit_v8_ns(&mut index, e);
      }
      EntityVisitResult::Continue
    } else {
      EntityVisitResult::Recurse
    }
  });
}

pub fn generate(tu: &TranslationUnit) {
  println!("{}", boilerplate());
  visit_translation_unit(tu);
}

fn boilerplate() -> &'static str {
  r#"
// Copyright 2019-2020 the Deno authors. All rights reserved. MIT license.

//! # Why these `impl_into_some_callback!()` macros?
//!
//! It appears that Rust is unable to use information that is available from
//! super traits for type and/or lifetime inference purposes. This causes it to
//! rejects well formed closures for no reason at all. These macros provide
//! a workaround for this issue.
//!
//! ```rust,ignore
//! // First, require that *all* implementors of `MyCallback` also implement a
//! // `Fn(...)` supertrait.
//! trait MyCallback: Sized + for<'a> Fn(&'a u32) -> &'a u32 {}
//!
//! // Povide a blanket `MyCallback` impl for all compatible types. This makes
//! // `MyCallback` essentially an alias of `Fn(&u32) -> &u32`.
//! impl<F> MyCallback for F where F: Sized + for<'a> Fn(&'a u32) -> &'a u32 {}
//!
//! // Define two functions with a parameter of the trait we just defined.
//! // One function uses the shorthand 'MyCallback', the other uses exactly the
//! // same `for<'a> Fn(...)` notation as we did when specifying the supertrait.
//! fn do_this(callback: impl MyCallback) {
//!   let val = 123u32;
//!   let _ = callback(&val);
//! }
//! fn do_that(callback: impl for<'a> Fn(&'a u32) -> &'a u32) {
//!   let val = 456u32;
//!   let _ = callback(&val);
//! }
//!
//! // Both of the above functions will accept an ordinary function (with a
//! // matching signature) as the only argument.
//! fn test_cb(a: &u32) -> &u32 { a }
//! do_this(test_cb);   // Ok!
//! do_that(test_cb);   // Ok!
//!
//! // However, when attempting to do the same with a closure, Rust loses it
//! // as it tries to reconcile the type of the closure with `impl MyCallback`.
//! do_this(|a| a);     // "Type mismatch resolving..."
//! do_that(|a| a);     // Ok!
//!
//! // Note that even when we explicitly define the closure's argument and
//! // return types, the Rust compiler still wants nothing to do with it...
//! //   ⚠ Type mismatch resolving
//! //   ⚠ `for<'a> <[closure] as FnOnce<(&'a u32,)>>::Output == &'a u32`.
//! //   ⚠ Expected bound lifetime parameter 'a, found concrete lifetime.
//! do_this(|a: &u32| -> &u32 { a });
//!
//! // The function signature used in this example is short and simple, but
//! // real world `Fn` traits tend to get long and complicated. These macros
//! // are there to make closure syntax possible without replicating the full
//! // `Fn(...)` trait definition over and over again.
//! macro_rules! impl_my_callback {
//!   () => {
//!     impl MyCallback + for<'a> Fn(&'a u32) -> &'a u32
//!   };
//! }
//!
//! // It lets us define a function with a `MyCallback` parameter as follows:
//! fn do_such(callback: impl_my_callback!()) {
//!   let val = 789u32;
//!   let _ = callback(&val);
//! }
//!
//! // And, as expected, we can pass either a function or a closure for the
//! // first argument.
//! do_such(test_cb);   // Ok!
//! do_such(|a| a);     // Ok!
//! ```

#![allow(clippy::needless_lifetimes)]

use std::ffi::c_void;
use std::os::raw::c_int;

use crate::scope::CallbackScope;
use crate::support::Opaque;
use crate::support::UnitType;
use crate::Array;
use crate::Boolean;
use crate::Context;
use crate::FunctionCallbackArguments;
use crate::FunctionCallbackInfo;
use crate::HandleScope;
use crate::Integer;
use crate::Isolate;
use crate::Local;
use crate::Message;
use crate::Module;
use crate::Name;
use crate::Object;
use crate::Promise;
use crate::PromiseRejectMessage;
use crate::PropertyCallbackArguments;
use crate::PropertyCallbackInfo;
use crate::ReturnValue;
use crate::ScriptOrModule;
use crate::StartupData;
use crate::String;
use crate::Value;

// Placeholder types that don't have Rust bindings yet.
#[repr(C)] pub struct PropertyDescriptor(Opaque);
#[repr(C)] pub enum  AccessType { _TODO }
#[repr(C)] pub enum  AtomicsWaitEvent { _TODO }
#[repr(C)] pub enum  CrashKeyId { _TODO }
#[repr(C)] pub enum  GCCallbackFlags { _TODO }
#[repr(C)] pub enum  GCType { _TODO }
#[repr(C)] pub enum  PromiseHookType { _TODO }
#[repr(C)] pub enum  UseCounterFeature { _TODO }
"#
  .trim()
}
