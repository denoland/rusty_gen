#![allow(dead_code)]

use clang::*;
use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashSet;
use std::convert::AsRef;
use std::fmt::{self, Display, Formatter};
use std::hash::Hash;
use std::io;
use std::io::Write;
use std::iter::once;
use std::iter::IntoIterator;
use std::process::Command;
use std::process::Output;
use std::process::Stdio;
use std::vec;

type CallbackIndex<'tu> = Vec<String>;

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

fn where_is_type_used<'tu>(
  translation_unit: &'tu TranslationUnit<'tu>,
  ty: Type<'tu>,
) -> Vec<Entity<'tu>> {
  let can_ty = ty.get_canonical_type();
  let root = translation_unit.get_entity();
  let mut refs = Vec::<Entity>::new();
  root.visit_children(|e, _| {
    if e.get_storage_class().is_some()
      && e
        .get_type()
        .map(|var_ty| var_ty.get_canonical_type() == can_ty)
        .unwrap_or(false)
    {
      refs.push(e);
      EntityVisitResult::Continue
    } else {
      EntityVisitResult::Recurse
    }
  });
  refs
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

fn is_v8_isolate_type<'tu>(ty: Type<'tu>, name: &str) -> Option<Type<'tu>> {
  let _def = ty
    .get_declaration()
    .filter(|d| d.get_name().map(|n| n == name).unwrap_or(false))
    .filter(|d| {
      d.get_semantic_parent()
        .map(|e| is_v8_top_level_class(e, "Isolate"))
        .unwrap_or(false)
    })?;
  Some(ty)
}

fn is_v8_isolate_type_pointee<'tu>(
  ty: Type<'tu>,
  name: &str,
) -> Option<Type<'tu>> {
  ty.get_pointee_type()
    .and_then(|ty| is_v8_isolate_type(ty, name))
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
    (None, ..) => TypeParams::Zero,
    (Some(p), None, _) => TypeParams::One(p?),
    (Some(p), Some(q), None) => TypeParams::Two(p?, q?),
    _ => panic!("More than 2 type parameters"),
  };
  Some(info)
}

fn is_std_or_root_ns(mut e: Entity) -> bool {
  loop {
    match e.get_kind() {
      EntityKind::Namespace => {
        if e
          .get_name()
          .map(|name| ["std", "__1"].contains(&&*name))
          .to_owned()
          .unwrap_or(false)
        {
          if let Some(ep) = get_named_semantic_parent(e) {
            e = ep;
            continue;
          }
        }
      }
      EntityKind::TranslationUnit => break true,
      _ => {}
    }
    break false;
  }
}

fn is_std_type<'tu>(ty: Type<'tu>, name: &str) -> bool {
  ty.get_declaration()
    .map(|d| d.get_definition().unwrap_or(d))
    .filter(|d| d.get_name().map(|n| n == name).unwrap_or(false))
    .filter(|d| {
      get_named_semantic_parent(*d)
        .map(|p| is_std_or_root_ns(p))
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

#[derive(Debug, Clone)]
enum SigType<'tu> {
  Void {
    disposition: Disposition,
  },
  Bool,
  Char {
    disposition: Disposition,
    signed: Option<bool>,
  },
  Int {
    disposition: Disposition,
    signed: bool,
  },
  IntFixedSize {
    disposition: Disposition,
    bits: u8,
    signed: bool,
  },
  IntPtrSize {
    signed: bool,
  },
  Float {
    bits: u8,
  },
  Isolate {
    disposition: Disposition,
  },
  CallbackScope {
    param_var_name: String,
    param_expression: String,
    with_context: bool,
  },
  Local {
    inner_ty: Type<'tu>,
    inner_ty_name: String,
  },
  MaybeLocal {
    inner_ty_name: String,
  },
  ModifyCodeGenerationFromStringsResult,
  PromiseRejectMessage,
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
  CString {
    disposition: Disposition,
    source_ty: Box<SigType<'tu>>,
  },
  CxxString {
    disposition: Disposition,
  },
  String {
    ty_name: String,
    disposition: Disposition,
  },
  Struct {
    ty_name: String,
    disposition: Disposition,
  },
  Enum {
    ty_name: String,
  },
  ByteSlice {
    disposition: Disposition,
    ptr_name: String,
    len_name: String,
    needs_cast: bool,
  },
  Unknown(Type<'tu>),
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash)]
struct DisplayMode {
  pub raw: bool,
  pub win64_stack_return_fix: bool,
  pub for_macro: bool,
}

thread_local! {
  static DISPLAY_MODE: Cell<DisplayMode> = Default::default();
}

impl DisplayMode {
  fn set(new_mode: Self) {
    DISPLAY_MODE.with(|m| m.set(new_mode));
  }

  fn get() -> Self {
    DISPLAY_MODE.with(|m| m.get())
  }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Lifetime {
  Anon,
  Named(Cow<'static, str>),
  Static,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
enum Disposition {
  Owned,
  ConstAuto,
  MutAuto,
  Cell,
  ConstRef,
  MutRef,
  ConstPtr,
  MutPtr,
}

impl Default for Disposition {
  fn default() -> Self {
    Self::Owned
  }
}

impl Disposition {
  pub fn auto(pointee_ty: Type<'_>) -> Self {
    if pointee_ty.is_const_qualified() {
      Self::ConstAuto
    } else {
      Self::MutAuto
    }
  }

  pub fn as_set_raw(self, raw: bool) -> Self {
    match self {
      Self::ConstAuto if raw => Self::ConstPtr,
      Self::ConstAuto if !raw => Self::ConstRef,
      Self::MutAuto if raw => Self::MutPtr,
      Self::MutAuto if !raw => Self::MutRef,
      other => other,
    }
  }

  pub fn as_native(self) -> Self {
    self.as_set_raw(false)
  }

  pub fn as_raw(self) -> Self {
    self.as_set_raw(true)
  }

  pub fn is_owned(self) -> bool {
    match self {
      Self::Owned => true,
      _ => false,
    }
  }

  pub fn is_address(self) -> bool {
    match self {
      Self::Owned => false,
      _ => true,
    }
  }

  pub fn is_const_address(self) -> bool {
    match self {
      Self::ConstAuto | Self::ConstRef | Self::ConstPtr => true,
      _ => false,
    }
  }

  pub fn is_mut_address(self) -> bool {
    match self {
      Self::MutAuto | Self::MutRef | Self::MutPtr => true,
      _ => false,
    }
  }

  pub fn fmt_type(self, ty_name: impl Display) -> String {
    let raw = DisplayMode::get().raw;
    match self {
      Self::Cell if !raw => format!("&'static Cell<{}>", ty_name),
      _ => format!("{}{}", self, ty_name),
    }
  }
}

impl Display for Disposition {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Self::ConstAuto | Self::MutAuto => {
        write!(f, "{}", self.as_set_raw(DisplayMode::get().raw))
      }
      Self::ConstRef => write!(f, "&"),
      Self::MutRef => write!(f, "&mut "),
      Self::ConstPtr => write!(f, "*const "),
      Self::MutPtr => write!(f, "*mut "),
      Self::Owned => Ok(()),
      Self::Cell => panic!("use Disposition::fmt_type"),
    }
  }
}

impl From<&'static str> for Lifetime {
  fn from(name: &'static str) -> Self {
    Self::Named(name.into())
  }
}

impl Display for Lifetime {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let for_macro = DisplayMode::get().for_macro;
    match self {
      Self::Anon => write!(f, "'_"),
      Self::Named(name) if !for_macro => write!(f, "'{}", name),
      Self::Named(name) if for_macro => write!(f, "'__{}", name),
      Self::Static => write!(f, "'static"),
      _ => unreachable!(),
    }
  }
}

#[derive(Default)]
struct TypeInfo {
  pub disposition: Disposition,
  pub name: Cow<'static, str>,
  pub lifetimes: Vec<Lifetime>,
  pub type_args: Vec<TypeInfo>,
  pub win64_return_value_on_stack: bool,
}

impl Display for TypeInfo {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let angle_bracket_params = self
      .lifetimes
      .iter()
      .map(|l| l.to_string())
      .chain(self.type_args.iter().map(|p| p.to_string()))
      .collect::<Vec<_>>()
      .join(", ");
    let name_and_params = if angle_bracket_params.is_empty() {
      format!("{}", self.name)
    } else {
      format!("{}<{}>", self.name, angle_bracket_params)
    };
    write!(f, "{}", self.disposition.fmt_type(name_and_params),)?;
    Ok(())
  }
}

impl TypeInfo {
  fn from(sig: &SigType) -> TypeInfo {
    let DisplayMode { raw, .. } = DisplayMode::get();
    use Disposition as D;
    use SigType as S;
    use TypeInfo as I;
    match sig {
      S::Void {
        disposition: D::Owned,
      } => I {
        name: "()".into(),
        ..I::default()
      },
      S::Void { disposition } => I {
        disposition: disposition.as_raw(),
        name: "c_void".into(),
        ..I::default()
      },
      S::Bool => I {
        name: "bool".into(),
        ..I::default()
      },
      S::Char {
        signed: None,
        disposition,
      } => I {
        disposition: disposition.as_raw(),
        name: "c_char".into(),
        ..I::default()
      },
      S::Char {
        signed: Some(false),
        disposition,
      } => I {
        disposition: disposition.as_raw(),
        name: "c_uchar".into(),
        ..I::default()
      },
      S::Char { .. } => unreachable!(),
      S::Int {
        signed: false,
        disposition,
      } => I {
        disposition: disposition.as_raw(),
        name: "c_uint".into(),
        ..I::default()
      },
      S::Int {
        signed: true,
        disposition,
      } => I {
        disposition: disposition.as_raw(),
        name: "c_int".into(),
        ..I::default()
      },
      S::IntFixedSize {
        disposition,
        signed: false,
        bits,
      } => I {
        disposition: *disposition,
        name: format!("u{}", bits).into(),
        ..I::default()
      },
      S::IntFixedSize {
        disposition,
        signed: true,
        bits,
      } => I {
        disposition: *disposition,
        name: format!("i{}", bits).into(),
        ..I::default()
      },
      S::IntPtrSize { signed: false } => I {
        name: "usize".into(),
        ..I::default()
      },
      S::IntPtrSize { signed: true } => I {
        name: "isize".into(),
        ..I::default()
      },
      S::Float { bits: 64 } if raw => I {
        name: "c_double".into(),
        ..I::default()
      },
      S::Float { bits } if !raw => I {
        name: format!("f{}", bits).into(),
        ..I::default()
      },
      S::Float { .. } => unreachable!(),
      S::Isolate { disposition } => I {
        disposition: *disposition,
        name: "Isolate".into(),
        ..I::default()
      },
      S::CallbackScope { with_context, .. } => I {
        disposition: D::MutRef,
        name: "HandleScope".into(),
        lifetimes: vec!["s".into()],
        type_args: once(I {
          name: "()".into(),
          ..I::default()
        })
        .filter(|_| !with_context)
        .collect(),
        ..I::default()
      },
      S::Local { inner_ty_name, .. } => I {
        name: "Local".into(),
        lifetimes: vec!["s".into()],
        type_args: vec![I {
          name: inner_ty_name.clone().into(),
          ..I::default()
        }],
        win64_return_value_on_stack: true,
        ..I::default()
      },
      S::MaybeLocal { inner_ty_name, .. } => I {
        name: "Option".into(),
        type_args: vec![I {
          name: "Local".into(),
          lifetimes: vec!["s".into()],
          type_args: vec![I {
            name: inner_ty_name.clone().into(),
            ..I::default()
          }],
          ..I::default()
        }],
        win64_return_value_on_stack: true,
        ..I::default()
      },
      S::ModifyCodeGenerationFromStringsResult => I {
        name: "ModifyCodeGenerationFromStringsResult".into(),
        lifetimes: vec!["s".into()],
        win64_return_value_on_stack: true,
        ..I::default()
      },
      S::PromiseRejectMessage => I {
        name: "PromiseRejectMessage".into(),
        lifetimes: vec!["s".into()],
        ..I::default()
      },
      S::CallbackInfo { ty_name, .. } => I {
        disposition: D::ConstPtr,
        name: ty_name.clone().into(),
        ..I::default()
      },
      S::CallbackArguments { ty_name, .. } => I {
        name: ty_name.clone().into(),
        lifetimes: vec!["s".into()],
        ..I::default()
      },
      S::CallbackReturnValue { ret_ty_name, .. } => I {
        name: "ReturnValue".into(),
        lifetimes: vec!["s".into()],
        type_args: vec![I {
          name: ret_ty_name.clone().into(),
          ..I::default()
        }],
        ..I::default()
      },
      S::String { disposition, .. } => I {
        disposition: *disposition,
        name: if disposition.is_address() {
          "str"
        } else {
          "String"
        }
        .into(),
        ..I::default()
      },
      S::CString { disposition, .. } => I {
        disposition: *disposition,
        name: if disposition.is_address() {
          "CStr"
        } else {
          "CString"
        }
        .into(),
        ..I::default()
      },
      S::CxxString { disposition } => I {
        disposition: *disposition,
        name: "CxxString".into(),
        ..I::default()
      },
      S::Struct {
        disposition,
        ty_name,
      } => I {
        disposition: *disposition,
        name: ty_name.clone().into(),
        ..I::default()
      },
      S::Enum { ty_name } => I {
        name: ty_name.clone().into(),
        ..I::default()
      },
      S::ByteSlice { disposition, .. } => I {
        disposition: disposition.as_native(),
        name: "[u8]".into(),
        ..I::default()
      },
      S::Unknown(ty) => I {
        name: format!("T??`{}`", ty.get_display_name()).into(),
        ..I::default()
      },
    }
  }
}

fn collect_named_lifetime_params<I>(type_infos: I) -> Vec<Lifetime>
where
  I: IntoIterator<Item = TypeInfo>,
{
  let mut set = HashSet::new();
  type_infos
    .into_iter()
    .flat_map(|ti| {
      ti.lifetimes
        .clone()
        .into_iter()
        .filter_map(|lt| match lt {
          lt @ Lifetime::Named(_) => Some(lt),
          _ => None,
        })
        .chain(collect_named_lifetime_params(ti.type_args).into_iter())
    })
    .filter(|name| set.insert(name.clone()))
    .collect::<Vec<_>>()
}

fn generate_angle_bracket_params<'tu>(
  sigs: &[Sig<'tu>],
  include_return_type: bool,
  mode: DisplayMode,
  wrap_fn: impl Fn(String) -> String,
) -> String {
  DisplayMode::set(mode);
  let type_infos = sigs
    .iter()
    .filter_map(|sig| match sig {
      Sig {
        id: SigIdent::Param(_),
        ty,
      } => Some(ty),
      Sig {
        id: SigIdent::Return,
        ty,
      } if include_return_type => Some(ty),
      _ => None,
    })
    .map(|ty| TypeInfo::from(ty));
  let lifetimes = collect_named_lifetime_params(type_infos)
    .into_iter()
    .map(|lt| lt.to_string())
    .collect::<Vec<_>>()
    .join(", ");
  if lifetimes.is_empty() {
    lifetimes
  } else {
    wrap_fn(lifetimes)
  }
}

impl<'tu> Display for SigType<'tu> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{}", TypeInfo::from(self))
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

  pub fn generate_call_signature<R>(
    &self,
    rest: R,
    with_types: bool,
    with_names: bool,
    closure_style: bool,
    used_inputs: Option<&HashSet<String>>,
  ) -> String
  where
    R: Iterator<Item = Sig<'tu>> + Clone,
  {
    let DisplayMode {
      raw,
      win64_stack_return_fix,
      ..
    } = DisplayMode::get();
    let gen_rest = |mut rest: R| {
      let next = rest.next();
      next
        .map(|n| {
          n.generate_call_signature(
            rest,
            with_types,
            with_names,
            closure_style,
            used_inputs,
          )
        })
        .unwrap_or_default()
    };
    let fmt_separator = || {
      if with_names && with_types {
        ": "
      } else {
        ""
      }
    };
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
        format!("{}{}", fmt_name_prefix(v), v)
      } else {
        Default::default()
      }
    };
    let fmt_type = |v| {
      if with_types {
        format!("{}", v)
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
        format!("(\n{}    )\n", gen_rest(rest))
      }
      Sig {
        id: I::Return,
        ty: ret_ty,
      } => {
        let mut rti = TypeInfo::from(ret_ty);
        if !rti.lifetimes.is_empty() {
          let param_lifetimes = rest
            .clone()
            .into_iter()
            .map(|sig| TypeInfo::from(&sig.ty))
            .flat_map(|ti| ti.lifetimes.into_iter())
            .collect::<HashSet<_>>();
          rti.lifetimes = rti
            .lifetimes
            .into_iter()
            .map(|lt| match lt {
              lt @ Lifetime::Named(_) if !param_lifetimes.contains(&lt) => {
                Lifetime::Static
              }
              lt => lt,
            })
            .collect();
        }
        format!("(\n{}    ) -> {}\n", gen_rest(rest), rti)
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
        ty: SigType::CallbackScope { param_var_name, .. },
        ..
      } => {
        used_inputs.insert(param_var_name);
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
        ty: SigType::ByteSlice {
          ptr_name, len_name, ..
        },
        ..
      } => {
        used_inputs.insert(ptr_name);
        used_inputs.insert(len_name);
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
    R: Clone + Iterator<Item = Sig<'tu>>,
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
        ty: SigType::Int { disposition, .. },
      }
      | Sig {
        id: SigIdent::Param(Some(name)),
        ty: SigType::Isolate { disposition },
      }
      | Sig {
        id: SigIdent::Param(Some(name)),
        ty: SigType::Struct { disposition, .. },
      } if disposition.is_address() => format!(
        "  let {} = unsafe {{ {}*{} }};\n{}",
        name,
        disposition,
        name,
        gen_rest(rest)
      ),
      Sig {
        id: SigIdent::Param(Some(name)),
        ty:
          SigType::CString {
            disposition,
            source_ty,
          },
      } if disposition.is_const_address() => match &**source_ty {
        SigType::Char { signed: None, .. } => format!(
          "  let {} = unsafe {{ CStr::from_ptr({}) }};\n{}",
          name,
          name,
          gen_rest(rest)
        ),
        SigType::CxxString { .. } => format!(
          "  let {} = <&CStr>::from(unsafe {{ &*{} }});\n{}",
          name,
          name,
          gen_rest(rest)
        ),
        _ => unreachable!(),
      },
      Sig {
        id: SigIdent::Param(Some(name)),
        ty: SigType::CallbackScope {
          param_expression, ..
        },
      } => format!(
        "  let {} = &mut unsafe {{ CallbackScope::new({}) }};\n{}",
        name,
        param_expression,
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
      Sig {
        id: SigIdent::Param(Some(name)),
        ty:
          SigType::ByteSlice {
            disposition,
            ptr_name,
            len_name,
            needs_cast,
          },
      } => {
        let method = match disposition.as_native() {
          Disposition::ConstRef => "from_raw_parts",
          Disposition::MutRef => "from_raw_parts_mut",
          _ => unreachable!(),
        };
        let cast = match needs_cast {
          true => format!(" as {} u8", disposition.as_raw()),
          false => "".to_owned(),
        };
        format!(
          "  let {} = unsafe {{ slice::{}({}{}, {}) }};\n{}",
          name,
          method,
          ptr_name,
          cast,
          len_name,
          gen_rest(rest)
        )
      }
      Sig {
        id: SigIdent::Return,
        ty:
          SigType::IntFixedSize {
            disposition: Disposition::Cell,
            signed,
            bits: 32,
          },
      } => format!(
        "{}.as_ptr()",
        Sig {
          id: SigIdent::Return,
          ty: SigType::Int {
            disposition: Disposition::MutPtr,
            signed: *signed
          }
        }
        .gather_raw_to_native_conversions(rest)
      ),
      sig @ Sig {
        id: SigIdent::Return,
        ..
      } => {
        let params = once(sig.clone()).chain(rest.clone()).collect::<Vec<_>>();
        let call_params = generate_call_params(
          &params,
          DisplayMode {
            ..Default::default()
          },
          false,
          true,
          false,
          None,
        );
        format!("{}  (F::get()){}", gen_rest(rest), call_params)
      }
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
        disposition: Disposition::auto(pty),
      }
    } else if ty.get_kind() == K::Bool {
      M::Bool
    } else if let Some(pty) =
      ty.get_pointee_type().filter(|pty| match pty.get_kind() {
        K::CharS | K::CharU => true,
        _ => false,
      })
    {
      M::Char {
        disposition: Disposition::auto(pty),
        signed: None,
      }
    } else if let Some(pty) = ty
      .get_pointee_type()
      // .and_then(|pty| pty.get_modified_type())
      .filter(|&pty| is_std_type(pty, "string"))
    {
      M::CxxString {
        disposition: Disposition::auto(pty),
      }
    } else if let Some(pty) = ty
      .get_pointee_type()
      .filter(|pty| pty.get_kind() == K::UChar)
    {
      M::Char {
        disposition: Disposition::auto(pty),
        signed: Some(false),
      }
    } else if ty.get_kind() == K::Int {
      M::Int {
        disposition: Disposition::Owned,
        signed: true,
      }
    } else if let Some(pty) =
      ty.get_pointee_type().filter(|pty| pty.get_kind() == K::Int)
    {
      M::Int {
        disposition: Disposition::auto(pty),
        signed: true,
      }
    } else if is_std_type(ty, "int32_t") {
      M::IntFixedSize {
        bits: 32,
        signed: true,
        disposition: Disposition::Owned,
      }
    } else if is_std_type(ty, "int64_t") {
      M::IntFixedSize {
        bits: 64,
        signed: true,
        disposition: Disposition::Owned,
      }
    } else if is_std_type(ty, "uint32_t") {
      M::IntFixedSize {
        bits: 32,
        signed: false,
        disposition: Disposition::Owned,
      }
    } else if is_std_type(ty, "uint64_t") {
      M::IntFixedSize {
        bits: 64,
        signed: false,
        disposition: Disposition::Owned,
      }
    } else if is_std_type(ty, "ssize_t") || is_std_type(ty, "intptr_t") {
      M::IntPtrSize { signed: true }
    } else if is_std_type(ty, "size_t") || is_std_type(ty, "uintptr_t") {
      M::IntPtrSize { signed: false }
    } else if ty.get_kind() == K::Double {
      M::Float { bits: 64 }
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
        disposition: Disposition::auto(pty),
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
    } else if let Some(_ty) =
      is_v8_type(ty, "ModifyCodeGenerationFromStringsResult")
    {
      M::ModifyCodeGenerationFromStringsResult
    } else if let Some(_ty) = is_v8_type(ty, "PromiseRejectMessage") {
      M::PromiseRejectMessage
    } else if let Some(_ty) = is_v8_type(ty, "StartupData") {
      M::Struct {
        ty_name: "StartupData".to_owned(),
        disposition: Disposition::Owned,
      }
    } else if let Some(pty) = is_v8_type_pointee(ty, "JitCodeEvent") {
      M::Struct {
        ty_name: "JitCodeEvent".to_owned(),
        disposition: Disposition::auto(pty),
      }
    } else if let Some(pty) = is_v8_type_pointee(ty, "PropertyDescriptor") {
      M::Struct {
        ty_name: "PropertyDescriptor".to_owned(),
        disposition: Disposition::auto(pty),
      }
    } else if let Some(pty) =
      is_v8_isolate_type_pointee(ty, "AtomicsWaitWakeHandle")
    {
      M::Struct {
        ty_name: "AtomicsWaitWakeHandle".to_owned(),
        disposition: Disposition::auto(pty),
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
      Self::Void { disposition } => disposition.is_address(),
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

fn generate_call_params<'tu>(
  sigs: &[Sig<'tu>],
  mode: DisplayMode,
  with_types: bool,
  with_names: bool,
  closure_style: bool,
  used_inputs: Option<&HashSet<String>>,
) -> String {
  DisplayMode::set(mode);
  let call_params = gather_recursively_with(sigs.to_owned(), |first, rest| {
    first.generate_call_signature(
      rest,
      with_types,
      with_names,
      closure_style,
      used_inputs,
    )
  });
  call_params
}

fn contains_unknown_cxx_types<'tu>(sigs: &[Sig<'tu>]) -> Option<Vec<String>> {
  let unk = sigs
    .iter()
    .filter_map(|sig| match sig {
      Sig {
        ty: SigType::Unknown(ty),
        ..
      } => Some(ty.get_display_name()),
      _ => None,
    })
    .collect::<Vec<_>>();
  if unk.is_empty() {
    None
  } else {
    Some(unk)
  }
}

fn gather_raw_to_native_conversions<'tu>(sigs: &[Sig<'tu>]) -> String {
  DisplayMode::set(Default::default());
  gather_recursively_with(sigs.to_owned(), |first, rest| {
    first.gather_raw_to_native_conversions(rest)
  })
  .trim_end()
  .to_owned()
}

fn gather_used_inputs<'tu>(sigs_native: &[Sig<'tu>]) -> HashSet<String> {
  DisplayMode::set(Default::default());
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
        id: SigIdent::Param(Some(name)),
      } if type_has_base_class_in_v8_ns(inner_ty, "Context") => {
        Some((name.clone(), name.clone(), true))
      }
      _ => None,
    })
    // If no Local<Context> found, look for other options.
    .or_else(|| {
      sigs.iter().find_map(|sig| match sig {
        Sig {
          ty: SigType::Local { inner_ty, .. },
          id: SigIdent::Param(Some(name)),
        } if type_has_base_class_in_v8_ns(inner_ty, "Object")
          || type_has_base_class_in_v8_ns(inner_ty, "Message") =>
        {
          Some((name.clone(), name.clone(), true))
        }
        Sig {
          ty: SigType::PromiseRejectMessage,
          id: SigIdent::Param(Some(name)),
        } => Some((name.clone(), format!("&{}", &name), true)),
        Sig {
          ty: SigType::CallbackInfo { .. },
          id: SigIdent::Param(Some(name)),
        } => Some((name.clone(), format!("&*{}", &name), true)),
        _ => None,
      })
    })
    // If any of the params or the return type has an `'s` (scope) lifetime,
    // the last resort is to create a CallbackScope<'s, ()> from just the
    // Isolate handle.
    .or_else(|| {
      DisplayMode::set(DisplayMode {
        raw: true,
        ..Default::default()
      });
      let has_lifetimes = !collect_named_lifetime_params(
        sigs.iter().map(|sig| TypeInfo::from(&sig.ty)),
      )
      .is_empty();
      if !has_lifetimes {
        return None;
      }
      // Confirmed that there are lifetimes.
      sigs.iter().find_map(|d| match d {
        Sig {
          ty: SigType::Isolate { .. },
          id: SigIdent::Param(Some(name)),
        } => Some((
          name.clone(),
          format!("{}*{}", Disposition::MutRef, name),
          false,
        )),
        _ => None,
      })
    })
    .map(|(param_var_name, param_expression, with_context)| Sig {
      ty: SigType::CallbackScope {
        param_var_name,
        param_expression,
        with_context,
      },
      id: "scope".into(),
    });

  let has_scope = scope_param.is_some();

  sigs
    .iter()
    .cloned()
    .map(|sig| match sig {
      // Change the return type to an &'static Cell if the function has a &mut i32
      // output and no scope.
      Sig { id: SigIdent::Return, ty: SigType::Int { disposition, signed }} if disposition.is_mut_address() && !has_scope => {
        Sig { id: SigIdent::Return, ty: SigType::Int { disposition: Disposition::Cell, signed }}
      },
      sig => sig
    })
    .flat_map(move |sig| match sig {
      // Keep the return type at the beginning of the list.
      // Insert the CallbackScopeCallbackScope (if any) right after the return type.
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
    .map(|sig| {
      let Sig { ty, id } = sig;
      let ty = match ty {
        SigType::Int { disposition, signed } =>
          SigType::IntFixedSize { disposition, signed, bits: 32 },
        SigType::Char { disposition, signed: None } =>
          SigType::CString { disposition, source_ty: Box::new(ty) },
        SigType::CxxString { disposition } =>
          SigType::CString { disposition, source_ty: Box::new(ty) },
        ty => ty
      };
      Sig { ty, id }
      })
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
    // Find an adjacent set of two parameters: first a `*mut|*const c_void`,
    // followed by a `usize` parameter. Then second parameter must have `len`
    // in its name to filter false positives.
    .map(Some)
    .chain(once(None))
    .filter_map({ let mut prev_slot: Option<_> = None; move |sig: Option<_>| {
      match (prev_slot.take(), sig) {
        (Some(Sig {
          ty: SigType::Void { disposition },
          id: SigIdent::Param(Some(ptr_name))
        }),
        Some(Sig {
          ty: SigType::IntPtrSize { signed: false},
          id: SigIdent::Param(Some(len_name))
        })) if disposition.is_address() && len_name.contains("len") => {
          let name = ptr_name.clone();
          Some(Sig {
            ty: SigType::ByteSlice { disposition, ptr_name, len_name, needs_cast: true },
            id: SigIdent::Param(Some(name))
          })
        }
        (Some(Sig {
          ty: SigType::Char { signed: Some(false), disposition },
          id: SigIdent::Param(Some(ptr_name))
        }),
        Some(Sig {
          ty: SigType::IntPtrSize { signed: false},
          id: SigIdent::Param(Some(len_name))
        })) if disposition.is_address() && len_name.contains("len") => {
          let name = ptr_name.clone();
          Some(Sig {
            ty: SigType::ByteSlice { disposition, ptr_name, len_name, needs_cast: false },
            id: SigIdent::Param(Some(name))
          })
        }
        (prev, sig) => {
          prev_slot = sig;
          prev
        }
      }
    }})
    .collect::<Vec<_>>()
}

fn return_value_requires_win64_stack_return_fix<'tu>(
  sigs: &[Sig<'tu>],
) -> bool {
  sigs
    .iter()
    .filter_map(|sig| match sig {
      Sig {
        id: SigIdent::Return,
        ty,
      } => Some(ty),
      _ => None,
    })
    .map(|ty| TypeInfo::from(ty))
    .map(|ti| ti.win64_return_value_on_stack)
    .next()
    .unwrap()
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
    DisplayMode::default(),
    |s| format!("for<{}> ", s),
  );
  let for_lifetimes_native_for_macro = generate_angle_bracket_params(
    sigs_native,
    false,
    DisplayMode {
      for_macro: true,
      ..Default::default()
    },
    |s| format!("for<{}> ", s),
  );
  let lifetimes_native = generate_angle_bracket_params(
    sigs_native,
    false,
    DisplayMode::default(),
    |s| s,
  );
  let for_lifetimes_in_raw = generate_angle_bracket_params(
    sigs_raw,
    false,
    DisplayMode {
      raw: true,
      ..Default::default()
    },
    |s| format!("for<{}> ", s),
  );
  let for_lifetimes_inout_raw = generate_angle_bracket_params(
    sigs_raw,
    true,
    DisplayMode {
      raw: true,
      ..Default::default()
    },
    |s| format!("for<{}> ", s),
  );
  let lifetimes_in_raw_comma = generate_angle_bracket_params(
    sigs_raw,
    false,
    DisplayMode {
      raw: true,
      ..Default::default()
    },
    |s| format!("{}, ", s),
  );
  let lifetimes_inout_raw_comma = generate_angle_bracket_params(
    sigs_raw,
    true,
    DisplayMode {
      raw: true,
      ..Default::default()
    },
    |s| format!("{}, ", s),
  );
  let call_param_types_native = generate_call_params(
    sigs_native,
    Default::default(),
    true,
    false,
    false,
    None,
  );
  let call_param_types_native_for_macro = generate_call_params(
    sigs_native,
    DisplayMode {
      for_macro: true,
      ..Default::default()
    },
    true,
    false,
    false,
    None,
  );
  let call_param_types_raw = generate_call_params(
    sigs_raw,
    DisplayMode {
      raw: true,
      ..Default::default()
    },
    true,
    false,
    false,
    None,
  );
  let call_param_types_raw_win64fix = generate_call_params(
    sigs_raw,
    DisplayMode {
      raw: true,
      win64_stack_return_fix: true,
      ..Default::default()
    },
    true,
    false,
    false,
    None,
  );
  let _call_param_names_native = generate_call_params(
    sigs_native,
    Default::default(),
    false,
    true,
    false,
    None,
  );
  let call_param_names_native_closure_notused = generate_call_params(
    sigs_native,
    Default::default(),
    false,
    true,
    true,
    Some(&Default::default()),
  );
  let call_param_names_raw = generate_call_params(
    sigs_raw,
    DisplayMode {
      raw: true,
      ..Default::default()
    },
    false,
    true,
    false,
    Some(&used_inputs),
  );
  let call_params_full_native_notused = generate_call_params(
    sigs_native,
    Default::default(),
    true,
    true,
    false,
    Some(&Default::default()),
  );
  let call_params_full_raw = generate_call_params(
    sigs_raw,
    DisplayMode {
      raw: true,
      ..Default::default()
    },
    true,
    true,
    false,
    Some(&used_inputs),
  );
  let call_params_full_raw_win64fix = generate_call_params(
    sigs_raw,
    DisplayMode {
      raw: true,
      win64_stack_return_fix: true,
      ..Default::default()
    },
    true,
    true,
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
type Raw{cb_name_uc} = {for_lifetimes_in_raw}extern "C" fn{call_param_types_raw};

impl<F> From<F> for {cb_name_uc}
where
  F: UnitType
    + {for_lifetimes_native}FnOnce{call_param_types_native}
{{
  fn from(_: F) -> Self {{
    #[inline(always)]
    extern "C" fn adapter<{lifetimes_in_raw_comma}F: Into{cb_name_uc}>{call_params_full_raw} {{
      {raw_to_native_conversions}
    }}

    Self(adapter::<F>)
  }}
}}
"#,
      cb_name_uc = cb_name_uc,
      for_lifetimes_native = for_lifetimes_native,
      for_lifetimes_in_raw = for_lifetimes_in_raw,
      lifetimes_in_raw_comma = lifetimes_in_raw_comma,
      call_param_types_native = call_param_types_native,
      call_param_types_raw = call_param_types_raw,
      call_params_full_raw = call_params_full_raw,
      raw_to_native_conversions = raw_to_native_conversions,
    )
  } else {
    format!(
      r#"
#[cfg(target_family = "unix")]
type Raw{cb_name_uc} = {for_lifetimes_in_raw}extern "C" fn{call_param_types_raw};

#[cfg(all(target_family = "windows", target_arch = "x86_64"))]
type Raw{cb_name_uc} = {for_lifetimes_inout_raw}extern "C" fn{call_param_types_raw_win64fix};

impl<F> From<F> for {cb_name_uc}
  where
    F: UnitType
      + {for_lifetimes_native}FnOnce{call_param_types_native}
{{
  fn from(_: F) -> Self {{
    #[inline(always)]
    fn signature_adapter<{lifetimes_in_raw_comma}F: Into{cb_name_uc}>{call_params_full_raw} {{
      {raw_to_native_conversions}
    }}

    #[cfg(target_family = "unix")]
    #[inline(always)]
    extern "C" fn abi_adapter<{lifetimes_in_raw_comma}F: Into{cb_name_uc}>{call_params_full_raw} {{
      signature_adapter::<F>{call_param_names_raw}
    }}

    #[cfg(all(target_family = "windows", target_arch = "x86_64"))]
    #[inline(always)]
    extern "C" fn abi_adapter<{lifetimes_inout_raw_comma}F: Into{cb_name_uc}>{call_params_full_raw_win64fix} {{
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
      for_lifetimes_in_raw = for_lifetimes_in_raw,
      for_lifetimes_inout_raw = for_lifetimes_inout_raw,
      lifetimes_in_raw_comma = lifetimes_in_raw_comma,
      lifetimes_inout_raw_comma = lifetimes_inout_raw_comma,
      call_param_types_native = call_param_types_native,
      call_param_types_raw = call_param_types_raw,
      call_param_types_raw_win64fix = call_param_types_raw_win64fix,
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

#[derive(Clone, Debug, Eq, PartialEq)]
enum CallbackTranslationError {
  GetResultTypeFailed,
  GetArgumentTypesFailed,
  UnknownType(Vec<String>),
}

fn visit_callback_definition<'tu>(
  e: Entity<'tu>,   // The typedef definition node.
  fn_ty: Type<'tu>, // The callback function prototype.
) -> Result<String, CallbackTranslationError> {
  let cb_name = get_flat_name_for_callback_type(e);
  let cb_comment = e.get_comment();
  let ret_ty = fn_ty
    .get_result_type()
    .ok_or(CallbackTranslationError::GetResultTypeFailed)?;
  let arg_names = e
    .get_children()
    .into_iter()
    .filter(|c| c.get_kind() == EntityKind::ParmDecl)
    .map(|c| c.get_name());
  let arg_tys = fn_ty
    .get_argument_types()
    .ok_or(CallbackTranslationError::GetArgumentTypesFailed)?;
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
  if let Some(unk_ty_names) = contains_unknown_cxx_types(&sigs_raw) {
    Err(CallbackTranslationError::UnknownType(unk_ty_names))
  } else {
    Ok(code)
  }
}

fn visit_declaration<'tu>(
  index: &mut CallbackIndex<'tu>,
  e: Entity<'tu>,
) -> Option<String> {
  if e.is_definition() {
    if let Some(ty) = e.get_typedef_underlying_type() {
      if ty.get_kind() == TypeKind::Pointer {
        if let Some(pointee_ty) = ty.get_pointee_type() {
          if pointee_ty.get_kind() == TypeKind::FunctionPrototype {
            if is_type_used(e.get_translation_unit(), ty) {
              match visit_callback_definition(e, pointee_ty) {
                //index.extend(
                //  where_is_type_used(e.get_translation_unit(), ty)
                //    .into_iter()
                //    .map(|e| -> Option<String> {
                //      let vn = e.get_display_name()?;
                //      let pn = e.get_semantic_parent()?.get_display_name()?;
                //      let s = format!("{}::{}", pn, vn);
                //      Some(s)
                //    })
                //    .map(|o| o.unwrap_or_else(|| format!("{:?}", e)))
                //    .map(|n| format!("// @ - {}", n))
                //);
                Ok(code) => index.push(code),
                Err(e) => {
                  eprintln!("Skipped: `{}`: {:?}", ty.get_display_name(), e)
                }
              }
            } else {
              eprintln!("Not used: `{}`", ty.get_display_name());
            }
          }
        }
      }
    }
  }
  None
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

fn visit_translation_unit<'tu>(
  translation_unit: &'tu TranslationUnit<'tu>,
) -> String {
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
  index.join("\n")
}

pub fn generate(tu: &TranslationUnit) {
  let code = format!("{}\n{}", boilerplate(), visit_translation_unit(tu));
  let code = rustfmt(&code);
  print!("{}", code);
}

fn rustfmt(code: &str) -> String {
  run_rustfmt(code, true)
    .or_else(|_| run_rustfmt(code, false))
    .unwrap()
}

fn run_rustfmt(code: &str, nightly: bool) -> io::Result<String> {
  let mut c = Command::new("rustfmt");
  c.stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .arg("--edition=2018")
    .arg(rustfmt_config("max_width", 80))
    .arg(rustfmt_config("tab_spaces", 2));
  if nightly {
    c.arg("--unstable-features")
      .arg(rustfmt_config("format_macro_matchers", true))
      .arg(rustfmt_config("format_macro_bodies", true));
  }
  let mut c = c.spawn()?;
  c.stdin.as_mut().unwrap().write_all(code.as_bytes())?;
  let stdout = match c.wait_with_output()? {
    Output { status, stdout, .. } if status.success() => Ok(stdout),
    Output { status, .. } => Err(io::Error::new(
      io::ErrorKind::Other,
      format!("rustfmt exit status: {:?}", status),
    )),
  }?;
  String::from_utf8(stdout)
    .map_err(|err| io::Error::new(io::ErrorKind::InvalidData, err))
}

fn rustfmt_config<V: Display>(key: &str, value: V) -> String {
  format!("--config={}={}", key, value)
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
#![allow(clippy::too_many_arguments)]

use std::cell::Cell;
use std::ffi::c_void;
use std::ffi::CStr;
use std::os::raw::c_char;
use std::os::raw::c_double;
use std::os::raw::c_int;
use std::os::raw::c_uchar;
use std::slice;

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
use crate::SharedArrayBuffer;
use crate::StartupData;
use crate::String;
use crate::Value;

// Placeholder types that don't have Rust bindings yet.
#[repr(C)] pub struct AtomicsWaitWakeHandle(Opaque);
#[repr(C)] pub struct JitCodeEvent(Opaque);
#[repr(C)] pub struct PropertyDescriptor(Opaque);
#[repr(C)] pub enum  AccessType { _TODO }
#[repr(C)] pub enum  AtomicsWaitEvent { _TODO }
#[repr(C)] pub enum  CrashKeyId { _TODO }
#[repr(C)] pub enum  GCCallbackFlags { _TODO }
#[repr(C)] pub enum  GCType { _TODO }
#[repr(C)] pub enum  PromiseHookType { _TODO }
#[repr(C)] pub enum  UseCounterFeature { _TODO }

/// Rust representation of a C++ `std::string`.
#[repr(C)]
pub struct CxxString(Opaque);

impl<'a> From<&'a CxxString> for &'a [u8] {
  fn from(_cxx_str: &'a CxxString) -> Self { unimplemented!() }
}

impl<'a> From<&'a CxxString> for &'a CStr {
  fn from(_cxx_str: &'a CxxString) -> Self { unimplemented!() }
}

// Notes:
// * This enum should really be #[repr(bool)] but Rust doesn't support that.
// * It must have the same layout as the C++ struct. Do not reorder fields!
#[repr(u8)]
pub enum ModifyCodeGenerationFromStringsResult<'s> {
  /// Block the codegen algorithm.
  Block,
  /// Proceed with the codegen algorithm. Otherwise, block it.
  Allow {
    /// Overwrite the original source with this string, if present.
    /// Use the original source if empty.
    modified_source: Option<Local<'s, String>>,
  },
}
"#
  .trim()
}
