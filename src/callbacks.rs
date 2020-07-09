#![allow(dead_code)]

use std::borrow::Borrow;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::hash::Hash;
use std::hash::Hasher;
use std::iter::once;
use std::marker::PhantomData;
use std::mem::transmute;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use clang::*;

#[derive(Copy, Clone, Eq, PartialEq)]
struct TypeExt<'tu>(Type<'tu>);

impl<'tu> From<Type<'tu>> for TypeExt<'tu> {
  fn from(ty: Type<'tu>) -> Self {
    Self(ty)
  }
}

impl<'tu> Hash for TypeExt<'tu> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    let (_kind, data, _tu): (usize, [usize; 2], usize) =
      unsafe { transmute(self.0) };
    data.hash(state)
  }
}

impl<'tu> Deref for TypeExt<'tu> {
  type Target = Type<'tu>;
  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

struct ClassIndex<'tu, T> {
  hash_map: HashMap<TypeExt<'tu>, T>,
  sort_key_cache: ClassSortKeyCache<'tu>,
}

impl<'tu, T> ClassIndex<'tu, T> {
  pub fn new_with_cache(sort_key_cache: ClassSortKeyCache<'tu>) -> Self {
    Self {
      hash_map: HashMap::new(),
      sort_key_cache,
    }
  }

  //pub fn to_sorted_vec(&self) -> Vec<&T> {
  //  let cache = &self.sort_key_cache;
  //  let mut defs = self.hash_map.iter().collect::<Vec<_>>();
  //  defs.sort_by(|(c1, _), (c2, _)| cache.compare(*c1, *c2));
  //  defs.into_iter().map(|(_, v)| v).collect::<Vec<_>>()
  //}
}

impl<'tu, T> Deref for ClassIndex<'tu, T> {
  type Target = HashMap<TypeExt<'tu>, T>;
  fn deref(&self) -> &Self::Target {
    &self.hash_map
  }
}

impl<'tu, T> DerefMut for ClassIndex<'tu, T> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.hash_map
  }
}

impl<'tu, T> Display for ClassIndex<'tu, T>
where
  T: Display,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    for (_, v) in self.iter() {
      v.fmt(f)?;
    }
    Ok(())
  }
}

struct ClassDef<'tu> {
  ty: Type<'tu>,
  definition: String,
  visited: bool,
  function_prototype: Option<Type<'tu>>,
  alias_decls: HashSet<Entity<'tu>>,
  phantom: PhantomData<&'tu ()>,
}

impl<'tu> ClassDef<'tu> {
  pub fn new(ty: Type<'tu>) -> Self {
    Self {
      ty,
      definition: Default::default(),
      visited: false,
      function_prototype: None,
      alias_decls: HashSet::new(),
      phantom: PhantomData,
    }
  }

  pub fn definition(&mut self) -> &mut String {
    &mut self.definition
  }

  pub fn visited(&mut self) -> &mut bool {
    &mut self.visited
  }

  pub fn function_prototype(&mut self) -> &mut Option<Type<'tu>> {
    &mut self.function_prototype
  }

  pub fn alias_decls(&mut self) -> &mut HashSet<Entity<'tu>> {
    &mut self.alias_decls
  }

  pub fn get_names(&self) -> Vec<String> {
    let mut names = self
      .alias_decls
      .iter()
      .map(|e| e.get_name().unwrap())
      .collect::<Vec<_>>();
    if names.is_empty() {
      names.push("<Anonymous>".to_owned());
    }
    names
  }
}

impl<'tu> Display for ClassDef<'tu> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    if let Some(fn_ty) = self.function_prototype {
      //writeln!(f, "{:?} -> {}", self.ty, fn_ty.get_display_name())?;
      for name in self.get_names() {
        writeln!(
          f,
          "{} = {} = {}",
          name,
          self.ty.get_display_name(),
          fn_ty.get_display_name()
        )?;
      }
    }
    Ok(())
  }
}

type ClassDefIndex<'tu> = ClassIndex<'tu, ClassDef<'tu>>;

impl<'tu> ClassDefIndex<'tu> {
  pub fn new() -> Self {
    Self::new_with_cache(ClassSortKeyCache::new())
  }

  pub fn get_type_entry<'a>(
    &'a mut self,
    ty: impl Into<TypeExt<'tu>>,
  ) -> &'a mut ClassDef<'tu>
  where
    'tu: 'a,
  {
    let Self {
      hash_map,
      sort_key_cache,
    } = self;
    let ty = ty.into();
    hash_map.entry(ty).or_insert_with(|| ClassDef::new(*ty))
  }
}

#[derive(Clone, Default)]
struct ClassSortKeyCache<'tu>(Rc<RefCell<HashMap<Entity<'tu>, ClassSortKey>>>);

impl<'tu> ClassSortKeyCache<'tu> {
  #[allow(dead_code)]
  pub fn new() -> Self {
    Default::default()
  }

  fn add_to_cache_if_necessary(&self, class: &Entity<'tu>) {
    let class = *class;
    self
      .0
      .borrow_mut()
      .entry(class)
      .or_insert_with(|| ClassSortKey::new(class));
  }

  pub fn compare(
    &self,
    class1: impl Borrow<Entity<'tu>>,
    class2: impl Borrow<Entity<'tu>>,
  ) -> Ordering {
    let class1 = class1.borrow();
    let class2 = class2.borrow();
    self.add_to_cache_if_necessary(class1);
    self.add_to_cache_if_necessary(class2);
    let inner = (&*self.0).borrow();
    let sortkey1 = inner.get(class1).unwrap();
    let sortkey2 = inner.get(class2).unwrap();
    sortkey1.cmp(sortkey2)
  }
}

#[derive(Eq, PartialEq)]
struct ClassSortKey(Vec<String>);

impl ClassSortKey {
  pub fn new(class: Entity) -> Self {
    Self(Self::make_name_list(class))
  }

  fn make_name_list(class: Entity) -> Vec<String> {
    let mut sort_key = match get_single_base_class(class) {
      Some(base) => Self::make_name_list(base),
      None => Vec::new(),
    };
    sort_key.push(get_flat_name_for_callback_type(class));
    sort_key
  }
}

impl PartialOrd for ClassSortKey {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for ClassSortKey {
  fn cmp(&self, other: &Self) -> Ordering {
    use Ordering::*;
    self
      .0
      .iter()
      .zip(other.0.iter())
      .map(|(a, b)| a.cmp(b))
      .find(|o| *o != Equal)
      .unwrap_or_else(|| self.0.len().cmp(&other.0.len()))
  }
}

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
    .replace("CallbackCallback", "Callback")
    .replace("CallbackInfoCallback", "Callback")
}

fn format_comment(comment: String) -> String {
  let delims: &[_] = &['/', '*', ' ', '\n'];
  comment
    .trim_start_matches(delims)
    .trim_end_matches(delims)
    .replacen("", "/// ", 1)
    .replace("\n * ", "\n/// ")
    .replace("\n *\n", "\n///\n")
    .replace("\\code", "```ignore")
    .replace("\\endcode", "```")
    .replace(".  ", ". ")
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

fn get_type_name<'tu>(ty: Type<'tu>) -> Option<String> {
  ty.get_declaration().and_then(|d| d.get_name())
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
enum TypeMapping<'tu> {
  Void,
  Bool,
  Int { signed: bool },
  IntBits { bits: u8, signed: bool },
  IntSize { signed: bool },
  Local(String),
  MaybeLocal(String),
  Isolate { mutable: bool },
  CallbackInfo { name: String, ret_ty_name: String },
  Unknown(Type<'tu>),
}

#[derive(Debug)]
enum Identifier {
  Return,
  Anonymous,
  Param(String),
}

impl From<Option<String>> for Identifier {
  fn from(s: Option<String>) -> Identifier {
    s.map(Identifier::Param)
      .unwrap_or_else(|| Identifier::Anonymous)
  }
}

fn visit_type<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  ty: Type<'tu>,
  id: Identifier,
) -> Option<(Identifier, TypeMapping<'tu>)> {
  use TypeKind as K;
  use TypeMapping as M;

  let ty_map = if ty.get_kind() == K::Void {
    M::Void
  } else if ty.get_kind() == K::Bool {
    M::Bool
  } else if ty.get_kind() == K::Int {
    M::Int { signed: true }
  } else if is_std_type(ty, "int32_t") {
    M::IntBits {
      bits: 32,
      signed: true,
    }
  } else if is_std_type(ty, "int64_t") {
    M::IntBits {
      bits: 64,
      signed: true,
    }
  } else if is_std_type(ty, "uint32_t") {
    M::IntBits {
      bits: 32,
      signed: false,
    }
  } else if is_std_type(ty, "uint64_t") {
    M::IntBits {
      bits: 64,
      signed: false,
    }
  } else if is_std_type(ty, "ssize_t") || is_std_type(ty, "intptr_t") {
    M::IntSize { signed: true }
  } else if is_std_type(ty, "size_t") || is_std_type(ty, "uintptr_t") {
    M::IntSize { signed: false }
  } else if let Some(TypeParams::One(p)) =
    is_v8_type(ty, "Local").and_then(get_type_params)
  {
    M::Local(get_type_name(p).unwrap_or_else(|| "<ERR>".to_owned()))
  } else if let Some(TypeParams::One(p)) =
    is_v8_type(ty, "MaybeLocal").and_then(get_type_params)
  {
    M::MaybeLocal(get_type_name(p).unwrap_or_else(|| "<ERR>".to_owned()))
  } else if let Some(pty) = is_v8_type_pointee(ty, "Isolate") {
    M::Isolate {
      mutable: !pty.is_const_qualified(),
    }
  } else if let Some(ty2) = is_v8_type_pointee(ty, "FunctionCallbackInfo")
    .or_else(|| is_v8_type_pointee(ty, "PropertyCallbackInfo"))
  {
    let name = get_type_name(ty2).unwrap_or_else(|| "<ERR>".to_owned());
    let ret_ty_name = get_type_params(ty2)
      .and_then(|ps| match ps {
        TypeParams::Zero => None,
        TypeParams::One(p) => Some(p),
        _ => panic!(),
      })
      .and_then(get_type_name)
      .unwrap_or_else(|| "<ERR>".to_owned());
    M::CallbackInfo { name, ret_ty_name }
  } else {
    //M::Unknown(ty)
    return None;
  };
  Some((id, ty_map))
}

fn visit_callback_definition<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  e: Entity<'tu>,   // The typedef definition node.
  fn_ty: Type<'tu>, // The callback function prototype.
) -> Option<Vec<(Identifier, TypeMapping<'tu>)>> {
  let ret_ty = fn_ty.get_result_type()?;
  let arg_tys = fn_ty.get_argument_types()?;
  let arg_names = e
    .get_children()
    .into_iter()
    .filter(|c| c.get_kind() == EntityKind::ParmDecl)
    .map(|c| c.get_name())
    .map(Identifier::from);
  once(visit_type(defs, ret_ty, Identifier::Return))
    .chain(
      arg_tys
        .into_iter()
        .zip(arg_names)
        .map(|(ty, id)| visit_type(defs, ty, id)),
    )
    .collect()
}

fn visit_declaration<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  e: Entity<'tu>,
) -> Option<()> {
  if e.is_definition() {
    if let Some(ty) = e.get_typedef_underlying_type() {
      if ty.get_kind() == TypeKind::Pointer {
        if let Some(pointee_ty) = ty.get_pointee_type() {
          if pointee_ty.get_kind() == TypeKind::FunctionPrototype
            && is_type_used(e.get_translation_unit(), ty)
          {
            if let Some(ty_maps) =
              visit_callback_definition(defs, e, pointee_ty)
            {
              eprintln!(
                "{:?}\n{:?}",
                get_flat_name_for_callback_type(e),
                ty_maps
              )
            } else {
              eprintln!(
                "// \x1b[41m{}\x1b[0m",
                get_flat_name_for_callback_type(e)
              );
            }
          }
        }
      }
    }
  }
  Some(())
}

fn visit_v8_ns<'tu>(defs: &'_ mut ClassDefIndex<'tu>, ns: Entity<'tu>) {
  ns.visit_children(|e, _| {
    if e.is_declaration() {
      visit_declaration(defs, e);
      EntityVisitResult::Recurse
    } else {
      EntityVisitResult::Continue
    }
  });
}

fn visit_translation_unit<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  translation_unit: &'tu TranslationUnit<'tu>,
) {
  let root = translation_unit.get_entity();
  root.visit_children(|e, _| {
    if e.get_kind() == EntityKind::Namespace {
      if is_v8_ns(e) {
        visit_v8_ns(defs, e);
      }
      EntityVisitResult::Continue
    } else {
      EntityVisitResult::Recurse
    }
  });
}

pub fn generate(tu: &TranslationUnit) {
  let mut defs = ClassDefIndex::new();
  visit_translation_unit(&mut defs, tu);

  println!("{}", boilerplate());
  println!("{}", defs);
}

fn boilerplate() -> &'static str {
  r#"
// Copyright 2019-2020 the Deno authors. All rights reserved. MIT license.
"#
  .trim()
}
