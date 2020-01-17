use std::borrow::Borrow;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter, Write};
use std::mem::replace;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

use clang::*;

struct ClassIndex<'tu, T> {
  hash_map: HashMap<Entity<'tu>, T>,
  sort_key_cache: ClassSortKeyCache<'tu>,
}

impl<'tu, T> ClassIndex<'tu, T> {
  pub fn new_with_cache(sort_key_cache: ClassSortKeyCache<'tu>) -> Self {
    Self {
      hash_map: HashMap::new(),
      sort_key_cache,
    }
  }

  pub fn to_sorted_vec(&self) -> Vec<&T> {
    let cache = &self.sort_key_cache;
    let mut defs = self.hash_map.iter().collect::<Vec<_>>();
    defs.sort_by(|(c1, _), (c2, _)| cache.compare(*c1, *c2));
    defs.into_iter().map(|(_, v)| v).collect::<Vec<_>>()
  }
}

impl<'tu, T> Deref for ClassIndex<'tu, T> {
  type Target = HashMap<Entity<'tu>, T>;
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
    for item in self.to_sorted_vec() {
      write!(f, "{}", item)?;
    }
    Ok(())
  }
}

struct ClassDef<'tu> {
  struct_definition: String,
  deref_impl: String,
  from_impls: ClassIndex<'tu, String>,
  try_from_impls: ClassIndex<'tu, String>,
  eq_impl: String,
  partial_eq_impls: ClassIndex<'tu, String>,
  visited: bool,
}

impl<'tu> ClassDef<'tu> {
  pub fn new(sort_key_cache: ClassSortKeyCache<'tu>) -> Self {
    Self {
      struct_definition: Default::default(),
      deref_impl: Default::default(),
      from_impls: ClassIndex::new_with_cache(sort_key_cache.clone()),
      try_from_impls: ClassIndex::new_with_cache(sort_key_cache.clone()),
      eq_impl: Default::default(),
      partial_eq_impls: ClassIndex::new_with_cache(sort_key_cache.clone()),
      visited: false,
    }
  }

  pub fn struct_definition(&mut self) -> &mut String {
    &mut self.struct_definition
  }

  pub fn deref_impl(&mut self) -> &mut String {
    &mut self.deref_impl
  }

  pub fn from_impl(&mut self, from_class: Entity<'tu>) -> &mut String {
    self.from_impls.entry(from_class).or_default()
  }

  pub fn try_from_impl(&mut self, from_class: Entity<'tu>) -> &mut String {
    self.try_from_impls.entry(from_class).or_default()
  }

  pub fn eq_impl(&mut self) -> &mut String {
    &mut self.eq_impl
  }

  pub fn partial_eq_impl(&mut self, other_class: Entity<'tu>) -> &mut String {
    self.partial_eq_impls.entry(other_class).or_default()
  }

  pub fn visited(&mut self) -> &mut bool {
    &mut self.visited
  }

  fn has_traits(&self) -> bool {
    !self.deref_impl.is_empty()
      || !self.try_from_impls.is_empty()
      || !self.from_impls.is_empty()
      || !self.eq_impl.is_empty()
      || !self.partial_eq_impls.is_empty()
  }
}

impl<'tu> Display for ClassDef<'tu> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "\n{}{}{}{}{}{}{}",
      self.struct_definition,
      if self.has_traits() { "\n" } else { "" },
      self.deref_impl,
      self.try_from_impls,
      self.from_impls,
      self.eq_impl,
      self.partial_eq_impls
    )
  }
}

type ClassDefIndex<'tu> = ClassIndex<'tu, ClassDef<'tu>>;

impl<'tu> ClassDefIndex<'tu> {
  pub fn new() -> Self {
    Self::new_with_cache(ClassSortKeyCache::new())
  }

  pub fn get_class_def<'a>(
    &'a mut self,
    e: Entity<'tu>,
  ) -> &'a mut ClassDef<'tu>
  where
    'tu: 'a,
  {
    let Self {
      hash_map,
      sort_key_cache,
    } = self;
    hash_map
      .entry(e)
      .or_insert_with(|| ClassDef::new(sort_key_cache.clone()))
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
    sort_key.push(get_flat_name(class));
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

fn get_class_and_all_derived_classes(e: Entity) -> Option<Vec<Entity>> {
  Some(
    Some(e)
      .into_iter()
      .chain(get_direct_subclasses(e)?.into_iter().flat_map(|s| {
        get_class_and_all_derived_classes(s).unwrap().into_iter()
      }))
      .collect::<Vec<_>>(),
  )
}

fn is_v8_ns(e: Entity) -> bool {
  e.get_kind() == EntityKind::Namespace
    && e.get_name().map(|n| n == "v8").unwrap_or(false)
    && e
      .get_semantic_parent()
      .map(|p| p.get_kind() == EntityKind::TranslationUnit)
      .unwrap_or(false)
}

fn is_class_in_v8_ns(e: Entity, class_name: &'static str) -> bool {
  e.get_kind() == EntityKind::ClassDecl
    && e.get_name().map(|n| n == class_name).unwrap_or(false)
    && e.get_semantic_parent().map(is_v8_ns).unwrap_or(false)
}

// This function also returns `true` if `e` itself has name `v8::{class_name}`.
fn has_base_class_in_v8_ns(e: Entity, class_name: &'static str) -> bool {
  is_class_in_v8_ns(e, class_name)
    || get_single_base_class(e)
      .map(|b| has_base_class_in_v8_ns(b, class_name))
      .unwrap_or(false)
}

// This function also returns `true` if `e` itself has name `v8::{class_name}`.
fn has_derived_class_in_v8_ns(e: Entity, class_name: &'static str) -> bool {
  get_class_and_all_derived_classes(e)
    .map(|descendants| {
      descendants
        .into_iter()
        .any(|s| is_class_in_v8_ns(s, class_name))
    })
    .unwrap_or(false)
}

fn get_local_handle_data_type(ty: Type) -> Option<Entity> {
  let _def = ty.get_declaration().filter(|d| {
    d.get_kind() == EntityKind::ClassDecl
      && d
        .get_name()
        .map(|n| n == "Local" || n == "MaybeLocal")
        .unwrap_or(false)
      && d.get_semantic_parent().map(is_v8_ns).unwrap_or(false)
  })?;
  let mut args = ty
    .get_template_argument_types()?
    .into_iter()
    .filter_map(|t| t?.get_declaration())
    .filter_map(|b| b.get_definition());
  match args.next() {
    Some(a) if args.next().is_none() => Some(a),
    _ => None, // Return None if there are 0 or 2+ type arguments.
  }
}

// Returns the name of an entity for use in a flat namespace.
// E.g. "v8::Promise::Resolver" -> "PromiseResolver".
fn get_flat_name(e: Entity) -> String {
  let mut name = e.get_name().unwrap();
  let mut p = e;
  loop {
    use EntityKind::*;
    p = p.get_semantic_parent().unwrap();
    match p.get_kind() {
      ClassDecl => {
        name = format!("{}{}", p.get_name().unwrap(), name);
      }
      Namespace => break name,
      _ => {}
    }
  }
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

fn add_struct_definition<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
) -> fmt::Result {
  let w = defs.get_class_def(class).struct_definition();
  if let Some(comment) = class.get_comment() {
    writeln!(w, "{}", format_comment(comment))?;
  }
  writeln!(w, "#[repr(C)]")?;
  writeln!(w, "pub struct {}(Opaque);", get_flat_name(class))
}

fn add_deref_impl<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
  base: Entity<'tu>,
) -> fmt::Result {
  let w = defs.get_class_def(class).deref_impl();
  writeln!(
    w,
    "impl_deref! {{ {} for {} }}",
    get_flat_name(base),
    get_flat_name(class)
  )
}

fn add_from_impls<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
  ancestor: Entity<'tu>,
) -> fmt::Result {
  if let Some(ancestor_base) = get_single_base_class(ancestor) {
    add_from_impls(defs, class, ancestor_base)?;
  }
  let w = defs.get_class_def(ancestor).from_impl(class);
  writeln!(
    w,
    "impl_from! {{ {} for {} }}",
    get_flat_name(class),
    get_flat_name(ancestor),
  )
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

fn get_try_from_test_method<'tu>(
  e: Entity<'tu>, // Target class, e.g. Boolean.
  a: Entity<'tu>, // Ancestor class, e.g. Value.
) -> Option<Entity<'tu>> {
  use EntityKind::*;
  let method_name = format!("Is{}", e.get_name()?); // e.g. "IsBoolean".
  a.get_children()
    .into_iter()
    .find(|m| {
      m.get_name().map(|n| n == method_name).unwrap_or(false)
        && m.get_kind() == Method
        && m.is_const_method()
        && !m.is_static_method()
        && !m.is_virtual_method()
        && !m
          .get_children()
          .into_iter()
          .any(|p| p.get_kind() == ParmDecl)
    })
    .or_else(|| get_try_from_test_method(e, get_single_base_class(a)?))
}

fn get_try_from_check<'tu>(
  e: Entity<'tu>, // Target class, e.g. Boolean.
  b: Entity<'tu>, // Base class, e.g. Primitive.
) -> Option<String> {
  get_try_from_test_method(e, b)
    .and_then(|m| Some(format!("v.{}()", to_snake_case(m.get_name()?))))
    .or_else(|| {
      get_direct_subclasses(e)?.into_iter().try_fold(
        match e.get_name()?.as_str() {
          // Special case: 'null' and 'undefined' don't have a class of their
          // own but they are primitive nonetheless.
          "Primitive" => Some("v.is_null_or_undefined()".to_owned()),
          _ => None,
        },
        |check, s| {
          Some(Some(format!(
            "{}{}",
            check.map(|s| format!("{} || ", s)).unwrap_or_default(),
            get_try_from_check(s, b)?
          )))
        },
      )?
    })
}

fn add_try_from_impls<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
  ancestor: Entity<'tu>,
) -> fmt::Result {
  if let Some(check) = get_try_from_check(class, ancestor) {
    let w = defs.get_class_def(class).try_from_impl(ancestor);
    writeln!(
      w,
      "impl_try_from! {{ {} for {} if v => {} }}",
      get_flat_name(ancestor),
      get_flat_name(class),
      check
    )?;
  }
  if let Some(ancestor_base) = get_single_base_class(ancestor) {
    add_try_from_impls(defs, class, ancestor_base)?;
  }
  Ok(())
}

fn is_class_comparable_by_identity(e: Entity) -> bool {
  // A class supports comparison by identity if:
  //  - EITHER it is any of the following classes:
  //      - `v8::Boolean`
  //      - `v8::Symbol`
  //  - OR it is NOT any of the following:
  //      - A base class of `v8::Primitive`.
  //      - The class `v8::Primitive` itself.
  //      - A class derived from `v8:Primitive`.
  //
  // Optimization: searching all derived classes is quite slow for classes
  // with many descendants. Therefore, some classes are hard coded:
  //   - Comparable by identity: `Object`. `ArrayBufferView`, `TypedArray`.
  //   - NOT comparable by identity: `Data`, `Value`.
  is_class_in_v8_ns(e, "Boolean")
    || is_class_in_v8_ns(e, "Symbol")
    || is_class_in_v8_ns(e, "Object")
    || is_class_in_v8_ns(e, "ArrayBufferView")
    || is_class_in_v8_ns(e, "TypedArray")
    || !(is_class_in_v8_ns(e, "Data")
      || is_class_in_v8_ns(e, "Value")
      || has_base_class_in_v8_ns(e, "Primitive")
      || has_derived_class_in_v8_ns(e, "Primitive"))
}

fn is_class_comparable_by_strict_equals(e: Entity) -> bool {
  has_base_class_in_v8_ns(e, "Value")
}

fn get_partial_eq_compare_method(
  class1: Entity,
  class2: Entity,
) -> Option<&'static str> {
  // Comparison by identity is possible if the type on *either* side of the
  // comparison supports this. However, comparison by strict equality is only
  // possible when the types on *both* sides support it.
  if is_class_comparable_by_identity(class1)
    || is_class_comparable_by_identity(class2)
  {
    Some("identity")
  } else if is_class_comparable_by_strict_equals(class1)
    && is_class_comparable_by_strict_equals(class2)
  {
    Some("strict_equals")
  } else {
    None
  }
}

fn add_partial_eq_impl<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  lhs: Entity<'tu>,
  rhs: Entity<'tu>,
  compare_method: &'static str,
) -> fmt::Result {
  let w = defs.get_class_def(lhs).partial_eq_impl(rhs);
  writeln!(
    w,
    "impl_partial_eq! {{ {} for {} use {} }}",
    get_flat_name(rhs),
    get_flat_name(lhs),
    compare_method,
  )
}

fn add_partial_eq_impls<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
  ancestor: Entity<'tu>,
) -> fmt::Result {
  if let Some(compare_method) = get_partial_eq_compare_method(class, ancestor) {
    // Implement `PartialEq<Ancestor> for Class`.
    add_partial_eq_impl(defs, class, ancestor, compare_method)?;
    if class != ancestor {
      // When `Class` and `Ancestor` are not the same, also implement the
      // reverse comparison `PartialEq<Class> for Ancestor`.
      add_partial_eq_impl(defs, ancestor, class, compare_method)?;
    }
  }
  if let Some(ancestor_base) = get_single_base_class(ancestor) {
    add_partial_eq_impls(defs, class, ancestor_base)?;
  }
  Ok(())
}

fn maybe_add_eq_impl<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
) -> fmt::Result {
  // Total equality (the `Eq` trait) requires that comparison between two
  // values of the same type is reflexive (a == a). This true for all JavaScript
  // types except `Number`, because NaN != NaN. Therefore we implement Eq for
  // all classes except `Number` and it's base classes.
  if get_partial_eq_compare_method(class, class).is_some()
    && !has_derived_class_in_v8_ns(class, "Number")
  {
    let w = defs.get_class_def(class).eq_impl();
    writeln!(w, "impl_eq! {{ for {} }}", get_flat_name(class))?;
  }
  Ok(())
}

fn visit_class<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
) -> fmt::Result {
  add_struct_definition(defs, class)?;
  maybe_add_eq_impl(defs, class)?;
  add_partial_eq_impls(defs, class, class)?;
  if let Some(base) = get_single_base_class(class) {
    add_deref_impl(defs, class, base)?;
    add_from_impls(defs, class, base)?;
    add_try_from_impls(defs, class, base)?;
  }
  Ok(())
}

fn maybe_visit_class<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
) {
  let visited = defs.get_class_def(class).visited();
  if !replace(visited, true) {
    visit_class(defs, class).unwrap()
  }
}

fn visit_translation_unit<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  translation_unit: &'tu TranslationUnit<'tu>,
) {
  let root = translation_unit.get_entity();
  root.visit_children(|e, _| {
    // Add all derivatives of v8::Data.
    if e.is_definition() && has_base_class_in_v8_ns(e, "Data") {
      maybe_visit_class(defs, e)
    }
    // A small number of v8::Local<T> types are not a derivative of v8::Data.
    // We find them by visiting the type parameter of every Local<T>.
    if let Some(a) = e.get_type().and_then(get_local_handle_data_type) {
      maybe_visit_class(defs, a)
    }
    if let Some(a) = e
      .get_type()
      .and_then(|ty| ty.get_result_type())
      .and_then(get_local_handle_data_type)
    {
      maybe_visit_class(defs, a)
    }
    EntityVisitResult::Recurse
  });
}

pub fn generate_data_rs(tu: &TranslationUnit) {
  let mut defs = ClassDefIndex::new();
  visit_translation_unit(&mut defs, tu);

  println!("{}", boilerplate());
  println!("{}", defs);
}

fn boilerplate() -> &'static str {
  r#"
// Copyright 2019-2020 the Deno authors. All rights reserved. MIT license.

use std::convert::From;
use std::convert::TryFrom;
use std::error::Error;
use std::ffi::c_void;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::mem::transmute;
use std::ops::Deref;

use crate::support::Opaque;
use crate::Local;

macro_rules! impl_deref {
  { $target:ident for $type:ident } => {
    impl Deref for $type {
      type Target = $target;
      fn deref(&self) -> &Self::Target {
        unsafe { &*(self as *const _ as *const Self::Target) }
      }
    }
  };
}

macro_rules! impl_from {
  { $source:ident for $type:ident } => {
    impl<'sc> From<Local<'sc, $source>> for Local<'sc, $type> {
      fn from(l: Local<'sc, $source>) -> Self {
        unsafe { transmute(l) }
      }
    }
  };
}

macro_rules! impl_try_from {
  { $source:ident for $target:ident if $value:pat => $check:expr } => {
    impl<'sc> TryFrom<Local<'sc, $source>> for Local<'sc, $target> {
      type Error = TryFromTypeError;
      fn try_from(l: Local<'sc, $source>) -> Result<Self, Self::Error> {
        match l {
          $value if $check => Ok(unsafe { transmute(l) }),
          _ => Err(TryFromTypeError::new(stringify!($target)))
        }
      }
    }
  };
}

macro_rules! impl_eq {
  { for $type:ident } => {
    impl<'sc> Eq for Local<'sc, $type> {}
  };
}

macro_rules! impl_partial_eq {
  { $rhs:ident for $type:ident use identity } => {
    impl<'sc> PartialEq<Local<'sc, $rhs>> for Local<'sc, $type> {
      fn eq(&self, other: &Local<'sc, $rhs>) -> bool {
        unsafe { v8__Local__EQ(transmute(*self), transmute(*other)) }
      }
    }
  };
  { $rhs:ident for $type:ident use strict_equals } => {
    impl<'sc> PartialEq<Local<'sc, $rhs>> for Local<'sc, $type> {
      fn eq(&self, other: &Local<'sc, $rhs>) -> bool {
        self.strict_equals((*other).into())
      }
    }
  };
}

extern "C" {
  fn v8__Local__EQ(this: Local<c_void>, other: Local<c_void>) -> bool;
}

#[derive(Clone, Copy, Debug)]
pub struct TryFromTypeError {
  expected_type: &'static str,
}

impl TryFromTypeError {
  fn new(expected_type: &'static str) -> Self {
    Self { expected_type }
  }
}

impl Display for TryFromTypeError {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{} expected", self.expected_type)
  }
}

impl Error for TryFromTypeError {}
"#
  .trim()
}
