use std::borrow::Borrow;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter, Write};
use std::ops::{Deref, DerefMut};
use std::path::Path;
use std::process::exit;
use std::rc::Rc;

use clang::diagnostic::Severity;
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
}

impl<'tu> ClassDef<'tu> {
  pub fn new(sort_key_cache: ClassSortKeyCache<'tu>) -> Self {
    Self {
      struct_definition: Default::default(),
      deref_impl: Default::default(),
      from_impls: ClassIndex::new_with_cache(sort_key_cache.clone()),
      try_from_impls: ClassIndex::new_with_cache(sort_key_cache.clone()),
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
}

impl<'tu> Display for ClassDef<'tu> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "\n{}\n{}{}{}",
      self.struct_definition,
      self.deref_impl,
      self.try_from_impls,
      self.from_impls,
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
    let mut sort_key = match get_base_class(class) {
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

fn main() {
  let base_path = Path::new("/v8rs");

  let clang = Clang::new().unwrap();
  let index = Index::new(&clang, false, false);

  #[allow(clippy::useless_format)]
  let arg = |s| format!("{}", s);
  let isystem =
    |suffix| format!("-isystem{}", base_path.join(suffix).to_str().unwrap());
  let tu = index
    .parser(base_path.join("./v8/include/v8.h"))
    .arguments(&[
      arg("-x"),
      arg("c++"),
      arg("-nostdinc++"),
      isystem("./buildtools/third_party/libc++/trunk/include"),
      isystem("./buildtools/third_party/libc++abi/trunk/include"),
    ])
    .parse()
    .unwrap();

  if tu
    .get_diagnostics()
    .into_iter()
    .inspect(|d| eprintln!("{}", d))
    .filter(|d| d.get_severity() >= Severity::Error)
    .count()
    > 0
  {
    exit(1);
  }

  let mut defs = ClassDefIndex::new();
  visit_translation_unit(&mut defs, &tu);

  println!("{}", boilerplate());
  println!("{}", defs);
}

fn boilerplate() -> &'static str {
  r#"
// Copyright 2019-2020 the Deno authors. All rights reserved. MIT license.

use std::convert::From;
use std::convert::TryFrom;
use std::error::Error;
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

fn get_base_class(e: Entity) -> Option<Entity> {
  e.get_children()
    .into_iter()
    .filter(|c| c.get_kind() == EntityKind::BaseSpecifier)
    .filter_map(|c| c.get_type())
    .filter_map(|t| t.get_declaration())
    .filter_map(|b| b.get_definition())
    .next()
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

fn is_v8_ns(e: Entity) -> bool {
  e.get_kind() == EntityKind::Namespace
    && e.get_name().map(|n| n == "v8").unwrap_or(false)
    && e
      .get_semantic_parent()
      .map(|p| p.get_kind() == EntityKind::TranslationUnit)
      .unwrap_or(false)
}

fn is_data_class(e: Entity) -> bool {
  e.get_kind() == EntityKind::ClassDecl
    && e.get_name().map(|n| n == "Data").unwrap_or(false)
    && e.get_semantic_parent().map(is_v8_ns).unwrap_or(false)
}

fn is_data_subclass(e: Entity) -> bool {
  is_data_class(e) || get_base_class(e).map(is_data_subclass).unwrap_or(false)
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
  comment
    .replace("\n * ", "\n/// ")
    .replace("\n *\n", "\n///\n")
    .trim_start_matches("/**")
    .trim_start()
    .trim_end_matches("*/")
    .trim_end()
    .to_owned()
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
  if let Some(ancestor_base) = get_base_class(ancestor) {
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
    .or_else(|| get_try_from_test_method(e, get_base_class(a)?))
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
  if let Some(ancestor_base) = get_base_class(ancestor) {
    add_try_from_impls(defs, class, ancestor_base)?;
  }
  Ok(())
}

fn visit_data_subclass<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
) -> fmt::Result {
  add_struct_definition(defs, class)?;
  if let Some(base) = get_base_class(class) {
    add_deref_impl(defs, class, base)?;
    add_from_impls(defs, class, base)?;
    add_try_from_impls(defs, class, base)?;
  }
  Ok(())
}

fn visit_translation_unit<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  translation_unit: &'tu TranslationUnit<'tu>,
) {
  let root = translation_unit.get_entity();
  root.visit_children(|e, _| {
    if e.is_definition() && is_data_subclass(e) {
      visit_data_subclass(defs, e).unwrap();
    }
    EntityVisitResult::Recurse
  });
}
