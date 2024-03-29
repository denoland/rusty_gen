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
  hash_impl: String,
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
      hash_impl: Default::default(),
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

  pub fn hash_impl(&mut self) -> &mut String {
    &mut self.hash_impl
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
      || !self.hash_impl.is_empty()
  }
}

impl<'tu> Display for ClassDef<'tu> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "\n{}{}{}{}{}{}{}{}",
      self.struct_definition,
      if self.has_traits() { "\n" } else { "" },
      self.deref_impl,
      self.try_from_impls,
      self.from_impls,
      self.eq_impl,
      self.hash_impl,
      self.partial_eq_impls,
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
    let mut sort_key = match get_single_base_class_or_v8_data(class) {
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

#[derive(Copy, Clone, Debug)]
enum NoSingleBaseClass {
  None,
  MoreThanOne,
}

fn get_single_base_class_base(e: Entity) -> Result<Entity, NoSingleBaseClass> {
  let mut it = e
    .get_children()
    .into_iter()
    .filter(|c| c.get_kind() == EntityKind::BaseSpecifier)
    .filter_map(|c| c.get_type())
    .filter_map(|t| t.get_declaration())
    .filter_map(|b| b.get_definition());
  match it.next() {
    Some(base) if it.next().is_none() => Ok(base),
    Some(_) => Err(NoSingleBaseClass::MoreThanOne),
    None => Err(NoSingleBaseClass::None),
  }
}

fn get_single_base_class(e: Entity) -> Option<Entity> {
  get_single_base_class_base(e).ok()
}

// Returns the actual base class for `e`, or `v8::Data` if the class has no
// base class at all.
fn get_single_base_class_or_v8_data(e: Entity) -> Option<Entity> {
  match get_single_base_class_base(e) {
    Ok(base) => Some(base),
    Err(NoSingleBaseClass::MoreThanOne) => None,
    Err(NoSingleBaseClass::None) if is_class_in_v8_ns(e, "Data") => None,
    Err(NoSingleBaseClass::None) => e
      .get_translation_unit()
      .get_entity()
      .get_children()
      .into_iter()
      .filter(|&e| is_v8_ns(e))
      .flat_map(|e| e.get_children().into_iter())
      .filter(|&e| is_class_in_v8_ns(e, "Data"))
      .filter_map(|e| e.get_definition())
      .next(),
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
    .replace("\n   ", "\n/// ")
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
  writeln!(w, "#[derive(Debug)]")?;
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

#[allow(dead_code)]
fn get_cast_method<'tu>(
  target: Entity<'tu>, // Target class, e.g. Boolean.
  base: Entity<'tu>,   // Ancestor class, e.g. Value.
) -> Option<(Entity<'tu>, Entity<'tu>)> {
  use EntityKind::*;
  ["CheckCast", "Cast"]
    .iter()
    .find_map(|&method_name| {
      target
        .get_children()
        .into_iter()
        .filter(|m| {
          m.get_name().map(|n| n == method_name).unwrap_or(false)
            && m.get_kind() == Method
            && m.is_static_method()
        })
        .find(|m| {
          let params = m
            .get_children()
            .into_iter()
            .filter(|p| p.get_kind() == ParmDecl)
            .collect::<Vec<_>>();
          params
            .get(0)
            .and_then(|p| p.get_type())
            .and_then(|t| t.get_pointee_type())
            .and_then(|t| t.get_declaration())
            .and_then(|b| b.get_definition())
            .map(|b| b == base)
            .unwrap_or(false)
            && params.get(1).is_none()
        })
        .map(|method| (method, base))
    })
    .or_else(|| get_cast_method(target, get_single_base_class(base)?))
}

fn get_custom_is_type_method<'tu>(
  target: Entity<'tu>, // Target class, e.g. Boolean.
  _base: Entity<'tu>,  // Ancestor class, e.g. Value.
) -> Option<String> {
  let target_name = target.get_name()?;
  if [
    "BigInt",
    "Boolean",
    "Context",
    "FixedArray",
    "FunctionTemplate",
    "Module",
    "ModuleRequest",
    "Name",
    "Number",
    "ObjectTemplate",
    "Primitive",
    "Private",
    "String",
    "Symbol",
    "Value",
  ]
  .iter()
  .any(|&n| n == &*target_name)
  {
    let method_name = format!("Is{}", target_name);
    Some(method_name)
  } else {
    None
  }
}

fn get_is_type_method<'tu>(
  target: Entity<'tu>, // Target class, e.g. Boolean.
  base: Entity<'tu>,   // Ancestor class, e.g. Value.
) -> Option<String> {
  use EntityKind::*;
  let method_name = format!("Is{}", target.get_name()?); // e.g. "IsBoolean".
  base
    .get_children()
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
    .map(|m| m.get_name().unwrap())
    .or_else(|| get_is_type_method(target, get_single_base_class(base)?))
}

fn get_try_from_check_inner<'tu>(
  target: Entity<'tu>, // Target class, e.g. Boolean.
  base: Entity<'tu>,   // Base class, e.g. Primitive.
  var_name: &str,
  wrap: bool,
) -> Option<String> {
  get_custom_is_type_method(target, base)
    .or_else(|| get_is_type_method(target, base))
    .map(|method_name| format!("{}.{}()", var_name, to_snake_case(method_name)))
    .or_else(|| {
      let subclasses =
        get_direct_subclasses(target).filter(|list| list.len() > 1)?;
      let expr = match target.get_name()?.as_str() {
        // Special case: 'null' and 'undefined' don't have a class of their
        // own but they are primitive nonetheless.
        "Primitive" => match base.get_name()?.as_str() {
          "Value" => format!("{}.is_null_or_undefined()", var_name),
          _ => return None,
        },
        _ => Default::default(),
      };
      subclasses
        .into_iter()
        .try_fold(expr, |mut expr0, subclass| {
          let expr1 =
            get_try_from_check_inner(subclass, base, var_name, false)?;
          if !expr0.is_empty() {
            expr0.push_str(" || ");
          }
          expr0.push_str(&expr1);
          Some(expr0)
        })
        .map(|mut expr| {
          if wrap {
            expr = format!("({})", expr);
          }
          expr
        })
    })
}

fn get_try_from_check<'tu>(
  target: Entity<'tu>, // Target class, e.g. Boolean.
  base: Entity<'tu>,   // Base class, e.g. Primitive.
  var_name: &str,
  wrap: bool,
) -> Option<String> {
  get_try_from_check_inner(target, base, var_name, wrap).or_else(|| {
    std::iter::successors(Some(target), |&target| {
      get_single_base_class(target).filter(|&middle| middle != base)
    })
    .skip(1)
    .find_map(|middle| {
      let expr1 = get_try_from_check_inner(middle, base, var_name, true)?;
      let expr2 = get_try_from_check_inner(
        target,
        middle,
        &format!("cast::<{}>(v)", get_flat_name(middle)),
        true,
      )?;
      let expr = format!("{} && {}", expr1, expr2);
      Some(expr)
    })
  })
}

fn add_try_from_impls<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
  ancestor: Entity<'tu>,
) -> fmt::Result {
  if let Some(expr) = get_try_from_check(class, ancestor, "v", false) {
    let w = defs.get_class_def(class).try_from_impl(ancestor);
    writeln!(
      w,
      "impl_try_from! {{ {} for {} if v => {} }}",
      get_flat_name(ancestor),
      get_flat_name(class),
      expr
    )?;
  }
  if let Some(ancestor_base) = get_single_base_class(ancestor) {
    add_try_from_impls(defs, class, ancestor_base)?;
  }
  Ok(())
}

fn is_class_comparable_by_identity(e: Entity) -> bool {
  // A class supports comparison by identity if:
  //  - EITHER it is any of the following classes:p
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
    && !has_derived_class_in_v8_ns(e, "Number")
}

fn is_class_comparable_by_same_value_zero(e: Entity) -> bool {
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
  } else if is_class_comparable_by_same_value_zero(class1)
    && is_class_comparable_by_same_value_zero(class2)
  {
    // Total equality (the `Eq` trait) requires that comparison between two
    // values of the same type is reflexive (a == a). This true for all
    // JavaScript types except `Number`, because NaN != NaN. However, for
    // practical reasons such as being able to add a `v8::Value` to a HashMap,
    // we do want to implement `Eq` for all its descendants including `Number`.
    // So we use the semantics EcmaScript defines when e.g. an element is added
    // to a Set and it has to decide whether that element already existed in the
    // set before. The abstract operation is called `SameValueZero`, which is
    // essentially defined as follows:
    // (ECMA-262 6th edition § 7.2.10;
    //  http://ecma-international.org/ecma-262/6.0/#sec-samevaluezero)
    //
    // ```js
    // function same_value_zero(a, b) {
    //   return Object.is(a, b) || (a === 0 && b === 0);
    // }
    // ```
    //
    // The only difference with `Value::SameValue()` and `Object.is()` is that
    // `-0` and `0` compare equal under these rules.
    Some("same_value_zero")
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

fn class_has_get_identiy_hash_method(class: Entity) -> bool {
  use EntityKind::*;
  class.get_children().into_iter().any(|m| {
    m.get_name()
      .map(|n| n == "GetIdentityHash")
      .unwrap_or(false)
      && m.get_kind() == Method
      && !m.is_static_method()
      && !m.is_virtual_method()
      && !m
        .get_children()
        .into_iter()
        .any(|p| p.get_kind() == ParmDecl)
  }) || get_single_base_class(class)
    .map(class_has_get_identiy_hash_method)
    .unwrap_or(false)
}

fn get_hash_method(e: Entity) -> Option<&'static str> {
  if class_has_get_identiy_hash_method(e) {
    Some("get_identity_hash")
  } else if has_base_class_in_v8_ns(e, "Value") {
    Some("get_hash")
  } else {
    None
  }
}

fn maybe_add_eq_and_hash_impl<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
) -> fmt::Result {
  if get_partial_eq_compare_method(class, class).is_some() {
    let class_def = defs.get_class_def(class);
    let w_eq = class_def.eq_impl();
    writeln!(w_eq, "impl_eq! {{ for {} }}", get_flat_name(class))?;
  }
  if let Some(hash_method) = get_hash_method(class) {
    let class_def = defs.get_class_def(class);
    let w_hash = class_def.hash_impl();
    writeln!(
      w_hash,
      "impl_hash! {{ for {} use {} }}",
      get_flat_name(class),
      hash_method
    )?;
  }
  Ok(())
}

fn visit_class<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  class: Entity<'tu>,
) -> fmt::Result {
  add_struct_definition(defs, class)?;
  maybe_add_eq_and_hash_impl(defs, class)?;
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

pub fn generate_data_rs(tu: TranslationUnit) {
  let mut defs = ClassDefIndex::new();
  visit_translation_unit(&mut defs, &tu);

  println!("{}", boilerplate());
  println!("{}", defs);
}

fn boilerplate() -> &'static str {
  r#"
// Copyright 2019-2022 the Deno authors. All rights reserved. MIT license.

use std::any::type_name;
use std::convert::From;
use std::convert::TryFrom;
use std::error::Error;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::hash::Hash;
use std::hash::Hasher;
use std::mem::transmute;
use std::ops::Deref;

use crate::support::Opaque;
use crate::Local;

extern "C" {
  fn v8__Data__EQ(this: *const Data, other: *const Data) -> bool;
  fn v8__Data__IsBigInt(this: *const Data) -> bool;
  fn v8__Data__IsBoolean(this: *const Data) -> bool;
  fn v8__Data__IsContext(this: *const Data) -> bool;
  fn v8__Data__IsFixedArray(this: *const Data) -> bool;
  fn v8__Data__IsFunctionTemplate(this: *const Data) -> bool;
  fn v8__Data__IsModule(this: *const Data) -> bool;
  fn v8__Data__IsModuleRequest(this: *const Data) -> bool;
  fn v8__Data__IsName(this: *const Data) -> bool;
  fn v8__Data__IsNumber(this: *const Data) -> bool;
  fn v8__Data__IsObjectTemplate(this: *const Data) -> bool;
  fn v8__Data__IsPrimitive(this: *const Data) -> bool;
  fn v8__Data__IsPrivate(this: *const Data) -> bool;
  fn v8__Data__IsString(this: *const Data) -> bool;
  fn v8__Data__IsSymbol(this: *const Data) -> bool;
  fn v8__Data__IsValue(this: *const Data) -> bool;

  fn v8__Value__SameValue(this: *const Value, other: *const Value) -> bool;
  fn v8__Value__StrictEquals(this: *const Value, other: *const Value) -> bool;
}

impl Data {
  /// Returns true if this data is a `BigInt`.
  pub fn is_big_int(&self) -> bool {
    unsafe { v8__Data__IsBigInt(self) }
  }

  /// Returns true if this data is a `Boolean`.
  pub fn is_boolean(&self) -> bool {
    unsafe { v8__Data__IsBoolean(self) }
  }

  /// Returns true if this data is a `Context`.
  pub fn is_context(&self) -> bool {
    unsafe { v8__Data__IsContext(self) }
  }

  /// Returns true if this data is a `FixedArray`.
  pub fn is_fixed_array(&self) -> bool {
    unsafe { v8__Data__IsFixedArray(self) }
  }

  /// Returns true if this data is a `FunctionTemplate`.
  pub fn is_function_template(&self) -> bool {
    unsafe { v8__Data__IsFunctionTemplate(self) }
  }

  /// Returns true if this data is a `Module`.
  pub fn is_module(&self) -> bool {
    unsafe { v8__Data__IsModule(self) }
  }

  /// Returns true if this data is a `ModuleRequest`.
  pub fn is_module_request(&self) -> bool {
    unsafe { v8__Data__IsModuleRequest(self) }
  }

  /// Returns true if this data is a `Name`.
  pub fn is_name(&self) -> bool {
    unsafe { v8__Data__IsName(self) }
  }

  /// Returns true if this data is a `Number`.
  pub fn is_number(&self) -> bool {
    unsafe { v8__Data__IsNumber(self) }
  }

  /// Returns true if this data is a `ObjectTemplate`.
  pub fn is_object_template(&self) -> bool {
    unsafe { v8__Data__IsObjectTemplate(self) }
  }

  /// Returns true if this data is a `Primitive`.
  pub fn is_primitive(&self) -> bool {
    unsafe { v8__Data__IsPrimitive(self) }
  }

  /// Returns true if this data is a `Private`.
  pub fn is_private(&self) -> bool {
    unsafe { v8__Data__IsPrivate(self) }
  }

  /// Returns true if this data is a `String`.
  pub fn is_string(&self) -> bool {
    unsafe { v8__Data__IsString(self) }
  }

  /// Returns true if this data is a `Symbol`.
  pub fn is_symbol(&self) -> bool {
    unsafe { v8__Data__IsSymbol(self) }
  }

  /// Returns true if this data is a `Value`.
  pub fn is_value(&self) -> bool {
    unsafe { v8__Data__IsValue(self) }
  }
}

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
    impl<'s> From<Local<'s, $source>> for Local<'s, $type> {
      fn from(l: Local<'s, $source>) -> Self {
        unsafe { transmute(l) }
      }
    }
  };
}

macro_rules! impl_try_from {
  { $source:ident for $target:ident if $value:pat => $check:expr } => {
    impl<'s> TryFrom<Local<'s, $source>> for Local<'s, $target> {
      type Error = DataError;
      fn try_from(l: Local<'s, $source>) -> Result<Self, Self::Error> {
        #[allow(dead_code)]
        fn cast<T>(l: Local<$source>) -> Local<T> {
          unsafe { transmute(l) }
        }
        match l {
          $value if $check => Ok(unsafe { transmute(l) }),
          _ => Err(DataError::bad_type::<$target, $source>())
        }
      }
    }
  };
}

macro_rules! impl_eq {
  { for $type:ident } => {
    impl Eq for $type {}
  };
}

macro_rules! impl_hash {
  { for $type:ident use $method:ident } => {
    impl Hash for $type {
      fn hash<H: Hasher>(&self, state: &mut H) {
        self.$method().hash(state)
      }
    }
  };
}

macro_rules! impl_partial_eq {
  { $rhs:ident for $type:ident use identity } => {
    impl<'s> PartialEq<$rhs> for $type {
      fn eq(&self, other: &$rhs) -> bool {
        let a = self as *const _ as *const Data;
        let b = other as *const _ as *const Data;
        unsafe { v8__Data__EQ(a, b) }
      }
    }
  };
  { $rhs:ident for $type:ident use strict_equals } => {
    impl<'s> PartialEq<$rhs> for $type {
      fn eq(&self, other: &$rhs) -> bool {
        let a = self as *const _ as *const Value;
        let b = other as *const _ as *const Value;
        unsafe { v8__Value__StrictEquals(a, b) }
      }
    }
  };

  { $rhs:ident for $type:ident use same_value_zero } => {
    impl<'s> PartialEq<$rhs> for $type {
      fn eq(&self, other: &$rhs) -> bool {
        let a = self as *const _ as *const Value;
        let b = other as *const _ as *const Value;
        unsafe {
          v8__Value__SameValue(a, b) || {
            let zero = &*Local::<Value>::from(Integer::zero());
            v8__Value__StrictEquals(a, zero) && v8__Value__StrictEquals(b, zero)
          }
        }
      }
    }
  };
}

#[derive(Clone, Copy, Debug)]
pub enum DataError {
  BadType {
    actual: &'static str,
    expected: &'static str,
  },
  NoData {
    expected: &'static str,
  },
}

impl DataError {
  pub(crate) fn bad_type<E: 'static, A: 'static>() -> Self {
    Self::BadType {
      expected: type_name::<E>(),
      actual: type_name::<A>(),
    }
  }

  pub(crate) fn no_data<E: 'static>() -> Self {
    Self::NoData {
      expected: type_name::<E>(),
    }
  }
}

impl Display for DataError {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Self::BadType { expected, actual } => {
        write!(f, "expected type `{}`, got `{}`", expected, actual)
      }
      Self::NoData { expected } => {
        write!(f, "expected `Some({})`, found `None`", expected)
      }
    }
  }
}

impl Error for DataError {}  
"#
  .trim()
}
