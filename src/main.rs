use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter};
use std::path::Path;
use std::process::exit;

use clang::diagnostic::Severity;
use clang::*;

#[derive(Eq, PartialEq)]
struct Def<'tu> {
  entity: Entity<'tu>,
  sort_key: Vec<String>,
  body: Vec<String>,
}

impl<'tu> Def<'tu> {
  pub fn new(entity: Entity<'tu>) -> Self {
    Self {
      entity,
      sort_key: Vec::new(),
      body: Vec::new(),
    }
  }

  pub fn entity(&self) -> Entity<'tu> {
    self.entity
  }

  pub fn push_sort_key(&mut self, s: String) {
    self.sort_key.push(s);
  }

  pub fn add_line(&mut self, s: String) {
    self.body.push(s);
  }
}

impl<'tu> PartialOrd for Def<'tu> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<'tu> Ord for Def<'tu> {
  fn cmp(&self, other: &Self) -> Ordering {
    use Ordering::*;
    self
      .sort_key
      .iter()
      .zip(other.sort_key.iter())
      .map(|(a, b)| a.cmp(b))
      .find(|o| *o != Equal)
      .unwrap_or_else(|| self.sort_key.len().cmp(&other.sort_key.len()))
  }
}

impl<'tu> Display for Def<'tu> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    for l in self.body.iter() {
      writeln!(f, "{}", l)?;
    }
    Ok(())
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

  let defs = visit_tu(tu.get_entity());

  println!("{}", boilerplate());
  for d in defs {
    println!("{}", d);
  }
}

fn boilerplate() -> &'static str {
  r"// Copyright 2018-2019 the Deno authors. All rights reserved. MIT license.

use std::convert::From;
use std::convert::TryFrom;
use std::mem::transmute;
use std::ops::Deref;

use crate::support::Opaque;
use crate::Local;

macro_rules! impl_deref {
  { $a:ident for $b:ident } => {
    impl Deref for $a {
      type Target = $b;
      fn deref(&self) -> &Self::Target {
        unsafe { &*(self as *const _ as *const Self::Target) }
      }
    }
  };
}

macro_rules! impl_from {
  { $a:ident for $b:ident } => {
    impl<'sc> From<Local<'sc, $a>> for Local<'sc, $b> {
      fn from(l: Local<'sc, $a>) -> Self {
        unsafe { transmute(l) }
      }
    }
  };
}

#[derive(Clone, Copy, Debug)]
pub struct TryFromTypeError;

macro_rules! impl_try_from {
  { $a:ident for $b:ident if $p:pat => $c:expr } => {
    impl<'sc> TryFrom<Local<'sc, $a>> for Local<'sc, $b> {
      type Error = TryFromTypeError;
      fn try_from(l: Local<'sc, $a>) -> Result<Self, Self::Error> {
        match l {
          $p if $c => Ok(unsafe { transmute(l) }),
          _ => Err(TryFromTypeError)
        }
      }
    }
  };
}
"
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

// Returns the name of an entity for use in a flat namespace.
// E.g. "v8::Promise::Resolver" -> "PromiseResolver".
fn get_flat_name(e: Entity) -> Option<String> {
  let mut name = e.get_name()?;
  let mut p = e;
  loop {
    use EntityKind::*;
    p = p.get_semantic_parent()?;
    match p.get_kind() {
      ClassDecl => {
        name = format!("{}{}", p.get_name()?, name);
      }
      Namespace => break Some(name),
      _ => {}
    }
  }
}

fn is_data_or_subclass(e: Entity) -> bool {
  is_data_class(e)
    || get_base_class(e).map(is_data_or_subclass).unwrap_or(false)
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

fn to_snake_case(s: impl AsRef<str>) -> String {
  let mut words = vec![];
  // Preserve leading underscores
  let s = s.as_ref();
  let s = s.trim_start_matches(|c: char| {
    if c == '_' {
      words.push(String::new());
      true
    } else {
      false
    }
  });
  for part in s.split('_') {
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

fn get_try_from_condition<'tu>(
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
        |condition, s| {
          Some(Some(format!(
            "{}{}",
            condition.map(|s| format!("{} || ", s)).unwrap_or_default(),
            get_try_from_condition(s, b)?
          )))
        },
      )?
    })
}

fn add_sort_key(def: &mut Def, e: Entity) {
  if let Some(b) = get_base_class(e) {
    add_sort_key(def, b);
  }
  def.push_sort_key(get_flat_name(e).unwrap());
}

fn add_local_from_impls(def: &mut Def, a: Entity) -> Option<()> {
  let e = def.entity();
  if let Some(b) = get_base_class(a) {
    add_local_from_impls(def, b)?;
  }
  def.add_line(format!(
    "impl_from! {{ {} for {} }}",
    get_flat_name(e)?,
    get_flat_name(a)?,
  ));
  Some(())
}

fn add_local_try_from_impls(def: &mut Def, a: Entity) -> Option<()> {
  let e = def.entity();
  def.add_line(format!(
    "impl_try_from! {{ {} for {} if v => {} }}",
    get_flat_name(a)?,
    get_flat_name(e)?,
    get_try_from_condition(e, a)?
  ));
  if let Some(b) = get_base_class(a) {
    add_local_try_from_impls(def, b)?;
  }
  Some(())
}

fn wrap_comment_line(comment: String) -> Vec<String> {
  let mut lines = Vec::<String>::new();
  for part in comment.split_ascii_whitespace() {
    match lines.last_mut() {
      Some(l) if l.len() + 1 + part.len() < 80 => {
        l.push(' ');
        l.push_str(part);
      }
      _ => {
        lines.push(format!("/// {}", part));
      }
    }
  }
  lines
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

fn visit_data_or_subclass(def: &mut Def) -> Option<()> {
  let e = def.entity();
  add_sort_key(def, e);
  if let Some(comment) = e.get_comment() {
    def.add_line(format_comment(comment));
  }
  def.add_line("#[repr(C)]".to_owned());
  def.add_line(format!("pub struct {}(Opaque);", get_flat_name(e)?));
  if let Some(b) = get_base_class(e) {
    def.add_line(format!(
      "impl_deref! {{ {} for {} }}",
      get_flat_name(e)?,
      get_flat_name(b)?
    ));
    add_local_from_impls(def, b)?;
    add_local_try_from_impls(def, b)?;
  }
  Some(())
}

fn visit_entity(e: Entity) -> Option<Def> {
  if e.is_definition() && is_data_or_subclass(e) {
    let mut def = Def::new(e);
    visit_data_or_subclass(&mut def);
    Some(def)
  } else {
    None
  }
}

fn visit_tu<'tu>(tu: Entity<'tu>) -> Vec<Def<'tu>> {
  let mut defs: Vec<Def<'tu>> = Vec::new();
  tu.visit_children(|e: Entity<'tu>, _| {
    if let Some(def) = visit_entity(e) {
      defs.push(def);
    }
    EntityVisitResult::Recurse
  });
  defs.sort();
  defs
}
