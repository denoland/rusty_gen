use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter};
use std::path::Path;
use std::process::exit;

use clang::diagnostic::Severity;
use clang::*;

#[derive(Eq, PartialEq)]
struct Def<'tu> {
  entity: Entity<'tu>,
  key: Vec<String>,
  body: Vec<String>,
}

impl<'tu> Def<'tu> {
  pub fn new(entity: Entity<'tu>) -> Self {
    Self {
      entity,
      key: Vec::new(),
      body: Vec::new(),
    }
  }

  pub fn entity(&self) -> Entity<'tu> {
    self.entity
  }

  pub fn add_key(&mut self, s: String) {
    self.key.push(s);
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
      .key
      .iter()
      .zip(other.key.iter())
      .map(|(a, b)| a.cmp(b))
      .find(|o| *o != Equal)
      .unwrap_or_else(|| self.key.len().cmp(&other.key.len()))
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

macro_rules! impl_local_from {
  { $a:ident for $b:ident } => {
    impl<'sc> From<Local<'sc, $a>> for Local<'sc, $b> {
      fn from(l: Local<'sc, $a>) -> Self {
        unsafe { transmute(l) }
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

fn visit_ancestors(def: &mut Def, a: Entity) -> Option<()> {
  let e = def.entity();
  if let Some(b) = get_base_class(a) {
    visit_ancestors(def, b)?;
  }
  def.add_line(format!(
    "impl_local_from! {{ {} for {} }}",
    get_flat_name(e)?,
    get_flat_name(a)?,
  ));
  def.add_key(get_flat_name(a)?);
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
    visit_ancestors(def, b)?;
  }
  def.add_key(get_flat_name(e)?);
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
