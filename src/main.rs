mod data;

use std::path::Path;
use std::process::exit;

use clang::diagnostic::Severity;
use clang::*;

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

  data::generate_data_rs(tu);
}
