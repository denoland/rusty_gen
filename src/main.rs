mod data;

use std::path::Path;
use std::process::exit;

use clang::diagnostic::Severity;
use clang::*;

fn main() {
  let base_path = Path::new("/Users/piscisaureus/d/rusty_v8");

  let clang = Clang::new().unwrap();
  let index = Index::new(&clang, false, false);

  #[allow(clippy::useless_format)]
  let arg = |s| format!("{}", s);
  let path_arg = |suffix: &str| {
    let p = base_path.join(suffix);
    let s = p.to_str().unwrap();
    if cfg!(target_os = "windown") {
      s.replace('\\', "/")
    } else {
      s.to_owned()
    }
  };
  let isystem = |suffix: &str| format!("-isystem{}", path_arg(suffix));
  let tu = index
    .parser(base_path.join("v8/include/v8.h"))
    .arguments(&[
      arg("-x"),
      arg("c++"),
      arg("-std=c++17"),
      arg("-nostdinc++"),
      isystem("v8/include"),
      isystem("target/debug/clang/lib/clang/12.0.0/include"),
      isystem("buildtools/third_party/libc++/trunk/include"),
      isystem("buildtools/third_party/libc++abi/trunk/include"),
      arg("-DV8_IMMINENT_DEPRECATION_WARNINGS"),
      arg("-DV8_ENABLE_CHECKS")
      //arg("-D_LIBCPP_HAS_NO_VENDOR_AVAILABILITY_ANNOTATIONS"),
      //arg("-D_LIBCPP_DISABLE_VISIBILITY_ANNOTATIONS"),
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
