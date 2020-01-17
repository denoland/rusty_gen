#include <cassert>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <iostream>
#include <sstream>
#include <string>
#include <type_traits>
#include <typeinfo>
#include <utility>

// Functions and static methods.
template <class F, template <bool, class, class...> class Functor>
class transform_function {
  template <class R, class... A>
  static constexpr auto deduce(R (*)(A...))
      -> Functor<std::is_void_v<R>, R, A...>;

public:
  using type = decltype(deduce(std::declval<F>()));
};

template <class F, template <bool, class, class...> class Functor>
using transform_function_t = typename transform_function<F, Functor>::type;


// Functions and static methods.
template <auto wrapped_fn, intptr_t context>
class add_context {
  template <bool is_void, class R, class... A>
  struct wrap;

  // Call function without return value.
  template <class R, class... A>
  struct wrap<true, R, intptr_t, A...> {
    __attribute__((noinline))
    static void fn(A... args) {
      wrapped_fn(context, std::forward<A>(args)...);
    }
  };

  // Call function with return value.
  template <class R, class... A>
  struct wrap<false, R, intptr_t, A...> {
    __attribute__((noinline))
    static R fn(A... args) {
      return wrapped_fn(context, std::forward<A>(args)...);
    }
  };

public:
  static constexpr auto fn =
      transform_function_t<decltype(wrapped_fn), wrap>::fn;


  static auto _gen() {
    return std::make_pair(add_context<wrapped_fn, context - 1>::_gen(), fn);
  }
};

template <auto wrapped_fn>
class add_context<wrapped_fn, -1>
{
public:
  static std::nullptr_t _gen() {
    return nullptr;
  }
};

__attribute__((noinline))
intptr_t leuk(intptr_t v, const char* s) {
  std::cout << s << v << std::endl;
  return v * 2;
}


void mooi_1(intptr_t v, char a, int b, double c, uint16_t d, void* e, bool f) {}
extern decltype(mooi_1)* mooi_2 = &mooi_1;

void mooi(intptr_t v, char a, int b, double c, uint16_t d, void* e, bool f) {
    mooi_2(v,a,b,c,d,e,f);
}

intptr_t forward(intptr_t (*fn)(const char* s)) {
  return fn("text");
}

extern auto f = add_context<leuk, 5>::_gen();
extern auto g = add_context<mooi, 5>::_gen();

int main() {
  auto r = forward(add_context<leuk, 5>::fn);
  return static_cast<int>(r);
}




