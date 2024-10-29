/* Copyright (C) 2017, 2021-2024 Hans Åberg.

   This file is part of MLI, MetaLogic Inference.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */


  // Template classes for runtime polymorphic variables.
  //
  // The class ref<A> provides a plain reference.


#pragma once

#include "relation.hh"

#include <initializer_list>
#include <memory>
#include <variant>


namespace mli {

  template<class A>
  class ref;

  template<class A>
  class val;


  // Placeholder struct and value
  struct make_t {};
  constexpr make_t make{};


  // Class ref<A> provides collectible, finalized, dynamically allocated objects,
  // i.e., those are not to be expected to be removed using operator delete. When
  // finalized, the destructor ~A is invoced, so its uncollectible object become
  // deallocated.
  template<class A>
  class ref {
  protected:
    std::shared_ptr<A> data_{new A};

  public:
    using element_type = A;
    using value_type = A;
    using reference = A&;
    using pointer = A*;
    using const_reference = const A&;
    using const_pointer = const A*;

    ref() = default;
    ~ref() = default;

    ref(const ref& x) = default;
    ref(ref&& x) = default;

    ref& operator=(const ref& x) & = default;
    ref& operator=(ref&& x) & = default;


    // Conversion constructors:

    template<class B> friend class ref;

    template<class B>
    ref(const ref<B>& br) : data_(dynamic_pointer_cast<A>(br.data_)) {}

    // Conversion val<B> → ref<A>:

    template<class B>
    ref(const val<B>& br) : data_(&dynamic_cast<A&>(*br->new_p())) {}

    // Allocate and construct a ref<A> object, invoked by using
    // the placeholder value 'make' in the firat argument. Semantics:
    // 1. Forward remaining arguments B&&... bs to the constructor of A.
    // 2. Allocate a heap object using new (collect) A(bs...).
    // 3. Register the created object for finalization with the GC.
    template<class... B>
    ref(make_t, B&&... bs) : data_(new A(bs...)) {}

    template<class B, class... C>
    ref(make_t, std::initializer_list<B> bs, C&&... cs) : data_(new A(bs, cs...)) {}


    // Conversion from std::variant<B...> to val<A>.
    // All classes B... must be polymorphic. If the B that the variant
    // holds cannot be dynamic cast to A, an exception is thrown.
    template<class... B>
    ref(const std::variant<B...>& v)
     : data_(std::visit([](auto&& x) -> A*
     { return &dynamic_cast<A&>(*new std::decay_t<decltype(x)>(x)); }, v)) {}


    // Access to stored pointer:
    constexpr A* data() const noexcept { return data_.get(); }


    // Dereference object:

    constexpr const A& operator*() const& { return *data_.get(); }
    constexpr A& operator*() & { return *data_.get(); }

    constexpr const A&& operator*() const&& { return std::move(*data_.get()); }
    constexpr A&& operator*() && { return std::move(*data_.get()); }


    // Dereference object member:
    constexpr A* operator->() noexcept { return data_.get(); }
    constexpr const A* operator->() const noexcept { return data_.get(); }


    // Return the operator() value the the data held:
    template<class... B>
    auto operator()(B&&... bs) -> typename std::invoke_result<A, B...>::type
    { return (*data_)(bs...); }

    template<class... B>
    auto operator()(B&&... bs) const -> typename std::invoke_result<A, B...>::type
    { return (*data_)(bs...); }
  };
}


namespace std {
  // Hash code to ref<A> if class A has it:
  template<class A> struct hash<mli::ref<A>> {
    size_t operator()(const mli::ref<A>& x) const {
      return typeid(x).hash_code() ^ std::hash<A>()(*x);
    }
  };
} // namespace std


namespace mli {

  // Functions providing dynamic_cast shorthands from ref<B> to A* or A&.
  // For x of type ref<B>, one has
  //   dyn_cast<A*>(x) = dynamic_cast<A*>(x.data())
  //   dyn_cast<A&>(x) = dynamic_cast<A&>(*x.data())
  // Usage is similar to that of dynamic_cast:
  //   ref<B> b;
  //   A* ap = dyn_cast<A*>(b);
  //   A& ar = dyn_cast<A&>(b);
  // As an alternative, one can also use
  //   ref<A> a(b);
  // Then ap = a.data(), ar = *a = *a.data(), and, by operator->, ap->x = a->x.
  template<class A, class B>
  inline typename std::enable_if<std::is_pointer<A>::value, A>::type
  dyn_cast(const ref<B>& b) { return dynamic_cast<A>(b.data()); }

  template<class A, class B>
  inline typename std::enable_if<std::is_lvalue_reference<A>::value, A>::type
  dyn_cast(const ref<B>& b) { return dynamic_cast<A>(*b.data()); }


  template<class A>
  inline std::istream& operator>>(std::istream& is, ref<A>& a) { return is >> (*a); }

  template<class A>
  inline std::ostream& operator<<(std::ostream& os, const ref<A>& a) { return os << (*a); }


  template<class A, class B>
  inline order operator<=>(const ref<A>& x, const ref<B>& y) { return *x <=> *y; }


  template<class A, class B>
  constexpr bool operator==(const ref<A>& x, const ref<B>& y) { return comparison(equal)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator!=(const ref<A>& x, const ref<B>& y) { return comparison(~equal)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator<(const ref<A>& x, const ref<B>& y) { return comparison(less)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator>(const ref<A>& x, const ref<B>& y) { return comparison(greater)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator<=(const ref<A>& x, const ref<B>& y) { return comparison(less|equal)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator>=(const ref<A>& x, const ref<B>& y) { return comparison(greater|equal)(*x <=> *y); }


  template<class A, class B>
  inline ref<A> operator+(const ref<A>& x, const ref<B>& y) {
    return (*x + *y);
  }

  template<class A, class B>
  inline ref<A> operator*(const ref<A>& x, const ref<B>& y) {
    return ((*x) * (*y));
  }


  template<class A>
  class val {
  protected:
    A* data_ = new A; // Always non-null.

  public:
    using element_type = A;
    using value_type = A;

    using reference = A&;
    using pointer = A*;
    using const_reference = const A&;
    using const_pointer = const A*;

    template<typename B> friend class val;


    val() = default;
    ~val() { delete data_; }

    val(const val& x) : data_(x.data_->new_p()) {}
    val(val&& x) { data_ = x.data_; x.data_ = (new val)->data_; }

    val& operator=(const val& x) & {
      // Do nothing if assigning to self:
      if (this != std::addressof(x)) {
        // If polymorphic types are the same, polymorphic placement new_p is used
        // to avoid memory allocation:
        //   x.data_->new_p(data_);
        // By contrast, '*data_ = *x.data_' only assigns type A, an error here.
        if (typeid(*data_) == typeid(*x.data_)) {
          data_->~A();
          x.data_->new_p(data_);
        }
        else {
          this->~val();
          data_ = x.data_->new_p();
        }
      }

      return *this;
    }


    val& operator=(val&& x) & {
      // Do nothing if assigning to self:
      if (this != std::addressof(x)) {
        this->~val();
        data_ = x.data_;
        x.data_ = new A;
      }

      return *this;
    }


    val& operator=(const A& x) & {
      // If polymorphic types are the same (the type of x may be derived from A),
      // polymorphic placement new_p is used
      // to avoid memory allocation:
      //   x.new_p(data_);
      // By contrast, '*data_ = x' only assigns type A, an error here.
      if (typeid(*data_) == typeid(x)) {
        data_->~A();
        x.new_p(data_);
      }
      else {
        this->~val();
        data_ = x.new_p();
      }

      return *this;
    }


    val& operator=(A&& x) & {
      // As the type of x may be derived from A, polymorphic operator new_p is used:
      this->~val();
      data_ = std::move(x).new_p();
      return *this;
    }


    // Allocate and construct a val<A> object, invoked by using the placeholder
    // value 'make' in the firat argument. Semantics:
    // 1. Forward the arguments B&&... bs to the constructor of A.
    // 2. Allocate an objecte new A(bs...).

    template<class... B>
    val(make_t, B&&... bs) : data_(new A(bs...)) {}

    template<class B, class... C>
    val(make_t, std::initializer_list<B> bs, C&&... cs) : data_(new A(bs, cs...)) {}


    // Conversion constructors:

    // Conversion A → val<A>:
    val(const A& ar) : data_(ar.new_p()) {}
    val(A&& ar) : data_(std::move(ar).new_p()) {}

    // Conversion val<B> → val<A>:

    template<class B>
    val(const val<B>& br) : data_(&dynamic_cast<A&>(*br->new_p())) {}

    template<class B>
    val(val<B>&& br) { this->~val(); data_ = &dynamic_cast<A&>(*br.data()); br.data_ = new B; }

    // Conversion ref<B> → val<A>:
    // Since ref<B> pointer values cannot be moved, as may have other references,
    // there is only a copy constructor.
    template<class B>
    val(const ref<B>& br) : data_(&dynamic_cast<A&>(*br->new_p())) {}


    // Conversion from std::variant<B...> to val<A>.
    // All classes B... must be polymorphic. If the B that the variant
    // holds cannot be dynamic cast to A, an exception is thrown.
    template<class... B>
    val(const std::variant<B...>& v)
     : data_(std::visit([](auto&& x) -> A*
     { return &dynamic_cast<A&>(*new std::decay_t<decltype(x)>(x)); }, v)) {}


    // Access to stored pointer:
    A* data() const noexcept { return data_; }


    // Dereference object:
    A const& operator*() const& { return *data_; }
    A& operator*() & { return *data_; }
    A&& operator*() && { return std::move(*data_); }

    // Dereference object member:
    A* operator->() noexcept { return data_; }
    const A* operator->() const noexcept { return data_; }

    // Return the operator() value the the data held:
    template<class... B>
    auto operator()(B&&... bs) -> typename std::invoke_result<A, B...>::type
    { return (*data_)(bs...); }

    template<class... B>
    auto operator()(B&&... bs) const -> typename std::invoke_result<A, B...>::type
    { return (*data_)(bs...); }


    template<typename B>
    friend class ref;
  };

} // namespace mli


namespace std {
  // Hash code to val<A> if class A has it:
  template<class A> struct hash<mli::val<A>> {
    size_t operator()(const mli::val<A>& x) const {
      return typeid(x).hash_code() ^ std::hash<A>()(*x);
    }
  };
} // namespace std


namespace mli {

  // Functions providing dynamic_cast shorthands from val<B> to A* or A&.
  // For x of type val<B>, one has
  //   dyn_cast<A*>(x) = dynamic_cast<A*>(x.data())
  //   dyn_cast<A&>(x) = dynamic_cast<A&>(*x.data())
  // Usage is similar to that of dynamic_cast:
  //   dyn_cast<B> b;
  //   A* ap = dyn_cast<A*>(b);
  //   A& ar = dyn_cast<A&>(b);
  // As an alternative, also making a copy, one can use
  //   val<A> a(b);
  // Then ap = a.data(), ar = *a = *a.data(), and, by operator->, ap->x = a->x.
  template<class A, class B>
  inline typename std::enable_if<std::is_pointer<A>::value, A>::type
  dyn_cast(const val<B>& b) { return dynamic_cast<A>(b.data()); }

  template<class A, class B>
  inline typename std::enable_if<std::is_lvalue_reference<A>::value, A>::type
  dyn_cast(const val<B>& b) { return dynamic_cast<A>(*b.data()); }


  template<class A>
  inline std::istream& operator>>(std::istream& is, val<A>& a) { return is >> (*a); }

  template<class A>
  inline std::ostream& operator<<(std::ostream& os, const val<A>& a) { return os << (*a); }


  template<class A, class B>
  inline order operator<=>(const val<A>& x, const val<B>& y) { return *x <=> *y; }


  template<class A, class B>
  constexpr bool operator==(const val<A>& x, const val<B>& y) { return comparison(equal)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator!=(const val<A>& x, const val<B>& y) { return comparison(~equal)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator<(const val<A>& x, const val<B>& y) { return comparison(less)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator>(const val<A>& x, const val<B>& y) { return comparison(greater)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator<=(const val<A>& x, const val<B>& y) { return comparison(less|equal)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator>=(const val<A>& x, const val<B>& y) { return comparison(greater|equal)(*x <=> *y); }


  template<class A, class B>
  inline val<A> operator+(const val<A>& x, const val<B>& y) {
    return (*x + *y);
  }

  template<class A, class B>
  inline val<A> operator*(const val<A>& x, const val<B>& y) {
    return ((*x) * (*y));
  }


  template<class A, class B>
  constexpr bool operator==(const ref<A>& x, const val<B>& y) { return comparison(equal)(*x <=> *y); }

  template<class A, class B>
  constexpr bool operator==(const val<A>& x, const ref<B>& y) { return comparison(equal)(*x <=> *y); }


  // val<A> when 1, ref<A> when 0.
#define USE_VAL0 0 // <sequence>
#define USE_VAL1 0 // <theory>
#define USE_VAL2 0 // <sequence_database>
#define USE_VAL3 0 // <sublevel_database>
#define USE_VAL4 0 // <statement>
#define USE_VAL5 0 // <level_database>
#define USE_VAL6 0 // <unit>
#define USE_VAL7 1

#if USE_VAL0
  template<class A>
  using ref0 = val<A>;
#else
  template<class A>
  using ref0 = ref<A>;
#endif

#if USE_VAL1
  template<class A>
  using ref1 = val<A>;
#else
  template<class A>
  using ref1 = ref<A>;
#endif

#if USE_VAL2
  template<class A>
  using ref2 = val<A>;
#else
  template<class A>
  using ref2 = ref<A>;
#endif

#if USE_VAL3
  template<class A>
  using ref3 = val<A>;
#else
  template<class A>
  using ref3 = ref<A>;
#endif

#if USE_VAL4
  template<class A>
  using ref4 = val<A>;
#else
  template<class A>
  using ref4 = ref<A>;
#endif

#if USE_VAL5
  template<class A>
  using ref5 = val<A>;
#else
  template<class A>
  using ref5 = ref<A>;
#endif

#if USE_VAL6
  template<class A>
  using ref6 = val<A>;
#else
  template<class A>
  using ref6 = ref<A>;
#endif

#if USE_VAL7
  template<class A>
  using ref7 = val<A>;
#else
  template<class A>
  using ref7 = ref<A>;
#endif


} // namespace mli

