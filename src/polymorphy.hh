/* Copyright (C) 2017, 2021-2023 Hans Åberg.

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

#include "gc.hh"
#include "relation.hh"

#include <initializer_list>


namespace mli {

  // Functions providing cast shorthands: If an implicit cast is possible,
  // static_cast is use, otherwise dynamic_cast is tried (which requires polymorhic
  // types, i.e., with a function declared 'virtual').
  template<class A, class B>
  inline typename std::enable_if<std::is_convertible<B, A>::value, A>::type
  cast(B&& x) { return static_cast<A>(x); }

  template<class A, class B>
  inline typename std::enable_if<!std::is_convertible<B, A>::value, A>::type
  cast(B&& x) { return dynamic_cast<A>(x); }


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
    A* data_ = new (shared, 1) A;

  public:
    typedef A         element_type;
    typedef A         value_type;
    typedef A&        reference;
    typedef A*        pointer;
    typedef const A&  const_reference;
    typedef const A*  const_pointer;

    ref() = default;

    ~ref() {
      void* op = static_cast<char*>((void*)data_) - sizeof(size_t); // Original pointer.

      auto k = std::atomic_ref<size_t>(*(size_t*)op); // Find reference count value.

      --k;

      if (k == 0)
        operator delete(data_, shared);
    }


    // Make a copy by incrementing the reference count.
    static A* copy(A* ap) {
      // The reference count is stored one word below ap:
      void* op = static_cast<char*>((void*)ap) - sizeof(size_t);

      auto k = std::atomic_ref<size_t>(*(size_t*)op);

      ++k;

      return ap;
    }


    ref(const ref& x) : data_(copy(x.data_)) {}
#if 0
    ref(ref&& x) { std::swap(data_, x.data_); }
#endif

    ref& operator=(const ref& x) & {
      if (data_ != x.data_) {
        this->~ref();
        data_ = copy(x.data_);
      }

      return *this;
    }
#if 0
    ref& operator=(ref&& x) & { std::swap(data_, x.data_); return *this; }
#endif


    // Conversion constructors:

    // Requires argument to refer to a GC allocated object:
    ref(A* ap) : data_(copy(ap)) {}
    ref(const A* ap) : data_(copy(const_cast<A*>(ap))) {}

    // Creates a polymorhic copy (clone).
    ref(const A& ar) : data_(ar.new_p(1)) {}

    template<class B>
    explicit ref(B* bp) : data_(copy(&cast<A&>(*bp))) {}


    template<class B>
    ref(const ref<B>& br) : data_(copy(&cast<A&>(*br.data()))) {}


    // Allocate and construct a ref<A> object, invoked by using
    // the placeholder value 'make' in the firat argument. Semantics:
    // 1. Forward remaining arguments B&&... bs to the constructor of A.
    // 2. Allocate a heap object using new (collect) A(bs...).
    // 3. Register the created object for finalization with the GC.
    template<class... B>
    ref(make_t, B&&... bs) : data_(new (shared, 1) A(bs...)) {}

    template<class B, class... C>
    ref(make_t, std::initializer_list<B> bs, C&&... cs) : data_(new (shared, 1) A(bs, cs...)) {}


    // Access to stored pointer:
    constexpr A* data() const noexcept { return data_; }


    // Reference (address) of contained object, using operator&.
    // For x of type ref<A>, &x = &*x.
    // Note: operator& overloading disables address of the object itself,
    // which then requires the use of std::addressof.
    constexpr A* operator&() noexcept { return data_; }
    constexpr const A* operator&() const noexcept { return data_; }


    // Dereference object:

    constexpr const A& operator*() const& { return *data_; }
    constexpr A& operator*() & { return *data_; }

    constexpr const A&& operator*() const&& { return std::move(*data_); }
    constexpr A&& operator*() && { return std::move(*data_); }


    // Dereference object member:
    constexpr A* operator->() noexcept { return data_; }
    constexpr const A* operator->() const noexcept { return data_; }


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

  // Functions providing cast shorthands from ref<B> to A* or A&.
  // For x of type ref<B>, one has
  //   ref_cast<A*>(x) = cast<A*>(x.data())
  //   ref_cast<A&>(x) = cast<A&>(*x.data())
  // where 'cast' is the template function above that selects static_cast or dynamic_cast.
  // Usage is similar to that of dynamic_cast:
  //   ref<B> b;
  //   A* ap = ref_cast<A*>(b);
  //   A& ar = ref_cast<A&>(b);
  // As an alternative, one can also use
  //   ref<A> a(b);
  // and then ap = a.data(), ar = *a = *a.data(), and ap->x = a->x.
  template<class A, class B>
  inline typename std::enable_if<std::is_pointer<A>::value, A>::type
  ref_cast(const ref<B>& b) { return cast<A>(b.data()); }

  template<class A, class B>
  inline typename std::enable_if<std::is_lvalue_reference<A>::value, A>::type
  ref_cast(const ref<B>& b) { return cast<A>(*b.data()); }


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
    A* data_ = new (shared, 1) A; // Always non-null.

  public:
    typedef A         element_type;
    typedef A         value_type;

    typedef A&         reference;
    typedef A*         pointer;
    typedef const A&   const_reference;
    typedef const A*   const_pointer;

    template<typename B> friend class val;


    val() = default;

    ~val() {
      void* op = static_cast<char*>((void*)data_) - sizeof(size_t); // Original pointer.

      auto k = std::atomic_ref<size_t>(*(size_t*)op);

      --k;

      if (k == 0)
        operator delete(data_, shared);
    }


    val(const val& x) : data_(x.data_->new_p(1)) {}
    val(val&& x) { std::swap(data_, x.data_); }

    val& operator=(const val& x) & {
      // Do nothing if assigning to self:
      if (this != std::addressof(x)) {
        // Same polymorphic type does not need reallocation:
        if (typeid(*data_) == typeid(*x.data_))
          *data_ = *x.data_;
        else {
          delete data_;
          data_ = x.data_->new_p(1);
        }
      }

      return *this;
    }

    val& operator=(val&& x) & { std::swap(data_, x.data_); return *this; }


    // Allocate and construct a val<A> object. Invoked by using
    // the placeholder value 'make' in the firat argument. Semantics:
    // 1. Forward the arguments B&&... bs to the constructor of A.
    // 2. Allocate an objecte new A(bs...).
    template<class... B>
    val(make_t, B&&... bs) : data_(new (shared, 1) A(bs...)) {}

#if 0
    // Not used, apparently.
    template<class B, class... C>
    val(make_t, std::initializer_list<B> bs, C&&... cs) : data_(new (shared, 1) A(bs, cs...)) {}
#endif


    // Conversion constructors:

    template<class B>
    val(val<B>& br) : data_(br->new_p(1)) {}

    template<class B>
    val(val<B>&& br) { std::swap(data_, br.data()); }

    template<class B>
    val(const val<B>& br) : data_(br->new_p(1)) {}

    // Requires argument to refer to a GC allocated object:
    val(A* ap) : data_(ap->new_p(1)) {}
    val(const A* ap) : data_(ap->new_p(1)) {}

    val(const A& ar) : data_(ar.new_p(1)) {}

    template<class B>
    explicit val(B* bp) : data_(bp->new_p(1)) {}


    // Conversions from val<A> to ref<B>, and vice versa:

    template<class B>
    val(ref<B>& br) : data_(br->new_p(1)) {}

    template<class B>
    val(const ref<B>& br) : data_(br->new_p(1)) {}


    template<class B>
    operator ref<B>() const { return ref<B>(data_); }


    // Access to stored pointer:
    A* data() const noexcept { return data_; }


    // Reference (address) of contained object, using operator~.
    // For x of type ref<A>, &x = &*x.
    // Note: operator& overloading disables address of the object itself,
    // which then requires the use of std::addressof.
    A* operator&() noexcept { return data_; }
    const A* operator&() const noexcept { return data_; }

    // Dereference object:
    A const& operator*() const& { return *data_; }
    A& operator*() & { return *data_; }
    A&& operator*() && { return std::move(*data_); }

    // Dereference object member:
    A* operator->() noexcept { return data_; }
    const A* operator->() const noexcept { return data_; }

    template<typename B>
    friend class ref;

    template<typename B>
    friend std::ostream& operator<<(std::ostream& os, const val<B>&);
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

  // Functions providing cast shorthands from ref<B> to A* or A&.
  // For x of type ref<B>, one has
  //   ref_cast<A*>(x) = cast<A*>(x.data())
  //   ref_cast<A&>(x) = cast<A&>(*x.data())
  // where 'cast' is the template function above that selects static_cast or dynamic_cast.
  // Usage is similar to that of dynamic_cast:
  //   ref<B> b;
  //   A* ap = ref_cast<A*>(b);
  //   A& ar = ref_cast<A&>(b);
  // As an alternative, one can also use
  //   ref<A> a(b);
  // and then ap = a.data(), ar = *a = *a.data(), and ap->x = a->x.
  template<class A, class B>
  inline typename std::enable_if<std::is_pointer<A>::value, A>::type
  val_cast(const val<B>& b) { return cast<A>(b.data()); }

  template<class A, class B>
  inline typename std::enable_if<std::is_lvalue_reference<A>::value, A>::type
  val_cast(const val<B>& b) { return cast<A>(*b.data()); }


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

} // namespace mli

