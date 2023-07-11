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

#pragma once


#define USE_ATOMIC_REF 1


// Clang does not support C++20 std::atomic_ref.
#if __clang__
#undef USE_ATOMIC_REF
#define USE_ATOMIC_REF 0
#endif


#if USE_ATOMIC_REF
#include <atomic>

// If no support for C++20 std::atomic_ref, use mutex instead.
#ifndef __cpp_lib_atomic_ref
#undef USE_ATOMIC_REF
#define USE_ATOMIC_REF 0
#endif

#endif // USE_ATOMIC_REF

#if !USE_ATOMIC_REF
#include <mutex>

extern std::mutex shared_mutex;


namespace std {

  template<class A> class atomic_ref;

  template<>
  class atomic_ref<size_t> {
    size_t* tp;

  public:
    explicit atomic_ref(size_t& x) : tp(&x) {}

    operator size_t() const noexcept { return *tp; }

    size_t operator++() const noexcept {
      std::lock_guard<std::mutex> guard(shared_mutex);
      ++*tp;
      return *tp;
    }

    size_t operator--() const noexcept {
      std::lock_guard<std::mutex> guard(shared_mutex);
      --*tp;
      return *tp;
    }
  };

} // namespace std

#endif // USE_ATOMIC_REF


// Placeholder value, to select GC collectible operator new.
struct shared_t {};
constexpr shared_t shared{};


void* operator new(std::size_t n, shared_t, size_t);
void operator delete(void* p, shared_t) noexcept;

// Stores a word att the bottom of the memory allocation for the reference count.
inline void* operator new(std::size_t n, shared_t, size_t k = 0) {
  // Allocate a word for the reference count value. Alignment usually fulfilled by:
  // std::atomic_ref<size_t>::required_alignment <= __STDCPP_DEFAULT_NEW_ALIGNMENT__
  void* p = operator new(n + sizeof(size_t));

  *(size_t*)p = k; // Set reference count to 0: the class ref<A> increments it.

  void* rp = static_cast<char*>(p) + sizeof(size_t);

  return rp; // Return the base for the object allocation.
}


inline void operator delete(void* p, shared_t) noexcept {
  if (p == nullptr)
    return;

  void* op = static_cast<char*>(p) - sizeof(size_t); // Original pointer.

  operator delete(op);
}
