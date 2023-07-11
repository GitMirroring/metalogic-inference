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


#include <iostream>
#include <string>
#include <utility>

#include <gmp.h>

#include "gc.hh"


inline void mpz_move(mpz_t x, mpz_t y) { *x = *y; }
inline void mpq_move(mpq_t x, mpq_t y) { *x = *y; }


namespace gmp {

  class integer;
  class rational;

  class integer {
  public:
    mpz_t value_;

  public:
    integer() { mpz_init(value_); }
    ~integer() { mpz_clear(value_); }

    integer(const integer& x) { mpz_init(value_); mpz_set(value_, x.value_); }
    integer(integer&& x) { mpz_move(value_, x.value_); mpz_init(x.value_); }

    integer& operator=(const integer& x) {  // Assignment operator.
      // Do nothing if assigning to self:
      if (this != &x)  mpz_set(value_, x.value_);
      return *this;
    }

    integer& operator=(integer&& x) {  // Move assignment operator.
      // Do nothing if assigning to self:
      if (this != &x) { mpz_clear(value_); mpz_move(value_, x.value_); mpz_init(x.value_); }
      return *this;
    }

    integer(int x) { mpz_init_set_si(value_, x); }
    integer(unsigned x) { mpz_init_set_ui(value_, x); }
    integer(signed long int x) { mpz_init_set_si(value_, x); }
    integer(unsigned long int x) { mpz_init_set_ui(value_, x); }

    integer(double x) { mpz_init_set_d(value_, x); }

    explicit integer(const char* x, int base = 10) { mpz_init_set_str(value_, x, base); }
    explicit integer(const std::string& x, int base = 10)
    { mpz_init_set_str(value_, (char*)x.c_str(), base); }

    // Reduces the use of move assignment operator:
    integer& operator=(unsigned int x) { mpz_set_ui(value_, x); return *this; }
    integer& operator=(signed int x) { mpz_set_si(value_, x); return *this; }
    integer& operator=(unsigned long int x) { mpz_set_ui(value_, x); return *this; }
    integer& operator=(signed long int x) { mpz_set_si(value_, x); return *this; }
    integer& operator=(double x) { mpz_set_d(value_, x); return *this; }
    integer& operator=(const char* str) { mpz_set_str(value_, str, 10); return *this; }
    

    explicit operator signed long int() const { return mpz_get_si(value_); }
    explicit operator unsigned long int() const { return mpz_get_ui(value_); }

    explicit operator double() const { return mpz_get_d(value_); }

    std::string str(int base = 10) const {
      char* cs = new char[mpz_sizeinbase(value_, base) + 2];
      mpz_get_str(cs, base, value_);
      std::string str_r(cs); delete[] cs;
      return str_r;
    }

    int compare(integer const& x) const { return mpz_cmp(value_, x.value_); }

    void swap(integer& x) { mpz_swap(value_, x.value_); }
    
    friend integer operator+(integer const&, integer const&);
    friend integer& operator+(integer&);
    friend integer operator-(integer const&);
    friend integer operator-(integer const&, integer const&);
    friend integer operator*(integer const&, integer const&);
    friend rational operator/(integer const&, integer const&);

    integer& operator+=(integer const&);
    integer& operator+=(unsigned long int);

    integer& operator-=(integer const&);
    integer& operator-=(unsigned long int);
    
    integer& operator*=(integer const&);
    integer& operator*=(long int);
    integer& operator*=(unsigned long int);

    friend bool operator==(integer const&, integer const&);
    friend bool operator!=(integer const&, integer const&);

    friend bool operator<(integer const&, integer const&);
    friend bool operator>(integer const&, integer const&);
    friend bool operator<=(integer const&, integer const&);
    friend bool operator>=(integer const&, integer const&);

    friend integer abs(integer const&); // Absolute value.

    friend std::istream& operator>>(std::istream&, integer&);
    friend std::ostream& operator<<(std::ostream&, integer const&);
    
    friend size_t sizeinbase(integer const&, int base);
    friend integer divexact(integer const& n, integer const& d);
    friend integer divexact(integer const& n, unsigned long d);

    friend std::hash<integer>;
  };


  inline integer operator+(integer const& x, integer const& y) {
    integer r;  mpz_add(r.value_, x.value_, y.value_);  return r;
  }

  inline integer operator+(integer const& x, unsigned long int y) {
    integer r;  mpz_add_ui(r.value_, x.value_, y);  return r;
  }

  inline integer& operator+(integer& x) { return x; }
  
  inline integer operator-(integer const& x) {
    integer r;  mpz_neg(r.value_, x.value_);  return r;
  }

  // Use negate(x, y) to avoid use of move assignment operator in x = -y.
  inline integer& negate(integer& x, integer const& y) {
    mpz_neg(x.value_, y.value_);  return x;
  }

  inline integer operator-(integer const& x, integer const& y) {
    integer r;  mpz_sub(r.value_, x.value_, y.value_);  return r;
  }

  inline integer operator*(integer const& x, integer const& y) {
    integer r;  mpz_mul(r.value_, x.value_, y.value_);  return r;
  }
  
  inline integer operator*(integer const& x, unsigned long int y) {
    integer r;  mpz_mul_ui(r.value_, x.value_, y);  return r;
  }

  
  inline integer& integer::operator+=(integer const& x) {
    mpz_add(value_, value_, x.value_);  return *this;
  }
  
  inline integer& integer::operator+=(unsigned long int x) {
    mpz_add_ui(value_, value_, x);  return *this;
  }
  
  inline integer& integer::operator-=(integer const& x) {
    mpz_sub(value_, value_, x.value_);  return *this;
  }
  
  inline integer& integer::operator-=(unsigned long int x) {
    mpz_sub_ui(value_, value_, x);  return *this;
  }
  
  inline integer& integer::operator*=(integer const& x) {
    mpz_mul(value_, value_, x.value_);  return *this;
  }

  inline integer& integer::operator*=(long int x) {
    mpz_mul_si(value_, value_, x);  return *this;
  }

  inline integer& integer::operator*=(unsigned long int x) {
    mpz_mul_ui(value_, value_, x);  return *this;
  }


  inline bool operator==(integer const& x, integer const& y)  { return x.compare(y) == 0; }
  inline bool operator!=(integer const& x, integer const& y)  { return x.compare(y) != 0; }

  inline bool operator<(integer const& x, integer const& y)   { return x.compare(y) < 0; }
  inline bool operator>(integer const& x, integer const& y)   { return x.compare(y) > 0; }
  inline bool operator<=(integer const& x, integer const& y)  { return x.compare(y) <= 0; }
  inline bool operator>=(integer const& x, integer const& y)  { return x.compare(y) >= 0; }


  inline integer abs(integer const& x) {
    integer r;  mpz_abs(r.value_, x.value_);  return r;
  }


  inline std::ostream& operator<<(std::ostream& os, integer const& n) {
    return os << n.str();
  }

  inline size_t sizeinbase(integer const& x, int b) {
    return mpz_sizeinbase(x.value_, b);
  }
  
  inline integer divexact(integer const& n, integer const& d) {
    integer q;  mpz_divexact(q.value_, n.value_, d.value_);  return q;
  }
  
  inline integer divexact(integer const& n, unsigned long d) {
    integer q;  mpz_divexact_ui(q.value_, n.value_, d);  return q;
  }

  // Avoids move assignement operator:
  inline integer& divexact(integer& q, integer const& n, integer const& d) {
    mpz_divexact(q.value_, n.value_, d.value_);  return q;
  }
  
  inline integer& divexact(integer& q, integer const& n, unsigned long d) {
    mpz_divexact_ui(q.value_, n.value_, d);  return q;
  }

} // namespace gmp


namespace std {
  template<> struct hash<gmp::integer> {
    size_t operator()(gmp::integer const& x) const {
      std::size_t h = std::hash<mp_size_t>()(x.value_->_mp_size);
      for (mp_size_t i = 0; i < mpz_size(x.value_); ++i)
        h ^= std::hash<mp_limb_t>()(mpz_getlimbn(x.value_, i));
      return h;
    }
  };
} // namespace std


namespace gmp {

  
  class rational {
  public:
    mpq_t value_;

  public:
    rational() { mpq_init(value_); }
    ~rational() { mpq_clear(value_); }

    rational(rational const& x) { mpq_init(value_); mpq_set(value_, x.value_); }
    rational(rational&& x) { mpq_move(value_, x.value_); mpq_init(x.value_); }

    rational& operator=(rational const& x) {  // Assignment operator.
      // Do nothing if assigning to self:
      if (this != &x)  mpq_set(value_, x.value_);
      return *this;
    }

    rational& operator=(rational&& x) {       // Move assignment operator.
      // Do nothing if assigning to self:
      if (this != &x) { mpq_clear(value_); mpq_move(value_, x.value_); mpq_init(x.value_); }
      return *this;
    }

    void canonicalize() { mpq_canonicalize(value_); }

    rational(signed long int x, unsigned long int y = 1)
    { mpq_init(value_);  mpq_set_si(value_, x, y);  mpq_canonicalize(value_); }
    rational(unsigned long int x, unsigned long int y = 1)
    { mpq_init(value_);  mpq_set_ui(value_, x, y);  mpq_canonicalize(value_); }

    explicit rational(double x) { mpq_init(value_); mpq_set_d(value_, x); }

    explicit rational(const char* x, int base = 10) {
      mpq_init(value_);
      mpq_set_str(value_, x, base);
      mpq_canonicalize(value_);
    }
    
    explicit rational(const std::string& x, int base = 10) {
      mpq_init(value_);
      mpq_set_str(value_, (char*)x.c_str(), base);
      mpq_canonicalize(value_);
    }

    rational(integer const& x) { mpq_init(value_); mpq_set_z(value_, x.value_); }
    rational(integer const& p, integer const& q) { mpq_init(value_);
      mpq_set_num(value_, p.value_); mpq_set_den(value_, q.value_); canonicalize(); }

    integer num() const { integer p; mpq_get_num(p.value_, value_); return p; }
    integer den() const { integer q; mpq_get_den(q.value_, value_); return q; }

    explicit operator double() const { return mpq_get_d(value_); }

    operator std::pair<integer, integer>() const { return std::pair<integer, integer>(num(), den()); }
    
    std::string str(int base = 10) const {
      char* cs = new char[mpz_sizeinbase(mpq_numref(value_), base)
                          + mpz_sizeinbase (mpq_denref(value_), base) + 3];
      mpq_get_str(cs, base, value_);
      std::string str_r(cs); delete[] cs;
      return str_r;
    }
    

    int compare(rational const& x) const { return mpq_cmp(value_, x.value_); }
    int equal(rational const& x) const { return mpq_equal(value_, x.value_); }


    void swap(rational& x) { mpq_swap(value_, x.value_); }

    rational& operator+=(rational const& x) { mpq_add(value_, value_, x.value_); return *this; }
    
    friend rational operator+(rational const&, rational const&);
    friend rational& operator+(rational&);
    friend rational operator-(rational const&, rational const&);
    friend rational operator-(rational const&);
    friend rational operator*(rational const&, rational const&);
    friend rational operator/(rational const&, rational const&);

    friend bool operator==(rational const&, rational const&);
    friend bool operator!=(rational const&, rational const&);

    friend bool operator<(rational const&, rational const&);
    friend bool operator>(rational const&, rational const&);
    friend bool operator<=(rational const&, rational const&);
    friend bool operator>=(rational const&, rational const&);

    friend std::istream& operator>>(std::istream&, rational&);
    friend std::ostream& operator<<(std::ostream&, rational const&);
  };


  inline rational operator+(rational const& x, rational const& y) {
    rational r;  mpq_add(r.value_, x.value_, y.value_);  return r;
  }

  inline rational& operator+(rational& x) { return x; }

  inline rational operator-(rational const& x, rational const& y) {
    rational r;  mpq_sub(r.value_, x.value_, y.value_);  return r;
  }

  inline rational operator-(rational const& x) {
    rational r;  mpq_neg(r.value_, x.value_);  return r;
  }

  inline rational operator*(rational const& x, rational const& y) {
    rational r;  mpq_mul(r.value_, x.value_, y.value_);  return r;
  }

  inline rational operator/(rational const& x, rational const& y) {
    rational r;  mpq_div(r.value_, x.value_, y.value_);  return r;
  }


  inline bool operator==(rational const& x, rational const& y)
  {  return x.equal(y) != 0;  }

  inline bool operator!=(rational const& x, rational const& y)
  {  return x.equal(y) == 0;  }


  inline bool operator<(rational const& x, rational const& y)
  {  return x.compare(y) < 0;  }

  inline bool operator>(rational const& x, rational const& y)
  {  return x.compare(y) > 0;  }

  inline bool operator<=(rational const& x, rational const& y)
  {  return x.compare(y) <= 0;  }

  inline bool operator>=(rational const& x, rational const& y)
  {  return x.compare(y) >= 0;  }


  inline std::ostream& operator<<(std::ostream& os, rational const& r) {
    return os << r.str();
  }


  inline rational operator/(integer const& x, integer const& y) {
    rational x0(x), y0(y), r;  mpq_div(r.value_, x0.value_, y0.value_);  return r;
  }
  
  inline rational abs(rational const& x) {
    rational r;  mpz_abs(mpq_numref(r.value_), mpq_numref(x.value_));
    mpq_set_den(r.value_, mpq_denref(x.value_));  return r;
  }


  inline integer ceil(rational const& x) {
    integer r;  mpz_cdiv_q(r.value_, mpq_numref(x.value_), mpq_denref(x.value_));  return r;
  }

  inline integer floor(rational const& x) {
    integer r;  mpz_fdiv_q(r.value_, mpq_numref(x.value_), mpq_denref(x.value_));  return r;
  }

  inline integer trunc(rational const& x) {
    integer r;  mpz_tdiv_q(r.value_, mpq_numref(x.value_), mpq_denref(x.value_));  return r;
  }

  inline rational frac_ceil(rational const& x) {
    rational r;  mpz_cdiv_r(mpq_numref(r.value_), mpq_numref(x.value_), mpq_denref(x.value_));
    mpq_set_den(r.value_, mpq_denref(x.value_));  return r;
  }

  inline rational frac_floor(rational const& x) {
    rational r;  mpz_fdiv_r(mpq_numref(r.value_), mpq_numref(x.value_), mpq_denref(x.value_));
    mpq_set_den(r.value_, mpq_denref(x.value_));  return r;
  }

  inline rational frac_trunc(rational const& x) {
    rational r;  mpz_tdiv_r(mpq_numref(r.value_), mpq_numref(x.value_), mpq_denref(x.value_));
    mpq_set_den(r.value_, mpq_denref(x.value_));  return r;
  }

  inline std::pair<integer, rational> div_ceil(rational const& x) {
    std::pair<integer, rational> r;
    mpz_cdiv_qr(r.first.value_, mpq_numref(r.second.value_), mpq_numref(x.value_), mpq_denref(x.value_));
    mpq_set_den(r.second.value_, mpq_denref(x.value_));
    return r;
  }

  inline std::pair<integer, rational> div_floor(rational const& x) {
    std::pair<integer, rational> r;
    mpz_fdiv_qr(r.first.value_, mpq_numref(r.second.value_), mpq_numref(x.value_), mpq_denref(x.value_));
    mpq_set_den(r.second.value_, mpq_denref(x.value_));
    return r;
  }

  inline std::pair<integer, rational> div_trunc(rational const& x) {
    std::pair<integer, rational> r;
    mpz_tdiv_qr(r.first.value_, mpq_numref(r.second.value_), mpq_numref(x.value_), mpq_denref(x.value_));
    mpq_set_den(r.second.value_, mpq_denref(x.value_));
    return r;
  }


} // namespace gmp


namespace std {
  template<> struct hash<gmp::rational> {
    size_t operator()(gmp::rational const& x) const {
      return std::hash<gmp::integer>()(x.num()) ^ std::hash<gmp::integer>()(x.den());
    }
  };
} // namespace std


