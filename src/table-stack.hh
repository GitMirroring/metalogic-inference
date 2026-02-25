/* Copyright (C) 2017, 2021-2026 Hans Åberg.

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

#include <vector>
#include <unordered_map>

#include <utility>


namespace mli {

  template<class Key, class T>
  class table_stack {
  public:
    using key_type = Key;
    using table = std::unordered_map<Key, T>;
    using stack = std::vector<std::pair<bool, table>>;
    using size_type = typename stack::size_type;

    using mapped_type = T;
    using value_type = std::pair<const key_type, T>;

  //private:
    stack table_stack_;

  public:
    table_stack() = default;

    // Refer to the stack, not the table at each level:
    bool      empty() const { return table_stack_.empty(); }
    size_type size() const  { return table_stack_.size(); }
    table& top()            { return table_stack_.back().second; }

    bool insert(const Key&, const T&);
    bool insert_or_assign(const Key&, const T&);

    // Insert at level below top, if possible.
    bool insert_below(const Key&, const T&);

    std::optional<T> find(const Key&);
    std::optional<T> find_top(const Key&);
    
    // Finds highest level matching both name and mapped value property:
    template<class Property>
    std::optional<T> find(const Key& key, Property p) {
      typename stack::reverse_iterator i, i0 = table_stack_.rbegin(), i1 = table_stack_.rend();
      for (i = i0; i != i1; ++i) {
        typename table::iterator j = i->find(key);
        if (j != i->end() && p(j->second))
          return j->second.second;  // Variable key with matching property found:
      }
      return {};
    }

    // Argument b true if a principal level, used by insert_or_assign.
    void push_level(bool = true);
    void pop_level();
    void clear();

    void write(std::ostream& os) const;
  };


  template<class Key, class T>
  bool table_stack<Key, T>::insert(const Key& key, const T& x) {
    if (table_stack_.empty())
      return false;

    return table_stack_.back().second.insert(std::pair<const Key, T>(key, x)).second;
  }


  template<class Key, class T>
  bool table_stack<Key, T>::insert_or_assign(const Key& key, const T& x) {
    if (table_stack_.empty())
      return false;

    typename stack::reverse_iterator i, i0 = table_stack_.rbegin(), i1 = table_stack_.rend();

    for (i = i0; i != i1; ++i) {
      // Find from top, first principal level.
      if (!i->first)
        continue;

      return i->second.insert_or_assign(key, x).second;
    }

    return false;
  }


  template<class Key, class T>
  bool table_stack<Key, T>::insert_below(const Key& key, const T& x) {
    if (table_stack_.empty())
      return false;
    if (table_stack_.size() == 1)
      return table_stack_.back().insert(std::pair<const Key, T>(key, x)).second;
    return (--(--table_stack_.end()))->insert(std::pair<const Key, T>(key, x)).second;
  }


  template<class Key, class T>
  std::optional<T> table_stack<Key, T>::find(const Key& key) {
    typename stack::reverse_iterator i, i0 = table_stack_.rbegin(), i1 = table_stack_.rend();
    for (i = i0; i != i1; ++i) {
      typename table::iterator j = i->second.find(key);
      if (j != i->second.end())
        return j->second;  // Variable key found:
    }

    return {};
  }


  template<class Key, class T>
  std::optional<T> table_stack<Key, T>::find_top(const Key& key) {
    typename stack::reverse_iterator i0 = table_stack_.rbegin();
    typename table::iterator j = i0->second.find(key);
    if (j != i0->second.end())
      return j->second;  // Variable key found:

    return {};
  }


  template<class Key, class T>
  void table_stack<Key, T>::push_level(bool b) {
    table_stack_.push_back({b, table()});
  }


  template<class Key, class T>
  void table_stack<Key, T>::pop_level() {
    table_stack_.pop_back();
  }


  template<class Key, class T>
  void table_stack<Key, T>::clear() {
    table_stack_.clear();
    push_level();
  }


  template<class Key, class T>
  void table_stack<Key, T>::write(std::ostream& os) const {
    size_t k = 0;
    for (auto& i: table_stack_) {
      os << k++ << ": ";
      for (auto& j: i)
        os << j.first << " ";
      os << std::endl;
    }
  }


  template<class Key>
  class set_stack {
  public:
    using key_type = Key;
    using table = std::set<Key>;
    using stack = std::vector<table>;
    using size_type = typename stack::size_type;

    using mapped_type = Key;
    using value_type = key_type;

    //private:
    stack table_stack_;
    std::vector<size_type> bottom_stack_; // Top value defines bottom for find_local.

  public:
    set_stack() = default;

    set_stack(std::initializer_list<std::initializer_list<Key>> xs) {
      for (auto& i: xs) {
        table_stack_.push_back(table());
        for (auto& j: i)
         table_stack_.back().insert(j);
      }
    }

    // Refers to the stack, not the table at each level:
    bool      empty() const { return table_stack_.empty(); }
    size_type size() const  { return table_stack_.size(); }
    table& top()            { return table_stack_.back().second; }

    bool insert(const Key&);

    void insert(std::initializer_list<Key> xs) {
      if (table_stack_.empty()) return;

      for (auto& i: xs)
        insert(i);
    }

    // Search from the top table down to the bottom level table.
    bool contains(const Key&) const;
    bool contains_top(const Key&) const;

    // Search from the top table down to the bottom level table, and return
    // size to the bottom, 0 if not in the table.
    size_t depth(const Key&) const;

    // Search from the top table down to immediately above the bottom level
    // table, as defined by the bottom stack.
    bool contains_local(const Key&) const;

    // Collects all stored objects from the top table down to immediately above
    // the bottom level table.
    void find_local(std::set<Key>&) const;
    std::set<Key> find_local() const { std::set<Key> ks; find_local(ks); return ks; }

    void push_level();
    void pop_level();
    void clear();

    // A stack for the bottom level searched by contains_local.
    void push_bottom();
    void pop_bottom();

    void write(std::ostream& os) const;
  };


  template<class Key>
  std::ostream& operator<<(std::ostream& os, const set_stack<Key>& x) { x.write(os); return os; }


  template<class Key>
  bool set_stack<Key>::insert(const Key& key) {
    if (table_stack_.empty())
      return false;

    return table_stack_.back().insert(key).second;
  }


  template<class Key>
  bool set_stack<Key>::contains(const Key& key) const {
    for (auto i = table_stack_.crbegin(); i != table_stack_.crend(); ++i) {
      if (i->find(key) != i->end())
        return true;  // Variable key found:
    }

    return false;
  }


  template<class Key>
  bool set_stack<Key>::contains_top(const Key& key) const {
    if (table_stack_.empty())
      return false;

    typename stack::reverse_iterator i0 = table_stack_.crbegin();

    if (i0->second.find(key) != i0->second.end())
      return true;  // Variable key found:

    return false;
  }


  template<class Key>
  size_t set_stack<Key>::depth(const Key& key) const {

    for (auto i = table_stack_.crbegin(); i != table_stack_.crend(); ++i) {
      typename table::iterator j = i->find(key);
      if (j != i->end())
        return std::distance(i, table_stack_.crend());  // Variable key found:
    }

    return 0;
  }


  template<class Key>
  bool set_stack<Key>::contains_local(const Key& key) const {
    typename stack::const_reverse_iterator i, i0 = table_stack_.rbegin(), i1 = table_stack_.rend();

    if (!bottom_stack_.empty())
      i1 -= bottom_stack_.back();

    for (i = i0; i != i1; ++i) {
      typename table::iterator j = i->find(key);
      if (j != i->end())
        return true;  // Variable key found:
    }

    return false;
  }


  template<class Key>
  void set_stack<Key>::find_local(std::set<Key>& ks) const {
    typename stack::const_reverse_iterator i, i0 = table_stack_.rbegin(), i1 = table_stack_.rend();

    if (!bottom_stack_.empty())
      i1 -= bottom_stack_.back();

    for (i = i0; i != i1; ++i)
      for (auto& j: *i)
        ks.insert(j);
  }


  template<class Key>
  void set_stack<Key>::push_level() {
    table_stack_.push_back(table());
  }


  template<class Key>
  void set_stack<Key>::pop_level() {
    table_stack_.pop_back();
  }


  template<class Key>
  void set_stack<Key>::clear() {
    table_stack_.clear();
    bottom_stack_.clear();
  }


  template<class Key>
  void set_stack<Key>::push_bottom() {
    bottom_stack_.push_back(table_stack_.size());
  }

  template<class Key>
  void set_stack<Key>::pop_bottom() { bottom_stack_.pop_back(); }


  template<class Key>
  void set_stack<Key>::write(std::ostream& os) const {
    size_t k = 0;
    bool it0 = true;
    for (auto& i: table_stack_) {
      if (it0) it0 = false; else os << std::endl;
      os << k++ << ": ";
      for (auto& j: i) {
        os << j << " ";
      }
    }
    it0 = true;
    if (!bottom_stack_.empty()) os << std::endl;
    for (auto& i: bottom_stack_) {
      if (it0) it0 = false; else os << ", ";
      os << i;
    }
  }


  // Guard classes for exception safe push/pop of level and bottom.

  template<class Stack>
  class level_guard {
    Stack* stack_ = nullptr;

  public:
    level_guard() = delete;

    explicit level_guard(Stack& s) : stack_(&s) { stack_->push_level(); }
    ~level_guard() { stack_->pop_level(); }

    level_guard(const level_guard&) = delete;
  };


  template<class Stack>
  class bottom_guard {
    Stack* stack_ = nullptr;

  public:
    bottom_guard() = delete;

    explicit bottom_guard(Stack& s) : stack_(&s) { stack_->push_bottom(); }
    ~bottom_guard() { stack_->pop_bottom(); }

    bottom_guard(const bottom_guard&) = delete;
  };

} // namespace mli

