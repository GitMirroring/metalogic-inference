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

#include <unordered_map>
#include <vector>

#include "MLI.hh"


namespace mli {

  // Propositions treated as a formula sequence in unification.
  class sequence_database : public database {
  public:
    typedef std::vector<ref<statement>> sequence_table;
    typedef sequence_table::iterator sequence_iterator;
    typedef sequence_table::const_iterator const_sequence_iterator;

    typedef std::unordered_map<std::string, ref<statement>> name_table;
    typedef name_table::iterator name_iterator;
    typedef name_table::const_iterator name_const_iterator;

    sequence_table sequence_table_;
    name_table name_table_;
    bool has_definition_;

    sequence_database() : has_definition_(false) {}

    new_copy(sequence_database);
    new_move(sequence_database);

    sequence_database(const ref<statement>& x) { insert(x); }

    sequence_database(const sequence_database&, const sequence_database&);

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual alternatives unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const override;


    virtual ref<formula> rename(level, degree) const;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

    virtual bool empty() const { return sequence_table_.empty(); }
    virtual int get_level() const { return 1; }
    virtual bool has_definition(level) const { return has_definition_; }

    virtual bool insert(const ref<statement>&);
    virtual void insert(const ref<sequence_database>&);

    virtual std::optional<ref<statement>> find(const std::string& name, level) override;

    virtual size_type metasize() const override;

    virtual bool expand_premise(level) const override;

    virtual void write(std::ostream&, write_style) const;
  };


  class sublevel_database : public database {
  public:
    typedef std::vector<ref<database>> level_table;
    typedef level_table::iterator level_iterator;
    typedef level_table::const_iterator const_level_iterator;

    level_table table_;

    sublevel_database() = default;

    new_copy(sublevel_database);
    new_move(sublevel_database);

    sublevel_database(const ref<database>& x) : table_{x} {}

    void push_back(const ref<database>& x) { table_.push_back(x); }

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual alternatives unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const override;


    virtual ref<formula> rename(level, degree) const;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

    virtual bool empty() const;
    virtual int get_level() const { return table_.size(); }
    virtual bool has_definition(level) const;

    virtual bool insert(const ref<statement>& s);

    virtual std::optional<ref<statement>> find(const std::string& name, level) override;

    virtual size_type metasize() const override;

    virtual bool expand_premise(level) const override;

    virtual void write(std::ostream&, write_style) const;
  };


  class level_database : public database {
  public:
    typedef std::vector<ref<database>> level_table;
    typedef level_table::iterator level_iterator;
    typedef level_table::const_iterator const_level_iterator;

    level_table table_;

    level_database() = default;

    new_copy(level_database);
    new_move(level_database);

    level_database(const ref<database>& x) : table_{x} {}

    void push_back(const ref<database>& x) { table_.push_back(x); }

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual alternatives unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const override;

    virtual ref<formula> rename(level, degree) const;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

    virtual database& operator[](size_type lv) override;

    virtual bool empty() const;
    virtual int get_level() const { return table_.size(); }
    virtual bool has_definition(level) const;

    virtual bool insert(const ref<statement>& s);

    virtual std::optional<ref<statement>> find(const std::string& name, level) override;

    virtual size_type metasize() const override;

    virtual bool expand_premise(level) const override;

    virtual void write(std::ostream&, write_style) const;
  };


  // Propositions recorded in the order entered into the database.
  class sequential_database : public database {
  public:
    typedef std::vector<ref<statement>> sequential_table;
    typedef sequential_table::iterator sequential_iterator;
    typedef sequential_table::const_iterator const_sequential_iterator;

    typedef std::unordered_map<std::string, ref<statement>> name_table;
    typedef name_table::iterator name_iterator;
    typedef name_table::const_iterator name_const_iterator;

    sequential_table sequential_table_;
    name_table name_table_;
    bool has_definition_;

    sequential_database() : has_definition_(false) {}

    new_copy(sequential_database);
    new_move(sequential_database);

    sequential_database(const ref<statement>& x) { insert(x); }

    sequential_database(const sequential_database&, const sequential_database&);

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual alternatives unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const override;


    virtual ref<formula> rename(level, degree) const;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

    virtual bool empty() const { return sequential_table_.empty(); }
    virtual int get_level() const { return 1; }
    virtual bool has_definition(level) const { return has_definition_; }

    virtual bool insert(const ref<statement>&);

    virtual std::optional<ref<statement>> find(const std::string& name, level) override;

    virtual size_type metasize() const override;

    virtual void write(std::ostream&, write_style) const;
  };


  // Propositions recorded in the order entered in the theory;
  // also name search keys.
  class theory : public sequential_database {
  public:
    std::string name_;                // Name of theory.
    std::list<ref<theory>> includes_; // Other theories included.

    theory() = default;

    new_copy(theory);
    new_move(theory);

    theory(const std::string& name) : name_(name) {}

    virtual std::string name() const { return name_; }

    virtual bool insert(const ref<theory>& x)    { includes_.push_back(x); return true; }
    virtual bool insert(const ref<statement>& p) { return sequential_database::insert(p); }

    virtual std::optional<ref<statement>> find(const std::string& name, level) override;

    virtual void write(std::ostream&, write_style) const;
  };


  class theory_database : public unit {
  public:
    typedef std::vector<ref<theory>> sequential_table;
    typedef sequential_table::iterator sequential_iterator;
    typedef sequential_table::const_iterator const_sequential_iterator;

    typedef std::unordered_map<std::string, ref<theory>> name_table;
    typedef name_table::iterator name_iterator;
    typedef name_table::const_iterator name_const_iterator;

    std::string name_; // Name of theory database.
    
    // Set of theories recorded in two ways:
    sequential_table sequential_table_;
    name_table name_table_;

    theory_database() = default;

    new_copy(theory_database);
    new_move(theory_database);

    theory_database(const std::string& name) : name_(name) {}

    virtual std::string name() const { return name_; }

    virtual bool empty() const { return sequential_table_.empty(); }
    virtual int get_level() const { return 1; }

    virtual bool insert(const ref<theory>&);

    virtual std::optional<ref<theory>> find(const std::string& name);

    virtual void read(std::istream&);  // Defined in database-parser.yy.
    virtual void write(std::ostream&, write_style) const;
  };


  inline std::istream& operator>>(std::istream& is, theory_database& a) {
    a.read(is);  return is;
  }

} // namespace mli



