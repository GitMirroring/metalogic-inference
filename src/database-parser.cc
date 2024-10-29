// A Bison parser, made by GNU Bison 3.8.2.

// Skeleton implementation for Bison LALR(1) parsers in C++

// Copyright (C) 2002-2015, 2018-2021 Free Software Foundation, Inc.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

// As a special exception, you may create a larger work that contains
// part or all of the Bison parser skeleton and distribute that work
// under terms of your choice, so long as that work isn't itself a
// parser generator using the skeleton or a modified version thereof
// as a parser skeleton.  Alternatively, if you modify or redistribute
// the parser skeleton itself, you may (at your option) remove this
// special exception, which will cause the skeleton and the resulting
// Bison output files to be licensed under the GNU General Public
// License without this special exception.

// This special exception was added by the Free Software Foundation in
// version 2.2 of Bison.

// DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
// especially those whose name start with YY_ or yy_.  They are
// private implementation details that can be changed or removed.


// Take the name prefix into account.
#define yylex   mlilex



#include "database-parser.hh"


// Unqualified %code blocks.
#line 119 "../../mli-root/src/database-parser.yy"


  // #define YYDEBUG 1


    /* MetaLogic Inference Database Parser. */

  #include <algorithm>
  #include <fstream>
  #include <iostream>
  #include <iterator>
  #include <sstream>
  #include <stack>
  #include <vector>
  #include <utility>

  #include "database.hh"
  #include "definition.hh"
  #include "proposition.hh"
  #include "substitution.hh"
  #include "metacondition.hh"

  #include "function.hh"

  #include "precedence.hh"


  std::string infile_name;

  extern bool declaration_context;
  extern bool maybe_set_declaration_context;
  extern bool proofline_database_context;
  extern bool statement_substitution_context;
  extern int bracket_depth;

  extern mli::database_parser::token_type declared_token;   // Lookahead token
  mli::database_parser::token_type current_declared_token;  // May be set in mid action to avoid using the lookahe token.
  extern int declared_type;
  extern int current_token;
  extern std::string current_line;

  extern std::set<std::string> clp_parser_variables;


  namespace mli {

    kleenean unused_variable = false;


    symbol_table_t symbol_table;

    std::set<val<variable>> statement_variables_;

    ref1<theory> theory_;  // Theory to enter propositions into.
    val<database> theorem_theory_;  // Theory used for a theorem proof.

    // Stacks to handle nested statements and their proofs:
    std::vector<ref4<statement>> statement_stack_; // Pushed & popped at statement boundaries.

    // Pushed & popped at proof boundaries:
    table_stack<std::string, ref4<statement>> proofline_stack_; // Proof line table.

    // The proofe depth is used for nested proof variable renumbering.
    // Incremented at the beginning of a theorem or subtheorem, and decremented at the proof end.
    depth proof_depth = 0, proof_depth0 = 0;


    database_parser::token_type to_token(variable::type t) {
      switch (t) {
        case variable::formula_:       return database_parser::token::object_formula_variable;
        case variable::predicate_:     return database_parser::token::predicate_variable;
        case variable::atom_:          return database_parser::token::atom_variable;
        case variable::function_:      return database_parser::token::function_variable;
        case variable::object_:        return database_parser::token::object_variable;
        default:                       return database_parser::token::token_error;
      }
    }


    // For bound variable definitions, set to the token type that
    // should be inserted in the symbol table:
    database_parser::token_type bound_variable_type = database_parser::token_type(0);

    val<formula> head(const statement& x) {
      auto xp = dyn_cast<inference*>(x.statement_);
      if (xp != nullptr)
        return xp->head_;
      return x.statement_;
    }


    database_parser::token_type define_variable(const std::string& text, database_parser::value_type& yylval) {
      if (statement_substitution_context) {
        statement_substitution_context = false;
        std::optional<symbol_table_value> x = symbol_table.find_top(text);

        if (!x) {
          yylval.emplace<std::string>(text);
          return database_parser::token::plain_name;
        }

        yylval.emplace<val<unit>>(x->second);

        return x->first;
      }

      if (declaration_context) {
        yylval.emplace<std::string>(text);
        return database_parser::token::plain_name;
      }

      std::optional<symbol_table_value> x = symbol_table.find(text);

      if (!x) {
        // Not a bound variable case:
        if (bound_variable_type == free_variable_context) {
          yylval.emplace<std::string>(text);
          return database_parser::token::plain_name;
        }

        // Bound variable case: Create a limited variable of bind 1, insert at the secondary
        // (bound variable) stack level.
        val<variable> v = val<variable>(make, text, variable::limited_, variable::object_, proof_depth);

        v->bind_ = 1;
        symbol_table.insert(text, {bound_variable_type, v});

        yylval.emplace<val<unit>>(v);

        return bound_variable_type;
      }

      variable* vp = dyn_cast<variable*>(x->second);

      if (vp != nullptr
        && (vp->depth_ == -1 || bound_variable_type != free_variable_context)) {

        if (bound_variable_type == free_variable_context) {
          // Case definition of a free variable:

          // Check if it is a variable which is declared without definition, in which case make
          // a copy with right proof depth, insert it in the symbol table, and change x->second
          // so subsequently the new copy is used instead of the original lookup value.
          val<variable> v(make, *vp);
          v->depth_ = proof_depth;

          symbol_table.insert_or_assign(text, {x->first, v});

          x->second = v;
        }
        else {
          // Case definition of a bound variable:

          // If ordinary (not limited), create a limited variable of bind 1, insert at
          // the secondary (bound variable) stack level.
          // If limited:
          //   If not defined, create a limited variable of bind 1, and insert at the
          //   primary (free variable) stack level.
          //   If defined, return it (do nothing, as x is already set to it).

          if (!vp->is_limited()) {
            val<variable> v(make, *vp);
            v->depth_ = proof_depth;
            v->metatype_ = variable::limited_;
            v->bind_ = 1;

            symbol_table.insert(text, {x->first, v});

            x->second = v;
          }
          else if (vp->depth_ == -1) {
            val<variable> v(make, *vp);
            v->depth_ = proof_depth;

            symbol_table.insert_or_assign(text, {x->first, v});

            x->second = v;
          }

          yylval.emplace<val<unit>>(x->second);

          return bound_variable_type;
        }
      }

      yylval.emplace<val<unit>>(x->second);

      return x->first;
    }

  } // namespace mli



#line 243 "../../mli-root/src/database-parser.cc"


#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> // FIXME: INFRINGES ON USER NAME SPACE.
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif


// Whether we are compiled with exception support.
#ifndef YY_EXCEPTIONS
# if defined __GNUC__ && !defined __EXCEPTIONS
#  define YY_EXCEPTIONS 0
# else
#  define YY_EXCEPTIONS 1
# endif
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K].location)
/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

# ifndef YYLLOC_DEFAULT
#  define YYLLOC_DEFAULT(Current, Rhs, N)                               \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).begin  = YYRHSLOC (Rhs, 1).begin;                   \
          (Current).end    = YYRHSLOC (Rhs, N).end;                     \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).begin = (Current).end = YYRHSLOC (Rhs, 0).end;      \
        }                                                               \
    while (false)
# endif


// Enable debugging if requested.
#if MLIDEBUG

// A pseudo ostream that takes yydebug_ into account.
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Symbol)         \
  do {                                          \
    if (yydebug_)                               \
    {                                           \
      *yycdebug_ << Title << ' ';               \
      yy_print_ (*yycdebug_, Symbol);           \
      *yycdebug_ << '\n';                       \
    }                                           \
  } while (false)

# define YY_REDUCE_PRINT(Rule)          \
  do {                                  \
    if (yydebug_)                       \
      yy_reduce_print_ (Rule);          \
  } while (false)

# define YY_STACK_PRINT()               \
  do {                                  \
    if (yydebug_)                       \
      yy_stack_print_ ();                \
  } while (false)

#else // !MLIDEBUG

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Symbol)  YY_USE (Symbol)
# define YY_REDUCE_PRINT(Rule)           static_cast<void> (0)
# define YY_STACK_PRINT()                static_cast<void> (0)

#endif // !MLIDEBUG

#define yyerrok         (yyerrstatus_ = 0)
#define yyclearin       (yyla.clear ())

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)

#line 22 "../../mli-root/src/database-parser.yy"
namespace mli {
#line 336 "../../mli-root/src/database-parser.cc"

  /// Build a parser object.
  database_parser::database_parser (mli::theory_database& yypval_yyarg, mli::database_lexer& mlilex_yyarg)
#if MLIDEBUG
    : yydebug_ (false),
      yycdebug_ (&std::cerr),
#else
    :
#endif
      yy_lac_established_ (false),
      yypval (yypval_yyarg),
      mlilex (mlilex_yyarg)
  {}

  database_parser::~database_parser ()
  {}

  database_parser::syntax_error::~syntax_error () YY_NOEXCEPT YY_NOTHROW
  {}

  /*---------.
  | symbol.  |
  `---------*/

  // basic_symbol.
  template <typename Base>
  database_parser::basic_symbol<Base>::basic_symbol (const basic_symbol& that)
    : Base (that)
    , value ()
    , location (that.location)
  {
    switch (this->kind ())
    {
      case symbol_kind::S_integer_value: // "integer value"
      case symbol_kind::S_subscript_natural_number_value: // "subscript natural number value"
      case symbol_kind::S_subscript_integer_value: // "subscript integer value"
      case symbol_kind::S_superscript_natural_number_value: // "superscript natural number value"
      case symbol_kind::S_superscript_integer_value: // "superscript integer value"
      case symbol_kind::S_optional_superscript_natural_number_value: // optional_superscript_natural_number_value
        value.copy< integer > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_metaformula_substitution_sequence: // metaformula_substitution_sequence
      case symbol_kind::S_substitution_for_metaformula: // substitution_for_metaformula
      case symbol_kind::S_metaformula_substitution: // metaformula_substitution
      case symbol_kind::S_formula_substitution_sequence: // formula_substitution_sequence
      case symbol_kind::S_substitution_for_formula: // substitution_for_formula
      case symbol_kind::S_formula_substitution: // formula_substitution
      case symbol_kind::S_term_substitution_sequence: // term_substitution_sequence
      case symbol_kind::S_term_substitution: // term_substitution
      case symbol_kind::S_predicate_function_application: // predicate_function_application
      case symbol_kind::S_term_function_application: // term_function_application
      case symbol_kind::S_theory: // theory
      case symbol_kind::S_include_theories: // include_theories
      case symbol_kind::S_include_theory: // include_theory
      case symbol_kind::S_theory_body: // theory_body
      case symbol_kind::S_formal_system: // formal_system
      case symbol_kind::S_formal_system_body: // formal_system_body
      case symbol_kind::S_formal_system_body_item: // formal_system_body_item
      case symbol_kind::S_theory_body_list: // theory_body_list
      case symbol_kind::S_theory_body_item: // theory_body_item
      case symbol_kind::S_postulate: // postulate
      case symbol_kind::S_conjecture: // conjecture
      case symbol_kind::S_theorem: // theorem
      case symbol_kind::S_theorem_statement: // theorem_statement
      case symbol_kind::S_proof: // proof
      case symbol_kind::S_198_11: // $@11
      case symbol_kind::S_199_compound_proof: // compound-proof
      case symbol_kind::S_proof_head: // proof_head
      case symbol_kind::S_proof_lines: // proof_lines
      case symbol_kind::S_proof_line: // proof_line
      case symbol_kind::S_proof_of_conclusion: // proof_of_conclusion
      case symbol_kind::S_find_statement: // find_statement
      case symbol_kind::S_find_statement_list: // find_statement_list
      case symbol_kind::S_find_statement_sequence: // find_statement_sequence
      case symbol_kind::S_find_definition_sequence: // find_definition_sequence
      case symbol_kind::S_find_statement_item: // find_statement_item
      case symbol_kind::S_find_statement_name: // find_statement_name
      case symbol_kind::S_214_13: // @13
      case symbol_kind::S_statement: // statement
      case symbol_kind::S_definition_statement: // definition_statement
      case symbol_kind::S_identifier_declaration: // identifier_declaration
      case symbol_kind::S_declarator_list: // declarator_list
      case symbol_kind::S_declarator_identifier_list: // declarator_identifier_list
      case symbol_kind::S_identifier_function_list: // identifier_function_list
      case symbol_kind::S_identifier_function_name: // identifier_function_name
      case symbol_kind::S_identifier_constant_list: // identifier_constant_list
      case symbol_kind::S_identifier_constant_name: // identifier_constant_name
      case symbol_kind::S_identifier_variable_list: // identifier_variable_list
      case symbol_kind::S_identifier_variable_name: // identifier_variable_name
      case symbol_kind::S_definition: // definition
      case symbol_kind::S_metaformula_definition: // metaformula_definition
      case symbol_kind::S_object_formula_definition: // object_formula_definition
      case symbol_kind::S_term_definition: // term_definition
      case symbol_kind::S_metaformula: // metaformula
      case symbol_kind::S_pure_metaformula: // pure_metaformula
      case symbol_kind::S_optional_varied_variable_matrix: // optional_varied_variable_matrix
      case symbol_kind::S_varied_variable_conclusions: // varied_variable_conclusions
      case symbol_kind::S_varied_variable_conclusion: // varied_variable_conclusion
      case symbol_kind::S_varied_variable_premises: // varied_variable_premises
      case symbol_kind::S_varied_variable_premise: // varied_variable_premise
      case symbol_kind::S_varied_variable_set: // varied_variable_set
      case symbol_kind::S_varied_variable: // varied_variable
      case symbol_kind::S_optional_varied_in_reduction_variable_matrix: // optional_varied_in_reduction_variable_matrix
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
      case symbol_kind::S_varied_in_reduction_variable_premises: // varied_in_reduction_variable_premises
      case symbol_kind::S_varied_in_reduction_variable_premise: // varied_in_reduction_variable_premise
      case symbol_kind::S_varied_in_reduction_variable_set: // varied_in_reduction_variable_set
      case symbol_kind::S_varied_in_reduction_variable: // varied_in_reduction_variable
      case symbol_kind::S_simple_metaformula: // simple_metaformula
      case symbol_kind::S_atomic_metaformula: // atomic_metaformula
      case symbol_kind::S_special_metaformula: // special_metaformula
      case symbol_kind::S_meta_object_free: // meta_object_free
      case symbol_kind::S_metapredicate: // metapredicate
      case symbol_kind::S_metapredicate_function: // metapredicate_function
      case symbol_kind::S_metapredicate_argument: // metapredicate_argument
      case symbol_kind::S_metapredicate_argument_body: // metapredicate_argument_body
      case symbol_kind::S_object_formula: // object_formula
      case symbol_kind::S_hoare_triple: // hoare_triple
      case symbol_kind::S_code_statement: // code_statement
      case symbol_kind::S_code_sequence: // code_sequence
      case symbol_kind::S_code_term: // code_term
      case symbol_kind::S_very_simple_formula: // very_simple_formula
      case symbol_kind::S_quantized_formula: // quantized_formula
      case symbol_kind::S_simple_formula: // simple_formula
      case symbol_kind::S_quantized_body: // quantized_body
      case symbol_kind::S_atomic_formula: // atomic_formula
      case symbol_kind::S_predicate: // predicate
      case symbol_kind::S_predicate_expression: // predicate_expression
      case symbol_kind::S_predicate_identifier: // predicate_identifier
      case symbol_kind::S_logic_formula: // logic_formula
      case symbol_kind::S_prefix_logic_formula: // prefix_logic_formula
      case symbol_kind::S_quantizer_declaration: // quantizer_declaration
      case symbol_kind::S_quantized_variable_list: // quantized_variable_list
      case symbol_kind::S_all_variable_list: // all_variable_list
      case symbol_kind::S_exist_variable_list: // exist_variable_list
      case symbol_kind::S_exclusion_set: // exclusion_set
      case symbol_kind::S_exclusion_list: // exclusion_list
      case symbol_kind::S_all_identifier_list: // all_identifier_list
      case symbol_kind::S_exist_identifier_list: // exist_identifier_list
      case symbol_kind::S_optional_in_term: // optional_in_term
      case symbol_kind::S_tuple: // tuple
      case symbol_kind::S_tuple_body: // tuple_body
      case symbol_kind::S_term: // term
      case symbol_kind::S_simple_term: // simple_term
      case symbol_kind::S_term_identifier: // term_identifier
      case symbol_kind::S_variable_exclusion_set: // variable_exclusion_set
      case symbol_kind::S_variable_exclusion_list: // variable_exclusion_list
      case symbol_kind::S_bound_variable: // bound_variable
      case symbol_kind::S_function_term: // function_term
      case symbol_kind::S_set_term: // set_term
      case symbol_kind::S_implicit_set_identifier_list: // implicit_set_identifier_list
      case symbol_kind::S_set_member_list: // set_member_list
      case symbol_kind::S_function_term_identifier: // function_term_identifier
        value.copy< ref6<unit> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_end_theory_name: // end_theory_name
        value.copy< std::pair<std::string, bool> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_natural_number_value: // "natural number value"
        value.copy< std::pair<std::string, integer> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_theorem_head: // theorem_head
        value.copy< std::pair<theorem::type, std::string> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_result_key: // "result"
      case symbol_kind::S_plain_name: // "name"
      case symbol_kind::S_label_key: // "label"
      case symbol_kind::S_all_key: // "∀"
      case symbol_kind::S_exist_key: // "∃"
      case symbol_kind::S_logical_not_key: // "¬"
      case symbol_kind::S_logical_and_key: // "∧"
      case symbol_kind::S_logical_or_key: // "∨"
      case symbol_kind::S_implies_key: // "⇒"
      case symbol_kind::S_impliedby_key: // "⇐"
      case symbol_kind::S_equivalent_key: // "⇔"
      case symbol_kind::S_natural_number_key: // "ℕ"
      case symbol_kind::S_less_key: // "<"
      case symbol_kind::S_greater_key: // ">"
      case symbol_kind::S_less_or_equal_key: // "≤"
      case symbol_kind::S_greater_or_equal_key: // "≥"
      case symbol_kind::S_not_less_key: // "≮"
      case symbol_kind::S_not_greater_key: // "≯"
      case symbol_kind::S_not_less_or_equal_key: // "≰"
      case symbol_kind::S_not_greater_or_equal_key: // "≱"
      case symbol_kind::S_equal_key: // "="
      case symbol_kind::S_not_equal_key: // "≠"
      case symbol_kind::S_divides_key: // "∣"
      case symbol_kind::S_not_divides_key: // "∤"
      case symbol_kind::S_mapsto_key: // "↦"
      case symbol_kind::S_Mapsto_key: // "⤇"
      case symbol_kind::S_factorial_key: // "!"
      case symbol_kind::S_mult_key: // "⋅"
      case symbol_kind::S_plus_key: // "+"
      case symbol_kind::S_minus_key: // "-"
      case symbol_kind::S_in_key: // "∈"
      case symbol_kind::S_not_in_key: // "∉"
      case symbol_kind::S_set_complement_key: // "∁"
      case symbol_kind::S_set_union_key: // "∪"
      case symbol_kind::S_set_intersection_key: // "∩"
      case symbol_kind::S_set_difference_key: // "∖"
      case symbol_kind::S_set_union_operator_key: // "⋃"
      case symbol_kind::S_set_intersection_operator_key: // "⋂"
      case symbol_kind::S_subset_key: // "⊆"
      case symbol_kind::S_proper_subset_key: // "⊊"
      case symbol_kind::S_superset_key: // "⊇"
      case symbol_kind::S_proper_superset_key: // "⊋"
      case symbol_kind::S_slash_key: // "/"
      case symbol_kind::S_backslash_key: // "\\"
      case symbol_kind::S_theory_name: // theory_name
      case symbol_kind::S_statement_name: // statement_name
      case symbol_kind::S_statement_label: // statement_label
      case symbol_kind::S_subproof_statement: // subproof_statement
      case symbol_kind::S_207_optional_result: // optional-result
        value.copy< std::string > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_theorem_key: // "theorem"
        value.copy< theorem::type > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_definition_labelstatement: // definition_labelstatement
        value.copy< val<definition> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_metapredicate_constant: // "metapredicate constant"
      case symbol_kind::S_function_key: // "function"
      case symbol_kind::S_predicate_key: // "predicate"
      case symbol_kind::S_predicate_constant: // "predicate constant"
      case symbol_kind::S_atom_constant: // "atom constant"
      case symbol_kind::S_function_constant: // "function constant"
      case symbol_kind::S_term_constant: // "term constant"
      case symbol_kind::S_metaformula_variable: // "metaformula variable"
      case symbol_kind::S_object_formula_variable: // "object formula variable"
      case symbol_kind::S_predicate_variable: // "predicate variable"
      case symbol_kind::S_atom_variable: // "atom variable"
      case symbol_kind::S_prefix_formula_variable: // "prefix formula variable"
      case symbol_kind::S_function_variable: // "function variable"
      case symbol_kind::S_object_variable: // "object variable"
      case symbol_kind::S_code_variable: // "code variable"
      case symbol_kind::S_all_variable: // "all variable"
      case symbol_kind::S_exist_variable: // "exist variable"
      case symbol_kind::S_function_map_variable: // "function map variable"
      case symbol_kind::S_is_set_variable: // "Set variable"
      case symbol_kind::S_set_variable: // "set variable"
      case symbol_kind::S_set_variable_definition: // "set variable definition"
      case symbol_kind::S_implicit_set_variable: // "implicit set variable"
        value.copy< val<unit> > (YY_MOVE (that.value));
        break;

      default:
        break;
    }

  }




  template <typename Base>
  database_parser::symbol_kind_type
  database_parser::basic_symbol<Base>::type_get () const YY_NOEXCEPT
  {
    return this->kind ();
  }


  template <typename Base>
  bool
  database_parser::basic_symbol<Base>::empty () const YY_NOEXCEPT
  {
    return this->kind () == symbol_kind::S_YYEMPTY;
  }

  template <typename Base>
  void
  database_parser::basic_symbol<Base>::move (basic_symbol& s)
  {
    super_type::move (s);
    switch (this->kind ())
    {
      case symbol_kind::S_integer_value: // "integer value"
      case symbol_kind::S_subscript_natural_number_value: // "subscript natural number value"
      case symbol_kind::S_subscript_integer_value: // "subscript integer value"
      case symbol_kind::S_superscript_natural_number_value: // "superscript natural number value"
      case symbol_kind::S_superscript_integer_value: // "superscript integer value"
      case symbol_kind::S_optional_superscript_natural_number_value: // optional_superscript_natural_number_value
        value.move< integer > (YY_MOVE (s.value));
        break;

      case symbol_kind::S_metaformula_substitution_sequence: // metaformula_substitution_sequence
      case symbol_kind::S_substitution_for_metaformula: // substitution_for_metaformula
      case symbol_kind::S_metaformula_substitution: // metaformula_substitution
      case symbol_kind::S_formula_substitution_sequence: // formula_substitution_sequence
      case symbol_kind::S_substitution_for_formula: // substitution_for_formula
      case symbol_kind::S_formula_substitution: // formula_substitution
      case symbol_kind::S_term_substitution_sequence: // term_substitution_sequence
      case symbol_kind::S_term_substitution: // term_substitution
      case symbol_kind::S_predicate_function_application: // predicate_function_application
      case symbol_kind::S_term_function_application: // term_function_application
      case symbol_kind::S_theory: // theory
      case symbol_kind::S_include_theories: // include_theories
      case symbol_kind::S_include_theory: // include_theory
      case symbol_kind::S_theory_body: // theory_body
      case symbol_kind::S_formal_system: // formal_system
      case symbol_kind::S_formal_system_body: // formal_system_body
      case symbol_kind::S_formal_system_body_item: // formal_system_body_item
      case symbol_kind::S_theory_body_list: // theory_body_list
      case symbol_kind::S_theory_body_item: // theory_body_item
      case symbol_kind::S_postulate: // postulate
      case symbol_kind::S_conjecture: // conjecture
      case symbol_kind::S_theorem: // theorem
      case symbol_kind::S_theorem_statement: // theorem_statement
      case symbol_kind::S_proof: // proof
      case symbol_kind::S_198_11: // $@11
      case symbol_kind::S_199_compound_proof: // compound-proof
      case symbol_kind::S_proof_head: // proof_head
      case symbol_kind::S_proof_lines: // proof_lines
      case symbol_kind::S_proof_line: // proof_line
      case symbol_kind::S_proof_of_conclusion: // proof_of_conclusion
      case symbol_kind::S_find_statement: // find_statement
      case symbol_kind::S_find_statement_list: // find_statement_list
      case symbol_kind::S_find_statement_sequence: // find_statement_sequence
      case symbol_kind::S_find_definition_sequence: // find_definition_sequence
      case symbol_kind::S_find_statement_item: // find_statement_item
      case symbol_kind::S_find_statement_name: // find_statement_name
      case symbol_kind::S_214_13: // @13
      case symbol_kind::S_statement: // statement
      case symbol_kind::S_definition_statement: // definition_statement
      case symbol_kind::S_identifier_declaration: // identifier_declaration
      case symbol_kind::S_declarator_list: // declarator_list
      case symbol_kind::S_declarator_identifier_list: // declarator_identifier_list
      case symbol_kind::S_identifier_function_list: // identifier_function_list
      case symbol_kind::S_identifier_function_name: // identifier_function_name
      case symbol_kind::S_identifier_constant_list: // identifier_constant_list
      case symbol_kind::S_identifier_constant_name: // identifier_constant_name
      case symbol_kind::S_identifier_variable_list: // identifier_variable_list
      case symbol_kind::S_identifier_variable_name: // identifier_variable_name
      case symbol_kind::S_definition: // definition
      case symbol_kind::S_metaformula_definition: // metaformula_definition
      case symbol_kind::S_object_formula_definition: // object_formula_definition
      case symbol_kind::S_term_definition: // term_definition
      case symbol_kind::S_metaformula: // metaformula
      case symbol_kind::S_pure_metaformula: // pure_metaformula
      case symbol_kind::S_optional_varied_variable_matrix: // optional_varied_variable_matrix
      case symbol_kind::S_varied_variable_conclusions: // varied_variable_conclusions
      case symbol_kind::S_varied_variable_conclusion: // varied_variable_conclusion
      case symbol_kind::S_varied_variable_premises: // varied_variable_premises
      case symbol_kind::S_varied_variable_premise: // varied_variable_premise
      case symbol_kind::S_varied_variable_set: // varied_variable_set
      case symbol_kind::S_varied_variable: // varied_variable
      case symbol_kind::S_optional_varied_in_reduction_variable_matrix: // optional_varied_in_reduction_variable_matrix
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
      case symbol_kind::S_varied_in_reduction_variable_premises: // varied_in_reduction_variable_premises
      case symbol_kind::S_varied_in_reduction_variable_premise: // varied_in_reduction_variable_premise
      case symbol_kind::S_varied_in_reduction_variable_set: // varied_in_reduction_variable_set
      case symbol_kind::S_varied_in_reduction_variable: // varied_in_reduction_variable
      case symbol_kind::S_simple_metaformula: // simple_metaformula
      case symbol_kind::S_atomic_metaformula: // atomic_metaformula
      case symbol_kind::S_special_metaformula: // special_metaformula
      case symbol_kind::S_meta_object_free: // meta_object_free
      case symbol_kind::S_metapredicate: // metapredicate
      case symbol_kind::S_metapredicate_function: // metapredicate_function
      case symbol_kind::S_metapredicate_argument: // metapredicate_argument
      case symbol_kind::S_metapredicate_argument_body: // metapredicate_argument_body
      case symbol_kind::S_object_formula: // object_formula
      case symbol_kind::S_hoare_triple: // hoare_triple
      case symbol_kind::S_code_statement: // code_statement
      case symbol_kind::S_code_sequence: // code_sequence
      case symbol_kind::S_code_term: // code_term
      case symbol_kind::S_very_simple_formula: // very_simple_formula
      case symbol_kind::S_quantized_formula: // quantized_formula
      case symbol_kind::S_simple_formula: // simple_formula
      case symbol_kind::S_quantized_body: // quantized_body
      case symbol_kind::S_atomic_formula: // atomic_formula
      case symbol_kind::S_predicate: // predicate
      case symbol_kind::S_predicate_expression: // predicate_expression
      case symbol_kind::S_predicate_identifier: // predicate_identifier
      case symbol_kind::S_logic_formula: // logic_formula
      case symbol_kind::S_prefix_logic_formula: // prefix_logic_formula
      case symbol_kind::S_quantizer_declaration: // quantizer_declaration
      case symbol_kind::S_quantized_variable_list: // quantized_variable_list
      case symbol_kind::S_all_variable_list: // all_variable_list
      case symbol_kind::S_exist_variable_list: // exist_variable_list
      case symbol_kind::S_exclusion_set: // exclusion_set
      case symbol_kind::S_exclusion_list: // exclusion_list
      case symbol_kind::S_all_identifier_list: // all_identifier_list
      case symbol_kind::S_exist_identifier_list: // exist_identifier_list
      case symbol_kind::S_optional_in_term: // optional_in_term
      case symbol_kind::S_tuple: // tuple
      case symbol_kind::S_tuple_body: // tuple_body
      case symbol_kind::S_term: // term
      case symbol_kind::S_simple_term: // simple_term
      case symbol_kind::S_term_identifier: // term_identifier
      case symbol_kind::S_variable_exclusion_set: // variable_exclusion_set
      case symbol_kind::S_variable_exclusion_list: // variable_exclusion_list
      case symbol_kind::S_bound_variable: // bound_variable
      case symbol_kind::S_function_term: // function_term
      case symbol_kind::S_set_term: // set_term
      case symbol_kind::S_implicit_set_identifier_list: // implicit_set_identifier_list
      case symbol_kind::S_set_member_list: // set_member_list
      case symbol_kind::S_function_term_identifier: // function_term_identifier
        value.move< ref6<unit> > (YY_MOVE (s.value));
        break;

      case symbol_kind::S_end_theory_name: // end_theory_name
        value.move< std::pair<std::string, bool> > (YY_MOVE (s.value));
        break;

      case symbol_kind::S_natural_number_value: // "natural number value"
        value.move< std::pair<std::string, integer> > (YY_MOVE (s.value));
        break;

      case symbol_kind::S_theorem_head: // theorem_head
        value.move< std::pair<theorem::type, std::string> > (YY_MOVE (s.value));
        break;

      case symbol_kind::S_result_key: // "result"
      case symbol_kind::S_plain_name: // "name"
      case symbol_kind::S_label_key: // "label"
      case symbol_kind::S_all_key: // "∀"
      case symbol_kind::S_exist_key: // "∃"
      case symbol_kind::S_logical_not_key: // "¬"
      case symbol_kind::S_logical_and_key: // "∧"
      case symbol_kind::S_logical_or_key: // "∨"
      case symbol_kind::S_implies_key: // "⇒"
      case symbol_kind::S_impliedby_key: // "⇐"
      case symbol_kind::S_equivalent_key: // "⇔"
      case symbol_kind::S_natural_number_key: // "ℕ"
      case symbol_kind::S_less_key: // "<"
      case symbol_kind::S_greater_key: // ">"
      case symbol_kind::S_less_or_equal_key: // "≤"
      case symbol_kind::S_greater_or_equal_key: // "≥"
      case symbol_kind::S_not_less_key: // "≮"
      case symbol_kind::S_not_greater_key: // "≯"
      case symbol_kind::S_not_less_or_equal_key: // "≰"
      case symbol_kind::S_not_greater_or_equal_key: // "≱"
      case symbol_kind::S_equal_key: // "="
      case symbol_kind::S_not_equal_key: // "≠"
      case symbol_kind::S_divides_key: // "∣"
      case symbol_kind::S_not_divides_key: // "∤"
      case symbol_kind::S_mapsto_key: // "↦"
      case symbol_kind::S_Mapsto_key: // "⤇"
      case symbol_kind::S_factorial_key: // "!"
      case symbol_kind::S_mult_key: // "⋅"
      case symbol_kind::S_plus_key: // "+"
      case symbol_kind::S_minus_key: // "-"
      case symbol_kind::S_in_key: // "∈"
      case symbol_kind::S_not_in_key: // "∉"
      case symbol_kind::S_set_complement_key: // "∁"
      case symbol_kind::S_set_union_key: // "∪"
      case symbol_kind::S_set_intersection_key: // "∩"
      case symbol_kind::S_set_difference_key: // "∖"
      case symbol_kind::S_set_union_operator_key: // "⋃"
      case symbol_kind::S_set_intersection_operator_key: // "⋂"
      case symbol_kind::S_subset_key: // "⊆"
      case symbol_kind::S_proper_subset_key: // "⊊"
      case symbol_kind::S_superset_key: // "⊇"
      case symbol_kind::S_proper_superset_key: // "⊋"
      case symbol_kind::S_slash_key: // "/"
      case symbol_kind::S_backslash_key: // "\\"
      case symbol_kind::S_theory_name: // theory_name
      case symbol_kind::S_statement_name: // statement_name
      case symbol_kind::S_statement_label: // statement_label
      case symbol_kind::S_subproof_statement: // subproof_statement
      case symbol_kind::S_207_optional_result: // optional-result
        value.move< std::string > (YY_MOVE (s.value));
        break;

      case symbol_kind::S_theorem_key: // "theorem"
        value.move< theorem::type > (YY_MOVE (s.value));
        break;

      case symbol_kind::S_definition_labelstatement: // definition_labelstatement
        value.move< val<definition> > (YY_MOVE (s.value));
        break;

      case symbol_kind::S_metapredicate_constant: // "metapredicate constant"
      case symbol_kind::S_function_key: // "function"
      case symbol_kind::S_predicate_key: // "predicate"
      case symbol_kind::S_predicate_constant: // "predicate constant"
      case symbol_kind::S_atom_constant: // "atom constant"
      case symbol_kind::S_function_constant: // "function constant"
      case symbol_kind::S_term_constant: // "term constant"
      case symbol_kind::S_metaformula_variable: // "metaformula variable"
      case symbol_kind::S_object_formula_variable: // "object formula variable"
      case symbol_kind::S_predicate_variable: // "predicate variable"
      case symbol_kind::S_atom_variable: // "atom variable"
      case symbol_kind::S_prefix_formula_variable: // "prefix formula variable"
      case symbol_kind::S_function_variable: // "function variable"
      case symbol_kind::S_object_variable: // "object variable"
      case symbol_kind::S_code_variable: // "code variable"
      case symbol_kind::S_all_variable: // "all variable"
      case symbol_kind::S_exist_variable: // "exist variable"
      case symbol_kind::S_function_map_variable: // "function map variable"
      case symbol_kind::S_is_set_variable: // "Set variable"
      case symbol_kind::S_set_variable: // "set variable"
      case symbol_kind::S_set_variable_definition: // "set variable definition"
      case symbol_kind::S_implicit_set_variable: // "implicit set variable"
        value.move< val<unit> > (YY_MOVE (s.value));
        break;

      default:
        break;
    }

    location = YY_MOVE (s.location);
  }

  // by_kind.
  database_parser::by_kind::by_kind () YY_NOEXCEPT
    : kind_ (symbol_kind::S_YYEMPTY)
  {}

#if 201103L <= YY_CPLUSPLUS
  database_parser::by_kind::by_kind (by_kind&& that) YY_NOEXCEPT
    : kind_ (that.kind_)
  {
    that.clear ();
  }
#endif

  database_parser::by_kind::by_kind (const by_kind& that) YY_NOEXCEPT
    : kind_ (that.kind_)
  {}

  database_parser::by_kind::by_kind (token_kind_type t) YY_NOEXCEPT
    : kind_ (yytranslate_ (t))
  {}



  void
  database_parser::by_kind::clear () YY_NOEXCEPT
  {
    kind_ = symbol_kind::S_YYEMPTY;
  }

  void
  database_parser::by_kind::move (by_kind& that)
  {
    kind_ = that.kind_;
    that.clear ();
  }

  database_parser::symbol_kind_type
  database_parser::by_kind::kind () const YY_NOEXCEPT
  {
    return kind_;
  }


  database_parser::symbol_kind_type
  database_parser::by_kind::type_get () const YY_NOEXCEPT
  {
    return this->kind ();
  }



  // by_state.
  database_parser::by_state::by_state () YY_NOEXCEPT
    : state (empty_state)
  {}

  database_parser::by_state::by_state (const by_state& that) YY_NOEXCEPT
    : state (that.state)
  {}

  void
  database_parser::by_state::clear () YY_NOEXCEPT
  {
    state = empty_state;
  }

  void
  database_parser::by_state::move (by_state& that)
  {
    state = that.state;
    that.clear ();
  }

  database_parser::by_state::by_state (state_type s) YY_NOEXCEPT
    : state (s)
  {}

  database_parser::symbol_kind_type
  database_parser::by_state::kind () const YY_NOEXCEPT
  {
    if (state == empty_state)
      return symbol_kind::S_YYEMPTY;
    else
      return YY_CAST (symbol_kind_type, yystos_[+state]);
  }

  database_parser::stack_symbol_type::stack_symbol_type ()
  {}

  database_parser::stack_symbol_type::stack_symbol_type (YY_RVREF (stack_symbol_type) that)
    : super_type (YY_MOVE (that.state), YY_MOVE (that.location))
  {
    switch (that.kind ())
    {
      case symbol_kind::S_integer_value: // "integer value"
      case symbol_kind::S_subscript_natural_number_value: // "subscript natural number value"
      case symbol_kind::S_subscript_integer_value: // "subscript integer value"
      case symbol_kind::S_superscript_natural_number_value: // "superscript natural number value"
      case symbol_kind::S_superscript_integer_value: // "superscript integer value"
      case symbol_kind::S_optional_superscript_natural_number_value: // optional_superscript_natural_number_value
        value.YY_MOVE_OR_COPY< integer > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_metaformula_substitution_sequence: // metaformula_substitution_sequence
      case symbol_kind::S_substitution_for_metaformula: // substitution_for_metaformula
      case symbol_kind::S_metaformula_substitution: // metaformula_substitution
      case symbol_kind::S_formula_substitution_sequence: // formula_substitution_sequence
      case symbol_kind::S_substitution_for_formula: // substitution_for_formula
      case symbol_kind::S_formula_substitution: // formula_substitution
      case symbol_kind::S_term_substitution_sequence: // term_substitution_sequence
      case symbol_kind::S_term_substitution: // term_substitution
      case symbol_kind::S_predicate_function_application: // predicate_function_application
      case symbol_kind::S_term_function_application: // term_function_application
      case symbol_kind::S_theory: // theory
      case symbol_kind::S_include_theories: // include_theories
      case symbol_kind::S_include_theory: // include_theory
      case symbol_kind::S_theory_body: // theory_body
      case symbol_kind::S_formal_system: // formal_system
      case symbol_kind::S_formal_system_body: // formal_system_body
      case symbol_kind::S_formal_system_body_item: // formal_system_body_item
      case symbol_kind::S_theory_body_list: // theory_body_list
      case symbol_kind::S_theory_body_item: // theory_body_item
      case symbol_kind::S_postulate: // postulate
      case symbol_kind::S_conjecture: // conjecture
      case symbol_kind::S_theorem: // theorem
      case symbol_kind::S_theorem_statement: // theorem_statement
      case symbol_kind::S_proof: // proof
      case symbol_kind::S_198_11: // $@11
      case symbol_kind::S_199_compound_proof: // compound-proof
      case symbol_kind::S_proof_head: // proof_head
      case symbol_kind::S_proof_lines: // proof_lines
      case symbol_kind::S_proof_line: // proof_line
      case symbol_kind::S_proof_of_conclusion: // proof_of_conclusion
      case symbol_kind::S_find_statement: // find_statement
      case symbol_kind::S_find_statement_list: // find_statement_list
      case symbol_kind::S_find_statement_sequence: // find_statement_sequence
      case symbol_kind::S_find_definition_sequence: // find_definition_sequence
      case symbol_kind::S_find_statement_item: // find_statement_item
      case symbol_kind::S_find_statement_name: // find_statement_name
      case symbol_kind::S_214_13: // @13
      case symbol_kind::S_statement: // statement
      case symbol_kind::S_definition_statement: // definition_statement
      case symbol_kind::S_identifier_declaration: // identifier_declaration
      case symbol_kind::S_declarator_list: // declarator_list
      case symbol_kind::S_declarator_identifier_list: // declarator_identifier_list
      case symbol_kind::S_identifier_function_list: // identifier_function_list
      case symbol_kind::S_identifier_function_name: // identifier_function_name
      case symbol_kind::S_identifier_constant_list: // identifier_constant_list
      case symbol_kind::S_identifier_constant_name: // identifier_constant_name
      case symbol_kind::S_identifier_variable_list: // identifier_variable_list
      case symbol_kind::S_identifier_variable_name: // identifier_variable_name
      case symbol_kind::S_definition: // definition
      case symbol_kind::S_metaformula_definition: // metaformula_definition
      case symbol_kind::S_object_formula_definition: // object_formula_definition
      case symbol_kind::S_term_definition: // term_definition
      case symbol_kind::S_metaformula: // metaformula
      case symbol_kind::S_pure_metaformula: // pure_metaformula
      case symbol_kind::S_optional_varied_variable_matrix: // optional_varied_variable_matrix
      case symbol_kind::S_varied_variable_conclusions: // varied_variable_conclusions
      case symbol_kind::S_varied_variable_conclusion: // varied_variable_conclusion
      case symbol_kind::S_varied_variable_premises: // varied_variable_premises
      case symbol_kind::S_varied_variable_premise: // varied_variable_premise
      case symbol_kind::S_varied_variable_set: // varied_variable_set
      case symbol_kind::S_varied_variable: // varied_variable
      case symbol_kind::S_optional_varied_in_reduction_variable_matrix: // optional_varied_in_reduction_variable_matrix
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
      case symbol_kind::S_varied_in_reduction_variable_premises: // varied_in_reduction_variable_premises
      case symbol_kind::S_varied_in_reduction_variable_premise: // varied_in_reduction_variable_premise
      case symbol_kind::S_varied_in_reduction_variable_set: // varied_in_reduction_variable_set
      case symbol_kind::S_varied_in_reduction_variable: // varied_in_reduction_variable
      case symbol_kind::S_simple_metaformula: // simple_metaformula
      case symbol_kind::S_atomic_metaformula: // atomic_metaformula
      case symbol_kind::S_special_metaformula: // special_metaformula
      case symbol_kind::S_meta_object_free: // meta_object_free
      case symbol_kind::S_metapredicate: // metapredicate
      case symbol_kind::S_metapredicate_function: // metapredicate_function
      case symbol_kind::S_metapredicate_argument: // metapredicate_argument
      case symbol_kind::S_metapredicate_argument_body: // metapredicate_argument_body
      case symbol_kind::S_object_formula: // object_formula
      case symbol_kind::S_hoare_triple: // hoare_triple
      case symbol_kind::S_code_statement: // code_statement
      case symbol_kind::S_code_sequence: // code_sequence
      case symbol_kind::S_code_term: // code_term
      case symbol_kind::S_very_simple_formula: // very_simple_formula
      case symbol_kind::S_quantized_formula: // quantized_formula
      case symbol_kind::S_simple_formula: // simple_formula
      case symbol_kind::S_quantized_body: // quantized_body
      case symbol_kind::S_atomic_formula: // atomic_formula
      case symbol_kind::S_predicate: // predicate
      case symbol_kind::S_predicate_expression: // predicate_expression
      case symbol_kind::S_predicate_identifier: // predicate_identifier
      case symbol_kind::S_logic_formula: // logic_formula
      case symbol_kind::S_prefix_logic_formula: // prefix_logic_formula
      case symbol_kind::S_quantizer_declaration: // quantizer_declaration
      case symbol_kind::S_quantized_variable_list: // quantized_variable_list
      case symbol_kind::S_all_variable_list: // all_variable_list
      case symbol_kind::S_exist_variable_list: // exist_variable_list
      case symbol_kind::S_exclusion_set: // exclusion_set
      case symbol_kind::S_exclusion_list: // exclusion_list
      case symbol_kind::S_all_identifier_list: // all_identifier_list
      case symbol_kind::S_exist_identifier_list: // exist_identifier_list
      case symbol_kind::S_optional_in_term: // optional_in_term
      case symbol_kind::S_tuple: // tuple
      case symbol_kind::S_tuple_body: // tuple_body
      case symbol_kind::S_term: // term
      case symbol_kind::S_simple_term: // simple_term
      case symbol_kind::S_term_identifier: // term_identifier
      case symbol_kind::S_variable_exclusion_set: // variable_exclusion_set
      case symbol_kind::S_variable_exclusion_list: // variable_exclusion_list
      case symbol_kind::S_bound_variable: // bound_variable
      case symbol_kind::S_function_term: // function_term
      case symbol_kind::S_set_term: // set_term
      case symbol_kind::S_implicit_set_identifier_list: // implicit_set_identifier_list
      case symbol_kind::S_set_member_list: // set_member_list
      case symbol_kind::S_function_term_identifier: // function_term_identifier
        value.YY_MOVE_OR_COPY< ref6<unit> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_end_theory_name: // end_theory_name
        value.YY_MOVE_OR_COPY< std::pair<std::string, bool> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_natural_number_value: // "natural number value"
        value.YY_MOVE_OR_COPY< std::pair<std::string, integer> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_theorem_head: // theorem_head
        value.YY_MOVE_OR_COPY< std::pair<theorem::type, std::string> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_result_key: // "result"
      case symbol_kind::S_plain_name: // "name"
      case symbol_kind::S_label_key: // "label"
      case symbol_kind::S_all_key: // "∀"
      case symbol_kind::S_exist_key: // "∃"
      case symbol_kind::S_logical_not_key: // "¬"
      case symbol_kind::S_logical_and_key: // "∧"
      case symbol_kind::S_logical_or_key: // "∨"
      case symbol_kind::S_implies_key: // "⇒"
      case symbol_kind::S_impliedby_key: // "⇐"
      case symbol_kind::S_equivalent_key: // "⇔"
      case symbol_kind::S_natural_number_key: // "ℕ"
      case symbol_kind::S_less_key: // "<"
      case symbol_kind::S_greater_key: // ">"
      case symbol_kind::S_less_or_equal_key: // "≤"
      case symbol_kind::S_greater_or_equal_key: // "≥"
      case symbol_kind::S_not_less_key: // "≮"
      case symbol_kind::S_not_greater_key: // "≯"
      case symbol_kind::S_not_less_or_equal_key: // "≰"
      case symbol_kind::S_not_greater_or_equal_key: // "≱"
      case symbol_kind::S_equal_key: // "="
      case symbol_kind::S_not_equal_key: // "≠"
      case symbol_kind::S_divides_key: // "∣"
      case symbol_kind::S_not_divides_key: // "∤"
      case symbol_kind::S_mapsto_key: // "↦"
      case symbol_kind::S_Mapsto_key: // "⤇"
      case symbol_kind::S_factorial_key: // "!"
      case symbol_kind::S_mult_key: // "⋅"
      case symbol_kind::S_plus_key: // "+"
      case symbol_kind::S_minus_key: // "-"
      case symbol_kind::S_in_key: // "∈"
      case symbol_kind::S_not_in_key: // "∉"
      case symbol_kind::S_set_complement_key: // "∁"
      case symbol_kind::S_set_union_key: // "∪"
      case symbol_kind::S_set_intersection_key: // "∩"
      case symbol_kind::S_set_difference_key: // "∖"
      case symbol_kind::S_set_union_operator_key: // "⋃"
      case symbol_kind::S_set_intersection_operator_key: // "⋂"
      case symbol_kind::S_subset_key: // "⊆"
      case symbol_kind::S_proper_subset_key: // "⊊"
      case symbol_kind::S_superset_key: // "⊇"
      case symbol_kind::S_proper_superset_key: // "⊋"
      case symbol_kind::S_slash_key: // "/"
      case symbol_kind::S_backslash_key: // "\\"
      case symbol_kind::S_theory_name: // theory_name
      case symbol_kind::S_statement_name: // statement_name
      case symbol_kind::S_statement_label: // statement_label
      case symbol_kind::S_subproof_statement: // subproof_statement
      case symbol_kind::S_207_optional_result: // optional-result
        value.YY_MOVE_OR_COPY< std::string > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_theorem_key: // "theorem"
        value.YY_MOVE_OR_COPY< theorem::type > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_definition_labelstatement: // definition_labelstatement
        value.YY_MOVE_OR_COPY< val<definition> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_metapredicate_constant: // "metapredicate constant"
      case symbol_kind::S_function_key: // "function"
      case symbol_kind::S_predicate_key: // "predicate"
      case symbol_kind::S_predicate_constant: // "predicate constant"
      case symbol_kind::S_atom_constant: // "atom constant"
      case symbol_kind::S_function_constant: // "function constant"
      case symbol_kind::S_term_constant: // "term constant"
      case symbol_kind::S_metaformula_variable: // "metaformula variable"
      case symbol_kind::S_object_formula_variable: // "object formula variable"
      case symbol_kind::S_predicate_variable: // "predicate variable"
      case symbol_kind::S_atom_variable: // "atom variable"
      case symbol_kind::S_prefix_formula_variable: // "prefix formula variable"
      case symbol_kind::S_function_variable: // "function variable"
      case symbol_kind::S_object_variable: // "object variable"
      case symbol_kind::S_code_variable: // "code variable"
      case symbol_kind::S_all_variable: // "all variable"
      case symbol_kind::S_exist_variable: // "exist variable"
      case symbol_kind::S_function_map_variable: // "function map variable"
      case symbol_kind::S_is_set_variable: // "Set variable"
      case symbol_kind::S_set_variable: // "set variable"
      case symbol_kind::S_set_variable_definition: // "set variable definition"
      case symbol_kind::S_implicit_set_variable: // "implicit set variable"
        value.YY_MOVE_OR_COPY< val<unit> > (YY_MOVE (that.value));
        break;

      default:
        break;
    }

#if 201103L <= YY_CPLUSPLUS
    // that is emptied.
    that.state = empty_state;
#endif
  }

  database_parser::stack_symbol_type::stack_symbol_type (state_type s, YY_MOVE_REF (symbol_type) that)
    : super_type (s, YY_MOVE (that.location))
  {
    switch (that.kind ())
    {
      case symbol_kind::S_integer_value: // "integer value"
      case symbol_kind::S_subscript_natural_number_value: // "subscript natural number value"
      case symbol_kind::S_subscript_integer_value: // "subscript integer value"
      case symbol_kind::S_superscript_natural_number_value: // "superscript natural number value"
      case symbol_kind::S_superscript_integer_value: // "superscript integer value"
      case symbol_kind::S_optional_superscript_natural_number_value: // optional_superscript_natural_number_value
        value.move< integer > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_metaformula_substitution_sequence: // metaformula_substitution_sequence
      case symbol_kind::S_substitution_for_metaformula: // substitution_for_metaformula
      case symbol_kind::S_metaformula_substitution: // metaformula_substitution
      case symbol_kind::S_formula_substitution_sequence: // formula_substitution_sequence
      case symbol_kind::S_substitution_for_formula: // substitution_for_formula
      case symbol_kind::S_formula_substitution: // formula_substitution
      case symbol_kind::S_term_substitution_sequence: // term_substitution_sequence
      case symbol_kind::S_term_substitution: // term_substitution
      case symbol_kind::S_predicate_function_application: // predicate_function_application
      case symbol_kind::S_term_function_application: // term_function_application
      case symbol_kind::S_theory: // theory
      case symbol_kind::S_include_theories: // include_theories
      case symbol_kind::S_include_theory: // include_theory
      case symbol_kind::S_theory_body: // theory_body
      case symbol_kind::S_formal_system: // formal_system
      case symbol_kind::S_formal_system_body: // formal_system_body
      case symbol_kind::S_formal_system_body_item: // formal_system_body_item
      case symbol_kind::S_theory_body_list: // theory_body_list
      case symbol_kind::S_theory_body_item: // theory_body_item
      case symbol_kind::S_postulate: // postulate
      case symbol_kind::S_conjecture: // conjecture
      case symbol_kind::S_theorem: // theorem
      case symbol_kind::S_theorem_statement: // theorem_statement
      case symbol_kind::S_proof: // proof
      case symbol_kind::S_198_11: // $@11
      case symbol_kind::S_199_compound_proof: // compound-proof
      case symbol_kind::S_proof_head: // proof_head
      case symbol_kind::S_proof_lines: // proof_lines
      case symbol_kind::S_proof_line: // proof_line
      case symbol_kind::S_proof_of_conclusion: // proof_of_conclusion
      case symbol_kind::S_find_statement: // find_statement
      case symbol_kind::S_find_statement_list: // find_statement_list
      case symbol_kind::S_find_statement_sequence: // find_statement_sequence
      case symbol_kind::S_find_definition_sequence: // find_definition_sequence
      case symbol_kind::S_find_statement_item: // find_statement_item
      case symbol_kind::S_find_statement_name: // find_statement_name
      case symbol_kind::S_214_13: // @13
      case symbol_kind::S_statement: // statement
      case symbol_kind::S_definition_statement: // definition_statement
      case symbol_kind::S_identifier_declaration: // identifier_declaration
      case symbol_kind::S_declarator_list: // declarator_list
      case symbol_kind::S_declarator_identifier_list: // declarator_identifier_list
      case symbol_kind::S_identifier_function_list: // identifier_function_list
      case symbol_kind::S_identifier_function_name: // identifier_function_name
      case symbol_kind::S_identifier_constant_list: // identifier_constant_list
      case symbol_kind::S_identifier_constant_name: // identifier_constant_name
      case symbol_kind::S_identifier_variable_list: // identifier_variable_list
      case symbol_kind::S_identifier_variable_name: // identifier_variable_name
      case symbol_kind::S_definition: // definition
      case symbol_kind::S_metaformula_definition: // metaformula_definition
      case symbol_kind::S_object_formula_definition: // object_formula_definition
      case symbol_kind::S_term_definition: // term_definition
      case symbol_kind::S_metaformula: // metaformula
      case symbol_kind::S_pure_metaformula: // pure_metaformula
      case symbol_kind::S_optional_varied_variable_matrix: // optional_varied_variable_matrix
      case symbol_kind::S_varied_variable_conclusions: // varied_variable_conclusions
      case symbol_kind::S_varied_variable_conclusion: // varied_variable_conclusion
      case symbol_kind::S_varied_variable_premises: // varied_variable_premises
      case symbol_kind::S_varied_variable_premise: // varied_variable_premise
      case symbol_kind::S_varied_variable_set: // varied_variable_set
      case symbol_kind::S_varied_variable: // varied_variable
      case symbol_kind::S_optional_varied_in_reduction_variable_matrix: // optional_varied_in_reduction_variable_matrix
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
      case symbol_kind::S_varied_in_reduction_variable_premises: // varied_in_reduction_variable_premises
      case symbol_kind::S_varied_in_reduction_variable_premise: // varied_in_reduction_variable_premise
      case symbol_kind::S_varied_in_reduction_variable_set: // varied_in_reduction_variable_set
      case symbol_kind::S_varied_in_reduction_variable: // varied_in_reduction_variable
      case symbol_kind::S_simple_metaformula: // simple_metaformula
      case symbol_kind::S_atomic_metaformula: // atomic_metaformula
      case symbol_kind::S_special_metaformula: // special_metaformula
      case symbol_kind::S_meta_object_free: // meta_object_free
      case symbol_kind::S_metapredicate: // metapredicate
      case symbol_kind::S_metapredicate_function: // metapredicate_function
      case symbol_kind::S_metapredicate_argument: // metapredicate_argument
      case symbol_kind::S_metapredicate_argument_body: // metapredicate_argument_body
      case symbol_kind::S_object_formula: // object_formula
      case symbol_kind::S_hoare_triple: // hoare_triple
      case symbol_kind::S_code_statement: // code_statement
      case symbol_kind::S_code_sequence: // code_sequence
      case symbol_kind::S_code_term: // code_term
      case symbol_kind::S_very_simple_formula: // very_simple_formula
      case symbol_kind::S_quantized_formula: // quantized_formula
      case symbol_kind::S_simple_formula: // simple_formula
      case symbol_kind::S_quantized_body: // quantized_body
      case symbol_kind::S_atomic_formula: // atomic_formula
      case symbol_kind::S_predicate: // predicate
      case symbol_kind::S_predicate_expression: // predicate_expression
      case symbol_kind::S_predicate_identifier: // predicate_identifier
      case symbol_kind::S_logic_formula: // logic_formula
      case symbol_kind::S_prefix_logic_formula: // prefix_logic_formula
      case symbol_kind::S_quantizer_declaration: // quantizer_declaration
      case symbol_kind::S_quantized_variable_list: // quantized_variable_list
      case symbol_kind::S_all_variable_list: // all_variable_list
      case symbol_kind::S_exist_variable_list: // exist_variable_list
      case symbol_kind::S_exclusion_set: // exclusion_set
      case symbol_kind::S_exclusion_list: // exclusion_list
      case symbol_kind::S_all_identifier_list: // all_identifier_list
      case symbol_kind::S_exist_identifier_list: // exist_identifier_list
      case symbol_kind::S_optional_in_term: // optional_in_term
      case symbol_kind::S_tuple: // tuple
      case symbol_kind::S_tuple_body: // tuple_body
      case symbol_kind::S_term: // term
      case symbol_kind::S_simple_term: // simple_term
      case symbol_kind::S_term_identifier: // term_identifier
      case symbol_kind::S_variable_exclusion_set: // variable_exclusion_set
      case symbol_kind::S_variable_exclusion_list: // variable_exclusion_list
      case symbol_kind::S_bound_variable: // bound_variable
      case symbol_kind::S_function_term: // function_term
      case symbol_kind::S_set_term: // set_term
      case symbol_kind::S_implicit_set_identifier_list: // implicit_set_identifier_list
      case symbol_kind::S_set_member_list: // set_member_list
      case symbol_kind::S_function_term_identifier: // function_term_identifier
        value.move< ref6<unit> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_end_theory_name: // end_theory_name
        value.move< std::pair<std::string, bool> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_natural_number_value: // "natural number value"
        value.move< std::pair<std::string, integer> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_theorem_head: // theorem_head
        value.move< std::pair<theorem::type, std::string> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_result_key: // "result"
      case symbol_kind::S_plain_name: // "name"
      case symbol_kind::S_label_key: // "label"
      case symbol_kind::S_all_key: // "∀"
      case symbol_kind::S_exist_key: // "∃"
      case symbol_kind::S_logical_not_key: // "¬"
      case symbol_kind::S_logical_and_key: // "∧"
      case symbol_kind::S_logical_or_key: // "∨"
      case symbol_kind::S_implies_key: // "⇒"
      case symbol_kind::S_impliedby_key: // "⇐"
      case symbol_kind::S_equivalent_key: // "⇔"
      case symbol_kind::S_natural_number_key: // "ℕ"
      case symbol_kind::S_less_key: // "<"
      case symbol_kind::S_greater_key: // ">"
      case symbol_kind::S_less_or_equal_key: // "≤"
      case symbol_kind::S_greater_or_equal_key: // "≥"
      case symbol_kind::S_not_less_key: // "≮"
      case symbol_kind::S_not_greater_key: // "≯"
      case symbol_kind::S_not_less_or_equal_key: // "≰"
      case symbol_kind::S_not_greater_or_equal_key: // "≱"
      case symbol_kind::S_equal_key: // "="
      case symbol_kind::S_not_equal_key: // "≠"
      case symbol_kind::S_divides_key: // "∣"
      case symbol_kind::S_not_divides_key: // "∤"
      case symbol_kind::S_mapsto_key: // "↦"
      case symbol_kind::S_Mapsto_key: // "⤇"
      case symbol_kind::S_factorial_key: // "!"
      case symbol_kind::S_mult_key: // "⋅"
      case symbol_kind::S_plus_key: // "+"
      case symbol_kind::S_minus_key: // "-"
      case symbol_kind::S_in_key: // "∈"
      case symbol_kind::S_not_in_key: // "∉"
      case symbol_kind::S_set_complement_key: // "∁"
      case symbol_kind::S_set_union_key: // "∪"
      case symbol_kind::S_set_intersection_key: // "∩"
      case symbol_kind::S_set_difference_key: // "∖"
      case symbol_kind::S_set_union_operator_key: // "⋃"
      case symbol_kind::S_set_intersection_operator_key: // "⋂"
      case symbol_kind::S_subset_key: // "⊆"
      case symbol_kind::S_proper_subset_key: // "⊊"
      case symbol_kind::S_superset_key: // "⊇"
      case symbol_kind::S_proper_superset_key: // "⊋"
      case symbol_kind::S_slash_key: // "/"
      case symbol_kind::S_backslash_key: // "\\"
      case symbol_kind::S_theory_name: // theory_name
      case symbol_kind::S_statement_name: // statement_name
      case symbol_kind::S_statement_label: // statement_label
      case symbol_kind::S_subproof_statement: // subproof_statement
      case symbol_kind::S_207_optional_result: // optional-result
        value.move< std::string > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_theorem_key: // "theorem"
        value.move< theorem::type > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_definition_labelstatement: // definition_labelstatement
        value.move< val<definition> > (YY_MOVE (that.value));
        break;

      case symbol_kind::S_metapredicate_constant: // "metapredicate constant"
      case symbol_kind::S_function_key: // "function"
      case symbol_kind::S_predicate_key: // "predicate"
      case symbol_kind::S_predicate_constant: // "predicate constant"
      case symbol_kind::S_atom_constant: // "atom constant"
      case symbol_kind::S_function_constant: // "function constant"
      case symbol_kind::S_term_constant: // "term constant"
      case symbol_kind::S_metaformula_variable: // "metaformula variable"
      case symbol_kind::S_object_formula_variable: // "object formula variable"
      case symbol_kind::S_predicate_variable: // "predicate variable"
      case symbol_kind::S_atom_variable: // "atom variable"
      case symbol_kind::S_prefix_formula_variable: // "prefix formula variable"
      case symbol_kind::S_function_variable: // "function variable"
      case symbol_kind::S_object_variable: // "object variable"
      case symbol_kind::S_code_variable: // "code variable"
      case symbol_kind::S_all_variable: // "all variable"
      case symbol_kind::S_exist_variable: // "exist variable"
      case symbol_kind::S_function_map_variable: // "function map variable"
      case symbol_kind::S_is_set_variable: // "Set variable"
      case symbol_kind::S_set_variable: // "set variable"
      case symbol_kind::S_set_variable_definition: // "set variable definition"
      case symbol_kind::S_implicit_set_variable: // "implicit set variable"
        value.move< val<unit> > (YY_MOVE (that.value));
        break;

      default:
        break;
    }

    // that is emptied.
    that.kind_ = symbol_kind::S_YYEMPTY;
  }

#if YY_CPLUSPLUS < 201103L
  database_parser::stack_symbol_type&
  database_parser::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
    switch (that.kind ())
    {
      case symbol_kind::S_integer_value: // "integer value"
      case symbol_kind::S_subscript_natural_number_value: // "subscript natural number value"
      case symbol_kind::S_subscript_integer_value: // "subscript integer value"
      case symbol_kind::S_superscript_natural_number_value: // "superscript natural number value"
      case symbol_kind::S_superscript_integer_value: // "superscript integer value"
      case symbol_kind::S_optional_superscript_natural_number_value: // optional_superscript_natural_number_value
        value.copy< integer > (that.value);
        break;

      case symbol_kind::S_metaformula_substitution_sequence: // metaformula_substitution_sequence
      case symbol_kind::S_substitution_for_metaformula: // substitution_for_metaformula
      case symbol_kind::S_metaformula_substitution: // metaformula_substitution
      case symbol_kind::S_formula_substitution_sequence: // formula_substitution_sequence
      case symbol_kind::S_substitution_for_formula: // substitution_for_formula
      case symbol_kind::S_formula_substitution: // formula_substitution
      case symbol_kind::S_term_substitution_sequence: // term_substitution_sequence
      case symbol_kind::S_term_substitution: // term_substitution
      case symbol_kind::S_predicate_function_application: // predicate_function_application
      case symbol_kind::S_term_function_application: // term_function_application
      case symbol_kind::S_theory: // theory
      case symbol_kind::S_include_theories: // include_theories
      case symbol_kind::S_include_theory: // include_theory
      case symbol_kind::S_theory_body: // theory_body
      case symbol_kind::S_formal_system: // formal_system
      case symbol_kind::S_formal_system_body: // formal_system_body
      case symbol_kind::S_formal_system_body_item: // formal_system_body_item
      case symbol_kind::S_theory_body_list: // theory_body_list
      case symbol_kind::S_theory_body_item: // theory_body_item
      case symbol_kind::S_postulate: // postulate
      case symbol_kind::S_conjecture: // conjecture
      case symbol_kind::S_theorem: // theorem
      case symbol_kind::S_theorem_statement: // theorem_statement
      case symbol_kind::S_proof: // proof
      case symbol_kind::S_198_11: // $@11
      case symbol_kind::S_199_compound_proof: // compound-proof
      case symbol_kind::S_proof_head: // proof_head
      case symbol_kind::S_proof_lines: // proof_lines
      case symbol_kind::S_proof_line: // proof_line
      case symbol_kind::S_proof_of_conclusion: // proof_of_conclusion
      case symbol_kind::S_find_statement: // find_statement
      case symbol_kind::S_find_statement_list: // find_statement_list
      case symbol_kind::S_find_statement_sequence: // find_statement_sequence
      case symbol_kind::S_find_definition_sequence: // find_definition_sequence
      case symbol_kind::S_find_statement_item: // find_statement_item
      case symbol_kind::S_find_statement_name: // find_statement_name
      case symbol_kind::S_214_13: // @13
      case symbol_kind::S_statement: // statement
      case symbol_kind::S_definition_statement: // definition_statement
      case symbol_kind::S_identifier_declaration: // identifier_declaration
      case symbol_kind::S_declarator_list: // declarator_list
      case symbol_kind::S_declarator_identifier_list: // declarator_identifier_list
      case symbol_kind::S_identifier_function_list: // identifier_function_list
      case symbol_kind::S_identifier_function_name: // identifier_function_name
      case symbol_kind::S_identifier_constant_list: // identifier_constant_list
      case symbol_kind::S_identifier_constant_name: // identifier_constant_name
      case symbol_kind::S_identifier_variable_list: // identifier_variable_list
      case symbol_kind::S_identifier_variable_name: // identifier_variable_name
      case symbol_kind::S_definition: // definition
      case symbol_kind::S_metaformula_definition: // metaformula_definition
      case symbol_kind::S_object_formula_definition: // object_formula_definition
      case symbol_kind::S_term_definition: // term_definition
      case symbol_kind::S_metaformula: // metaformula
      case symbol_kind::S_pure_metaformula: // pure_metaformula
      case symbol_kind::S_optional_varied_variable_matrix: // optional_varied_variable_matrix
      case symbol_kind::S_varied_variable_conclusions: // varied_variable_conclusions
      case symbol_kind::S_varied_variable_conclusion: // varied_variable_conclusion
      case symbol_kind::S_varied_variable_premises: // varied_variable_premises
      case symbol_kind::S_varied_variable_premise: // varied_variable_premise
      case symbol_kind::S_varied_variable_set: // varied_variable_set
      case symbol_kind::S_varied_variable: // varied_variable
      case symbol_kind::S_optional_varied_in_reduction_variable_matrix: // optional_varied_in_reduction_variable_matrix
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
      case symbol_kind::S_varied_in_reduction_variable_premises: // varied_in_reduction_variable_premises
      case symbol_kind::S_varied_in_reduction_variable_premise: // varied_in_reduction_variable_premise
      case symbol_kind::S_varied_in_reduction_variable_set: // varied_in_reduction_variable_set
      case symbol_kind::S_varied_in_reduction_variable: // varied_in_reduction_variable
      case symbol_kind::S_simple_metaformula: // simple_metaformula
      case symbol_kind::S_atomic_metaformula: // atomic_metaformula
      case symbol_kind::S_special_metaformula: // special_metaformula
      case symbol_kind::S_meta_object_free: // meta_object_free
      case symbol_kind::S_metapredicate: // metapredicate
      case symbol_kind::S_metapredicate_function: // metapredicate_function
      case symbol_kind::S_metapredicate_argument: // metapredicate_argument
      case symbol_kind::S_metapredicate_argument_body: // metapredicate_argument_body
      case symbol_kind::S_object_formula: // object_formula
      case symbol_kind::S_hoare_triple: // hoare_triple
      case symbol_kind::S_code_statement: // code_statement
      case symbol_kind::S_code_sequence: // code_sequence
      case symbol_kind::S_code_term: // code_term
      case symbol_kind::S_very_simple_formula: // very_simple_formula
      case symbol_kind::S_quantized_formula: // quantized_formula
      case symbol_kind::S_simple_formula: // simple_formula
      case symbol_kind::S_quantized_body: // quantized_body
      case symbol_kind::S_atomic_formula: // atomic_formula
      case symbol_kind::S_predicate: // predicate
      case symbol_kind::S_predicate_expression: // predicate_expression
      case symbol_kind::S_predicate_identifier: // predicate_identifier
      case symbol_kind::S_logic_formula: // logic_formula
      case symbol_kind::S_prefix_logic_formula: // prefix_logic_formula
      case symbol_kind::S_quantizer_declaration: // quantizer_declaration
      case symbol_kind::S_quantized_variable_list: // quantized_variable_list
      case symbol_kind::S_all_variable_list: // all_variable_list
      case symbol_kind::S_exist_variable_list: // exist_variable_list
      case symbol_kind::S_exclusion_set: // exclusion_set
      case symbol_kind::S_exclusion_list: // exclusion_list
      case symbol_kind::S_all_identifier_list: // all_identifier_list
      case symbol_kind::S_exist_identifier_list: // exist_identifier_list
      case symbol_kind::S_optional_in_term: // optional_in_term
      case symbol_kind::S_tuple: // tuple
      case symbol_kind::S_tuple_body: // tuple_body
      case symbol_kind::S_term: // term
      case symbol_kind::S_simple_term: // simple_term
      case symbol_kind::S_term_identifier: // term_identifier
      case symbol_kind::S_variable_exclusion_set: // variable_exclusion_set
      case symbol_kind::S_variable_exclusion_list: // variable_exclusion_list
      case symbol_kind::S_bound_variable: // bound_variable
      case symbol_kind::S_function_term: // function_term
      case symbol_kind::S_set_term: // set_term
      case symbol_kind::S_implicit_set_identifier_list: // implicit_set_identifier_list
      case symbol_kind::S_set_member_list: // set_member_list
      case symbol_kind::S_function_term_identifier: // function_term_identifier
        value.copy< ref6<unit> > (that.value);
        break;

      case symbol_kind::S_end_theory_name: // end_theory_name
        value.copy< std::pair<std::string, bool> > (that.value);
        break;

      case symbol_kind::S_natural_number_value: // "natural number value"
        value.copy< std::pair<std::string, integer> > (that.value);
        break;

      case symbol_kind::S_theorem_head: // theorem_head
        value.copy< std::pair<theorem::type, std::string> > (that.value);
        break;

      case symbol_kind::S_result_key: // "result"
      case symbol_kind::S_plain_name: // "name"
      case symbol_kind::S_label_key: // "label"
      case symbol_kind::S_all_key: // "∀"
      case symbol_kind::S_exist_key: // "∃"
      case symbol_kind::S_logical_not_key: // "¬"
      case symbol_kind::S_logical_and_key: // "∧"
      case symbol_kind::S_logical_or_key: // "∨"
      case symbol_kind::S_implies_key: // "⇒"
      case symbol_kind::S_impliedby_key: // "⇐"
      case symbol_kind::S_equivalent_key: // "⇔"
      case symbol_kind::S_natural_number_key: // "ℕ"
      case symbol_kind::S_less_key: // "<"
      case symbol_kind::S_greater_key: // ">"
      case symbol_kind::S_less_or_equal_key: // "≤"
      case symbol_kind::S_greater_or_equal_key: // "≥"
      case symbol_kind::S_not_less_key: // "≮"
      case symbol_kind::S_not_greater_key: // "≯"
      case symbol_kind::S_not_less_or_equal_key: // "≰"
      case symbol_kind::S_not_greater_or_equal_key: // "≱"
      case symbol_kind::S_equal_key: // "="
      case symbol_kind::S_not_equal_key: // "≠"
      case symbol_kind::S_divides_key: // "∣"
      case symbol_kind::S_not_divides_key: // "∤"
      case symbol_kind::S_mapsto_key: // "↦"
      case symbol_kind::S_Mapsto_key: // "⤇"
      case symbol_kind::S_factorial_key: // "!"
      case symbol_kind::S_mult_key: // "⋅"
      case symbol_kind::S_plus_key: // "+"
      case symbol_kind::S_minus_key: // "-"
      case symbol_kind::S_in_key: // "∈"
      case symbol_kind::S_not_in_key: // "∉"
      case symbol_kind::S_set_complement_key: // "∁"
      case symbol_kind::S_set_union_key: // "∪"
      case symbol_kind::S_set_intersection_key: // "∩"
      case symbol_kind::S_set_difference_key: // "∖"
      case symbol_kind::S_set_union_operator_key: // "⋃"
      case symbol_kind::S_set_intersection_operator_key: // "⋂"
      case symbol_kind::S_subset_key: // "⊆"
      case symbol_kind::S_proper_subset_key: // "⊊"
      case symbol_kind::S_superset_key: // "⊇"
      case symbol_kind::S_proper_superset_key: // "⊋"
      case symbol_kind::S_slash_key: // "/"
      case symbol_kind::S_backslash_key: // "\\"
      case symbol_kind::S_theory_name: // theory_name
      case symbol_kind::S_statement_name: // statement_name
      case symbol_kind::S_statement_label: // statement_label
      case symbol_kind::S_subproof_statement: // subproof_statement
      case symbol_kind::S_207_optional_result: // optional-result
        value.copy< std::string > (that.value);
        break;

      case symbol_kind::S_theorem_key: // "theorem"
        value.copy< theorem::type > (that.value);
        break;

      case symbol_kind::S_definition_labelstatement: // definition_labelstatement
        value.copy< val<definition> > (that.value);
        break;

      case symbol_kind::S_metapredicate_constant: // "metapredicate constant"
      case symbol_kind::S_function_key: // "function"
      case symbol_kind::S_predicate_key: // "predicate"
      case symbol_kind::S_predicate_constant: // "predicate constant"
      case symbol_kind::S_atom_constant: // "atom constant"
      case symbol_kind::S_function_constant: // "function constant"
      case symbol_kind::S_term_constant: // "term constant"
      case symbol_kind::S_metaformula_variable: // "metaformula variable"
      case symbol_kind::S_object_formula_variable: // "object formula variable"
      case symbol_kind::S_predicate_variable: // "predicate variable"
      case symbol_kind::S_atom_variable: // "atom variable"
      case symbol_kind::S_prefix_formula_variable: // "prefix formula variable"
      case symbol_kind::S_function_variable: // "function variable"
      case symbol_kind::S_object_variable: // "object variable"
      case symbol_kind::S_code_variable: // "code variable"
      case symbol_kind::S_all_variable: // "all variable"
      case symbol_kind::S_exist_variable: // "exist variable"
      case symbol_kind::S_function_map_variable: // "function map variable"
      case symbol_kind::S_is_set_variable: // "Set variable"
      case symbol_kind::S_set_variable: // "set variable"
      case symbol_kind::S_set_variable_definition: // "set variable definition"
      case symbol_kind::S_implicit_set_variable: // "implicit set variable"
        value.copy< val<unit> > (that.value);
        break;

      default:
        break;
    }

    location = that.location;
    return *this;
  }

  database_parser::stack_symbol_type&
  database_parser::stack_symbol_type::operator= (stack_symbol_type& that)
  {
    state = that.state;
    switch (that.kind ())
    {
      case symbol_kind::S_integer_value: // "integer value"
      case symbol_kind::S_subscript_natural_number_value: // "subscript natural number value"
      case symbol_kind::S_subscript_integer_value: // "subscript integer value"
      case symbol_kind::S_superscript_natural_number_value: // "superscript natural number value"
      case symbol_kind::S_superscript_integer_value: // "superscript integer value"
      case symbol_kind::S_optional_superscript_natural_number_value: // optional_superscript_natural_number_value
        value.move< integer > (that.value);
        break;

      case symbol_kind::S_metaformula_substitution_sequence: // metaformula_substitution_sequence
      case symbol_kind::S_substitution_for_metaformula: // substitution_for_metaformula
      case symbol_kind::S_metaformula_substitution: // metaformula_substitution
      case symbol_kind::S_formula_substitution_sequence: // formula_substitution_sequence
      case symbol_kind::S_substitution_for_formula: // substitution_for_formula
      case symbol_kind::S_formula_substitution: // formula_substitution
      case symbol_kind::S_term_substitution_sequence: // term_substitution_sequence
      case symbol_kind::S_term_substitution: // term_substitution
      case symbol_kind::S_predicate_function_application: // predicate_function_application
      case symbol_kind::S_term_function_application: // term_function_application
      case symbol_kind::S_theory: // theory
      case symbol_kind::S_include_theories: // include_theories
      case symbol_kind::S_include_theory: // include_theory
      case symbol_kind::S_theory_body: // theory_body
      case symbol_kind::S_formal_system: // formal_system
      case symbol_kind::S_formal_system_body: // formal_system_body
      case symbol_kind::S_formal_system_body_item: // formal_system_body_item
      case symbol_kind::S_theory_body_list: // theory_body_list
      case symbol_kind::S_theory_body_item: // theory_body_item
      case symbol_kind::S_postulate: // postulate
      case symbol_kind::S_conjecture: // conjecture
      case symbol_kind::S_theorem: // theorem
      case symbol_kind::S_theorem_statement: // theorem_statement
      case symbol_kind::S_proof: // proof
      case symbol_kind::S_198_11: // $@11
      case symbol_kind::S_199_compound_proof: // compound-proof
      case symbol_kind::S_proof_head: // proof_head
      case symbol_kind::S_proof_lines: // proof_lines
      case symbol_kind::S_proof_line: // proof_line
      case symbol_kind::S_proof_of_conclusion: // proof_of_conclusion
      case symbol_kind::S_find_statement: // find_statement
      case symbol_kind::S_find_statement_list: // find_statement_list
      case symbol_kind::S_find_statement_sequence: // find_statement_sequence
      case symbol_kind::S_find_definition_sequence: // find_definition_sequence
      case symbol_kind::S_find_statement_item: // find_statement_item
      case symbol_kind::S_find_statement_name: // find_statement_name
      case symbol_kind::S_214_13: // @13
      case symbol_kind::S_statement: // statement
      case symbol_kind::S_definition_statement: // definition_statement
      case symbol_kind::S_identifier_declaration: // identifier_declaration
      case symbol_kind::S_declarator_list: // declarator_list
      case symbol_kind::S_declarator_identifier_list: // declarator_identifier_list
      case symbol_kind::S_identifier_function_list: // identifier_function_list
      case symbol_kind::S_identifier_function_name: // identifier_function_name
      case symbol_kind::S_identifier_constant_list: // identifier_constant_list
      case symbol_kind::S_identifier_constant_name: // identifier_constant_name
      case symbol_kind::S_identifier_variable_list: // identifier_variable_list
      case symbol_kind::S_identifier_variable_name: // identifier_variable_name
      case symbol_kind::S_definition: // definition
      case symbol_kind::S_metaformula_definition: // metaformula_definition
      case symbol_kind::S_object_formula_definition: // object_formula_definition
      case symbol_kind::S_term_definition: // term_definition
      case symbol_kind::S_metaformula: // metaformula
      case symbol_kind::S_pure_metaformula: // pure_metaformula
      case symbol_kind::S_optional_varied_variable_matrix: // optional_varied_variable_matrix
      case symbol_kind::S_varied_variable_conclusions: // varied_variable_conclusions
      case symbol_kind::S_varied_variable_conclusion: // varied_variable_conclusion
      case symbol_kind::S_varied_variable_premises: // varied_variable_premises
      case symbol_kind::S_varied_variable_premise: // varied_variable_premise
      case symbol_kind::S_varied_variable_set: // varied_variable_set
      case symbol_kind::S_varied_variable: // varied_variable
      case symbol_kind::S_optional_varied_in_reduction_variable_matrix: // optional_varied_in_reduction_variable_matrix
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
      case symbol_kind::S_varied_in_reduction_variable_premises: // varied_in_reduction_variable_premises
      case symbol_kind::S_varied_in_reduction_variable_premise: // varied_in_reduction_variable_premise
      case symbol_kind::S_varied_in_reduction_variable_set: // varied_in_reduction_variable_set
      case symbol_kind::S_varied_in_reduction_variable: // varied_in_reduction_variable
      case symbol_kind::S_simple_metaformula: // simple_metaformula
      case symbol_kind::S_atomic_metaformula: // atomic_metaformula
      case symbol_kind::S_special_metaformula: // special_metaformula
      case symbol_kind::S_meta_object_free: // meta_object_free
      case symbol_kind::S_metapredicate: // metapredicate
      case symbol_kind::S_metapredicate_function: // metapredicate_function
      case symbol_kind::S_metapredicate_argument: // metapredicate_argument
      case symbol_kind::S_metapredicate_argument_body: // metapredicate_argument_body
      case symbol_kind::S_object_formula: // object_formula
      case symbol_kind::S_hoare_triple: // hoare_triple
      case symbol_kind::S_code_statement: // code_statement
      case symbol_kind::S_code_sequence: // code_sequence
      case symbol_kind::S_code_term: // code_term
      case symbol_kind::S_very_simple_formula: // very_simple_formula
      case symbol_kind::S_quantized_formula: // quantized_formula
      case symbol_kind::S_simple_formula: // simple_formula
      case symbol_kind::S_quantized_body: // quantized_body
      case symbol_kind::S_atomic_formula: // atomic_formula
      case symbol_kind::S_predicate: // predicate
      case symbol_kind::S_predicate_expression: // predicate_expression
      case symbol_kind::S_predicate_identifier: // predicate_identifier
      case symbol_kind::S_logic_formula: // logic_formula
      case symbol_kind::S_prefix_logic_formula: // prefix_logic_formula
      case symbol_kind::S_quantizer_declaration: // quantizer_declaration
      case symbol_kind::S_quantized_variable_list: // quantized_variable_list
      case symbol_kind::S_all_variable_list: // all_variable_list
      case symbol_kind::S_exist_variable_list: // exist_variable_list
      case symbol_kind::S_exclusion_set: // exclusion_set
      case symbol_kind::S_exclusion_list: // exclusion_list
      case symbol_kind::S_all_identifier_list: // all_identifier_list
      case symbol_kind::S_exist_identifier_list: // exist_identifier_list
      case symbol_kind::S_optional_in_term: // optional_in_term
      case symbol_kind::S_tuple: // tuple
      case symbol_kind::S_tuple_body: // tuple_body
      case symbol_kind::S_term: // term
      case symbol_kind::S_simple_term: // simple_term
      case symbol_kind::S_term_identifier: // term_identifier
      case symbol_kind::S_variable_exclusion_set: // variable_exclusion_set
      case symbol_kind::S_variable_exclusion_list: // variable_exclusion_list
      case symbol_kind::S_bound_variable: // bound_variable
      case symbol_kind::S_function_term: // function_term
      case symbol_kind::S_set_term: // set_term
      case symbol_kind::S_implicit_set_identifier_list: // implicit_set_identifier_list
      case symbol_kind::S_set_member_list: // set_member_list
      case symbol_kind::S_function_term_identifier: // function_term_identifier
        value.move< ref6<unit> > (that.value);
        break;

      case symbol_kind::S_end_theory_name: // end_theory_name
        value.move< std::pair<std::string, bool> > (that.value);
        break;

      case symbol_kind::S_natural_number_value: // "natural number value"
        value.move< std::pair<std::string, integer> > (that.value);
        break;

      case symbol_kind::S_theorem_head: // theorem_head
        value.move< std::pair<theorem::type, std::string> > (that.value);
        break;

      case symbol_kind::S_result_key: // "result"
      case symbol_kind::S_plain_name: // "name"
      case symbol_kind::S_label_key: // "label"
      case symbol_kind::S_all_key: // "∀"
      case symbol_kind::S_exist_key: // "∃"
      case symbol_kind::S_logical_not_key: // "¬"
      case symbol_kind::S_logical_and_key: // "∧"
      case symbol_kind::S_logical_or_key: // "∨"
      case symbol_kind::S_implies_key: // "⇒"
      case symbol_kind::S_impliedby_key: // "⇐"
      case symbol_kind::S_equivalent_key: // "⇔"
      case symbol_kind::S_natural_number_key: // "ℕ"
      case symbol_kind::S_less_key: // "<"
      case symbol_kind::S_greater_key: // ">"
      case symbol_kind::S_less_or_equal_key: // "≤"
      case symbol_kind::S_greater_or_equal_key: // "≥"
      case symbol_kind::S_not_less_key: // "≮"
      case symbol_kind::S_not_greater_key: // "≯"
      case symbol_kind::S_not_less_or_equal_key: // "≰"
      case symbol_kind::S_not_greater_or_equal_key: // "≱"
      case symbol_kind::S_equal_key: // "="
      case symbol_kind::S_not_equal_key: // "≠"
      case symbol_kind::S_divides_key: // "∣"
      case symbol_kind::S_not_divides_key: // "∤"
      case symbol_kind::S_mapsto_key: // "↦"
      case symbol_kind::S_Mapsto_key: // "⤇"
      case symbol_kind::S_factorial_key: // "!"
      case symbol_kind::S_mult_key: // "⋅"
      case symbol_kind::S_plus_key: // "+"
      case symbol_kind::S_minus_key: // "-"
      case symbol_kind::S_in_key: // "∈"
      case symbol_kind::S_not_in_key: // "∉"
      case symbol_kind::S_set_complement_key: // "∁"
      case symbol_kind::S_set_union_key: // "∪"
      case symbol_kind::S_set_intersection_key: // "∩"
      case symbol_kind::S_set_difference_key: // "∖"
      case symbol_kind::S_set_union_operator_key: // "⋃"
      case symbol_kind::S_set_intersection_operator_key: // "⋂"
      case symbol_kind::S_subset_key: // "⊆"
      case symbol_kind::S_proper_subset_key: // "⊊"
      case symbol_kind::S_superset_key: // "⊇"
      case symbol_kind::S_proper_superset_key: // "⊋"
      case symbol_kind::S_slash_key: // "/"
      case symbol_kind::S_backslash_key: // "\\"
      case symbol_kind::S_theory_name: // theory_name
      case symbol_kind::S_statement_name: // statement_name
      case symbol_kind::S_statement_label: // statement_label
      case symbol_kind::S_subproof_statement: // subproof_statement
      case symbol_kind::S_207_optional_result: // optional-result
        value.move< std::string > (that.value);
        break;

      case symbol_kind::S_theorem_key: // "theorem"
        value.move< theorem::type > (that.value);
        break;

      case symbol_kind::S_definition_labelstatement: // definition_labelstatement
        value.move< val<definition> > (that.value);
        break;

      case symbol_kind::S_metapredicate_constant: // "metapredicate constant"
      case symbol_kind::S_function_key: // "function"
      case symbol_kind::S_predicate_key: // "predicate"
      case symbol_kind::S_predicate_constant: // "predicate constant"
      case symbol_kind::S_atom_constant: // "atom constant"
      case symbol_kind::S_function_constant: // "function constant"
      case symbol_kind::S_term_constant: // "term constant"
      case symbol_kind::S_metaformula_variable: // "metaformula variable"
      case symbol_kind::S_object_formula_variable: // "object formula variable"
      case symbol_kind::S_predicate_variable: // "predicate variable"
      case symbol_kind::S_atom_variable: // "atom variable"
      case symbol_kind::S_prefix_formula_variable: // "prefix formula variable"
      case symbol_kind::S_function_variable: // "function variable"
      case symbol_kind::S_object_variable: // "object variable"
      case symbol_kind::S_code_variable: // "code variable"
      case symbol_kind::S_all_variable: // "all variable"
      case symbol_kind::S_exist_variable: // "exist variable"
      case symbol_kind::S_function_map_variable: // "function map variable"
      case symbol_kind::S_is_set_variable: // "Set variable"
      case symbol_kind::S_set_variable: // "set variable"
      case symbol_kind::S_set_variable_definition: // "set variable definition"
      case symbol_kind::S_implicit_set_variable: // "implicit set variable"
        value.move< val<unit> > (that.value);
        break;

      default:
        break;
    }

    location = that.location;
    // that is emptied.
    that.state = empty_state;
    return *this;
  }
#endif

  template <typename Base>
  void
  database_parser::yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const
  {
    if (yymsg)
      YY_SYMBOL_PRINT (yymsg, yysym);
  }

#if MLIDEBUG
  template <typename Base>
  void
  database_parser::yy_print_ (std::ostream& yyo, const basic_symbol<Base>& yysym) const
  {
    std::ostream& yyoutput = yyo;
    YY_USE (yyoutput);
    if (yysym.empty ())
      yyo << "empty symbol";
    else
      {
        symbol_kind_type yykind = yysym.kind ();
        yyo << (yykind < YYNTOKENS ? "token" : "nterm")
            << ' ' << yysym.name () << " ("
            << yysym.location << ": ";
        YY_USE (yykind);
        yyo << ')';
      }
  }
#endif

  void
  database_parser::yypush_ (const char* m, YY_MOVE_REF (stack_symbol_type) sym)
  {
    if (m)
      YY_SYMBOL_PRINT (m, sym);
    yystack_.push (YY_MOVE (sym));
  }

  void
  database_parser::yypush_ (const char* m, state_type s, YY_MOVE_REF (symbol_type) sym)
  {
#if 201103L <= YY_CPLUSPLUS
    yypush_ (m, stack_symbol_type (s, std::move (sym)));
#else
    stack_symbol_type ss (s, sym);
    yypush_ (m, ss);
#endif
  }

  void
  database_parser::yypop_ (int n) YY_NOEXCEPT
  {
    yystack_.pop (n);
  }

#if MLIDEBUG
  std::ostream&
  database_parser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  database_parser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  database_parser::debug_level_type
  database_parser::debug_level () const
  {
    return yydebug_;
  }

  void
  database_parser::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif // MLIDEBUG

  database_parser::state_type
  database_parser::yy_lr_goto_state_ (state_type yystate, int yysym)
  {
    int yyr = yypgoto_[yysym - YYNTOKENS] + yystate;
    if (0 <= yyr && yyr <= yylast_ && yycheck_[yyr] == yystate)
      return yytable_[yyr];
    else
      return yydefgoto_[yysym - YYNTOKENS];
  }

  bool
  database_parser::yy_pact_value_is_default_ (int yyvalue) YY_NOEXCEPT
  {
    return yyvalue == yypact_ninf_;
  }

  bool
  database_parser::yy_table_value_is_error_ (int yyvalue) YY_NOEXCEPT
  {
    return yyvalue == yytable_ninf_;
  }

  int
  database_parser::operator() ()
  {
    return parse ();
  }

  int
  database_parser::parse ()
  {
    int yyn;
    /// Length of the RHS of the rule being reduced.
    int yylen = 0;

    // Error handling.
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// The lookahead symbol.
    symbol_type yyla;

    /// The locations where the error started and ended.
    stack_symbol_type yyerror_range[3];

    /// The return value of parse ().
    int yyresult;

    // Discard the LAC context in case there still is one left from a
    // previous invocation.
    yy_lac_discard_ ("init");

#if YY_EXCEPTIONS
    try
#endif // YY_EXCEPTIONS
      {
    YYCDEBUG << "Starting parse\n";


    // User initialization code.
#line 33 "../../mli-root/src/database-parser.yy"
{
  yyla.location.initialize(&infile_name); // Initialize the initial location.
}

#line 2035 "../../mli-root/src/database-parser.cc"


    /* Initialize the stack.  The initial state will be set in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystack_.clear ();
    yypush_ (YY_NULLPTR, 0, YY_MOVE (yyla));

  /*-----------------------------------------------.
  | yynewstate -- push a new symbol on the stack.  |
  `-----------------------------------------------*/
  yynewstate:
    YYCDEBUG << "Entering state " << int (yystack_[0].state) << '\n';
    YY_STACK_PRINT ();

    // Accept?
    if (yystack_[0].state == yyfinal_)
      YYACCEPT;

    goto yybackup;


  /*-----------.
  | yybackup.  |
  `-----------*/
  yybackup:
    // Try to take a decision without lookahead.
    yyn = yypact_[+yystack_[0].state];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    // Read a lookahead token.
    if (yyla.empty ())
      {
        YYCDEBUG << "Reading a token\n";
#if YY_EXCEPTIONS
        try
#endif // YY_EXCEPTIONS
          {
            yyla.kind_ = yytranslate_ (yylex (&yyla.value, &yyla.location));
          }
#if YY_EXCEPTIONS
        catch (const syntax_error& yyexc)
          {
            YYCDEBUG << "Caught exception: " << yyexc.what() << '\n';
            error (yyexc);
            goto yyerrlab1;
          }
#endif // YY_EXCEPTIONS
      }
    YY_SYMBOL_PRINT ("Next token is", yyla);

    if (yyla.kind () == symbol_kind::S_YYerror)
    {
      // The scanner already issued an error message, process directly
      // to error recovery.  But do not keep the error token as
      // lookahead, it is too special and may lead us to an endless
      // loop in error recovery. */
      yyla.kind_ = symbol_kind::S_YYUNDEF;
      goto yyerrlab1;
    }

    /* If the proper action on seeing token YYLA.TYPE is to reduce or
       to detect an error, take that action.  */
    yyn += yyla.kind ();
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yyla.kind ())
      {
        if (!yy_lac_establish_ (yyla.kind ()))
          goto yyerrlab;
        goto yydefault;
      }

    // Reduce or error.
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
        if (yy_table_value_is_error_ (yyn))
          goto yyerrlab;
        if (!yy_lac_establish_ (yyla.kind ()))
          goto yyerrlab;

        yyn = -yyn;
        goto yyreduce;
      }

    // Count tokens shifted since error; after three, turn off error status.
    if (yyerrstatus_)
      --yyerrstatus_;

    // Shift the lookahead token.
    yypush_ ("Shifting", state_type (yyn), YY_MOVE (yyla));
    yy_lac_discard_ ("shift");
    goto yynewstate;


  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[+yystack_[0].state];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;


  /*-----------------------------.
  | yyreduce -- do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    {
      stack_symbol_type yylhs;
      yylhs.state = yy_lr_goto_state_ (yystack_[yylen].state, yyr1_[yyn]);
      /* Variants are always initialized to an empty instance of the
         correct type. The default '$$ = $1' action is NOT applied
         when using variants.  */
      switch (yyr1_[yyn])
    {
      case symbol_kind::S_integer_value: // "integer value"
      case symbol_kind::S_subscript_natural_number_value: // "subscript natural number value"
      case symbol_kind::S_subscript_integer_value: // "subscript integer value"
      case symbol_kind::S_superscript_natural_number_value: // "superscript natural number value"
      case symbol_kind::S_superscript_integer_value: // "superscript integer value"
      case symbol_kind::S_optional_superscript_natural_number_value: // optional_superscript_natural_number_value
        yylhs.value.emplace< integer > ();
        break;

      case symbol_kind::S_metaformula_substitution_sequence: // metaformula_substitution_sequence
      case symbol_kind::S_substitution_for_metaformula: // substitution_for_metaformula
      case symbol_kind::S_metaformula_substitution: // metaformula_substitution
      case symbol_kind::S_formula_substitution_sequence: // formula_substitution_sequence
      case symbol_kind::S_substitution_for_formula: // substitution_for_formula
      case symbol_kind::S_formula_substitution: // formula_substitution
      case symbol_kind::S_term_substitution_sequence: // term_substitution_sequence
      case symbol_kind::S_term_substitution: // term_substitution
      case symbol_kind::S_predicate_function_application: // predicate_function_application
      case symbol_kind::S_term_function_application: // term_function_application
      case symbol_kind::S_theory: // theory
      case symbol_kind::S_include_theories: // include_theories
      case symbol_kind::S_include_theory: // include_theory
      case symbol_kind::S_theory_body: // theory_body
      case symbol_kind::S_formal_system: // formal_system
      case symbol_kind::S_formal_system_body: // formal_system_body
      case symbol_kind::S_formal_system_body_item: // formal_system_body_item
      case symbol_kind::S_theory_body_list: // theory_body_list
      case symbol_kind::S_theory_body_item: // theory_body_item
      case symbol_kind::S_postulate: // postulate
      case symbol_kind::S_conjecture: // conjecture
      case symbol_kind::S_theorem: // theorem
      case symbol_kind::S_theorem_statement: // theorem_statement
      case symbol_kind::S_proof: // proof
      case symbol_kind::S_198_11: // $@11
      case symbol_kind::S_199_compound_proof: // compound-proof
      case symbol_kind::S_proof_head: // proof_head
      case symbol_kind::S_proof_lines: // proof_lines
      case symbol_kind::S_proof_line: // proof_line
      case symbol_kind::S_proof_of_conclusion: // proof_of_conclusion
      case symbol_kind::S_find_statement: // find_statement
      case symbol_kind::S_find_statement_list: // find_statement_list
      case symbol_kind::S_find_statement_sequence: // find_statement_sequence
      case symbol_kind::S_find_definition_sequence: // find_definition_sequence
      case symbol_kind::S_find_statement_item: // find_statement_item
      case symbol_kind::S_find_statement_name: // find_statement_name
      case symbol_kind::S_214_13: // @13
      case symbol_kind::S_statement: // statement
      case symbol_kind::S_definition_statement: // definition_statement
      case symbol_kind::S_identifier_declaration: // identifier_declaration
      case symbol_kind::S_declarator_list: // declarator_list
      case symbol_kind::S_declarator_identifier_list: // declarator_identifier_list
      case symbol_kind::S_identifier_function_list: // identifier_function_list
      case symbol_kind::S_identifier_function_name: // identifier_function_name
      case symbol_kind::S_identifier_constant_list: // identifier_constant_list
      case symbol_kind::S_identifier_constant_name: // identifier_constant_name
      case symbol_kind::S_identifier_variable_list: // identifier_variable_list
      case symbol_kind::S_identifier_variable_name: // identifier_variable_name
      case symbol_kind::S_definition: // definition
      case symbol_kind::S_metaformula_definition: // metaformula_definition
      case symbol_kind::S_object_formula_definition: // object_formula_definition
      case symbol_kind::S_term_definition: // term_definition
      case symbol_kind::S_metaformula: // metaformula
      case symbol_kind::S_pure_metaformula: // pure_metaformula
      case symbol_kind::S_optional_varied_variable_matrix: // optional_varied_variable_matrix
      case symbol_kind::S_varied_variable_conclusions: // varied_variable_conclusions
      case symbol_kind::S_varied_variable_conclusion: // varied_variable_conclusion
      case symbol_kind::S_varied_variable_premises: // varied_variable_premises
      case symbol_kind::S_varied_variable_premise: // varied_variable_premise
      case symbol_kind::S_varied_variable_set: // varied_variable_set
      case symbol_kind::S_varied_variable: // varied_variable
      case symbol_kind::S_optional_varied_in_reduction_variable_matrix: // optional_varied_in_reduction_variable_matrix
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
      case symbol_kind::S_varied_in_reduction_variable_premises: // varied_in_reduction_variable_premises
      case symbol_kind::S_varied_in_reduction_variable_premise: // varied_in_reduction_variable_premise
      case symbol_kind::S_varied_in_reduction_variable_set: // varied_in_reduction_variable_set
      case symbol_kind::S_varied_in_reduction_variable: // varied_in_reduction_variable
      case symbol_kind::S_simple_metaformula: // simple_metaformula
      case symbol_kind::S_atomic_metaformula: // atomic_metaformula
      case symbol_kind::S_special_metaformula: // special_metaformula
      case symbol_kind::S_meta_object_free: // meta_object_free
      case symbol_kind::S_metapredicate: // metapredicate
      case symbol_kind::S_metapredicate_function: // metapredicate_function
      case symbol_kind::S_metapredicate_argument: // metapredicate_argument
      case symbol_kind::S_metapredicate_argument_body: // metapredicate_argument_body
      case symbol_kind::S_object_formula: // object_formula
      case symbol_kind::S_hoare_triple: // hoare_triple
      case symbol_kind::S_code_statement: // code_statement
      case symbol_kind::S_code_sequence: // code_sequence
      case symbol_kind::S_code_term: // code_term
      case symbol_kind::S_very_simple_formula: // very_simple_formula
      case symbol_kind::S_quantized_formula: // quantized_formula
      case symbol_kind::S_simple_formula: // simple_formula
      case symbol_kind::S_quantized_body: // quantized_body
      case symbol_kind::S_atomic_formula: // atomic_formula
      case symbol_kind::S_predicate: // predicate
      case symbol_kind::S_predicate_expression: // predicate_expression
      case symbol_kind::S_predicate_identifier: // predicate_identifier
      case symbol_kind::S_logic_formula: // logic_formula
      case symbol_kind::S_prefix_logic_formula: // prefix_logic_formula
      case symbol_kind::S_quantizer_declaration: // quantizer_declaration
      case symbol_kind::S_quantized_variable_list: // quantized_variable_list
      case symbol_kind::S_all_variable_list: // all_variable_list
      case symbol_kind::S_exist_variable_list: // exist_variable_list
      case symbol_kind::S_exclusion_set: // exclusion_set
      case symbol_kind::S_exclusion_list: // exclusion_list
      case symbol_kind::S_all_identifier_list: // all_identifier_list
      case symbol_kind::S_exist_identifier_list: // exist_identifier_list
      case symbol_kind::S_optional_in_term: // optional_in_term
      case symbol_kind::S_tuple: // tuple
      case symbol_kind::S_tuple_body: // tuple_body
      case symbol_kind::S_term: // term
      case symbol_kind::S_simple_term: // simple_term
      case symbol_kind::S_term_identifier: // term_identifier
      case symbol_kind::S_variable_exclusion_set: // variable_exclusion_set
      case symbol_kind::S_variable_exclusion_list: // variable_exclusion_list
      case symbol_kind::S_bound_variable: // bound_variable
      case symbol_kind::S_function_term: // function_term
      case symbol_kind::S_set_term: // set_term
      case symbol_kind::S_implicit_set_identifier_list: // implicit_set_identifier_list
      case symbol_kind::S_set_member_list: // set_member_list
      case symbol_kind::S_function_term_identifier: // function_term_identifier
        yylhs.value.emplace< ref6<unit> > ();
        break;

      case symbol_kind::S_end_theory_name: // end_theory_name
        yylhs.value.emplace< std::pair<std::string, bool> > ();
        break;

      case symbol_kind::S_natural_number_value: // "natural number value"
        yylhs.value.emplace< std::pair<std::string, integer> > ();
        break;

      case symbol_kind::S_theorem_head: // theorem_head
        yylhs.value.emplace< std::pair<theorem::type, std::string> > ();
        break;

      case symbol_kind::S_result_key: // "result"
      case symbol_kind::S_plain_name: // "name"
      case symbol_kind::S_label_key: // "label"
      case symbol_kind::S_all_key: // "∀"
      case symbol_kind::S_exist_key: // "∃"
      case symbol_kind::S_logical_not_key: // "¬"
      case symbol_kind::S_logical_and_key: // "∧"
      case symbol_kind::S_logical_or_key: // "∨"
      case symbol_kind::S_implies_key: // "⇒"
      case symbol_kind::S_impliedby_key: // "⇐"
      case symbol_kind::S_equivalent_key: // "⇔"
      case symbol_kind::S_natural_number_key: // "ℕ"
      case symbol_kind::S_less_key: // "<"
      case symbol_kind::S_greater_key: // ">"
      case symbol_kind::S_less_or_equal_key: // "≤"
      case symbol_kind::S_greater_or_equal_key: // "≥"
      case symbol_kind::S_not_less_key: // "≮"
      case symbol_kind::S_not_greater_key: // "≯"
      case symbol_kind::S_not_less_or_equal_key: // "≰"
      case symbol_kind::S_not_greater_or_equal_key: // "≱"
      case symbol_kind::S_equal_key: // "="
      case symbol_kind::S_not_equal_key: // "≠"
      case symbol_kind::S_divides_key: // "∣"
      case symbol_kind::S_not_divides_key: // "∤"
      case symbol_kind::S_mapsto_key: // "↦"
      case symbol_kind::S_Mapsto_key: // "⤇"
      case symbol_kind::S_factorial_key: // "!"
      case symbol_kind::S_mult_key: // "⋅"
      case symbol_kind::S_plus_key: // "+"
      case symbol_kind::S_minus_key: // "-"
      case symbol_kind::S_in_key: // "∈"
      case symbol_kind::S_not_in_key: // "∉"
      case symbol_kind::S_set_complement_key: // "∁"
      case symbol_kind::S_set_union_key: // "∪"
      case symbol_kind::S_set_intersection_key: // "∩"
      case symbol_kind::S_set_difference_key: // "∖"
      case symbol_kind::S_set_union_operator_key: // "⋃"
      case symbol_kind::S_set_intersection_operator_key: // "⋂"
      case symbol_kind::S_subset_key: // "⊆"
      case symbol_kind::S_proper_subset_key: // "⊊"
      case symbol_kind::S_superset_key: // "⊇"
      case symbol_kind::S_proper_superset_key: // "⊋"
      case symbol_kind::S_slash_key: // "/"
      case symbol_kind::S_backslash_key: // "\\"
      case symbol_kind::S_theory_name: // theory_name
      case symbol_kind::S_statement_name: // statement_name
      case symbol_kind::S_statement_label: // statement_label
      case symbol_kind::S_subproof_statement: // subproof_statement
      case symbol_kind::S_207_optional_result: // optional-result
        yylhs.value.emplace< std::string > ();
        break;

      case symbol_kind::S_theorem_key: // "theorem"
        yylhs.value.emplace< theorem::type > ();
        break;

      case symbol_kind::S_definition_labelstatement: // definition_labelstatement
        yylhs.value.emplace< val<definition> > ();
        break;

      case symbol_kind::S_metapredicate_constant: // "metapredicate constant"
      case symbol_kind::S_function_key: // "function"
      case symbol_kind::S_predicate_key: // "predicate"
      case symbol_kind::S_predicate_constant: // "predicate constant"
      case symbol_kind::S_atom_constant: // "atom constant"
      case symbol_kind::S_function_constant: // "function constant"
      case symbol_kind::S_term_constant: // "term constant"
      case symbol_kind::S_metaformula_variable: // "metaformula variable"
      case symbol_kind::S_object_formula_variable: // "object formula variable"
      case symbol_kind::S_predicate_variable: // "predicate variable"
      case symbol_kind::S_atom_variable: // "atom variable"
      case symbol_kind::S_prefix_formula_variable: // "prefix formula variable"
      case symbol_kind::S_function_variable: // "function variable"
      case symbol_kind::S_object_variable: // "object variable"
      case symbol_kind::S_code_variable: // "code variable"
      case symbol_kind::S_all_variable: // "all variable"
      case symbol_kind::S_exist_variable: // "exist variable"
      case symbol_kind::S_function_map_variable: // "function map variable"
      case symbol_kind::S_is_set_variable: // "Set variable"
      case symbol_kind::S_set_variable: // "set variable"
      case symbol_kind::S_set_variable_definition: // "set variable definition"
      case symbol_kind::S_implicit_set_variable: // "implicit set variable"
        yylhs.value.emplace< val<unit> > ();
        break;

      default:
        break;
    }


      // Default location.
      {
        stack_type::slice range (yystack_, yylen);
        YYLLOC_DEFAULT (yylhs.location, range, yylen);
        yyerror_range[1].location = yylhs.location;
      }

      // Perform the reduction.
      YY_REDUCE_PRINT (yyn);
#if YY_EXCEPTIONS
      try
#endif // YY_EXCEPTIONS
        {
          switch (yyn)
            {
  case 2: // file: %empty
#line 784 "../../mli-root/src/database-parser.yy"
           {}
#line 2400 "../../mli-root/src/database-parser.cc"
    break;

  case 3: // file: file_contents
#line 785 "../../mli-root/src/database-parser.yy"
                  {}
#line 2406 "../../mli-root/src/database-parser.cc"
    break;

  case 4: // file: error
#line 786 "../../mli-root/src/database-parser.yy"
          {
      declaration_context = false;
      bound_variable_type = free_variable_context;
      YYABORT;
    }
#line 2416 "../../mli-root/src/database-parser.cc"
    break;

  case 5: // file_contents: file_contents command
#line 795 "../../mli-root/src/database-parser.yy"
                          {}
#line 2422 "../../mli-root/src/database-parser.cc"
    break;

  case 6: // file_contents: command
#line 796 "../../mli-root/src/database-parser.yy"
                          {}
#line 2428 "../../mli-root/src/database-parser.cc"
    break;

  case 7: // $@1: %empty
#line 801 "../../mli-root/src/database-parser.yy"
    { symbol_table.clear(); }
#line 2434 "../../mli-root/src/database-parser.cc"
    break;

  case 8: // command: $@1 theory
#line 801 "../../mli-root/src/database-parser.yy"
                                     {}
#line 2440 "../../mli-root/src/database-parser.cc"
    break;

  case 9: // metaformula_substitution_sequence: substitution_for_metaformula
#line 806 "../../mli-root/src/database-parser.yy"
                                    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2446 "../../mli-root/src/database-parser.cc"
    break;

  case 10: // metaformula_substitution_sequence: metaformula_substitution_sequence substitution_for_metaformula
#line 807 "../../mli-root/src/database-parser.yy"
                                                                         {
      yylhs.value.as < ref6<unit> > () =  val<substitution>(yystack_[1].value.as < ref6<unit> > ()) * val<substitution>(yystack_[0].value.as < ref6<unit> > ());
    }
#line 2454 "../../mli-root/src/database-parser.cc"
    break;

  case 11: // substitution_for_metaformula: metaformula_substitution
#line 814 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2460 "../../mli-root/src/database-parser.cc"
    break;

  case 12: // substitution_for_metaformula: formula_substitution
#line 815 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2466 "../../mli-root/src/database-parser.cc"
    break;

  case 13: // substitution_for_metaformula: term_substitution
#line 816 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2472 "../../mli-root/src/database-parser.cc"
    break;

  case 14: // metaformula_substitution: "[" "metaformula variable" "⤇" metaformula "]"
#line 821 "../../mli-root/src/database-parser.yy"
                                                       {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2482 "../../mli-root/src/database-parser.cc"
    break;

  case 15: // formula_substitution_sequence: substitution_for_formula
#line 830 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2488 "../../mli-root/src/database-parser.cc"
    break;

  case 16: // formula_substitution_sequence: formula_substitution_sequence substitution_for_formula
#line 831 "../../mli-root/src/database-parser.yy"
                                                                 {
      yylhs.value.as < ref6<unit> > () = val<substitution>(yystack_[1].value.as < ref6<unit> > ()) * val<substitution>(yystack_[0].value.as < ref6<unit> > ());
    }
#line 2496 "../../mli-root/src/database-parser.cc"
    break;

  case 17: // substitution_for_formula: formula_substitution
#line 838 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2502 "../../mli-root/src/database-parser.cc"
    break;

  case 18: // substitution_for_formula: term_substitution
#line 839 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2508 "../../mli-root/src/database-parser.cc"
    break;

  case 19: // formula_substitution: "[" "object formula variable" "⤇" object_formula "]"
#line 844 "../../mli-root/src/database-parser.yy"
                                                             {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2518 "../../mli-root/src/database-parser.cc"
    break;

  case 20: // formula_substitution: "[" "predicate variable" "⤇" predicate "]"
#line 849 "../../mli-root/src/database-parser.yy"
                                                   {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2528 "../../mli-root/src/database-parser.cc"
    break;

  case 21: // formula_substitution: "[" "atom variable" "⤇" "atom constant" "]"
#line 854 "../../mli-root/src/database-parser.yy"
                                                  {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2538 "../../mli-root/src/database-parser.cc"
    break;

  case 22: // term_substitution_sequence: term_substitution
#line 863 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2544 "../../mli-root/src/database-parser.cc"
    break;

  case 23: // term_substitution_sequence: term_substitution_sequence term_substitution
#line 864 "../../mli-root/src/database-parser.yy"
                                                       {
      yylhs.value.as < ref6<unit> > () = val<substitution>(yystack_[1].value.as < ref6<unit> > ()) * val<substitution>(yystack_[0].value.as < ref6<unit> > ());
    }
#line 2552 "../../mli-root/src/database-parser.cc"
    break;

  case 24: // term_substitution: "[" term_identifier "⤇" term "]"
#line 871 "../../mli-root/src/database-parser.yy"
                                           {
      val<variable> v(yystack_[3].value.as < ref6<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2562 "../../mli-root/src/database-parser.cc"
    break;

  case 25: // predicate_function_application: "(" "object variable" "↦" object_formula ")" tuple
#line 880 "../../mli-root/src/database-parser.yy"
                                                              {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[4].value.as < val<unit> > (), yystack_[2].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2570 "../../mli-root/src/database-parser.cc"
    break;

  case 26: // $@2: %empty
#line 883 "../../mli-root/src/database-parser.yy"
                                                           { symbol_table.pop_level(); }
#line 2576 "../../mli-root/src/database-parser.cc"
    break;

  case 27: // predicate_function_application: "(" "𝛌" "function map variable" "↦" object_formula $@2 ")" tuple
#line 883 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[5].value.as < val<unit> > (), yystack_[3].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2584 "../../mli-root/src/database-parser.cc"
    break;

  case 28: // predicate_function_application: "predicate" tuple
#line 886 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = val<function_application>(make, yystack_[1].value.as < val<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 2590 "../../mli-root/src/database-parser.cc"
    break;

  case 29: // term_function_application: "(" "object variable" "↦" term ")" tuple
#line 891 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[4].value.as < val<unit> > (), yystack_[2].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2598 "../../mli-root/src/database-parser.cc"
    break;

  case 30: // $@3: %empty
#line 894 "../../mli-root/src/database-parser.yy"
                                                 { symbol_table.pop_level(); }
#line 2604 "../../mli-root/src/database-parser.cc"
    break;

  case 31: // term_function_application: "(" "𝛌" "function map variable" "↦" term $@3 ")" tuple
#line 894 "../../mli-root/src/database-parser.yy"
                                                                                            {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[5].value.as < val<unit> > (), yystack_[3].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2612 "../../mli-root/src/database-parser.cc"
    break;

  case 32: // term_function_application: "function" tuple
#line 897 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.as < ref6<unit> > () = val<function_application>(make, yystack_[1].value.as < val<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 2618 "../../mli-root/src/database-parser.cc"
    break;

  case 33: // $@4: %empty
#line 903 "../../mli-root/src/database-parser.yy"
        { theory_ = ref1<theory>(make, yystack_[1].value.as < std::string > ());
          yypval.insert(theory_);
          symbol_table.push_level();
    }
#line 2627 "../../mli-root/src/database-parser.cc"
    break;

  case 34: // theory: "theory" statement_name "." $@4 include_theories theory_body "end" "theory" end_theory_name "."
#line 909 "../../mli-root/src/database-parser.yy"
                                          {
      if (yystack_[1].value.as < std::pair<std::string, bool> > ().second && yystack_[8].value.as < std::string > () != yystack_[1].value.as < std::pair<std::string, bool> > ().first) {
        database_parser::error(yystack_[1].location, "warning: Name mismatch, theory " + yystack_[8].value.as < std::string > ()
          + ", end theory " + yystack_[1].value.as < std::pair<std::string, bool> > ().first + ".");
      }

      symbol_table.pop_level();
    }
#line 2640 "../../mli-root/src/database-parser.cc"
    break;

  case 35: // end_theory_name: %empty
#line 921 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < std::pair<std::string, bool> > () = std::make_pair(std::string{}, false); }
#line 2646 "../../mli-root/src/database-parser.cc"
    break;

  case 36: // end_theory_name: statement_name
#line 922 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < std::pair<std::string, bool> > () = std::make_pair(yystack_[0].value.as < std::string > (), true); }
#line 2652 "../../mli-root/src/database-parser.cc"
    break;

  case 37: // include_theories: %empty
#line 927 "../../mli-root/src/database-parser.yy"
           {}
#line 2658 "../../mli-root/src/database-parser.cc"
    break;

  case 38: // include_theories: include_theories include_theory
#line 928 "../../mli-root/src/database-parser.yy"
                                    {}
#line 2664 "../../mli-root/src/database-parser.cc"
    break;

  case 39: // include_theory: "include" "theory" theory_name "."
#line 932 "../../mli-root/src/database-parser.yy"
                                         {
      std::optional<ref1<theory>> th = yypval.find(yystack_[1].value.as < std::string > ());

      if (!th)
        throw syntax_error(yystack_[1].location, "Include theory " + yystack_[1].value.as < std::string > () + " not found.");

      theory_->insert(*th);
    }
#line 2677 "../../mli-root/src/database-parser.cc"
    break;

  case 40: // theory_name: "name"
#line 944 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2683 "../../mli-root/src/database-parser.cc"
    break;

  case 41: // theory_name: "label"
#line 945 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2689 "../../mli-root/src/database-parser.cc"
    break;

  case 42: // theory_body: theory_body_list
#line 950 "../../mli-root/src/database-parser.yy"
                     {}
#line 2695 "../../mli-root/src/database-parser.cc"
    break;

  case 43: // theory_body: formal_system theory_body_list
#line 951 "../../mli-root/src/database-parser.yy"
                                   {}
#line 2701 "../../mli-root/src/database-parser.cc"
    break;

  case 44: // $@5: %empty
#line 957 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(); }
#line 2707 "../../mli-root/src/database-parser.cc"
    break;

  case 45: // formal_system: "formal system" "." $@5 formal_system_body "end" "formal system" "."
#line 959 "../../mli-root/src/database-parser.yy"
                              { symbol_table.pop_level(); }
#line 2713 "../../mli-root/src/database-parser.cc"
    break;

  case 46: // formal_system_body: %empty
#line 964 "../../mli-root/src/database-parser.yy"
           {}
#line 2719 "../../mli-root/src/database-parser.cc"
    break;

  case 47: // formal_system_body: formal_system_body formal_system_body_item
#line 965 "../../mli-root/src/database-parser.yy"
                                               {}
#line 2725 "../../mli-root/src/database-parser.cc"
    break;

  case 48: // formal_system_body_item: identifier_declaration
#line 970 "../../mli-root/src/database-parser.yy"
                           {}
#line 2731 "../../mli-root/src/database-parser.cc"
    break;

  case 49: // formal_system_body_item: postulate
#line 971 "../../mli-root/src/database-parser.yy"
                 { theory_->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 2737 "../../mli-root/src/database-parser.cc"
    break;

  case 50: // formal_system_body_item: definition_labelstatement
#line 972 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref4<statement>(yystack_[0].value.as < val<definition> > ())); }
#line 2743 "../../mli-root/src/database-parser.cc"
    break;

  case 51: // theory_body_list: %empty
#line 977 "../../mli-root/src/database-parser.yy"
           {}
#line 2749 "../../mli-root/src/database-parser.cc"
    break;

  case 52: // theory_body_list: theory_body_list theory_body_item
#line 978 "../../mli-root/src/database-parser.yy"
                                      {}
#line 2755 "../../mli-root/src/database-parser.cc"
    break;

  case 53: // theory_body_item: theorem
#line 988 "../../mli-root/src/database-parser.yy"
               { theory_->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 2761 "../../mli-root/src/database-parser.cc"
    break;

  case 54: // theory_body_item: identifier_declaration
#line 989 "../../mli-root/src/database-parser.yy"
                           {}
#line 2767 "../../mli-root/src/database-parser.cc"
    break;

  case 55: // theory_body_item: conjecture
#line 990 "../../mli-root/src/database-parser.yy"
                  { theory_->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 2773 "../../mli-root/src/database-parser.cc"
    break;

  case 56: // theory_body_item: definition_labelstatement
#line 992 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref4<statement>(yystack_[0].value.as < val<definition> > ())); }
#line 2779 "../../mli-root/src/database-parser.cc"
    break;

  case 57: // $@6: %empty
#line 998 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2785 "../../mli-root/src/database-parser.cc"
    break;

  case 58: // postulate: "postulate" statement_name "." $@6 statement "."
#line 999 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::postulate_, yystack_[4].value.as < std::string > (), yystack_[1].value.as < ref6<unit> > (), true);
    }
#line 2794 "../../mli-root/src/database-parser.cc"
    break;

  case 59: // postulate: conjecture
#line 1003 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2800 "../../mli-root/src/database-parser.cc"
    break;

  case 60: // $@7: %empty
#line 1005 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2806 "../../mli-root/src/database-parser.cc"
    break;

  case 61: // postulate: "axiom" statement_name "." $@7 statement "."
#line 1006 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      val<formula> f(yystack_[1].value.as < ref6<unit> > ());

      if (!f->is_axiom())
        throw syntax_error(yystack_[1].location, "Axiom statement not an object formula.");

      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::postulate_, yystack_[4].value.as < std::string > (), f);
    }
#line 2821 "../../mli-root/src/database-parser.cc"
    break;

  case 62: // $@8: %empty
#line 1017 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2827 "../../mli-root/src/database-parser.cc"
    break;

  case 63: // postulate: "rule" statement_name "." $@8 statement "."
#line 1018 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      val<formula> f(yystack_[1].value.as < ref6<unit> > ());

      if (!f->is_rule())
        throw syntax_error(yystack_[1].location, "Rule statement not an inference.");

      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::postulate_, yystack_[4].value.as < std::string > (), f);
    }
#line 2842 "../../mli-root/src/database-parser.cc"
    break;

  case 64: // $@9: %empty
#line 1033 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2848 "../../mli-root/src/database-parser.cc"
    break;

  case 65: // conjecture: "conjecture" statement_name "." $@9 statement "."
#line 1034 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::conjecture_, yystack_[4].value.as < std::string > (), yystack_[1].value.as < ref6<unit> > (), true);
    }
#line 2857 "../../mli-root/src/database-parser.cc"
    break;

  case 66: // $@10: %empty
#line 1042 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2863 "../../mli-root/src/database-parser.cc"
    break;

  case 67: // definition_labelstatement: "definition" statement_name "." $@10 definition_statement "."
#line 1043 "../../mli-root/src/database-parser.yy"
                                {
      symbol_table.pop_level();
      yylhs.value.as < val<definition> > () = val<definition>(make, yystack_[4].value.as < std::string > (), yystack_[1].value.as < ref6<unit> > ());
    }
#line 2872 "../../mli-root/src/database-parser.cc"
    break;

  case 68: // statement_name: "name"
#line 1051 "../../mli-root/src/database-parser.yy"
              { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2878 "../../mli-root/src/database-parser.cc"
    break;

  case 69: // statement_name: "label"
#line 1052 "../../mli-root/src/database-parser.yy"
               { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2884 "../../mli-root/src/database-parser.cc"
    break;

  case 70: // statement_name: "natural number value"
#line 1053 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < std::string > () = yystack_[0].value.as < std::pair<std::string, integer> > ().first; }
#line 2890 "../../mli-root/src/database-parser.cc"
    break;

  case 71: // theorem: theorem_statement proof
#line 1058 "../../mli-root/src/database-parser.yy"
                            {
      yylhs.value.as < ref6<unit> > () = statement_stack_.back();
      ref4<statement> t(yylhs.value.as < ref6<unit> > ()); // The theorem.
      t->prove(proof_count);     // Attempt to prove the theorem.
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
#line 2902 "../../mli-root/src/database-parser.cc"
    break;

  case 72: // theorem_statement: theorem_head statement
#line 1069 "../../mli-root/src/database-parser.yy"
                                 {
      symbol_table_t::table& top = symbol_table.top();
      val<theorem> tr(make,  yystack_[1].value.as < std::pair<theorem::type, std::string> > ().first, yystack_[1].value.as < std::pair<theorem::type, std::string> > ().second, yystack_[0].value.as < ref6<unit> > (), theory_, proof_depth);
      statement_stack_.back() = tr;
      theorem_theory_ = tr->get_theory();
    }
#line 2913 "../../mli-root/src/database-parser.cc"
    break;

  case 73: // theorem_head: "theorem" statement_name "."
#line 1079 "../../mli-root/src/database-parser.yy"
                                       {
      yylhs.value.as < std::pair<theorem::type, std::string> > ().second = yystack_[1].value.as < std::string > ();
      yylhs.value.as < std::pair<theorem::type, std::string> > ().first = yystack_[2].value.as < theorem::type > ();
      symbol_table.push_level();
      statement_stack_.push_back(ref4<statement>());
    }
#line 2924 "../../mli-root/src/database-parser.cc"
    break;

  case 74: // proof: compound-proof
#line 1089 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2930 "../../mli-root/src/database-parser.cc"
    break;

  case 75: // $@11: %empty
#line 1090 "../../mli-root/src/database-parser.yy"
                {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 2940 "../../mli-root/src/database-parser.cc"
    break;

  case 76: // proof: $@11 proof_of_conclusion
#line 1095 "../../mli-root/src/database-parser.yy"
                        {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 2950 "../../mli-root/src/database-parser.cc"
    break;

  case 77: // compound-proof: proof_head proof_lines "∎"
#line 1104 "../../mli-root/src/database-parser.yy"
                               {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 2960 "../../mli-root/src/database-parser.cc"
    break;

  case 78: // compound-proof: "∎"
#line 1109 "../../mli-root/src/database-parser.yy"
        {}
#line 2966 "../../mli-root/src/database-parser.cc"
    break;

  case 79: // proof_head: "proof"
#line 1114 "../../mli-root/src/database-parser.yy"
            {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 2976 "../../mli-root/src/database-parser.cc"
    break;

  case 80: // proof_lines: %empty
#line 1123 "../../mli-root/src/database-parser.yy"
           {}
#line 2982 "../../mli-root/src/database-parser.cc"
    break;

  case 81: // proof_lines: proof_lines proof_line
#line 1124 "../../mli-root/src/database-parser.yy"
                           {}
#line 2988 "../../mli-root/src/database-parser.cc"
    break;

  case 82: // statement_label: statement_name "."
#line 1129 "../../mli-root/src/database-parser.yy"
                          {
      yylhs.value.as < std::string > () = yystack_[1].value.as < std::string > ();
      symbol_table.push_level();
    }
#line 2997 "../../mli-root/src/database-parser.cc"
    break;

  case 83: // proof_line: statement_label statement "by" find_statement "."
#line 1137 "../../mli-root/src/database-parser.yy"
                                                               {
      // Handles explicit find_statement substitutions A[x⤇e].
      proofline_database_context = false;

      theorem& t = dyn_cast<theorem&>(statement_stack_.back());

      bool concluding = false;

      if (t.get_formula() == yystack_[3].value.as < ref6<unit> > () || head(t) == yystack_[3].value.as < ref6<unit> > ())
        concluding = true;

      if (!concluding && yystack_[4].value.as < std::string > () == "conclusion")
        throw syntax_error(yystack_[4].location, "Proof line name “conclusion” used when not the theorem conclusion.");

      if (!concluding && yystack_[4].value.as < std::string > () == "result")
        throw syntax_error(yystack_[4].location, "Proof line name “result” used when not the theorem result.");

      ref4<statement> proof_line =
        t.push_back(
          yystack_[4].value.as < std::string > (), val<formula>(yystack_[3].value.as < ref6<unit> > ()), val<database>(yystack_[1].value.as < ref6<unit> > ()), concluding, proof_depth);

      symbol_table.pop_level();

      if (!proofline_stack_.insert(yystack_[4].value.as < std::string > (), proof_line)) {
        if (yystack_[4].value.as < std::string > ().empty())
          throw syntax_error(yystack_[4].location, "Proof line empty name “” used.");
        else
          throw syntax_error(yystack_[4].location, "Proof line name " + yystack_[4].value.as < std::string > ()  + " already given to a proof line.");
      }
    }
#line 3032 "../../mli-root/src/database-parser.cc"
    break;

  case 84: // proof_line: subproof_statement compound-proof
#line 1168 "../../mli-root/src/database-parser.yy"
                                         {
    ref4<statement> top = statement_stack_.back();
    symbol_table.pop_level();
    statement_stack_.pop_back();

    theorem& t = dyn_cast<theorem&>(statement_stack_.back());
      ref4<statement> proof_line = t.push_back(ref4<statement>(top));
      if (!proofline_stack_.insert(yystack_[1].value.as < std::string > (), proof_line)) {
        if (yystack_[1].value.as < std::string > ().empty())
          throw syntax_error(yystack_[1].location, "Proof line empty name “” used.");
        else
          throw syntax_error(yystack_[1].location, "Proof line name " + yystack_[1].value.as < std::string > ()  + " already given to a proof line.");
      }
    }
#line 3051 "../../mli-root/src/database-parser.cc"
    break;

  case 85: // $@12: %empty
#line 1183 "../../mli-root/src/database-parser.yy"
    {}
#line 3057 "../../mli-root/src/database-parser.cc"
    break;

  case 86: // proof_line: $@12 identifier_declaration
#line 1183 "../../mli-root/src/database-parser.yy"
                              {}
#line 3063 "../../mli-root/src/database-parser.cc"
    break;

  case 87: // proof_line: definition_labelstatement
#line 1187 "../../mli-root/src/database-parser.yy"
                                 {
      theorem& t = dyn_cast<theorem&>(statement_stack_.back());
      ref4<statement> proof_line = t.push_back(ref4<statement>(yystack_[0].value.as < val<definition> > ()));

      if (!proofline_stack_.insert(proof_line->name_, proof_line)) {
        if (proof_line->name_.empty())
          throw syntax_error(yystack_[0].location, "Proof line name “” used.");
        else
          throw syntax_error(yystack_[0].location, "Proof line name " + proof_line->name_  + " already given to a proof line.");
      }
    }
#line 3079 "../../mli-root/src/database-parser.cc"
    break;

  case 88: // proof_line: proof_of_conclusion
#line 1198 "../../mli-root/src/database-parser.yy"
                        {}
#line 3085 "../../mli-root/src/database-parser.cc"
    break;

  case 89: // subproof_statement: statement_label statement
#line 1203 "../../mli-root/src/database-parser.yy"
                                    {
      yylhs.value.as < std::string > () = yystack_[1].value.as < std::string > ();
      symbol_table_t::table& top = symbol_table.top();
      val<theorem> tp(make, theorem::claim_, yystack_[1].value.as < std::string > (), yystack_[0].value.as < ref6<unit> > (), theory_, proof_depth);
      statement_stack_.push_back(tp);
    }
#line 3096 "../../mli-root/src/database-parser.cc"
    break;

  case 90: // proof_of_conclusion: optional-result "by" find_statement "."
#line 1213 "../../mli-root/src/database-parser.yy"
                                                  {
      proofline_database_context = false;

      theorem& t = dyn_cast<theorem&>(statement_stack_.back());
      ref4<statement> proof_line =
        t.push_back(yystack_[3].value.as < std::string > (), t.get_formula(), val<database>(yystack_[1].value.as < ref6<unit> > ()), true, proof_depth);
    }
#line 3108 "../../mli-root/src/database-parser.cc"
    break;

  case 91: // optional-result: %empty
#line 1224 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < std::string > () = "result"; }
#line 3114 "../../mli-root/src/database-parser.cc"
    break;

  case 92: // optional-result: "result"
#line 1225 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 3120 "../../mli-root/src/database-parser.cc"
    break;

  case 93: // find_statement: find_statement_list
#line 1230 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = ref5<level_database>(make, val<database>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3126 "../../mli-root/src/database-parser.cc"
    break;

  case 94: // find_statement: find_statement ":" find_statement_list
#line 1231 "../../mli-root/src/database-parser.yy"
                                                 {
      ref5<level_database>(yystack_[2].value.as < ref6<unit> > ())->push_back(val<database>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3135 "../../mli-root/src/database-parser.cc"
    break;

  case 95: // find_statement_list: find_statement_sequence
#line 1239 "../../mli-root/src/database-parser.yy"
                               {
      yylhs.value.as < ref6<unit> > () = ref3<sublevel_database>(make, ref2<sequence_database>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3143 "../../mli-root/src/database-parser.cc"
    break;

  case 96: // find_statement_list: find_statement_list ";" find_statement_sequence
#line 1242 "../../mli-root/src/database-parser.yy"
                                                          {
      ref3<sublevel_database>(yystack_[2].value.as < ref6<unit> > ())->push_back(val<database>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3152 "../../mli-root/src/database-parser.cc"
    break;

  case 97: // find_statement_sequence: %empty
#line 1250 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make); }
#line 3158 "../../mli-root/src/database-parser.cc"
    break;

  case 98: // find_statement_sequence: find_statement_item
#line 1251 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make, ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3165 "../../mli-root/src/database-parser.cc"
    break;

  case 99: // find_statement_sequence: find_statement_item "₍" find_definition_sequence "₎"
#line 1253 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make, ref4<statement>(yystack_[3].value.as < ref6<unit> > ()));
      ref2<sequence_database>(yylhs.value.as < ref6<unit> > ())->insert(ref2<sequence_database>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 3174 "../../mli-root/src/database-parser.cc"
    break;

  case 100: // find_statement_sequence: find_statement_sequence "," find_statement_item
#line 1257 "../../mli-root/src/database-parser.yy"
                                                          {
      ref2<sequence_database>(yystack_[2].value.as < ref6<unit> > ())->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3183 "../../mli-root/src/database-parser.cc"
    break;

  case 101: // find_statement_sequence: find_statement_sequence "," find_statement_item "₍" find_definition_sequence "₎"
#line 1261 "../../mli-root/src/database-parser.yy"
                                                                                              {
      yylhs.value.as < ref6<unit> > () = yystack_[5].value.as < ref6<unit> > ();
      ref2<sequence_database>(yylhs.value.as < ref6<unit> > ())->insert(ref4<statement>(yystack_[3].value.as < ref6<unit> > ()));
      ref2<sequence_database>(yylhs.value.as < ref6<unit> > ())->insert(ref2<sequence_database>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 3193 "../../mli-root/src/database-parser.cc"
    break;

  case 102: // find_definition_sequence: find_statement_item
#line 1270 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make, ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3200 "../../mli-root/src/database-parser.cc"
    break;

  case 103: // find_definition_sequence: find_definition_sequence "," find_statement_item
#line 1272 "../../mli-root/src/database-parser.yy"
                                                           {
      ref2<sequence_database>(yystack_[2].value.as < ref6<unit> > ())->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3209 "../../mli-root/src/database-parser.cc"
    break;

  case 104: // find_statement_item: find_statement_name
#line 1280 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();
    }
#line 3217 "../../mli-root/src/database-parser.cc"
    break;

  case 105: // find_statement_item: "premise"
#line 1283 "../../mli-root/src/database-parser.yy"
              {
      yylhs.value.as < ref6<unit> > () = val<premise>(make, statement_stack_.back());
    }
#line 3225 "../../mli-root/src/database-parser.cc"
    break;

  case 106: // find_statement_item: "premise" statement_name
#line 1286 "../../mli-root/src/database-parser.yy"
                                {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == yystack_[0].value.as < std::string > ()) {
          yylhs.value.as < ref6<unit> > () = val<premise>(make, *i);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(yystack_[0].location, "Proof line premise " + yystack_[0].value.as < std::string > ()  + " not found.");
    }
#line 3243 "../../mli-root/src/database-parser.cc"
    break;

  case 107: // find_statement_item: "premise" statement_name "subscript natural number value"
#line 1299 "../../mli-root/src/database-parser.yy"
                                                                  {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == yystack_[1].value.as < std::string > ()) {
          size_type k = (size_type)yystack_[0].value.as < integer > ();
          yylhs.value.as < ref6<unit> > () = val<premise>(make, *i, k);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(yystack_[1].location, "Proof line premise " + yystack_[1].value.as < std::string > ()  + " not found.");
    }
#line 3262 "../../mli-root/src/database-parser.cc"
    break;

  case 108: // find_statement_item: "premise" "⊢"
#line 1313 "../../mli-root/src/database-parser.yy"
                  {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      yylhs.value.as < ref6<unit> > () = val<premise>(make);
    }
#line 3272 "../../mli-root/src/database-parser.cc"
    break;

  case 109: // find_statement_item: "premise" "⊢" "subscript natural number value"
#line 1318 "../../mli-root/src/database-parser.yy"
                                                    {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      size_type k = (size_type)yystack_[0].value.as < integer > ();
      yylhs.value.as < ref6<unit> > () = val<premise>(make, k);
    }
#line 3283 "../../mli-root/src/database-parser.cc"
    break;

  case 110: // find_statement_name: statement_name
#line 1328 "../../mli-root/src/database-parser.yy"
                      {
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref4<statement>> st;
      st = proofline_stack_.find(yystack_[0].value.as < std::string > ());

      if (!st)
        st = theorem_theory_->find(yystack_[0].value.as < std::string > (), 0);

      if (!st)
        throw syntax_error(yystack_[0].location,
          "statement name " + yystack_[0].value.as < std::string > () + " not found earlier in proof, in premises or theory.");

      yylhs.value.as < ref6<unit> > () = *st;
    }
#line 3302 "../../mli-root/src/database-parser.cc"
    break;

  case 111: // @13: %empty
#line 1342 "../../mli-root/src/database-parser.yy"
                                  {
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref4<statement>> st;
      st = proofline_stack_.find(yystack_[0].value.as < std::string > ());
      if (!st)
        st = theorem_theory_->find(yystack_[0].value.as < std::string > (), 0);

      if (!st)
        throw syntax_error(yystack_[0].location,
          "statement name " + yystack_[0].value.as < std::string > () + " not found earlier in proof, in premises or theory.");

      yylhs.value.as < ref6<unit> > () = *st;
      // Find the variables of *st and record them for use in the substitution domain checks:
      ref4<statement> pr = *st;
      statement_variables_.clear();
      pr->declared(statement_variables_);
      // Then push the declared *st variables & constants onto symbol_table
      // making them usable in substitution codomains:
      symbol_table.push_level();
      for (auto& i: statement_variables_)
        symbol_table.insert(i->name, {to_token(i->type_), i});
    }
#line 3329 "../../mli-root/src/database-parser.cc"
    break;

  case 112: // find_statement_name: statement_name @13 metaformula_substitution_sequence
#line 1365 "../../mli-root/src/database-parser.yy"
                                         {
      // The try-catch checks whether the statement-substitution is legal:
      ref4<statement> p(yystack_[1].value.as < ref6<unit> > ());
      val<substitution> s(yystack_[0].value.as < ref6<unit> > ());
      try {
        yylhs.value.as < ref6<unit> > () = val<statement_substitution>(make, p, s);
      } catch (illegal_substitution&) {
        database_parser::error(yystack_[0].location, "Proposition substitute error.");
        p->write(std::cerr,
          write_style(write_name | write_type | write_statement));
        std::cerr << "\n  " << s << std::endl;
        YYERROR;        
      }
      symbol_table.pop_level();
    }
#line 3349 "../../mli-root/src/database-parser.cc"
    break;

  case 113: // statement: metaformula
#line 1384 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.as < ref6<unit> > () = dyn_cast<formula&>(yystack_[0].value.as < ref6<unit> > ()).set_bind(); }
#line 3355 "../../mli-root/src/database-parser.cc"
    break;

  case 114: // statement: identifier_declaration metaformula
#line 1385 "../../mli-root/src/database-parser.yy"
                                          {
      val<formula> f(yystack_[0].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = f->set_bind();

      if (unused_variable != false) {
        std::set<val<variable>> vs;
        f->contains(vs, occurrence::declared);

        std::set<val<variable>> vr;  // Redundant variables.

        for (auto& i: symbol_table.top()) {
          try {
            val<variable> v(i.second.second);
            if (vs.find(v) == vs.end())
              vr.insert(v);
          }
          catch (std::bad_cast&) {}
        }

        if (!vr.empty()) {
          std::string err;
          if (vr.size() > 1) err += "s";
          err += " ";
          bool it0 = true;

          for (auto& i: vr) {
            if (it0) it0 = false;
            else err += ", ";
            err += i->name;
          }

        std::string ds = "Declared variable" + err + " not used in statement.";

        if (unused_variable != true)
          database_parser::error(yystack_[0].location, "warning: " + ds);
        else
          throw syntax_error(yystack_[0].location, ds);
        }
      }
    }
#line 3400 "../../mli-root/src/database-parser.cc"
    break;

  case 115: // definition_statement: definition
#line 1429 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < ref6<unit> > () = dyn_cast<formula&>(yystack_[0].value.as < ref6<unit> > ()).set_bind(); }
#line 3406 "../../mli-root/src/database-parser.cc"
    break;

  case 116: // definition_statement: identifier_declaration definition
#line 1430 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.as < ref6<unit> > () = dyn_cast<formula&>(yystack_[0].value.as < ref6<unit> > ()).set_bind();
    }
#line 3414 "../../mli-root/src/database-parser.cc"
    break;

  case 117: // identifier_declaration: declarator_list "."
#line 1437 "../../mli-root/src/database-parser.yy"
                        {}
#line 3420 "../../mli-root/src/database-parser.cc"
    break;

  case 118: // declarator_list: declarator_identifier_list
#line 1442 "../../mli-root/src/database-parser.yy"
                               {}
#line 3426 "../../mli-root/src/database-parser.cc"
    break;

  case 119: // declarator_list: declarator_list declarator_identifier_list
#line 1443 "../../mli-root/src/database-parser.yy"
                                               {}
#line 3432 "../../mli-root/src/database-parser.cc"
    break;

  case 120: // declarator_identifier_list: "identifier constant" identifier_constant_list
#line 1448 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 3438 "../../mli-root/src/database-parser.cc"
    break;

  case 121: // declarator_identifier_list: "identifier variable" identifier_variable_list
#line 1449 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 3444 "../../mli-root/src/database-parser.cc"
    break;

  case 122: // declarator_identifier_list: "identifier function" identifier_function_list
#line 1450 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 3450 "../../mli-root/src/database-parser.cc"
    break;

  case 123: // identifier_function_list: identifier_function_name
#line 1455 "../../mli-root/src/database-parser.yy"
                             {}
#line 3456 "../../mli-root/src/database-parser.cc"
    break;

  case 124: // identifier_function_list: identifier_function_list "," identifier_function_name
#line 1456 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 3462 "../../mli-root/src/database-parser.cc"
    break;

  case 125: // $@14: %empty
#line 1467 "../../mli-root/src/database-parser.yy"
              { current_declared_token = declared_token; }
#line 3468 "../../mli-root/src/database-parser.cc"
    break;

  case 126: // $@15: %empty
#line 1468 "../../mli-root/src/database-parser.yy"
        { bound_variable_type = database_parser::token::function_map_variable; }
#line 3474 "../../mli-root/src/database-parser.cc"
    break;

  case 127: // identifier_function_name: "name" $@14 ":" $@15 "function map variable" "↦" object_formula
#line 1469 "../../mli-root/src/database-parser.yy"
                                                   {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top(yystack_[6].value.as < std::string > ());
      if (x0) {
        throw syntax_error(yystack_[6].location, "Name " + yystack_[6].value.as < std::string > () + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[6].value.as < std::string > (), {current_declared_token,
        val<function_map>(make, yystack_[2].value.as < val<unit> > (), yystack_[0].value.as < ref6<unit> > ())});
    }
#line 3490 "../../mli-root/src/database-parser.cc"
    break;

  case 128: // identifier_constant_list: identifier_constant_name
#line 1502 "../../mli-root/src/database-parser.yy"
                             {}
#line 3496 "../../mli-root/src/database-parser.cc"
    break;

  case 129: // identifier_constant_list: identifier_constant_list "," identifier_constant_name
#line 1503 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 3502 "../../mli-root/src/database-parser.cc"
    break;

  case 130: // identifier_constant_name: "name"
#line 1508 "../../mli-root/src/database-parser.yy"
              {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top(yystack_[0].value.as < std::string > ());
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.as < std::string > () + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.as < std::string > (), {declared_token,
        val<constant>(make, yystack_[0].value.as < std::string > (), constant::type(declared_type))});
    }
#line 3518 "../../mli-root/src/database-parser.cc"
    break;

  case 131: // identifier_variable_list: identifier_variable_name
#line 1523 "../../mli-root/src/database-parser.yy"
                             {}
#line 3524 "../../mli-root/src/database-parser.cc"
    break;

  case 132: // identifier_variable_list: identifier_variable_list "," identifier_variable_name
#line 1524 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 3530 "../../mli-root/src/database-parser.cc"
    break;

  case 133: // identifier_variable_name: "name"
#line 1529 "../../mli-root/src/database-parser.yy"
              {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top(yystack_[0].value.as < std::string > ());
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.as < std::string > () + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.as < std::string > (), {declared_token,
       val<variable>(make, yystack_[0].value.as < std::string > (), variable::ordinary_, variable::type(declared_type), -1)});
    }
#line 3546 "../../mli-root/src/database-parser.cc"
    break;

  case 134: // identifier_variable_name: "°" "name"
#line 1540 "../../mli-root/src/database-parser.yy"
                  {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top(yystack_[0].value.as < std::string > ());
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.as < std::string > () + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.as < std::string > (), {declared_token,
        val<variable>(make, yystack_[0].value.as < std::string > (), variable::limited_, variable::type(declared_type), -1)});
    }
#line 3562 "../../mli-root/src/database-parser.cc"
    break;

  case 135: // identifier_variable_name: "•" "name"
#line 1551 "../../mli-root/src/database-parser.yy"
                  {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top(yystack_[0].value.as < std::string > ());
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.as < std::string > () + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.as < std::string > (), {declared_token,
        val<variable>(make, yystack_[0].value.as < std::string > (), variable::term_, variable::type(declared_type), -1)});
    }
#line 3578 "../../mli-root/src/database-parser.cc"
    break;

  case 136: // definition: metaformula_definition
#line 1566 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3584 "../../mli-root/src/database-parser.cc"
    break;

  case 137: // definition: object_formula_definition
#line 1567 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3590 "../../mli-root/src/database-parser.cc"
    break;

  case 138: // definition: term_definition
#line 1568 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3596 "../../mli-root/src/database-parser.cc"
    break;

  case 139: // metaformula_definition: pure_metaformula "≔" pure_metaformula
#line 1573 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(),
        formula::logic, formula_definition_oprec);
    }
#line 3605 "../../mli-root/src/database-parser.cc"
    break;

  case 140: // metaformula_definition: pure_metaformula "≕" pure_metaformula
#line 1577 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(),
       formula::logic, formula_definition_oprec);
  }
#line 3614 "../../mli-root/src/database-parser.cc"
    break;

  case 141: // object_formula_definition: object_formula "≔" object_formula
#line 1590 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(),
        formula::logic, formula_definition_oprec);
    }
#line 3623 "../../mli-root/src/database-parser.cc"
    break;

  case 142: // object_formula_definition: object_formula "≕" object_formula
#line 1594 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(),
        formula::logic, formula_definition_oprec);
  }
#line 3632 "../../mli-root/src/database-parser.cc"
    break;

  case 143: // term_definition: term "≔" term
#line 1607 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(),
        formula::object, term_definition_oprec);
    }
#line 3641 "../../mli-root/src/database-parser.cc"
    break;

  case 144: // term_definition: term "≕" term
#line 1617 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(),
        formula::object, term_definition_oprec);
  }
#line 3650 "../../mli-root/src/database-parser.cc"
    break;

  case 145: // metaformula: pure_metaformula
#line 1625 "../../mli-root/src/database-parser.yy"
                        { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3656 "../../mli-root/src/database-parser.cc"
    break;

  case 146: // metaformula: object_formula
#line 1626 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3662 "../../mli-root/src/database-parser.cc"
    break;

  case 147: // pure_metaformula: atomic_metaformula
#line 1631 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3668 "../../mli-root/src/database-parser.cc"
    break;

  case 148: // pure_metaformula: special_metaformula
#line 1632 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3674 "../../mli-root/src/database-parser.cc"
    break;

  case 149: // pure_metaformula: "~" metaformula
#line 1633 "../../mli-root/src/database-parser.yy"
                       {
      yylhs.value.as < ref6<unit> > () = val<metanot>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3682 "../../mli-root/src/database-parser.cc"
    break;

  case 150: // pure_metaformula: metaformula ";" metaformula
#line 1636 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.as < ref6<unit> > () = concatenate(val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3690 "../../mli-root/src/database-parser.cc"
    break;

  case 151: // pure_metaformula: metaformula "," metaformula
#line 1639 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.as < ref6<unit> > () = concatenate(val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3698 "../../mli-root/src/database-parser.cc"
    break;

  case 152: // pure_metaformula: metaformula "⊩" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_matrix metaformula
#line 1644 "../../mli-root/src/database-parser.yy"
                     {
      size_type k = (size_type)yystack_[3].value.as < integer > ();

      if (k < 1)
        k = 2;
      else
        k += 2;

      val<inference> i(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[5].value.as < ref6<unit> > ()), metalevel_t(k));

      inference* mp = dyn_cast<inference*>(yystack_[2].value.as < ref6<unit> > ());
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = dyn_cast<inference*>(yystack_[1].value.as < ref6<unit> > ());
      if (mrp != nullptr)
        i->varied_in_reduction_ = mrp->varied_in_reduction_;


      // Check that varied and invariable indices given do not exceed
      // exceed the conclusion (head) and premise (body) sizes:

      formula_sequence* hp = dyn_cast<formula_sequence*>(i->head_);
      size_type n_head = (hp == nullptr)? 1 : hp->formulas_.size();

      formula_sequence* bp = dyn_cast<formula_sequence*>(i->body_);
      size_type n_body = (bp == nullptr)? 1 : bp->formulas_.size();


      if (!i->varied_.empty()) {
        // Max values of varied conclusion and premise indices.

        // As the conclusions are sorted by index, the max value is the last one:
        size_type vc_max = i->varied_.rbegin()->first;

        size_type vp_max = 0;
        for (auto& i: i->varied_) {
          size_type n = i.second.rbegin()->first;
          if (n > vp_max) vp_max = n;
        }

        if (vc_max >= n_head)
          throw syntax_error(yystack_[2].location,
            "inference varied variable conclusion index " + std::to_string(vc_max)
            + " must be less than the number of conclusions " + std::to_string(n_head) + ".");

        if (vp_max >= n_body)
          throw syntax_error(yystack_[2].location,
            "inference varied variable premise index " + std::to_string(vp_max)
            + " must be less than the number of premises " + std::to_string(n_body) + ".");
      }

      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3757 "../../mli-root/src/database-parser.cc"
    break;

  case 153: // pure_metaformula: metaformula "⊢" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_matrix metaformula
#line 1712 "../../mli-root/src/database-parser.yy"
                     {
      size_type k = (size_type)yystack_[3].value.as < integer > ();

      if (k < 1)
        k = 1;

      val<inference> i(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[5].value.as < ref6<unit> > ()), metalevel_t(k));

      inference* mp = dyn_cast<inference*>(yystack_[2].value.as < ref6<unit> > ());
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = dyn_cast<inference*>(yystack_[1].value.as < ref6<unit> > ());
      if (mrp != nullptr)
        i->varied_in_reduction_ = mrp->varied_in_reduction_;


      // Check that varied and invariable indices given do not exceed
      // exceed the conclusion (head) and premise (body) sizes:

      formula_sequence* hp = dyn_cast<formula_sequence*>(i->head_);
      size_type n_head = (hp == nullptr)? 1 : hp->formulas_.size();

      formula_sequence* bp = dyn_cast<formula_sequence*>(i->body_);
      size_type n_body = (bp == nullptr)? 1 : bp->formulas_.size();


      if (!i->varied_.empty()) {
        // Max values of varied conclusion and premise indices.

        // As the conclusions are sorted by index, the max value is the last one:
        size_type vc_max = i->varied_.rbegin()->first;

        size_type vp_max = 0;
        for (auto& i: i->varied_) {
          size_type n = i.second.rbegin()->first;
          if (n > vp_max) vp_max = n;
        }

        if (vc_max >= n_head)
          throw syntax_error(yystack_[2].location,
            "inference varied variable conclusion index " + std::to_string(vc_max)
            + " must be less than the number of conclusions " + std::to_string(n_head) + ".");

        if (vp_max >= n_body)
          throw syntax_error(yystack_[2].location,
            "inference varied variable premise index " + std::to_string(vp_max)
            + " must be less than the number of premises " + std::to_string(n_body) + ".");
      }

      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3814 "../../mli-root/src/database-parser.cc"
    break;

  case 154: // pure_metaformula: "⊢" metaformula
#line 1771 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = val<inference>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3820 "../../mli-root/src/database-parser.cc"
    break;

  case 155: // pure_metaformula: "(" pure_metaformula ")"
#line 1773 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3826 "../../mli-root/src/database-parser.cc"
    break;

  case 156: // pure_metaformula: simple_metaformula metaformula_substitution_sequence
#line 1774 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.as < ref6<unit> > () = val<substitution_formula>(make, val<substitution>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[1].value.as < ref6<unit> > ())); }
#line 3833 "../../mli-root/src/database-parser.cc"
    break;

  case 157: // optional_varied_variable_matrix: %empty
#line 1780 "../../mli-root/src/database-parser.yy"
           {}
#line 3839 "../../mli-root/src/database-parser.cc"
    break;

  case 158: // optional_varied_variable_matrix: "⁽" varied_variable_conclusions "⁾"
#line 1781 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3845 "../../mli-root/src/database-parser.cc"
    break;

  case 159: // optional_varied_variable_matrix: "⁽" varied_variable_premises "⁾"
#line 1782 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3851 "../../mli-root/src/database-parser.cc"
    break;

  case 160: // optional_varied_variable_matrix: "⁽" varied_variable_set "⁾"
#line 1783 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3857 "../../mli-root/src/database-parser.cc"
    break;

  case 161: // varied_variable_conclusions: varied_variable_conclusion
#line 1787 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3863 "../../mli-root/src/database-parser.cc"
    break;

  case 162: // varied_variable_conclusions: varied_variable_conclusions ";" varied_variable_conclusion
#line 1788 "../../mli-root/src/database-parser.yy"
                                                                      {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& i: x.varied_)
        for (auto& j: i.second)
          xs.varied_[i.first][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3878 "../../mli-root/src/database-parser.cc"
    break;

  case 163: // varied_variable_conclusion: "superscript natural number value" varied_variable_premises
#line 1801 "../../mli-root/src/database-parser.yy"
                                                                     {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_[k].insert(xs.varied_[0].begin(), xs.varied_[0].end());
      yylhs.value.as < ref6<unit> > () = i;

    }
#line 3892 "../../mli-root/src/database-parser.cc"
    break;

  case 164: // varied_variable_premises: varied_variable_premise
#line 1813 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3898 "../../mli-root/src/database-parser.cc"
    break;

  case 165: // varied_variable_premises: varied_variable_premises "," varied_variable_premise
#line 1814 "../../mli-root/src/database-parser.yy"
                                                                {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& j: x.varied_[0])
        xs.varied_[0][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3912 "../../mli-root/src/database-parser.cc"
    break;

  case 166: // varied_variable_premise: "superscript natural number value" varied_variable_set
#line 1826 "../../mli-root/src/database-parser.yy"
                                                                {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_[0][k].insert(xs.varied_[0][0].begin(), xs.varied_[0][0].end());

      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3926 "../../mli-root/src/database-parser.cc"
    break;

  case 167: // varied_variable_set: varied_variable
#line 1838 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3932 "../../mli-root/src/database-parser.cc"
    break;

  case 168: // varied_variable_set: varied_variable_set varied_variable
#line 1839 "../../mli-root/src/database-parser.yy"
                                               {
      inference& xs = dyn_cast<inference&>(yystack_[1].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      xs.varied_[0][0].insert(x.varied_[0][0].begin(), x.varied_[0][0].end());

      yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > ();
    }
#line 3945 "../../mli-root/src/database-parser.cc"
    break;

  case 169: // varied_variable: "object variable"
#line 1850 "../../mli-root/src/database-parser.yy"
                       {
      val<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3955 "../../mli-root/src/database-parser.cc"
    break;

  case 170: // varied_variable: "metaformula variable"
#line 1855 "../../mli-root/src/database-parser.yy"
                            {
      val<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3965 "../../mli-root/src/database-parser.cc"
    break;

  case 171: // optional_varied_in_reduction_variable_matrix: %empty
#line 1865 "../../mli-root/src/database-parser.yy"
           {}
#line 3971 "../../mli-root/src/database-parser.cc"
    break;

  case 172: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_conclusions "₎"
#line 1866 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3977 "../../mli-root/src/database-parser.cc"
    break;

  case 173: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_premises "₎"
#line 1867 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3983 "../../mli-root/src/database-parser.cc"
    break;

  case 174: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_set "₎"
#line 1868 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3989 "../../mli-root/src/database-parser.cc"
    break;

  case 175: // varied_in_reduction_variable_conclusions: varied_in_reduction_variable_conclusion
#line 1872 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3995 "../../mli-root/src/database-parser.cc"
    break;

  case 176: // varied_in_reduction_variable_conclusions: varied_in_reduction_variable_conclusions ";" varied_in_reduction_variable_conclusion
#line 1873 "../../mli-root/src/database-parser.yy"
                                                                                                {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& i: x.varied_in_reduction_)
        for (auto& j: i.second)
          xs.varied_in_reduction_[i.first][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 4010 "../../mli-root/src/database-parser.cc"
    break;

  case 177: // varied_in_reduction_variable_conclusion: "subscript natural number value" varied_in_reduction_variable_premises
#line 1886 "../../mli-root/src/database-parser.yy"
                                                                                {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_in_reduction_[k].insert(xs.varied_in_reduction_[0].begin(), xs.varied_in_reduction_[0].end());
      yylhs.value.as < ref6<unit> > () = i;

    }
#line 4024 "../../mli-root/src/database-parser.cc"
    break;

  case 178: // varied_in_reduction_variable_premises: varied_in_reduction_variable_premise
#line 1898 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4030 "../../mli-root/src/database-parser.cc"
    break;

  case 179: // varied_in_reduction_variable_premises: varied_in_reduction_variable_premises "," varied_in_reduction_variable_premise
#line 1899 "../../mli-root/src/database-parser.yy"
                                                                                          {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& j: x.varied_in_reduction_[0])
        xs.varied_in_reduction_[0][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 4044 "../../mli-root/src/database-parser.cc"
    break;

  case 180: // varied_in_reduction_variable_premise: "subscript natural number value" varied_in_reduction_variable_set
#line 1911 "../../mli-root/src/database-parser.yy"
                                                                           {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_in_reduction_[0][k].insert(xs.varied_in_reduction_[0][0].begin(), xs.varied_in_reduction_[0][0].end());

      yylhs.value.as < ref6<unit> > () = i;
    }
#line 4058 "../../mli-root/src/database-parser.cc"
    break;

  case 181: // varied_in_reduction_variable_set: varied_in_reduction_variable
#line 1923 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4064 "../../mli-root/src/database-parser.cc"
    break;

  case 182: // varied_in_reduction_variable_set: varied_in_reduction_variable_set varied_in_reduction_variable
#line 1924 "../../mli-root/src/database-parser.yy"
                                                                         {
      inference& xs = dyn_cast<inference&>(yystack_[1].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      xs.varied_in_reduction_[0][0].insert(x.varied_in_reduction_[0][0].begin(), x.varied_in_reduction_[0][0].end());

      yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > ();
    }
#line 4077 "../../mli-root/src/database-parser.cc"
    break;

  case 183: // varied_in_reduction_variable: "object variable"
#line 1935 "../../mli-root/src/database-parser.yy"
                       {
      val<inference> i(make);
      i->varied_in_reduction_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 4087 "../../mli-root/src/database-parser.cc"
    break;

  case 184: // varied_in_reduction_variable: "metaformula variable"
#line 1940 "../../mli-root/src/database-parser.yy"
                            {
      val<inference> i(make);
      i->varied_in_reduction_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 4097 "../../mli-root/src/database-parser.cc"
    break;

  case 185: // simple_metaformula: "metaformula variable"
#line 2008 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4103 "../../mli-root/src/database-parser.cc"
    break;

  case 186: // simple_metaformula: "(" pure_metaformula ")"
#line 2009 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4109 "../../mli-root/src/database-parser.cc"
    break;

  case 187: // atomic_metaformula: "metaformula variable"
#line 2014 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4115 "../../mli-root/src/database-parser.cc"
    break;

  case 188: // atomic_metaformula: metapredicate
#line 2015 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4121 "../../mli-root/src/database-parser.cc"
    break;

  case 189: // special_metaformula: meta_object_free "≢" meta_object_free
#line 2027 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<objectidentical>(make, val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<variable>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4129 "../../mli-root/src/database-parser.cc"
    break;

  case 190: // special_metaformula: meta_object_free "free in" object_formula
#line 2030 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4137 "../../mli-root/src/database-parser.cc"
    break;

  case 191: // special_metaformula: meta_object_free "free in" term
#line 2033 "../../mli-root/src/database-parser.yy"
                                          {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4145 "../../mli-root/src/database-parser.cc"
    break;

  case 192: // special_metaformula: meta_object_free "not" "free in" object_formula
#line 2036 "../../mli-root/src/database-parser.yy"
                                                          {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[3].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4153 "../../mli-root/src/database-parser.cc"
    break;

  case 193: // special_metaformula: meta_object_free "not" "free in" term
#line 2039 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[3].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4161 "../../mli-root/src/database-parser.cc"
    break;

  case 194: // special_metaformula: term "free for" meta_object_free "in" object_formula
#line 2042 "../../mli-root/src/database-parser.yy"
                                                                  {
      yylhs.value.as < ref6<unit> > () = val<free_for_object>(make, 
        val<formula>(yystack_[4].value.as < ref6<unit> > ()), val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4170 "../../mli-root/src/database-parser.cc"
    break;

  case 195: // special_metaformula: term "free for" meta_object_free "in" term
#line 2046 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.as < ref6<unit> > () = val<free_for_object>(make, 
        val<formula>(yystack_[4].value.as < ref6<unit> > ()), val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4179 "../../mli-root/src/database-parser.cc"
    break;

  case 196: // meta_object_free: "object variable"
#line 2054 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4185 "../../mli-root/src/database-parser.cc"
    break;

  case 197: // metapredicate: metapredicate_function
#line 2059 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4191 "../../mli-root/src/database-parser.cc"
    break;

  case 198: // metapredicate: object_formula "≣" object_formula
#line 2060 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4199 "../../mli-root/src/database-parser.cc"
    break;

  case 199: // metapredicate: object_formula "≣̷" object_formula
#line 2063 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4207 "../../mli-root/src/database-parser.cc"
    break;

  case 200: // metapredicate: term "≣" term
#line 2066 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4215 "../../mli-root/src/database-parser.cc"
    break;

  case 201: // metapredicate: term "≣̷" term
#line 2069 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4223 "../../mli-root/src/database-parser.cc"
    break;

  case 202: // metapredicate_function: "metapredicate constant" metapredicate_argument
#line 2076 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < val<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 4232 "../../mli-root/src/database-parser.cc"
    break;

  case 203: // metapredicate_function: "metaformula variable" metapredicate_argument
#line 2080 "../../mli-root/src/database-parser.yy"
                                                      {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < val<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 4241 "../../mli-root/src/database-parser.cc"
    break;

  case 204: // metapredicate_argument: "(" metapredicate_argument_body ")"
#line 2088 "../../mli-root/src/database-parser.yy"
                                           { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4247 "../../mli-root/src/database-parser.cc"
    break;

  case 205: // metapredicate_argument_body: object_formula
#line 2093 "../../mli-root/src/database-parser.yy"
                      {
      ref0<sequence> vr(make, sequence::tuple);
      yylhs.value.as < ref6<unit> > () = vr;
      vr->push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 4256 "../../mli-root/src/database-parser.cc"
    break;

  case 206: // metapredicate_argument_body: metapredicate_argument_body "," object_formula
#line 2097 "../../mli-root/src/database-parser.yy"
                                                         {
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
      sequence& vr = dyn_cast<sequence&>(yylhs.value.as < ref6<unit> > ());
      vr.push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 4265 "../../mli-root/src/database-parser.cc"
    break;

  case 207: // object_formula: atomic_formula
#line 2105 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4271 "../../mli-root/src/database-parser.cc"
    break;

  case 208: // object_formula: very_simple_formula formula_substitution_sequence
#line 2106 "../../mli-root/src/database-parser.yy"
                                                            {
      yylhs.value.as < ref6<unit> > () = val<substitution_formula>(make, val<substitution>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 4279 "../../mli-root/src/database-parser.cc"
    break;

  case 209: // object_formula: predicate_function_application
#line 2109 "../../mli-root/src/database-parser.yy"
                                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4285 "../../mli-root/src/database-parser.cc"
    break;

  case 210: // object_formula: logic_formula
#line 2110 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4291 "../../mli-root/src/database-parser.cc"
    break;

  case 211: // object_formula: "(" object_formula ")"
#line 2111 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4297 "../../mli-root/src/database-parser.cc"
    break;

  case 212: // object_formula: quantized_formula
#line 2112 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4303 "../../mli-root/src/database-parser.cc"
    break;

  case 213: // object_formula: hoare_triple
#line 2113 "../../mli-root/src/database-parser.yy"
                 {}
#line 4309 "../../mli-root/src/database-parser.cc"
    break;

  case 214: // hoare_triple: "{" object_formula "}" code_sequence "{" object_formula "}"
#line 2118 "../../mli-root/src/database-parser.yy"
                                                              { yylhs.value.as < ref6<unit> > () = val<formula>(); }
#line 4315 "../../mli-root/src/database-parser.cc"
    break;

  case 215: // code_statement: code_term
#line 2129 "../../mli-root/src/database-parser.yy"
              {}
#line 4321 "../../mli-root/src/database-parser.cc"
    break;

  case 216: // code_statement: "{" code_sequence "}"
#line 2130 "../../mli-root/src/database-parser.yy"
                          {}
#line 4327 "../../mli-root/src/database-parser.cc"
    break;

  case 217: // code_sequence: %empty
#line 2135 "../../mli-root/src/database-parser.yy"
           {}
#line 4333 "../../mli-root/src/database-parser.cc"
    break;

  case 218: // code_sequence: code_term
#line 2136 "../../mli-root/src/database-parser.yy"
              {}
#line 4339 "../../mli-root/src/database-parser.cc"
    break;

  case 219: // code_sequence: code_sequence ";" code_term
#line 2137 "../../mli-root/src/database-parser.yy"
                                {}
#line 4345 "../../mli-root/src/database-parser.cc"
    break;

  case 220: // code_term: "code variable"
#line 2142 "../../mli-root/src/database-parser.yy"
                 {}
#line 4351 "../../mli-root/src/database-parser.cc"
    break;

  case 221: // code_term: "∅"
#line 2143 "../../mli-root/src/database-parser.yy"
       {}
#line 4357 "../../mli-root/src/database-parser.cc"
    break;

  case 222: // code_term: "object variable" "≔" term
#line 2144 "../../mli-root/src/database-parser.yy"
                            {}
#line 4363 "../../mli-root/src/database-parser.cc"
    break;

  case 223: // code_term: "if" object_formula "then" code_statement "else" code_statement
#line 2145 "../../mli-root/src/database-parser.yy"
                                                                   {}
#line 4369 "../../mli-root/src/database-parser.cc"
    break;

  case 224: // code_term: "while" object_formula "do" code_statement
#line 2146 "../../mli-root/src/database-parser.yy"
                                              {}
#line 4375 "../../mli-root/src/database-parser.cc"
    break;

  case 225: // very_simple_formula: "object formula variable"
#line 2151 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4381 "../../mli-root/src/database-parser.cc"
    break;

  case 226: // very_simple_formula: "atom variable"
#line 2152 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4387 "../../mli-root/src/database-parser.cc"
    break;

  case 227: // very_simple_formula: "(" object_formula ")"
#line 2153 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4393 "../../mli-root/src/database-parser.cc"
    break;

  case 228: // quantized_formula: quantizer_declaration quantized_body
#line 2158 "../../mli-root/src/database-parser.yy"
                                               {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>(yystack_[1].value.as < ref6<unit> > ());
      val<bound_formula> bf(make, vsr, val<formula>(yystack_[0].value.as < ref6<unit> > ()));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      yylhs.value.as < ref6<unit> > () = bf;
    }
#line 4405 "../../mli-root/src/database-parser.cc"
    break;

  case 229: // quantized_formula: quantizer_declaration optional_in_term ":" object_formula
#line 2165 "../../mli-root/src/database-parser.yy"
                                                                       {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>(yystack_[3].value.as < ref6<unit> > ());
      val<bound_formula> bf(make, vsr, yystack_[2].value.as < ref6<unit> > (), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      yylhs.value.as < ref6<unit> > () = bf;
    }
#line 4417 "../../mli-root/src/database-parser.cc"
    break;

  case 230: // quantized_formula: quantizer_declaration optional_in_term quantized_formula
#line 2172 "../../mli-root/src/database-parser.yy"
                                                                      {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>(yystack_[2].value.as < ref6<unit> > ());
      val<bound_formula> bf(make, vsr, yystack_[1].value.as < ref6<unit> > (), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      yylhs.value.as < ref6<unit> > () = bf;
    }
#line 4429 "../../mli-root/src/database-parser.cc"
    break;

  case 231: // simple_formula: "object formula variable"
#line 2183 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4435 "../../mli-root/src/database-parser.cc"
    break;

  case 232: // simple_formula: "atom variable"
#line 2184 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4441 "../../mli-root/src/database-parser.cc"
    break;

  case 233: // simple_formula: predicate_expression
#line 2185 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4447 "../../mli-root/src/database-parser.cc"
    break;

  case 234: // simple_formula: "(" object_formula ")"
#line 2186 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4453 "../../mli-root/src/database-parser.cc"
    break;

  case 235: // simple_formula: quantized_formula
#line 2187 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4459 "../../mli-root/src/database-parser.cc"
    break;

  case 236: // quantized_body: atomic_formula
#line 2193 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4465 "../../mli-root/src/database-parser.cc"
    break;

  case 237: // quantized_body: "(" object_formula ")"
#line 2194 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4471 "../../mli-root/src/database-parser.cc"
    break;

  case 238: // atomic_formula: "atom constant"
#line 2198 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4477 "../../mli-root/src/database-parser.cc"
    break;

  case 239: // atomic_formula: "object formula variable"
#line 2199 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4483 "../../mli-root/src/database-parser.cc"
    break;

  case 240: // atomic_formula: "atom variable"
#line 2200 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4489 "../../mli-root/src/database-parser.cc"
    break;

  case 241: // atomic_formula: predicate
#line 2201 "../../mli-root/src/database-parser.yy"
                 { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4495 "../../mli-root/src/database-parser.cc"
    break;

  case 242: // predicate: predicate_expression
#line 2207 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4501 "../../mli-root/src/database-parser.cc"
    break;

  case 243: // predicate: term "=" term
#line 2208 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4507 "../../mli-root/src/database-parser.cc"
    break;

  case 244: // predicate: term "≠" term
#line 2209 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4513 "../../mli-root/src/database-parser.cc"
    break;

  case 245: // predicate: term "∣" term
#line 2212 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4519 "../../mli-root/src/database-parser.cc"
    break;

  case 246: // predicate: term "∤" term
#line 2213 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4525 "../../mli-root/src/database-parser.cc"
    break;

  case 247: // predicate: term "<" term
#line 2216 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, less_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4531 "../../mli-root/src/database-parser.cc"
    break;

  case 248: // predicate: term ">" term
#line 2217 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, greater_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4537 "../../mli-root/src/database-parser.cc"
    break;

  case 249: // predicate: term "≤" term
#line 2218 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, less_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4543 "../../mli-root/src/database-parser.cc"
    break;

  case 250: // predicate: term "≥" term
#line 2219 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, greater_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4549 "../../mli-root/src/database-parser.cc"
    break;

  case 251: // predicate: term "≮" term
#line 2220 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_less_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4555 "../../mli-root/src/database-parser.cc"
    break;

  case 252: // predicate: term "≯" term
#line 2221 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_greater_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4561 "../../mli-root/src/database-parser.cc"
    break;

  case 253: // predicate: term "≰" term
#line 2222 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_less_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4567 "../../mli-root/src/database-parser.cc"
    break;

  case 254: // predicate: term "≱" term
#line 2223 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_greater_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4573 "../../mli-root/src/database-parser.cc"
    break;

  case 255: // predicate: term "∈" term
#line 2225 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, in_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4579 "../../mli-root/src/database-parser.cc"
    break;

  case 256: // predicate: term "∉" term
#line 2226 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_in_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4585 "../../mli-root/src/database-parser.cc"
    break;

  case 257: // predicate: term "⊆" term
#line 2227 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, subset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4591 "../../mli-root/src/database-parser.cc"
    break;

  case 258: // predicate: term "⊊" term
#line 2228 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, proper_subset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4597 "../../mli-root/src/database-parser.cc"
    break;

  case 259: // predicate: term "⊇" term
#line 2229 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, superset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4603 "../../mli-root/src/database-parser.cc"
    break;

  case 260: // predicate: term "⊋" term
#line 2230 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, proper_superset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4609 "../../mli-root/src/database-parser.cc"
    break;

  case 261: // $@16: %empty
#line 2231 "../../mli-root/src/database-parser.yy"
          { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 4615 "../../mli-root/src/database-parser.cc"
    break;

  case 262: // $@17: %empty
#line 2232 "../../mli-root/src/database-parser.yy"
                               { bound_variable_type = free_variable_context; }
#line 4621 "../../mli-root/src/database-parser.cc"
    break;

  case 263: // predicate: "Set" $@16 "₍" "Set variable" "₎" $@17 simple_formula
#line 2233 "../../mli-root/src/database-parser.yy"
                       {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<bound_formula>(make,
        val<variable>(yystack_[3].value.as < val<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), bound_formula::is_set_);
    }
#line 4631 "../../mli-root/src/database-parser.cc"
    break;

  case 264: // predicate_expression: predicate_identifier tuple
#line 2242 "../../mli-root/src/database-parser.yy"
                                     {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::predicate, 0_ml, structure::postargument, precedence_t());
    }
#line 4640 "../../mli-root/src/database-parser.cc"
    break;

  case 265: // predicate_identifier: "predicate constant"
#line 2250 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > ();  }
#line 4646 "../../mli-root/src/database-parser.cc"
    break;

  case 266: // predicate_identifier: "predicate variable"
#line 2251 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > ();  }
#line 4652 "../../mli-root/src/database-parser.cc"
    break;

  case 267: // optional_superscript_natural_number_value: %empty
#line 2256 "../../mli-root/src/database-parser.yy"
           {}
#line 4658 "../../mli-root/src/database-parser.cc"
    break;

  case 268: // optional_superscript_natural_number_value: "superscript natural number value"
#line 2257 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < integer > () = yystack_[0].value.as < integer > (); }
#line 4664 "../../mli-root/src/database-parser.cc"
    break;

  case 269: // logic_formula: "¬" optional_superscript_natural_number_value object_formula
#line 2269 "../../mli-root/src/database-parser.yy"
                                                                          {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::prefix, logical_not_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 4675 "../../mli-root/src/database-parser.cc"
    break;

  case 270: // logic_formula: object_formula "∨" optional_superscript_natural_number_value object_formula
#line 2275 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, logical_or_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4686 "../../mli-root/src/database-parser.cc"
    break;

  case 271: // logic_formula: object_formula "∧" optional_superscript_natural_number_value object_formula
#line 2281 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, logical_and_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4697 "../../mli-root/src/database-parser.cc"
    break;

  case 272: // logic_formula: object_formula "⇒" optional_superscript_natural_number_value object_formula
#line 2287 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, implies_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4708 "../../mli-root/src/database-parser.cc"
    break;

  case 273: // logic_formula: object_formula "⇐" optional_superscript_natural_number_value object_formula
#line 2293 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, impliedby_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4719 "../../mli-root/src/database-parser.cc"
    break;

  case 274: // logic_formula: object_formula "⇔" optional_superscript_natural_number_value object_formula
#line 2299 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, equivalent_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4730 "../../mli-root/src/database-parser.cc"
    break;

  case 275: // logic_formula: prefix_logic_formula
#line 2305 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();  }
#line 4736 "../../mli-root/src/database-parser.cc"
    break;

  case 276: // prefix_logic_formula: "prefix formula variable"
#line 2310 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4742 "../../mli-root/src/database-parser.cc"
    break;

  case 277: // prefix_logic_formula: prefix_not_key prefix_logic_formula
#line 2311 "../../mli-root/src/database-parser.yy"
                                              {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "¬", structure::logic, 0_ml,
        structure::prefix, logical_not_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 4751 "../../mli-root/src/database-parser.cc"
    break;

  case 278: // prefix_logic_formula: prefix_or_key prefix_logic_formula prefix_logic_formula
#line 2315 "../../mli-root/src/database-parser.yy"
                                                                     {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "∨", structure::logic, 0_ml,
        structure::infix, logical_or_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4760 "../../mli-root/src/database-parser.cc"
    break;

  case 279: // prefix_logic_formula: prefix_and_key prefix_logic_formula prefix_logic_formula
#line 2319 "../../mli-root/src/database-parser.yy"
                                                                      {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "∧", structure::logic, 0_ml,
        structure::infix, logical_and_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4769 "../../mli-root/src/database-parser.cc"
    break;

  case 280: // prefix_logic_formula: prefix_implies_key prefix_logic_formula prefix_logic_formula
#line 2323 "../../mli-root/src/database-parser.yy"
                                                                          {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "⇒", structure::logic, 0_ml,
        structure::infix, implies_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4778 "../../mli-root/src/database-parser.cc"
    break;

  case 281: // prefix_logic_formula: prefix_equivalent_key prefix_logic_formula prefix_logic_formula
#line 2327 "../../mli-root/src/database-parser.yy"
                                                                             {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "⇔", structure::logic, 0_ml,
        structure::infix, equivalent_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
 }
#line 4787 "../../mli-root/src/database-parser.cc"
    break;

  case 282: // quantizer_declaration: quantized_variable_list
#line 2335 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4793 "../../mli-root/src/database-parser.cc"
    break;

  case 283: // quantized_variable_list: all_variable_list
#line 2339 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4799 "../../mli-root/src/database-parser.cc"
    break;

  case 284: // quantized_variable_list: exist_variable_list
#line 2340 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4805 "../../mli-root/src/database-parser.cc"
    break;

  case 285: // all_variable_list: "∀" exclusion_set all_identifier_list
#line 2345 "../../mli-root/src/database-parser.yy"
                                                 {
      auto bfp = dyn_cast<bound_formula*>(yystack_[1].value.as < ref6<unit> > ());
      if (bfp != nullptr) {
        variable_list& vsr = dyn_cast<variable_list&>(yystack_[0].value.as < ref6<unit> > ());
        vsr.excluded1_.insert(bfp->excluded1_.begin(), bfp->excluded1_.end());
      }
      yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();
    }
#line 4818 "../../mli-root/src/database-parser.cc"
    break;

  case 286: // exist_variable_list: "∃" exclusion_set exist_identifier_list
#line 2357 "../../mli-root/src/database-parser.yy"
                                                   {
      auto bfp = dyn_cast<bound_formula*>(yystack_[1].value.as < ref6<unit> > ());
      if (bfp != nullptr) {
        variable_list& vsr = dyn_cast<variable_list&>(yystack_[0].value.as < ref6<unit> > ());
        vsr.excluded1_.insert(bfp->excluded1_.begin(), bfp->excluded1_.end());
      }
      yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();
    }
#line 4831 "../../mli-root/src/database-parser.cc"
    break;

  case 287: // exclusion_set: %empty
#line 2369 "../../mli-root/src/database-parser.yy"
           {}
#line 4837 "../../mli-root/src/database-parser.cc"
    break;

  case 288: // $@18: %empty
#line 2370 "../../mli-root/src/database-parser.yy"
        { bound_variable_type = free_variable_context; }
#line 4843 "../../mli-root/src/database-parser.cc"
    break;

  case 289: // exclusion_set: "ₓ" $@18 "₍" exclusion_list "₎"
#line 2371 "../../mli-root/src/database-parser.yy"
                               {
      bound_variable_type = database_parser::token::exist_variable;
      yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > ();
    }
#line 4852 "../../mli-root/src/database-parser.cc"
    break;

  case 290: // exclusion_list: "object variable"
#line 2378 "../../mli-root/src/database-parser.yy"
                       { val<bound_formula> vr(make); vr->excluded1_.insert(yystack_[0].value.as < val<unit> > ()); yylhs.value.as < ref6<unit> > () = vr; }
#line 4858 "../../mli-root/src/database-parser.cc"
    break;

  case 291: // exclusion_list: exclusion_list "object variable"
#line 2379 "../../mli-root/src/database-parser.yy"
                                           {
      val<bound_formula> vr = yystack_[1].value.as < ref6<unit> > ();
      vr->excluded1_.insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = vr;
    }
#line 4868 "../../mli-root/src/database-parser.cc"
    break;

  case 292: // all_identifier_list: "all variable"
#line 2389 "../../mli-root/src/database-parser.yy"
                    {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = val<variable_list>(make, val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::all_);
    }
#line 4877 "../../mli-root/src/database-parser.cc"
    break;

  case 293: // $@19: %empty
#line 2393 "../../mli-root/src/database-parser.yy"
                           { bound_variable_type = token::all_variable; }
#line 4883 "../../mli-root/src/database-parser.cc"
    break;

  case 294: // all_identifier_list: all_identifier_list $@19 "," "all variable"
#line 2394 "../../mli-root/src/database-parser.yy"
                          {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = yystack_[3].value.as < ref6<unit> > ();
      dyn_cast<variable_list&>(yylhs.value.as < ref6<unit> > ()).push_back(val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::all_);
    }
#line 4893 "../../mli-root/src/database-parser.cc"
    break;

  case 295: // exist_identifier_list: "exist variable"
#line 2403 "../../mli-root/src/database-parser.yy"
                      {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = val<variable_list>(make, val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::exist_);
    }
#line 4902 "../../mli-root/src/database-parser.cc"
    break;

  case 296: // $@20: %empty
#line 2407 "../../mli-root/src/database-parser.yy"
                             { bound_variable_type = database_parser::token::exist_variable; }
#line 4908 "../../mli-root/src/database-parser.cc"
    break;

  case 297: // exist_identifier_list: exist_identifier_list $@20 "," "exist variable"
#line 2408 "../../mli-root/src/database-parser.yy"
                            {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = yystack_[3].value.as < ref6<unit> > ();
      dyn_cast<variable_list&>(yylhs.value.as < ref6<unit> > ()).push_back(val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::exist_);
    }
#line 4918 "../../mli-root/src/database-parser.cc"
    break;

  case 298: // optional_in_term: %empty
#line 2418 "../../mli-root/src/database-parser.yy"
           { yylhs.value.as < ref6<unit> > () = val<formula>(make); }
#line 4924 "../../mli-root/src/database-parser.cc"
    break;

  case 299: // optional_in_term: "∈" term
#line 2419 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4930 "../../mli-root/src/database-parser.cc"
    break;

  case 300: // tuple: "(" tuple_body ")"
#line 2426 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4936 "../../mli-root/src/database-parser.cc"
    break;

  case 301: // tuple_body: term
#line 2431 "../../mli-root/src/database-parser.yy"
            {
      ref0<sequence> vr(make, sequence::tuple);
      yylhs.value.as < ref6<unit> > () = vr;
      vr->push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 4946 "../../mli-root/src/database-parser.cc"
    break;

  case 302: // tuple_body: tuple_body "," term
#line 2436 "../../mli-root/src/database-parser.yy"
                              {
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
      sequence& vr = dyn_cast<sequence&>(yylhs.value.as < ref6<unit> > ());
      vr.push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 4956 "../../mli-root/src/database-parser.cc"
    break;

  case 303: // term: simple_term
#line 2445 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4962 "../../mli-root/src/database-parser.cc"
    break;

  case 304: // term: function_term
#line 2446 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4968 "../../mli-root/src/database-parser.cc"
    break;

  case 305: // term: simple_term term_substitution_sequence
#line 2447 "../../mli-root/src/database-parser.yy"
                                                 {
      yylhs.value.as < ref6<unit> > () = val<substitution_formula>(make, val<substitution>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 4976 "../../mli-root/src/database-parser.cc"
    break;

  case 306: // term: set_term
#line 2450 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4982 "../../mli-root/src/database-parser.cc"
    break;

  case 307: // simple_term: "term constant"
#line 2455 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4988 "../../mli-root/src/database-parser.cc"
    break;

  case 308: // simple_term: "natural number value"
#line 2456 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = val<integer>(make, yystack_[0].value.as < std::pair<std::string, integer> > ().second); }
#line 4994 "../../mli-root/src/database-parser.cc"
    break;

  case 309: // simple_term: "integer value"
#line 2457 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = val<integer>(make, yystack_[0].value.as < integer > ()); }
#line 5000 "../../mli-root/src/database-parser.cc"
    break;

  case 310: // simple_term: term_identifier
#line 2458 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 5006 "../../mli-root/src/database-parser.cc"
    break;

  case 311: // simple_term: "(" term ")"
#line 2459 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 5012 "../../mli-root/src/database-parser.cc"
    break;

  case 312: // term_identifier: "object variable" variable_exclusion_set
#line 2464 "../../mli-root/src/database-parser.yy"
                                                    {
      val<variable> xr = yystack_[1].value.as < val<unit> > ();
      val<variable> vr = yystack_[0].value.as < ref6<unit> > ();
      xr->excluded_.insert(vr->excluded_.begin(), vr->excluded_.end());
      yylhs.value.as < ref6<unit> > () = xr;
    }
#line 5023 "../../mli-root/src/database-parser.cc"
    break;

  case 313: // term_identifier: "function variable"
#line 2470 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5029 "../../mli-root/src/database-parser.cc"
    break;

  case 314: // term_identifier: "function map variable"
#line 2471 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5035 "../../mli-root/src/database-parser.cc"
    break;

  case 315: // term_identifier: "all variable"
#line 2472 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5041 "../../mli-root/src/database-parser.cc"
    break;

  case 316: // term_identifier: "exist variable"
#line 2473 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5047 "../../mli-root/src/database-parser.cc"
    break;

  case 317: // term_identifier: "Set variable"
#line 2474 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5053 "../../mli-root/src/database-parser.cc"
    break;

  case 318: // term_identifier: "set variable"
#line 2475 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5059 "../../mli-root/src/database-parser.cc"
    break;

  case 319: // term_identifier: "implicit set variable"
#line 2476 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5065 "../../mli-root/src/database-parser.cc"
    break;

  case 320: // variable_exclusion_set: %empty
#line 2481 "../../mli-root/src/database-parser.yy"
           { yylhs.value.as < ref6<unit> > () = val<variable>(make);  }
#line 5071 "../../mli-root/src/database-parser.cc"
    break;

  case 321: // variable_exclusion_set: "ₓ" "₍" variable_exclusion_list "₎"
#line 2482 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 5077 "../../mli-root/src/database-parser.cc"
    break;

  case 322: // variable_exclusion_list: bound_variable
#line 2487 "../../mli-root/src/database-parser.yy"
                      { val<variable> vr(make); vr->excluded_.insert(yystack_[0].value.as < ref6<unit> > ()); yylhs.value.as < ref6<unit> > () = vr; }
#line 5083 "../../mli-root/src/database-parser.cc"
    break;

  case 323: // variable_exclusion_list: variable_exclusion_list bound_variable
#line 2488 "../../mli-root/src/database-parser.yy"
                                                   {
      val<variable> vr = yystack_[1].value.as < ref6<unit> > ();
      vr->excluded_.insert(yystack_[0].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = vr;
    }
#line 5093 "../../mli-root/src/database-parser.cc"
    break;

  case 324: // bound_variable: "all variable"
#line 2497 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5099 "../../mli-root/src/database-parser.cc"
    break;

  case 325: // bound_variable: "exist variable"
#line 2498 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5105 "../../mli-root/src/database-parser.cc"
    break;

  case 326: // bound_variable: "Set variable"
#line 2499 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5111 "../../mli-root/src/database-parser.cc"
    break;

  case 327: // bound_variable: "set variable"
#line 2500 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5117 "../../mli-root/src/database-parser.cc"
    break;

  case 328: // bound_variable: "implicit set variable"
#line 2501 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5123 "../../mli-root/src/database-parser.cc"
    break;

  case 329: // function_term: function_term_identifier tuple
#line 2506 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::function, 0_ml, structure::postargument, precedence_t()); }
#line 5131 "../../mli-root/src/database-parser.cc"
    break;

  case 330: // function_term: term_function_application
#line 2509 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 5137 "../../mli-root/src/database-parser.cc"
    break;

  case 331: // function_term: term "!"
#line 2510 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[0].value.as < std::string > (), structure::function, 0_ml,
        structure::postfix, factorial_oprec, yystack_[1].value.as < ref6<unit> > ());
    }
#line 5146 "../../mli-root/src/database-parser.cc"
    break;

  case 332: // function_term: term "+" term
#line 2514 "../../mli-root/src/database-parser.yy"
                           { // $$ = val<integer_addition>(make, val<formula>($x), val<formula>($y));
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, plus_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5155 "../../mli-root/src/database-parser.cc"
    break;

  case 333: // function_term: term "-" term
#line 2518 "../../mli-root/src/database-parser.yy"
                           { // $$ = val<integer_addition>(make, val<formula>($x), val<integer_negative>(make, val<formula>($y)));
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, minus_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5164 "../../mli-root/src/database-parser.cc"
    break;

  case 334: // function_term: "-" term
#line 2522 "../../mli-root/src/database-parser.yy"
                                      { // $$ = val<integer_negative>(make, val<formula>($x)); }
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, unary_minus_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5173 "../../mli-root/src/database-parser.cc"
    break;

  case 335: // function_term: term "⋅" term
#line 2526 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, mult_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5182 "../../mli-root/src/database-parser.cc"
    break;

  case 336: // function_term: term "/" term
#line 2530 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, divide_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5191 "../../mli-root/src/database-parser.cc"
    break;

  case 337: // set_term: "{" "}"
#line 2538 "../../mli-root/src/database-parser.yy"
            { yylhs.value.as < ref6<unit> > () = ref0<sequence>(make, sequence::member_list_set); }
#line 5197 "../../mli-root/src/database-parser.cc"
    break;

  case 338: // set_term: "∅"
#line 2539 "../../mli-root/src/database-parser.yy"
        { yylhs.value.as < ref6<unit> > () = val<constant>(make, "∅", constant::object); }
#line 5203 "../../mli-root/src/database-parser.cc"
    break;

  case 339: // set_term: "{" set_member_list "}"
#line 2540 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 5209 "../../mli-root/src/database-parser.cc"
    break;

  case 340: // set_term: "{" "set variable definition" optional_in_term "|" object_formula "}"
#line 2541 "../../mli-root/src/database-parser.yy"
                                                                                 {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<bound_formula>(make, yystack_[4].value.as < val<unit> > (), yystack_[3].value.as < ref6<unit> > (), yystack_[1].value.as < ref6<unit> > (), bound_formula::set_);
    }
#line 5218 "../../mli-root/src/database-parser.cc"
    break;

  case 341: // set_term: "{" "₍" implicit_set_identifier_list optional_in_term "₎" term "|" object_formula "}"
#line 2545 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      symbol_table.pop_level();
      variable_list& vs = dyn_cast<variable_list&>(yystack_[6].value.as < ref6<unit> > ());
      ref0<sequence> sp(make, val<formula>(yystack_[3].value.as < ref6<unit> > ()), sequence::implicit_set);
      sp->push_back(val<formula>(yystack_[1].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () =
        val<bound_formula>(make, vs, yystack_[5].value.as < ref6<unit> > (), val<formula>(sp));
    }
#line 5231 "../../mli-root/src/database-parser.cc"
    break;

  case 342: // set_term: term "∪" term
#line 2553 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, set_union_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5240 "../../mli-root/src/database-parser.cc"
    break;

  case 343: // set_term: term "∩" term
#line 2557 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, set_intersection_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5249 "../../mli-root/src/database-parser.cc"
    break;

  case 344: // set_term: term "∖" term
#line 2561 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, set_difference_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5258 "../../mli-root/src/database-parser.cc"
    break;

  case 345: // set_term: "∁" term
#line 2565 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, set_complement_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5267 "../../mli-root/src/database-parser.cc"
    break;

  case 346: // set_term: "⋃" term
#line 2569 "../../mli-root/src/database-parser.yy"
                   { /* prefix union operator  */
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, set_union_operator_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5276 "../../mli-root/src/database-parser.cc"
    break;

  case 347: // set_term: "∩" term
#line 2573 "../../mli-root/src/database-parser.yy"
                   { /* prefix intersection operator  */
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, set_intersection_operator_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5285 "../../mli-root/src/database-parser.cc"
    break;

  case 348: // $@21: %empty
#line 2581 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 5291 "../../mli-root/src/database-parser.cc"
    break;

  case 349: // implicit_set_identifier_list: $@21 "Set variable"
#line 2582 "../../mli-root/src/database-parser.yy"
                       {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = val<variable_list>(make, val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::implicit_set);
    }
#line 5300 "../../mli-root/src/database-parser.cc"
    break;

  case 350: // $@22: %empty
#line 2586 "../../mli-root/src/database-parser.yy"
                                    { bound_variable_type = database_parser::token::is_set_variable; }
#line 5306 "../../mli-root/src/database-parser.cc"
    break;

  case 351: // implicit_set_identifier_list: implicit_set_identifier_list $@22 "," "Set variable"
#line 2587 "../../mli-root/src/database-parser.yy"
                             {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = yystack_[3].value.as < ref6<unit> > ();
      dyn_cast<variable_list&>(yylhs.value.as < ref6<unit> > ()).push_back(val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::implicit_set);
    }
#line 5316 "../../mli-root/src/database-parser.cc"
    break;

  case 352: // set_member_list: term
#line 2596 "../../mli-root/src/database-parser.yy"
            {
      ref0<sequence> vr(make, sequence::member_list_set);
      yylhs.value.as < ref6<unit> > () = vr;
      vr->push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 5325 "../../mli-root/src/database-parser.cc"
    break;

  case 353: // set_member_list: set_member_list "," term
#line 2600 "../../mli-root/src/database-parser.yy"
                                   {
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
      sequence& vr = dyn_cast<sequence&>(yylhs.value.as < ref6<unit> > ());
      vr.push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 5335 "../../mli-root/src/database-parser.cc"
    break;

  case 354: // function_term_identifier: "function constant"
#line 2609 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5341 "../../mli-root/src/database-parser.cc"
    break;

  case 355: // function_term_identifier: "function variable"
#line 2610 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5347 "../../mli-root/src/database-parser.cc"
    break;


#line 5351 "../../mli-root/src/database-parser.cc"

            default:
              break;
            }
        }
#if YY_EXCEPTIONS
      catch (const syntax_error& yyexc)
        {
          YYCDEBUG << "Caught exception: " << yyexc.what() << '\n';
          error (yyexc);
          YYERROR;
        }
#endif // YY_EXCEPTIONS
      YY_SYMBOL_PRINT ("-> $$ =", yylhs);
      yypop_ (yylen);
      yylen = 0;

      // Shift the result of the reduction.
      yypush_ (YY_NULLPTR, YY_MOVE (yylhs));
    }
    goto yynewstate;


  /*--------------------------------------.
  | yyerrlab -- here on detecting error.  |
  `--------------------------------------*/
  yyerrlab:
    // If not already recovering from an error, report this error.
    if (!yyerrstatus_)
      {
        ++yynerrs_;
        context yyctx (*this, yyla);
        std::string msg = yysyntax_error_ (yyctx);
        error (yyla.location, YY_MOVE (msg));
      }


    yyerror_range[1].location = yyla.location;
    if (yyerrstatus_ == 3)
      {
        /* If just tried and failed to reuse lookahead token after an
           error, discard it.  */

        // Return failure if at end of input.
        if (yyla.kind () == symbol_kind::S_YYEOF)
          YYABORT;
        else if (!yyla.empty ())
          {
            yy_destroy_ ("Error: discarding", yyla);
            yyla.clear ();
          }
      }

    // Else will try to reuse lookahead token after shifting the error token.
    goto yyerrlab1;


  /*---------------------------------------------------.
  | yyerrorlab -- error raised explicitly by YYERROR.  |
  `---------------------------------------------------*/
  yyerrorlab:
    /* Pacify compilers when the user code never invokes YYERROR and
       the label yyerrorlab therefore never appears in user code.  */
    if (false)
      YYERROR;

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    YY_STACK_PRINT ();
    goto yyerrlab1;


  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;   // Each real token shifted decrements this.
    // Pop stack until we find a state that shifts the error token.
    for (;;)
      {
        yyn = yypact_[+yystack_[0].state];
        if (!yy_pact_value_is_default_ (yyn))
          {
            yyn += symbol_kind::S_YYerror;
            if (0 <= yyn && yyn <= yylast_
                && yycheck_[yyn] == symbol_kind::S_YYerror)
              {
                yyn = yytable_[yyn];
                if (0 < yyn)
                  break;
              }
          }

        // Pop the current state because it cannot handle the error token.
        if (yystack_.size () == 1)
          YYABORT;

        yyerror_range[1].location = yystack_[0].location;
        yy_destroy_ ("Error: popping", yystack_[0]);
        yypop_ ();
        YY_STACK_PRINT ();
      }
    {
      stack_symbol_type error_token;

      yyerror_range[2].location = yyla.location;
      YYLLOC_DEFAULT (error_token.location, yyerror_range, 2);

      // Shift the error token.
      yy_lac_discard_ ("error recovery");
      error_token.state = state_type (yyn);
      yypush_ ("Shifting", YY_MOVE (error_token));
    }
    goto yynewstate;


  /*-------------------------------------.
  | yyacceptlab -- YYACCEPT comes here.  |
  `-------------------------------------*/
  yyacceptlab:
    yyresult = 0;
    goto yyreturn;


  /*-----------------------------------.
  | yyabortlab -- YYABORT comes here.  |
  `-----------------------------------*/
  yyabortlab:
    yyresult = 1;
    goto yyreturn;


  /*-----------------------------------------------------.
  | yyreturn -- parsing is finished, return the result.  |
  `-----------------------------------------------------*/
  yyreturn:
    if (!yyla.empty ())
      yy_destroy_ ("Cleanup: discarding lookahead", yyla);

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    YY_STACK_PRINT ();
    while (1 < yystack_.size ())
      {
        yy_destroy_ ("Cleanup: popping", yystack_[0]);
        yypop_ ();
      }

    return yyresult;
  }
#if YY_EXCEPTIONS
    catch (...)
      {
        YYCDEBUG << "Exception caught: cleaning lookahead and stack\n";
        // Do not try to display the values of the reclaimed symbols,
        // as their printers might throw an exception.
        if (!yyla.empty ())
          yy_destroy_ (YY_NULLPTR, yyla);

        while (1 < yystack_.size ())
          {
            yy_destroy_ (YY_NULLPTR, yystack_[0]);
            yypop_ ();
          }
        throw;
      }
#endif // YY_EXCEPTIONS
  }

  void
  database_parser::error (const syntax_error& yyexc)
  {
    error (yyexc.location, yyexc.what ());
  }

  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
  database_parser::yytnamerr_ (const char *yystr)
  {
    if (*yystr == '"')
      {
        std::string yyr;
        char const *yyp = yystr;

        for (;;)
          switch (*++yyp)
            {
            case '\'':
            case ',':
              goto do_not_strip_quotes;

            case '\\':
              if (*++yyp != '\\')
                goto do_not_strip_quotes;
              else
                goto append;

            append:
            default:
              yyr += *yyp;
              break;

            case '"':
              return yyr;
            }
      do_not_strip_quotes: ;
      }

    return yystr;
  }

  std::string
  database_parser::symbol_name (symbol_kind_type yysymbol)
  {
    return yytnamerr_ (yytname_[yysymbol]);
  }



  // database_parser::context.
  database_parser::context::context (const database_parser& yyparser, const symbol_type& yyla)
    : yyparser_ (yyparser)
    , yyla_ (yyla)
  {}

  int
  database_parser::context::expected_tokens (symbol_kind_type yyarg[], int yyargn) const
  {
    // Actual number of expected tokens
    int yycount = 0;

#if MLIDEBUG
    // Execute LAC once. We don't care if it is successful, we
    // only do it for the sake of debugging output.
    if (!yyparser_.yy_lac_established_)
      yyparser_.yy_lac_check_ (yyla_.kind ());
#endif

    for (int yyx = 0; yyx < YYNTOKENS; ++yyx)
      {
        symbol_kind_type yysym = YY_CAST (symbol_kind_type, yyx);
        if (yysym != symbol_kind::S_YYerror
            && yysym != symbol_kind::S_YYUNDEF
            && yyparser_.yy_lac_check_ (yysym))
          {
            if (!yyarg)
              ++yycount;
            else if (yycount == yyargn)
              return 0;
            else
              yyarg[yycount++] = yysym;
          }
      }
    if (yyarg && yycount == 0 && 0 < yyargn)
      yyarg[0] = symbol_kind::S_YYEMPTY;
    return yycount;
  }




  bool
  database_parser::yy_lac_check_ (symbol_kind_type yytoken) const
  {
    // Logically, the yylac_stack's lifetime is confined to this function.
    // Clear it, to get rid of potential left-overs from previous call.
    yylac_stack_.clear ();
    // Reduce until we encounter a shift and thereby accept the token.
#if MLIDEBUG
    YYCDEBUG << "LAC: checking lookahead " << symbol_name (yytoken) << ':';
#endif
    std::ptrdiff_t lac_top = 0;
    while (true)
      {
        state_type top_state = (yylac_stack_.empty ()
                                ? yystack_[lac_top].state
                                : yylac_stack_.back ());
        int yyrule = yypact_[+top_state];
        if (yy_pact_value_is_default_ (yyrule)
            || (yyrule += yytoken) < 0 || yylast_ < yyrule
            || yycheck_[yyrule] != yytoken)
          {
            // Use the default action.
            yyrule = yydefact_[+top_state];
            if (yyrule == 0)
              {
                YYCDEBUG << " Err\n";
                return false;
              }
          }
        else
          {
            // Use the action from yytable.
            yyrule = yytable_[yyrule];
            if (yy_table_value_is_error_ (yyrule))
              {
                YYCDEBUG << " Err\n";
                return false;
              }
            if (0 < yyrule)
              {
                YYCDEBUG << " S" << yyrule << '\n';
                return true;
              }
            yyrule = -yyrule;
          }
        // By now we know we have to simulate a reduce.
        YYCDEBUG << " R" << yyrule - 1;
        // Pop the corresponding number of values from the stack.
        {
          std::ptrdiff_t yylen = yyr2_[yyrule];
          // First pop from the LAC stack as many tokens as possible.
          std::ptrdiff_t lac_size = std::ptrdiff_t (yylac_stack_.size ());
          if (yylen < lac_size)
            {
              yylac_stack_.resize (std::size_t (lac_size - yylen));
              yylen = 0;
            }
          else if (lac_size)
            {
              yylac_stack_.clear ();
              yylen -= lac_size;
            }
          // Only afterwards look at the main stack.
          // We simulate popping elements by incrementing lac_top.
          lac_top += yylen;
        }
        // Keep top_state in sync with the updated stack.
        top_state = (yylac_stack_.empty ()
                     ? yystack_[lac_top].state
                     : yylac_stack_.back ());
        // Push the resulting state of the reduction.
        state_type state = yy_lr_goto_state_ (top_state, yyr1_[yyrule]);
        YYCDEBUG << " G" << int (state);
        yylac_stack_.push_back (state);
      }
  }

  // Establish the initial context if no initial context currently exists.
  bool
  database_parser::yy_lac_establish_ (symbol_kind_type yytoken)
  {
    /* Establish the initial context for the current lookahead if no initial
       context is currently established.

       We define a context as a snapshot of the parser stacks.  We define
       the initial context for a lookahead as the context in which the
       parser initially examines that lookahead in order to select a
       syntactic action.  Thus, if the lookahead eventually proves
       syntactically unacceptable (possibly in a later context reached via a
       series of reductions), the initial context can be used to determine
       the exact set of tokens that would be syntactically acceptable in the
       lookahead's place.  Moreover, it is the context after which any
       further semantic actions would be erroneous because they would be
       determined by a syntactically unacceptable token.

       yy_lac_establish_ should be invoked when a reduction is about to be
       performed in an inconsistent state (which, for the purposes of LAC,
       includes consistent states that don't know they're consistent because
       their default reductions have been disabled).

       For parse.lac=full, the implementation of yy_lac_establish_ is as
       follows.  If no initial context is currently established for the
       current lookahead, then check if that lookahead can eventually be
       shifted if syntactic actions continue from the current context.  */
    if (yy_lac_established_)
      return true;
    else
      {
#if MLIDEBUG
        YYCDEBUG << "LAC: initial context established for "
                 << symbol_name (yytoken) << '\n';
#endif
        yy_lac_established_ = true;
        return yy_lac_check_ (yytoken);
      }
  }

  // Discard any previous initial lookahead context.
  void
  database_parser::yy_lac_discard_ (const char* event)
  {
   /* Discard any previous initial lookahead context because of Event,
      which may be a lookahead change or an invalidation of the currently
      established initial context for the current lookahead.

      The most common example of a lookahead change is a shift.  An example
      of both cases is syntax error recovery.  That is, a syntax error
      occurs when the lookahead is syntactically erroneous for the
      currently established initial context, so error recovery manipulates
      the parser stacks to try to find a new initial context in which the
      current lookahead is syntactically acceptable.  If it fails to find
      such a context, it discards the lookahead.  */
    if (yy_lac_established_)
      {
        YYCDEBUG << "LAC: initial context discarded due to "
                 << event << '\n';
        yy_lac_established_ = false;
      }
  }


  int
  database_parser::yy_syntax_error_arguments_ (const context& yyctx,
                                                 symbol_kind_type yyarg[], int yyargn) const
  {
    /* There are many possibilities here to consider:
       - If this state is a consistent state with a default action, then
         the only way this function was invoked is if the default action
         is an error action.  In that case, don't check for expected
         tokens because there are none.
       - The only way there can be no lookahead present (in yyla) is
         if this state is a consistent state with a default action.
         Thus, detecting the absence of a lookahead is sufficient to
         determine that there is no unexpected or expected token to
         report.  In that case, just report a simple "syntax error".
       - Don't assume there isn't a lookahead just because this state is
         a consistent state with a default action.  There might have
         been a previous inconsistent state, consistent state with a
         non-default action, or user semantic action that manipulated
         yyla.  (However, yyla is currently not documented for users.)
         In the first two cases, it might appear that the current syntax
         error should have been detected in the previous state when
         yy_lac_check was invoked.  However, at that time, there might
         have been a different syntax error that discarded a different
         initial context during error recovery, leaving behind the
         current lookahead.
    */

    if (!yyctx.lookahead ().empty ())
      {
        if (yyarg)
          yyarg[0] = yyctx.token ();
        int yyn = yyctx.expected_tokens (yyarg ? yyarg + 1 : yyarg, yyargn - 1);
        return yyn + 1;
      }
    return 0;
  }

  // Generate an error message.
  std::string
  database_parser::yysyntax_error_ (const context& yyctx) const
  {
    // Its maximum.
    enum { YYARGS_MAX = 5 };
    // Arguments of yyformat.
    symbol_kind_type yyarg[YYARGS_MAX];
    int yycount = yy_syntax_error_arguments_ (yyctx, yyarg, YYARGS_MAX);

    char const* yyformat = YY_NULLPTR;
    switch (yycount)
      {
#define YYCASE_(N, S)                         \
        case N:                               \
          yyformat = S;                       \
        break
      default: // Avoid compiler warnings.
        YYCASE_ (0, YY_("syntax error"));
        YYCASE_ (1, YY_("syntax error, unexpected %s"));
        YYCASE_ (2, YY_("syntax error, unexpected %s, expecting %s"));
        YYCASE_ (3, YY_("syntax error, unexpected %s, expecting %s or %s"));
        YYCASE_ (4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
        YYCASE_ (5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
      }

    std::string yyres;
    // Argument number.
    std::ptrdiff_t yyi = 0;
    for (char const* yyp = yyformat; *yyp; ++yyp)
      if (yyp[0] == '%' && yyp[1] == 's' && yyi < yycount)
        {
          yyres += symbol_name (yyarg[yyi++]);
          ++yyp;
        }
      else
        yyres += *yyp;
    return yyres;
  }


  const short database_parser::yypact_ninf_ = -535;

  const short database_parser::yytable_ninf_ = -356;

  const short
  database_parser::yypact_[] =
  {
     171,  -535,    76,   115,  -535,   185,  -535,  -535,    77,  -535,
    -535,  -535,  -535,    97,  -535,  -535,   451,   231,   123,  -535,
     254,  -535,   449,   409,  -535,   257,   449,    77,    77,    77,
     233,    52,   269,  -535,  -535,  -535,  -535,   426,   525,  -535,
     134,  -535,  -535,  -535,   189,  -535,    77,   201,   209,   218,
    -535,   227,  -535,  -535,   334,   364,   303,  -535,  -535,   309,
    -535,  -535,  -535,  -535,   434,  -535,  -535,   725,   329,   338,
     338,  -535,  -535,  -535,  -535,   196,   355,  -535,   366,  -535,
     383,    10,  -535,  -535,  -535,  -535,  -535,  -535,   414,   414,
     405,   403,   403,   403,   403,   403,  -535,  -535,  1470,  -535,
    -535,  1470,  1470,  1470,   625,   936,   725,  -535,  -535,  -535,
     725,     6,  -535,   393,  -535,  -535,   332,  -535,  -535,   277,
    -535,   396,  -535,  -535,  -535,  -535,   338,  -535,  -535,  1373,
    -535,  -535,  -535,   850,   397,  -535,  -535,  -535,   338,  -535,
    -535,  -535,   478,   335,  -535,  -535,  -535,  -535,   233,  -535,
    -535,    52,   406,   269,  -535,  -535,   513,    62,   411,  1284,
    -535,  1470,  -535,  -535,  -535,   400,  -535,  -535,   472,   477,
    -535,  1284,  -535,   403,   403,   403,   403,   441,  1398,  1008,
    -535,   412,   214,   214,   214,   162,   482,     6,   416,    24,
     786,   435,  1106,  -535,  -535,    -7,  1626,   -82,  -535,     6,
     405,   405,   725,   725,   797,   393,  -535,  -535,  -535,  -535,
     511,   494,  1284,  1284,  1284,   405,   405,   405,   405,   405,
     862,   396,  -535,  -535,  -535,  -535,  -535,  -535,  1470,  1195,
    -535,  -535,    42,  1626,  1470,  1470,   494,  1470,  1470,  1470,
    1470,  1470,  1470,  1470,  1470,  1470,  1470,  1470,  1470,  -535,
    1470,  1470,  1470,  1470,  1470,  1470,  1470,  1470,  1470,  1470,
    1470,  1470,  1470,   654,   397,  -535,  -535,   540,    77,    77,
      77,  -535,  -535,  -535,  -535,  -535,  -535,   525,   525,  -535,
    -535,  -535,  -535,   132,  -535,  -535,   425,   525,  -535,   410,
     426,  -535,   -90,   448,   310,   539,   315,   417,  -535,   428,
    -535,   436,  -535,  -535,  -535,  -535,  -535,   127,   504,   490,
     539,   521,  1284,   515,   469,   479,  -535,   471,   268,   241,
    1528,    65,   527,    45,  1470,  -535,   486,   486,   -10,  -535,
     534,   535,   536,   537,  -535,   543,  -535,  1284,  -535,  -535,
     448,  1626,   448,   448,  1284,  1284,  1284,  1284,  1284,  -535,
     539,   270,  1284,  -535,   539,   539,   604,   539,   539,   539,
     539,   539,   539,   539,   539,   539,   539,   539,   539,  -535,
     -72,   -72,   539,   539,   510,   214,   214,   539,   539,   539,
     539,  -535,  -535,   522,   523,   530,   531,   532,   725,  -535,
    -535,  -535,  -535,   457,   487,   325,   533,   581,    35,   512,
     359,   562,   538,   526,  -535,  -535,   642,  -535,  -535,  1284,
    -535,  1470,  -535,  -535,  -535,  -535,  -535,  -535,   125,  -535,
     610,   563,   564,  1470,   598,   573,   348,  1577,  1284,  1284,
     579,   592,  -535,   662,  -535,  -535,  1284,  1284,    29,  -535,
     539,     1,   583,   583,   725,  1284,  1080,   676,  1470,   448,
    1626,  -535,   653,   353,   353,   429,  -535,   448,  1284,  -535,
    -535,  -535,  -535,  -535,  -535,   725,   725,  1284,  1284,  1470,
    1470,  -535,   633,   626,   627,   393,   132,  -535,   132,   132,
     132,   132,   448,   539,  -535,  -535,  -535,   -31,   672,   673,
     506,  1470,  -535,   338,   338,   448,  1626,   261,  1470,   670,
    1470,   163,   156,    45,  1284,  -535,  -535,     2,   119,  -535,
     -44,  -535,     0,  -535,   155,   725,   725,    -4,   135,   606,
     607,   590,   448,  1626,   525,   525,   525,   608,   613,   448,
     448,   539,   539,  1284,  -535,  -535,   393,   562,   538,   609,
      58,  -535,   380,  -535,  -535,  -535,  -535,   539,   113,  -535,
    -535,   615,   617,  -535,   690,  -535,   539,    13,    13,  -535,
     314,   167,   616,   167,   644,  -535,   645,  -535,  -535,  -535,
    -535,  -535,   166,   -63,  -535,    86,  -535,    -9,  -535,    11,
     411,  -535,  -535,  -535,  -535,  -535,   622,   623,   628,   448,
     132,   132,  -535,  -535,  -535,  -535,  1284,  -535,  -535,  -535,
     338,   338,  1284,    45,   611,  -535,  -535,  -535,   645,  -535,
    -535,   316,   630,   316,   651,  -535,   657,  -535,  -535,  -535,
    -535,  -535,  -535,   114,  -535,   399,  -535,  -535,   319,    71,
      13,   657,  -535,  -535,  -535,  -535,  -535,  -535,  -535
  };

  const short
  database_parser::yydefact_[] =
  {
       0,     4,     0,     3,     6,     0,     1,     5,     0,     8,
      68,    69,    70,     0,    33,    37,    51,     0,     0,    38,
       0,    51,    42,     0,    44,     0,    43,     0,     0,     0,
       0,     0,     0,    52,    55,    56,    53,    75,     0,    54,
       0,   118,    40,    41,     0,    46,    35,     0,     0,     0,
     130,   120,   128,   133,     0,     0,   121,   131,   125,   122,
     123,    79,    78,    71,    91,    74,    80,     0,     0,     0,
       0,   265,   238,   354,   307,   187,   239,   266,   240,   276,
     313,   320,   315,   316,   314,   317,   318,   319,   287,   287,
     267,     0,     0,     0,     0,     0,   308,   309,     0,   261,
     338,     0,     0,     0,     0,     0,     0,   209,   330,    72,
       0,   113,   145,     0,   147,   148,     0,   188,   197,   146,
     213,     0,   212,   207,   241,   242,     0,   210,   275,   298,
     282,   283,   284,     0,   303,   310,   304,   306,     0,   117,
     119,    39,     0,     0,    36,    66,    64,    73,     0,   134,
     135,     0,     0,     0,    92,    76,     0,    85,   154,     0,
     202,     0,    32,    28,   203,     0,   312,   288,     0,     0,
     268,     0,   277,     0,     0,     0,     0,   320,     0,     0,
     334,     0,   345,   347,   346,   320,     0,     0,   145,   146,
       0,   298,     0,   348,   337,     0,   352,     0,   149,   114,
     267,   267,     0,     0,     0,   156,     9,    11,    12,    13,
       0,     0,     0,     0,     0,   267,   267,   267,   267,   267,
       0,   208,    15,    17,    18,   264,   239,   240,     0,     0,
     228,   236,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   331,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   305,    22,   329,     0,     0,     0,
       0,    47,    49,    59,    50,    48,    34,     0,     0,   129,
     132,   126,   124,    97,    77,    87,     0,     0,    81,     0,
       0,    88,     0,   205,     0,   301,     0,     0,   292,   285,
     295,   286,   269,   279,   278,   280,   281,   320,     0,     0,
     352,     0,     0,     0,   155,   211,   311,     0,   320,     0,
       0,   298,     0,   217,     0,   339,   157,   157,   150,   151,
       0,     0,     0,     0,   313,     0,    10,     0,   196,   189,
     190,   191,   198,   199,     0,     0,     0,     0,     0,    16,
     299,     0,     0,   230,   200,   201,     0,   247,   248,   249,
     250,   251,   252,   253,   254,   243,   244,   245,   246,   335,
     332,   333,   255,   256,   342,   343,   344,   257,   258,   259,
     260,   336,    23,     0,     0,     0,     0,     0,     0,   115,
     136,   137,   138,   145,   146,     0,     0,     0,   105,   110,
       0,    93,    95,    98,   104,    82,    89,    86,    84,     0,
     204,     0,   300,   324,   325,   326,   327,   328,     0,   322,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   349,     0,   220,   221,     0,     0,     0,   218,
     353,     0,   171,   171,     0,     0,     0,     0,     0,   192,
     193,   271,   270,   272,   273,   274,   237,   229,     0,    45,
      57,    60,    62,    67,   116,     0,     0,     0,     0,     0,
       0,    65,     0,   108,   106,     0,    97,    90,    97,     0,
       0,    97,   206,   302,   321,   323,   290,     0,     0,     0,
       0,     0,   262,     0,     0,    26,    30,     0,     0,     0,
       0,     0,     0,     0,     0,   170,   169,     0,     0,   161,
       0,   164,     0,   167,     0,     0,     0,     0,     0,     0,
       0,     0,   194,   195,     0,     0,     0,   145,   145,   141,
     142,   143,   144,     0,   109,   107,   112,    94,    96,   100,
       0,   102,     0,   291,   289,   294,   297,    30,     0,    25,
      29,     0,     0,   340,     0,   351,   222,     0,     0,   219,
       0,     0,   163,   166,     0,   158,     0,   159,   160,   168,
     184,   183,     0,     0,   175,     0,   178,     0,   181,   152,
     153,    14,    19,    20,    21,    24,     0,     0,     0,   127,
       0,     0,    99,    83,   231,   232,     0,   235,   263,   233,
       0,     0,     0,   217,     0,   215,   224,   214,     0,   162,
     165,     0,   177,   180,     0,   172,     0,   173,   174,   182,
      58,    61,    63,     0,   103,     0,    27,    31,     0,     0,
       0,     0,   176,   179,   101,   234,   341,   216,   223
  };

  const short
  database_parser::yypgoto_[] =
  {
    -535,  -535,  -535,   748,  -535,   281,  -200,  -535,  -535,   541,
    -105,  -535,  -112,  -535,  -535,  -535,  -535,  -535,  -535,  -535,
    -535,  -535,  -535,  -535,  -535,  -535,  -535,  -535,   736,  -535,
    -535,  -535,  -535,  -535,   619,  -535,    57,  -535,    -1,  -535,
    -535,  -535,  -535,  -535,   468,  -535,  -535,  -535,  -535,  -535,
    -535,   602,  -535,   297,   308,   318,   197,  -468,  -535,  -535,
    -270,  -535,   -16,  -535,   746,  -535,   635,  -535,  -535,  -535,
     658,  -535,   656,   420,  -535,  -535,  -535,   -66,   -86,   483,
    -535,   245,   370,   239,   373,  -404,   372,  -535,   203,   304,
     204,   305,  -496,  -535,  -535,  -535,  -162,  -535,  -535,   749,
    -535,  -102,  -535,  -534,   220,  -303,  -535,  -228,  -535,  -535,
     696,   381,  -535,  -535,   280,  -535,   176,  -535,    -8,  -535,
    -535,  -535,  -535,   743,  -535,  -535,  -535,  -535,  -535,  -535,
    -177,   -70,  -535,    37,  -535,  -181,  -535,  -535,   419,  -535,
    -535,  -535,  -535,  -535,  -535,  -535
  };

  const short
  database_parser::yydefgoto_[] =
  {
       0,     2,     3,     4,     5,   205,   206,   207,   221,   222,
     208,   264,   209,   107,   551,   108,   552,     9,    15,   143,
      16,    19,    44,    20,    21,    45,   142,   271,    22,    33,
     272,   524,   525,   526,    34,   278,    35,   277,   399,    36,
      37,    38,    63,    64,    65,    66,   157,   287,   288,   289,
     290,   155,   156,   400,   401,   402,   540,   403,   404,   475,
     109,   387,   110,    40,    41,    59,    60,   152,   397,    51,
      52,    56,    57,   389,   390,   391,   392,   111,   112,   442,
     508,   509,   562,   511,   563,   513,   515,   573,   574,   612,
     576,   613,   578,   113,   114,   115,   116,   117,   118,   160,
     292,   119,   120,   604,   438,   605,   121,   122,   598,   230,
     123,   124,   181,   548,   125,   126,   171,   127,   128,   129,
     130,   131,   132,   168,   297,   487,   299,   421,   301,   422,
     232,   162,   294,   233,   134,   135,   166,   418,   419,   136,
     137,   321,   322,   431,   197,   138
  };

  const short
  database_parser::yytable_[] =
  {
     163,   158,   189,   195,   353,   336,    39,    13,   396,   224,
      39,   539,   541,   201,   317,   200,   223,   406,   188,   201,
     439,   543,   265,   335,   606,   200,    47,    48,    49,   201,
    -356,   250,  -196,   409,   201,  -196,   410,   570,   187,   335,
     198,   324,  -196,   571,   199,   144,   505,   505,   505,   339,
     213,   214,   506,   506,   506,   325,   225,   293,   473,   614,
     215,   216,   217,   218,   219,   433,   434,   262,   266,   302,
      27,   615,    10,    11,   356,   133,     6,   284,   -91,   566,
     154,   619,   335,   172,   173,   174,   175,   176,   567,    53,
     319,   215,   216,   217,   218,   219,   638,   433,   434,    10,
      11,   507,   561,   544,   133,   165,    88,    89,   569,   224,
     340,   342,   343,   203,    10,    11,   223,   619,   202,   203,
      -7,   435,   541,   624,   581,   618,   275,   351,   202,   203,
     323,    12,   568,   202,   203,   180,   328,   329,   182,   183,
     184,   190,   196,   133,   430,    54,    55,   133,   603,   398,
     315,   503,   382,   435,   436,    71,   286,   437,    12,   569,
     594,    77,   595,   352,   504,   303,   304,   305,   306,    10,
      11,    -2,     1,    12,   228,   394,    -7,    88,    89,   413,
     414,   591,   415,   416,  -196,   417,   436,  -196,  -350,   437,
       8,   393,   592,   503,  -196,    30,    31,    32,   295,   274,
     559,   570,   215,   216,   217,   218,   219,   571,   637,   616,
     426,   187,   570,   505,   285,   309,   310,   423,   571,   506,
     617,    14,   165,   215,   216,   217,   218,   219,    12,   320,
     215,   216,   217,   218,   219,   449,    23,   591,   596,   133,
     133,   564,   451,   452,   453,   454,   455,    24,   634,   341,
     457,   565,   312,   572,   586,   587,   588,   165,   139,   484,
      25,   388,    46,   582,   611,   350,   320,   384,   385,   386,
      50,   354,   355,   407,   357,   358,   359,   360,   361,   362,
     363,   364,   365,   366,   367,   368,   394,   369,   370,   371,
     372,   373,   374,   375,   376,   377,   378,   379,   380,   381,
     439,   558,   393,   213,   214,   557,    58,   482,   215,   216,
     217,   218,   219,   141,   395,   133,   249,   250,   251,   252,
     597,   159,   187,  -185,   133,   145,   495,   497,   215,   216,
     217,   218,   219,   146,   501,   502,   336,   215,   216,   217,
     218,   219,   147,   518,   215,   216,   217,   218,   219,   427,
     148,   234,   235,   262,   210,   236,   522,   211,   312,   469,
     470,   440,   570,   165,   212,   529,   530,   315,   571,   413,
     414,   149,   415,   416,   450,   417,   326,   327,   517,   527,
     528,   215,   216,   217,   218,   219,   215,   216,   217,   218,
     219,   344,   345,   346,   347,   348,   456,   474,   553,   187,
     187,   150,   560,   237,   238,   239,   240,   241,   242,   243,
     244,   245,   246,   247,   248,   215,   216,   217,   218,   219,
     215,   216,   217,   549,   550,   395,   151,   249,   250,   251,
     252,   589,   153,   411,   253,   254,   412,   255,   256,   257,
      61,    62,   258,   259,   260,   261,    42,    43,   483,   579,
     580,   607,   154,    79,   159,    17,   636,    27,    18,   276,
     490,    28,    29,   161,   262,   496,   215,   216,   217,   218,
     219,    30,    31,    32,   493,    91,    92,    93,    94,    95,
     476,   133,  -225,   477,   267,   521,    27,   268,   269,   270,
      28,   465,   466,  -226,   625,   523,   215,   216,   217,   218,
     628,   476,   133,   133,   593,   170,   531,   532,  -355,   167,
      30,    31,    32,   213,   214,   215,   216,   217,   218,   219,
     204,   467,   468,   220,   263,   635,   298,   281,   547,   283,
     626,   627,   300,   296,   203,   554,   165,   556,   313,    30,
      31,    32,   314,   337,   228,   311,   338,   383,    67,   405,
     420,  -293,   133,   133,   215,   216,   217,   218,   219,  -296,
     424,   133,   133,   133,    68,    69,    70,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,   425,    82,
      83,    84,    85,    86,   432,    87,    30,    31,    32,    88,
      89,    90,   249,   250,   251,   252,  -186,    91,    92,    93,
      94,    95,   255,   256,   257,   428,  -227,   429,   249,   250,
     251,   252,   249,   250,   251,   252,   316,   441,   255,   256,
     257,    96,    97,   256,   257,   444,   445,   446,   447,   262,
      98,    99,   494,   100,   448,   458,   101,   472,   102,  -111,
     103,   249,   250,   251,   252,   262,   459,   460,    67,   262,
     104,   255,   256,   257,   461,   462,   463,   471,   481,   480,
     105,   479,   486,   106,    68,    69,    70,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    80,   185,   262,    82,
      83,    84,    85,    86,   478,    87,   488,   489,   491,    88,
      89,    90,   249,   250,   251,   252,   500,    91,    92,    93,
      94,    95,   255,   256,   257,   334,   177,   492,    82,    83,
      84,    85,    86,   498,    87,   499,   514,   186,   585,   520,
     215,    96,    97,   533,   534,   535,   545,   555,   546,   262,
      98,    99,  -139,   100,   583,   584,   101,  -140,   102,   566,
     103,   600,   590,   601,   608,   561,   620,   621,    67,   631,
     104,     7,   622,   616,   630,   611,   536,    26,   408,   291,
     105,   273,   349,   106,    68,    69,    70,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,   542,    82,
      83,    84,    85,    86,   537,    87,   140,   623,   282,    88,
      89,    90,   249,   250,   251,   252,   538,    91,    92,    93,
      94,    95,   255,   256,   257,   610,   279,   280,   464,   609,
     443,   510,   234,   235,   512,   516,   236,   632,   575,   577,
     633,    96,    97,   629,   164,   231,   602,   519,   599,   262,
      98,    99,   169,   100,     0,     0,   101,   485,   102,     0,
     103,     0,     0,   330,   331,   332,   333,     0,   334,   177,
     104,    82,    83,    84,    85,    86,     0,    87,     0,     0,
     105,     0,     0,   106,   237,   238,   239,   240,   241,   242,
     243,   244,   245,   246,   247,   248,   234,   235,     0,     0,
     236,     0,     0,     0,     0,     0,     0,     0,   249,   250,
     251,   252,     0,     0,     0,   253,   254,     0,   255,   256,
     257,     0,     0,   258,   259,   260,   261,     0,     0,   331,
     332,   333,   316,   334,   177,     0,    82,    83,    84,    85,
      86,     0,    87,     0,     0,   262,     0,     0,   237,   238,
     239,   240,   241,   242,   243,   244,   245,   246,   247,   248,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   249,   250,   251,   252,     0,     0,     0,   253,
     254,     0,   255,   256,   257,     0,     0,   258,   259,   260,
     261,     0,     0,     0,     0,     0,    69,    70,    71,    72,
      73,    74,     0,    76,    77,    78,    79,    80,   177,   262,
      82,    83,    84,    85,    86,   191,    87,     0,     0,     0,
      88,    89,    90,     0,     0,     0,     0,     0,    91,    92,
      93,    94,    95,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    96,    97,     0,     0,     0,     0,     0,     0,
       0,    98,    99,     0,   100,     0,     0,   101,    69,   102,
       0,   103,    73,    74,     0,     0,     0,     0,     0,    80,
     177,   192,    82,    83,    84,    85,    86,   191,    87,   193,
       0,   105,     0,   194,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    96,    97,     0,     0,     0,     0,
       0,     0,     0,    98,     0,     0,   100,     0,     0,   101,
      69,   102,    71,   103,    73,    74,     0,     0,    77,     0,
       0,    80,   177,   178,    82,    83,    84,    85,    86,     0,
      87,   193,     0,   179,     0,   194,    69,    70,    71,    72,
      73,    74,     0,    76,    77,    78,    79,    80,   318,     0,
      82,    83,    84,    85,    86,     0,    87,     0,     0,     0,
      88,    89,    90,     0,     0,     0,    96,    97,    91,    92,
      93,    94,    95,     0,     0,    98,    99,     0,   100,     0,
       0,   101,     0,   102,     0,   103,     0,     0,   186,     0,
       0,     0,    96,    97,     0,   178,     0,     0,     0,     0,
       0,    98,    99,     0,   100,   179,     0,   101,     0,   102,
       0,   103,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   192,     0,     0,     0,    69,    70,    71,    72,    73,
      74,   105,    76,    77,    78,    79,    80,   307,     0,    82,
      83,    84,    85,    86,     0,    87,     0,     0,     0,    88,
      89,    90,     0,     0,     0,     0,     0,    91,    92,    93,
      94,    95,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   308,     0,     0,
       0,    96,    97,     0,     0,     0,     0,     0,     0,     0,
      98,    99,     0,   100,     0,     0,   101,     0,   102,     0,
     103,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     192,     0,     0,     0,    69,    70,    71,    72,    73,    74,
     105,    76,    77,    78,    79,    80,   177,     0,    82,    83,
      84,    85,    86,     0,    87,     0,     0,     0,    88,    89,
      90,     0,     0,     0,     0,     0,    91,    92,    93,    94,
      95,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      96,    97,     0,     0,     0,     0,     0,     0,     0,    98,
      99,     0,   100,     0,     0,   101,     0,   102,     0,   103,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   192,
       0,     0,     0,    69,     0,    71,    72,    73,    74,   105,
     226,    77,   227,     0,    80,   177,     0,    82,    83,    84,
      85,    86,     0,    87,     0,     0,     0,     0,    69,     0,
       0,     0,    73,    74,     0,     0,     0,     0,     0,    80,
     307,     0,    82,    83,    84,    85,    86,     0,    87,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    96,
      97,     0,     0,     0,     0,     0,     0,     0,    98,    99,
       0,   100,   228,     0,   101,     0,   102,     0,   103,     0,
     308,     0,     0,     0,    96,    97,     0,     0,   229,     0,
       0,     0,     0,    98,     0,     0,   100,     0,   179,   101,
      69,   102,     0,   103,    73,    74,     0,     0,     0,     0,
       0,    80,   177,   178,    82,    83,    84,    85,    86,     0,
      87,     0,     0,   179,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    96,    97,     0,     0,
       0,     0,     0,     0,     0,    98,     0,     0,   100,     0,
       0,   101,     0,   102,     0,   103,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   178,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   179,   237,   238,   239,   240,
     241,   242,   243,   244,   245,   246,   247,   248,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     249,   250,   251,   252,     0,     0,     0,   253,   254,     0,
     255,   256,   257,     0,     0,   258,   259,   260,   261,     0,
       0,     0,     0,     0,   316,   237,   238,   239,   240,   241,
     242,   243,   244,   245,   246,   247,   248,   262,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   249,
     250,   251,   252,     0,     0,     0,   253,   254,     0,   255,
     256,   257,     0,     0,   258,   259,   260,   261,     0,     0,
       0,     0,     0,   494,   237,   238,   239,   240,   241,   242,
     243,   244,   245,   246,   247,   248,   262,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   249,   250,
     251,   252,     0,     0,     0,   253,   254,     0,   255,   256,
     257,     0,     0,   258,   259,   260,   261,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   262
  };

  const short
  database_parser::yycheck_[] =
  {
      70,    67,   104,   105,   232,   205,    22,     8,   278,   121,
      26,   479,   480,    23,   191,    19,   121,   287,   104,    23,
     323,    52,   134,   204,   558,    19,    27,    28,    29,    23,
      19,   103,    22,   123,    23,    25,   126,    46,   104,   220,
     106,   123,    32,    52,   110,    46,    46,    46,    46,   211,
      26,    27,    52,    52,    52,   137,   126,   159,    23,   122,
      67,    68,    69,    70,    71,    52,    53,   139,   138,   171,
       8,   134,    37,    38,   236,    38,     0,    15,    16,   123,
      18,   577,   263,    91,    92,    93,    94,    95,   132,    37,
     192,    67,    68,    69,    70,    71,   630,    52,    53,    37,
      38,   100,   100,   134,    67,    95,    64,    65,   512,   221,
     212,   213,   214,   123,    37,    38,   221,   613,   122,   123,
       5,   108,   590,   591,   128,   134,   142,   229,   122,   123,
     137,    96,   132,   122,   123,    98,   202,   203,   101,   102,
     103,   104,   105,   106,   321,    93,    94,   110,   135,    17,
     126,   122,   264,   108,   141,    42,   157,   144,    96,   563,
      47,    48,    49,   121,   135,   173,   174,   175,   176,    37,
      38,     0,     1,    96,   109,   277,     5,    64,    65,    54,
      55,   123,    57,    58,    22,    60,   141,    25,   123,   144,
       5,   277,   134,   122,    32,    61,    62,    63,   161,   142,
     503,    46,    67,    68,    69,    70,    71,    52,   137,   123,
     312,   277,    46,    46,   157,   178,   179,    90,    52,    52,
     134,   124,    95,    67,    68,    69,    70,    71,    96,   192,
      67,    68,    69,    70,    71,   337,     5,   123,   125,   202,
     203,   122,   344,   345,   346,   347,   348,   124,   134,   212,
     352,   132,    90,    98,   524,   525,   526,    95,   124,   134,
       6,   277,     5,   128,    98,   228,   229,   268,   269,   270,
      37,   234,   235,   289,   237,   238,   239,   240,   241,   242,
     243,   244,   245,   246,   247,   248,   388,   250,   251,   252,
     253,   254,   255,   256,   257,   258,   259,   260,   261,   262,
     603,   145,   388,    26,    27,   142,    37,   409,    67,    68,
      69,    70,    71,   124,   277,   278,   102,   103,   104,   105,
     548,   125,   388,   127,   287,   124,   428,   429,    67,    68,
      69,    70,    71,   124,   436,   437,   536,    67,    68,    69,
      70,    71,   124,   445,    67,    68,    69,    70,    71,   312,
     123,    26,    27,   139,    22,    30,   458,    25,    90,    34,
      35,   324,    46,    95,    32,   467,   468,   126,    52,    54,
      55,    37,    57,    58,   337,    60,   200,   201,   444,   465,
     466,    67,    68,    69,    70,    71,    67,    68,    69,    70,
      71,   215,   216,   217,   218,   219,   126,   398,   137,   465,
     466,    37,   504,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    67,    68,    69,    70,    71,
      67,    68,    69,   493,   494,   388,   123,   102,   103,   104,
     105,   533,   123,   123,   109,   110,   126,   112,   113,   114,
      14,    15,   117,   118,   119,   120,    37,    38,   411,   515,
     516,   137,    18,    50,   125,     4,   137,     8,     7,   124,
     423,    12,    13,   125,   139,   428,    67,    68,    69,    70,
      71,    61,    62,    63,   126,    72,    73,    74,    75,    76,
     121,   444,   127,   124,     6,   448,     8,     9,    10,    11,
      12,    34,    35,   127,   596,   458,    67,    68,    69,    70,
     602,   121,   465,   466,   124,   100,   469,   470,   125,    95,
      61,    62,    63,    26,    27,    67,    68,    69,    70,    71,
     127,    34,    35,   127,   127,   126,    54,   121,   491,    16,
     600,   601,    55,   133,   123,   498,    95,   500,    56,    61,
      62,    63,   126,    32,   109,   133,    52,     7,    23,   124,
     133,   123,   515,   516,    67,    68,    69,    70,    71,   123,
      56,   524,   525,   526,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    57,    54,
      55,    56,    57,    58,    57,    60,    61,    62,    63,    64,
      65,    66,   102,   103,   104,   105,   127,    72,    73,    74,
      75,    76,   112,   113,   114,    90,   127,   136,   102,   103,
     104,   105,   102,   103,   104,   105,   126,   131,   112,   113,
     114,    96,    97,   113,   114,    91,    91,    91,    91,   139,
     105,   106,   126,   108,    91,    31,   111,    56,   113,   127,
     115,   102,   103,   104,   105,   139,   124,   124,    23,   139,
     125,   112,   113,   114,   124,   124,   124,   124,    16,   133,
     135,   123,    52,   138,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,   139,    54,
      55,    56,    57,    58,   122,    60,   123,   123,    90,    64,
      65,    66,   102,   103,   104,   105,    34,    72,    73,    74,
      75,    76,   112,   113,   114,    51,    52,   134,    54,    55,
      56,    57,    58,   134,    60,   123,   133,    92,   128,    43,
      67,    96,    97,    90,    98,    98,    54,    57,    55,   139,
     105,   106,   124,   108,   128,   128,   111,   124,   113,   123,
     115,   126,   133,   126,   100,   100,   124,   124,    23,    98,
     125,     3,   124,   123,   143,    98,   475,    21,   290,   157,
     135,   142,   221,   138,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,   481,    54,
      55,    56,    57,    58,   476,    60,    40,   590,   153,    64,
      65,    66,   102,   103,   104,   105,   478,    72,    73,    74,
      75,    76,   112,   113,   114,   566,   148,   151,   388,   564,
     327,   441,    26,    27,   441,   443,    30,   614,   514,   514,
     616,    96,    97,   603,    75,   129,   136,   446,   548,   139,
     105,   106,    89,   108,    -1,    -1,   111,   418,   113,    -1,
     115,    -1,    -1,    46,    47,    48,    49,    -1,    51,    52,
     125,    54,    55,    56,    57,    58,    -1,    60,    -1,    -1,
     135,    -1,    -1,   138,    78,    79,    80,    81,    82,    83,
      84,    85,    86,    87,    88,    89,    26,    27,    -1,    -1,
      30,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   102,   103,
     104,   105,    -1,    -1,    -1,   109,   110,    -1,   112,   113,
     114,    -1,    -1,   117,   118,   119,   120,    -1,    -1,    47,
      48,    49,   126,    51,    52,    -1,    54,    55,    56,    57,
      58,    -1,    60,    -1,    -1,   139,    -1,    -1,    78,    79,
      80,    81,    82,    83,    84,    85,    86,    87,    88,    89,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   102,   103,   104,   105,    -1,    -1,    -1,   109,
     110,    -1,   112,   113,   114,    -1,    -1,   117,   118,   119,
     120,    -1,    -1,    -1,    -1,    -1,    40,    41,    42,    43,
      44,    45,    -1,    47,    48,    49,    50,    51,    52,   139,
      54,    55,    56,    57,    58,    59,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    -1,    -1,    72,    73,
      74,    75,    76,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    96,    97,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   105,   106,    -1,   108,    -1,    -1,   111,    40,   113,
      -1,   115,    44,    45,    -1,    -1,    -1,    -1,    -1,    51,
      52,   125,    54,    55,    56,    57,    58,    59,    60,   133,
      -1,   135,    -1,   137,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    96,    97,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   105,    -1,    -1,   108,    -1,    -1,   111,
      40,   113,    42,   115,    44,    45,    -1,    -1,    48,    -1,
      -1,    51,    52,   125,    54,    55,    56,    57,    58,    -1,
      60,   133,    -1,   135,    -1,   137,    40,    41,    42,    43,
      44,    45,    -1,    47,    48,    49,    50,    51,    52,    -1,
      54,    55,    56,    57,    58,    -1,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    96,    97,    72,    73,
      74,    75,    76,    -1,    -1,   105,   106,    -1,   108,    -1,
      -1,   111,    -1,   113,    -1,   115,    -1,    -1,    92,    -1,
      -1,    -1,    96,    97,    -1,   125,    -1,    -1,    -1,    -1,
      -1,   105,   106,    -1,   108,   135,    -1,   111,    -1,   113,
      -1,   115,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   125,    -1,    -1,    -1,    40,    41,    42,    43,    44,
      45,   135,    47,    48,    49,    50,    51,    52,    -1,    54,
      55,    56,    57,    58,    -1,    60,    -1,    -1,    -1,    64,
      65,    66,    -1,    -1,    -1,    -1,    -1,    72,    73,    74,
      75,    76,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    92,    -1,    -1,
      -1,    96,    97,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     105,   106,    -1,   108,    -1,    -1,   111,    -1,   113,    -1,
     115,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     125,    -1,    -1,    -1,    40,    41,    42,    43,    44,    45,
     135,    47,    48,    49,    50,    51,    52,    -1,    54,    55,
      56,    57,    58,    -1,    60,    -1,    -1,    -1,    64,    65,
      66,    -1,    -1,    -1,    -1,    -1,    72,    73,    74,    75,
      76,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      96,    97,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,
     106,    -1,   108,    -1,    -1,   111,    -1,   113,    -1,   115,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   125,
      -1,    -1,    -1,    40,    -1,    42,    43,    44,    45,   135,
      47,    48,    49,    -1,    51,    52,    -1,    54,    55,    56,
      57,    58,    -1,    60,    -1,    -1,    -1,    -1,    40,    -1,
      -1,    -1,    44,    45,    -1,    -1,    -1,    -1,    -1,    51,
      52,    -1,    54,    55,    56,    57,    58,    -1,    60,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    96,
      97,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,   106,
      -1,   108,   109,    -1,   111,    -1,   113,    -1,   115,    -1,
      92,    -1,    -1,    -1,    96,    97,    -1,    -1,   125,    -1,
      -1,    -1,    -1,   105,    -1,    -1,   108,    -1,   135,   111,
      40,   113,    -1,   115,    44,    45,    -1,    -1,    -1,    -1,
      -1,    51,    52,   125,    54,    55,    56,    57,    58,    -1,
      60,    -1,    -1,   135,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    96,    97,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,   108,    -1,
      -1,   111,    -1,   113,    -1,   115,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   125,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   135,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    87,    88,    89,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     102,   103,   104,   105,    -1,    -1,    -1,   109,   110,    -1,
     112,   113,   114,    -1,    -1,   117,   118,   119,   120,    -1,
      -1,    -1,    -1,    -1,   126,    78,    79,    80,    81,    82,
      83,    84,    85,    86,    87,    88,    89,   139,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   102,
     103,   104,   105,    -1,    -1,    -1,   109,   110,    -1,   112,
     113,   114,    -1,    -1,   117,   118,   119,   120,    -1,    -1,
      -1,    -1,    -1,   126,    78,    79,    80,    81,    82,    83,
      84,    85,    86,    87,    88,    89,   139,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   102,   103,
     104,   105,    -1,    -1,    -1,   109,   110,    -1,   112,   113,
     114,    -1,    -1,   117,   118,   119,   120,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   139
  };

  const short
  database_parser::yystos_[] =
  {
       0,     1,   156,   157,   158,   159,     0,   158,     5,   172,
      37,    38,    96,   193,   124,   173,   175,     4,     7,   176,
     178,   179,   183,     5,   124,     6,   183,     8,    12,    13,
      61,    62,    63,   184,   189,   191,   194,   195,   196,   217,
     218,   219,    37,    38,   177,   180,     5,   193,   193,   193,
      37,   224,   225,    37,    93,    94,   226,   227,    37,   220,
     221,    14,    15,   197,   198,   199,   200,    23,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    54,    55,    56,    57,    58,    60,    64,    65,
      66,    72,    73,    74,    75,    76,    96,    97,   105,   106,
     108,   111,   113,   115,   125,   135,   138,   168,   170,   215,
     217,   232,   233,   248,   249,   250,   251,   252,   253,   256,
     257,   261,   262,   265,   266,   269,   270,   272,   273,   274,
     275,   276,   277,   288,   289,   290,   294,   295,   300,   124,
     219,   124,   181,   174,   193,   124,   124,   124,   123,    37,
      37,   123,   222,   123,    18,   206,   207,   201,   232,   125,
     254,   125,   286,   286,   254,    95,   291,    95,   278,   278,
     100,   271,   273,   273,   273,   273,   273,    52,   125,   135,
     288,   267,   288,   288,   288,    52,    92,   232,   233,   256,
     288,    59,   125,   133,   137,   256,   288,   299,   232,   232,
      19,    23,   122,   123,   127,   160,   161,   162,   165,   167,
      22,    25,    32,    26,    27,    67,    68,    69,    70,    71,
     127,   163,   164,   165,   167,   286,    47,    49,   109,   125,
     264,   265,   285,   288,    26,    27,    30,    78,    79,    80,
      81,    82,    83,    84,    85,    86,    87,    88,    89,   102,
     103,   104,   105,   109,   110,   112,   113,   114,   117,   118,
     119,   120,   139,   127,   166,   167,   286,     6,     9,    10,
      11,   182,   185,   189,   191,   217,   124,   192,   190,   225,
     227,   121,   221,    16,    15,   191,   193,   202,   203,   204,
     205,   206,   255,   256,   287,   288,   133,   279,    54,   281,
      55,   283,   256,   273,   273,   273,   273,    52,    92,   288,
     288,   133,    90,    56,   126,   126,   126,   285,    52,   256,
     288,   296,   297,   137,   123,   137,   271,   271,   232,   232,
      46,    47,    48,    49,    51,   290,   161,    32,    52,   251,
     256,   288,   256,   256,   271,   271,   271,   271,   271,   164,
     288,   256,   121,   262,   288,   288,   251,   288,   288,   288,
     288,   288,   288,   288,   288,   288,   288,   288,   288,   288,
     288,   288,   288,   288,   288,   288,   288,   288,   288,   288,
     288,   288,   167,     7,   193,   193,   193,   216,   217,   228,
     229,   230,   231,   233,   256,   288,   215,   223,    17,   193,
     208,   209,   210,   212,   213,   124,   215,   217,   199,   123,
     126,   123,   126,    54,    55,    57,    58,    60,   292,   293,
     133,   282,   284,    90,    56,    57,   256,   288,    90,   136,
     285,   298,    57,    52,    53,   108,   141,   144,   259,   260,
     288,   131,   234,   234,    91,    91,    91,    91,    91,   256,
     288,   256,   256,   256,   256,   256,   126,   256,    31,   124,
     124,   124,   124,   124,   228,    34,    35,    34,    35,    34,
      35,   124,    56,    23,   193,   214,   121,   124,   122,   123,
     133,    16,   256,   288,   134,   293,    52,   280,   123,   123,
     288,    90,   134,   126,   126,   256,   288,   256,   134,   123,
      34,   256,   256,   122,   135,    46,    52,   100,   235,   236,
     237,   238,   239,   240,   133,   241,   241,   232,   256,   266,
      43,   288,   256,   288,   186,   187,   188,   233,   233,   256,
     256,   288,   288,    90,    98,    98,   160,   209,   210,   212,
     211,   212,   208,    52,   134,    54,    55,   288,   268,   286,
     286,   169,   171,   137,   288,    57,   288,   142,   145,   260,
     256,   100,   237,   239,   122,   132,   123,   132,   132,   240,
      46,    52,    98,   242,   243,   244,   245,   246,   247,   232,
     232,   128,   128,   128,   128,   128,   215,   215,   215,   256,
     133,   123,   134,   124,    47,    49,   125,   262,   263,   269,
     126,   126,   136,   135,   258,   260,   258,   137,   100,   236,
     238,    98,   244,   246,   122,   134,   123,   134,   134,   247,
     124,   124,   124,   211,   212,   256,   286,   286,   256,   259,
     143,    98,   243,   245,   134,   126,   137,   137,   258
  };

  const short
  database_parser::yyr1_[] =
  {
       0,   155,   156,   156,   156,   157,   157,   159,   158,   160,
     160,   161,   161,   161,   162,   163,   163,   164,   164,   165,
     165,   165,   166,   166,   167,   168,   169,   168,   168,   170,
     171,   170,   170,   173,   172,   174,   174,   175,   175,   176,
     177,   177,   178,   178,   180,   179,   181,   181,   182,   182,
     182,   183,   183,   184,   184,   184,   184,   186,   185,   185,
     187,   185,   188,   185,   190,   189,   192,   191,   193,   193,
     193,   194,   195,   196,   197,   198,   197,   199,   199,   200,
     201,   201,   202,   203,   203,   204,   203,   203,   203,   205,
     206,   207,   207,   208,   208,   209,   209,   210,   210,   210,
     210,   210,   211,   211,   212,   212,   212,   212,   212,   212,
     213,   214,   213,   215,   215,   216,   216,   217,   218,   218,
     219,   219,   219,   220,   220,   222,   223,   221,   224,   224,
     225,   226,   226,   227,   227,   227,   228,   228,   228,   229,
     229,   230,   230,   231,   231,   232,   232,   233,   233,   233,
     233,   233,   233,   233,   233,   233,   233,   234,   234,   234,
     234,   235,   235,   236,   237,   237,   238,   239,   239,   240,
     240,   241,   241,   241,   241,   242,   242,   243,   244,   244,
     245,   246,   246,   247,   247,   248,   248,   249,   249,   250,
     250,   250,   250,   250,   250,   250,   251,   252,   252,   252,
     252,   252,   253,   253,   254,   255,   255,   256,   256,   256,
     256,   256,   256,   256,   257,   258,   258,   259,   259,   259,
     260,   260,   260,   260,   260,   261,   261,   261,   262,   262,
     262,   263,   263,   263,   263,   263,   264,   264,   265,   265,
     265,   265,   266,   266,   266,   266,   266,   266,   266,   266,
     266,   266,   266,   266,   266,   266,   266,   266,   266,   266,
     266,   267,   268,   266,   269,   270,   270,   271,   271,   272,
     272,   272,   272,   272,   272,   272,   273,   273,   273,   273,
     273,   273,   274,   275,   275,   276,   277,   278,   279,   278,
     280,   280,   281,   282,   281,   283,   284,   283,   285,   285,
     286,   287,   287,   288,   288,   288,   288,   289,   289,   289,
     289,   289,   290,   290,   290,   290,   290,   290,   290,   290,
     291,   291,   292,   292,   293,   293,   293,   293,   293,   294,
     294,   294,   294,   294,   294,   294,   294,   295,   295,   295,
     295,   295,   295,   295,   295,   295,   295,   295,   297,   296,
     298,   296,   299,   299,   300,   300
  };

  const signed char
  database_parser::yyr2_[] =
  {
       0,     2,     0,     1,     1,     2,     1,     0,     2,     1,
       2,     1,     1,     1,     5,     1,     2,     1,     1,     5,
       5,     5,     1,     2,     5,     6,     0,     8,     2,     6,
       0,     8,     2,     0,    10,     0,     1,     0,     2,     4,
       1,     1,     1,     2,     0,     7,     0,     2,     1,     1,
       1,     0,     2,     1,     1,     1,     1,     0,     6,     1,
       0,     6,     0,     6,     0,     6,     0,     6,     1,     1,
       1,     2,     2,     3,     1,     0,     2,     3,     1,     1,
       0,     2,     2,     5,     2,     0,     2,     1,     1,     2,
       4,     0,     1,     1,     3,     1,     3,     0,     1,     4,
       3,     6,     1,     3,     1,     1,     2,     3,     2,     3,
       1,     0,     3,     1,     2,     1,     2,     2,     1,     2,
       2,     2,     2,     1,     3,     0,     0,     7,     1,     3,
       1,     1,     3,     1,     2,     2,     1,     1,     1,     3,
       3,     3,     3,     3,     3,     1,     1,     1,     1,     2,
       3,     3,     6,     6,     2,     3,     2,     0,     3,     3,
       3,     1,     3,     2,     1,     3,     2,     1,     2,     1,
       1,     0,     3,     3,     3,     1,     3,     2,     1,     3,
       2,     1,     2,     1,     1,     1,     3,     1,     1,     3,
       3,     3,     4,     4,     5,     5,     1,     1,     3,     3,
       3,     3,     2,     2,     3,     1,     3,     1,     2,     1,
       1,     3,     1,     1,     7,     1,     3,     0,     1,     3,
       1,     1,     3,     6,     4,     1,     1,     3,     2,     4,
       3,     1,     1,     1,     3,     1,     1,     3,     1,     1,
       1,     1,     1,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     0,     0,     7,     2,     1,     1,     0,     1,     3,
       4,     4,     4,     4,     4,     1,     1,     2,     3,     3,
       3,     3,     1,     1,     1,     3,     3,     0,     0,     5,
       1,     2,     1,     0,     4,     1,     0,     4,     0,     2,
       3,     1,     3,     1,     1,     2,     1,     1,     1,     1,
       1,     3,     2,     1,     1,     1,     1,     1,     1,     1,
       0,     4,     1,     2,     1,     1,     1,     1,     1,     2,
       1,     2,     3,     3,     2,     3,     3,     2,     1,     3,
       6,     9,     3,     3,     3,     2,     2,     2,     0,     2,
       0,     4,     1,     3,     1,     1
  };


#if MLIDEBUG || 1
  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a YYNTOKENS, nonterminals.
  const char*
  const database_parser::yytname_[] =
  {
  "\"end of file\"", "error", "\"invalid token\"", "\"token error\"",
  "\"include\"", "\"theory\"", "\"end\"", "\"formal system\"",
  "\"definition\"", "\"postulate\"", "\"axiom\"", "\"rule\"",
  "\"conjecture\"", "\"theorem\"", "\"proof\"", "\"∎\"", "\"by\"",
  "\"premise\"", "\"result\"", "\"⊩\"", "\"or\"", "\"and\"", "\"not\"",
  "\"⊢\"", "\"≡\"", "\"≢\"", "\"≣\"", "\"≣̷\"", "\"fail\"", "\"succeed\"",
  "\"free for\"", "\"in\"", "\"free in\"", "\"use\"", "\"≔\"", "\"≕\"",
  "\"≝\"", "\"name\"", "\"label\"", "\"metapredicate constant\"",
  "\"function\"", "\"predicate\"", "\"predicate constant\"",
  "\"atom constant\"", "\"function constant\"", "\"term constant\"",
  "\"metaformula variable\"", "\"object formula variable\"",
  "\"predicate variable\"", "\"atom variable\"",
  "\"prefix formula variable\"", "\"function variable\"",
  "\"object variable\"", "\"code variable\"", "\"all variable\"",
  "\"exist variable\"", "\"function map variable\"", "\"Set variable\"",
  "\"set variable\"", "\"set variable definition\"",
  "\"implicit set variable\"", "\"identifier constant\"",
  "\"identifier variable\"", "\"identifier function\"", "\"∀\"", "\"∃\"",
  "\"¬\"", "\"∧\"", "\"∨\"", "\"⇒\"", "\"⇐\"", "\"⇔\"", "prefix_not_key",
  "prefix_and_key", "prefix_or_key", "prefix_implies_key",
  "prefix_equivalent_key", "\"ℕ\"", "\"<\"", "\">\"", "\"≤\"", "\"≥\"",
  "\"≮\"", "\"≯\"", "\"≰\"", "\"≱\"", "\"=\"", "\"≠\"", "\"∣\"", "\"∤\"",
  "\"↦\"", "\"⤇\"", "\"𝛌\"", "\"°\"", "\"•\"", "\"\342\202\223\"",
  "\"natural number value\"", "\"integer value\"",
  "\"subscript natural number value\"", "\"subscript integer value\"",
  "\"superscript natural number value\"", "\"superscript integer value\"",
  "\"!\"", "\"⋅\"", "\"+\"", "\"-\"", "\"Set\"", "\"Pow\"", "\"∅\"",
  "\"∈\"", "\"∉\"", "\"∁\"", "\"∪\"", "\"∩\"", "\"∖\"", "\"⋃\"", "\"⋂\"",
  "\"⊆\"", "\"⊊\"", "\"⊇\"", "\"⊋\"", "\":\"", "\";\"", "\",\"", "\".\"",
  "\"(\"", "\")\"", "\"[\"", "\"]\"", "\"⟨\"", "\"⟩\"", "\"⁽\"", "\"⁾\"",
  "\"₍\"", "\"₎\"", "\"{\"", "\"|\"", "\"}\"", "\"~\"", "\"/\"",
  "\"\\\\\"", "\"if\"", "\"then\"", "\"else\"", "\"while\"", "\"do\"",
  "\"loop\"", "\"for\"", "\"break\"", "\"continue\"", "\"throw\"",
  "\"try\"", "\"catch\"", "\"⊣\"", "unary_minus", "$accept", "file",
  "file_contents", "command", "$@1", "metaformula_substitution_sequence",
  "substitution_for_metaformula", "metaformula_substitution",
  "formula_substitution_sequence", "substitution_for_formula",
  "formula_substitution", "term_substitution_sequence",
  "term_substitution", "predicate_function_application", "$@2",
  "term_function_application", "$@3", "theory", "$@4", "end_theory_name",
  "include_theories", "include_theory", "theory_name", "theory_body",
  "formal_system", "$@5", "formal_system_body", "formal_system_body_item",
  "theory_body_list", "theory_body_item", "postulate", "$@6", "$@7", "$@8",
  "conjecture", "$@9", "definition_labelstatement", "$@10",
  "statement_name", "theorem", "theorem_statement", "theorem_head",
  "proof", "$@11", "compound-proof", "proof_head", "proof_lines",
  "statement_label", "proof_line", "$@12", "subproof_statement",
  "proof_of_conclusion", "optional-result", "find_statement",
  "find_statement_list", "find_statement_sequence",
  "find_definition_sequence", "find_statement_item", "find_statement_name",
  "@13", "statement", "definition_statement", "identifier_declaration",
  "declarator_list", "declarator_identifier_list",
  "identifier_function_list", "identifier_function_name", "$@14", "$@15",
  "identifier_constant_list", "identifier_constant_name",
  "identifier_variable_list", "identifier_variable_name", "definition",
  "metaformula_definition", "object_formula_definition", "term_definition",
  "metaformula", "pure_metaformula", "optional_varied_variable_matrix",
  "varied_variable_conclusions", "varied_variable_conclusion",
  "varied_variable_premises", "varied_variable_premise",
  "varied_variable_set", "varied_variable",
  "optional_varied_in_reduction_variable_matrix",
  "varied_in_reduction_variable_conclusions",
  "varied_in_reduction_variable_conclusion",
  "varied_in_reduction_variable_premises",
  "varied_in_reduction_variable_premise",
  "varied_in_reduction_variable_set", "varied_in_reduction_variable",
  "simple_metaformula", "atomic_metaformula", "special_metaformula",
  "meta_object_free", "metapredicate", "metapredicate_function",
  "metapredicate_argument", "metapredicate_argument_body",
  "object_formula", "hoare_triple", "code_statement", "code_sequence",
  "code_term", "very_simple_formula", "quantized_formula",
  "simple_formula", "quantized_body", "atomic_formula", "predicate",
  "$@16", "$@17", "predicate_expression", "predicate_identifier",
  "optional_superscript_natural_number_value", "logic_formula",
  "prefix_logic_formula", "quantizer_declaration",
  "quantized_variable_list", "all_variable_list", "exist_variable_list",
  "exclusion_set", "$@18", "exclusion_list", "all_identifier_list", "$@19",
  "exist_identifier_list", "$@20", "optional_in_term", "tuple",
  "tuple_body", "term", "simple_term", "term_identifier",
  "variable_exclusion_set", "variable_exclusion_list", "bound_variable",
  "function_term", "set_term", "implicit_set_identifier_list", "$@21",
  "$@22", "set_member_list", "function_term_identifier", YY_NULLPTR
  };
#endif


#if MLIDEBUG
  const short
  database_parser::yyrline_[] =
  {
       0,   784,   784,   785,   786,   795,   796,   801,   801,   806,
     807,   814,   815,   816,   821,   830,   831,   838,   839,   844,
     849,   854,   863,   864,   871,   880,   883,   883,   886,   891,
     894,   894,   897,   903,   902,   921,   922,   927,   928,   932,
     944,   945,   950,   951,   957,   956,   964,   965,   970,   971,
     972,   977,   978,   988,   989,   990,   992,   998,   997,  1003,
    1005,  1004,  1017,  1016,  1033,  1032,  1042,  1041,  1051,  1052,
    1053,  1058,  1069,  1079,  1089,  1090,  1090,  1104,  1109,  1114,
    1123,  1124,  1129,  1137,  1168,  1183,  1183,  1187,  1198,  1203,
    1213,  1224,  1225,  1230,  1231,  1239,  1242,  1250,  1251,  1253,
    1257,  1261,  1270,  1272,  1280,  1283,  1286,  1299,  1313,  1318,
    1328,  1342,  1342,  1384,  1385,  1429,  1430,  1437,  1442,  1443,
    1448,  1449,  1450,  1455,  1456,  1467,  1468,  1467,  1502,  1503,
    1508,  1523,  1524,  1529,  1540,  1551,  1566,  1567,  1568,  1573,
    1577,  1590,  1594,  1607,  1617,  1625,  1626,  1631,  1632,  1633,
    1636,  1639,  1642,  1710,  1771,  1773,  1774,  1780,  1781,  1782,
    1783,  1787,  1788,  1801,  1813,  1814,  1826,  1838,  1839,  1850,
    1855,  1865,  1866,  1867,  1868,  1872,  1873,  1886,  1898,  1899,
    1911,  1923,  1924,  1935,  1940,  2008,  2009,  2014,  2015,  2027,
    2030,  2033,  2036,  2039,  2042,  2046,  2054,  2059,  2060,  2063,
    2066,  2069,  2076,  2080,  2088,  2093,  2097,  2105,  2106,  2109,
    2110,  2111,  2112,  2113,  2118,  2129,  2130,  2135,  2136,  2137,
    2142,  2143,  2144,  2145,  2146,  2151,  2152,  2153,  2158,  2165,
    2172,  2183,  2184,  2185,  2186,  2187,  2193,  2194,  2198,  2199,
    2200,  2201,  2207,  2208,  2209,  2212,  2213,  2216,  2217,  2218,
    2219,  2220,  2221,  2222,  2223,  2225,  2226,  2227,  2228,  2229,
    2230,  2231,  2232,  2231,  2242,  2250,  2251,  2256,  2257,  2269,
    2275,  2281,  2287,  2293,  2299,  2305,  2310,  2311,  2315,  2319,
    2323,  2327,  2335,  2339,  2340,  2345,  2357,  2369,  2370,  2370,
    2378,  2379,  2389,  2393,  2393,  2403,  2407,  2407,  2418,  2419,
    2426,  2431,  2436,  2445,  2446,  2447,  2450,  2455,  2456,  2457,
    2458,  2459,  2464,  2470,  2471,  2472,  2473,  2474,  2475,  2476,
    2481,  2482,  2487,  2488,  2497,  2498,  2499,  2500,  2501,  2506,
    2509,  2510,  2514,  2518,  2522,  2526,  2530,  2538,  2539,  2540,
    2541,  2545,  2553,  2557,  2561,  2565,  2569,  2573,  2581,  2581,
    2586,  2586,  2596,  2600,  2609,  2610
  };

  void
  database_parser::yy_stack_print_ () const
  {
    *yycdebug_ << "Stack now";
    for (stack_type::const_iterator
           i = yystack_.begin (),
           i_end = yystack_.end ();
         i != i_end; ++i)
      *yycdebug_ << ' ' << int (i->state);
    *yycdebug_ << '\n';
  }

  void
  database_parser::yy_reduce_print_ (int yyrule) const
  {
    int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    // Print the symbols being reduced, and their result.
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
               << " (line " << yylno << "):\n";
    // The symbols being reduced.
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
                       yystack_[(yynrhs) - (yyi + 1)]);
  }
#endif // MLIDEBUG

  database_parser::symbol_kind_type
  database_parser::yytranslate_ (int t) YY_NOEXCEPT
  {
    // YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to
    // TOKEN-NUM as returned by yylex.
    static
    const unsigned char
    translate_table[] =
    {
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   128,   129,   130,   131,   132,   133,   134,
     135,   136,   137,   138,   139,   140,   141,   142,   143,   144,
     145,   146,   147,   148,   149,   150,   151,   152,   153,   154
    };
    // Last valid token kind.
    const int code_max = 409;

    if (t <= 0)
      return symbol_kind::S_YYEOF;
    else if (t <= code_max)
      return static_cast <symbol_kind_type> (translate_table[t]);
    else
      return symbol_kind::S_YYUNDEF;
  }

#line 22 "../../mli-root/src/database-parser.yy"
} // mli
#line 6763 "../../mli-root/src/database-parser.cc"

#line 2614 "../../mli-root/src/database-parser.yy"


  extern std::istream::pos_type line_position;

namespace mli {

  void database_parser::error(const location_type& loc, const std::string& errstr) {
    diagnostic(loc, errstr, mlilex.in(), line_position);
  }


  void theory_database::read(std::istream& is) {
    database_lexer lex(is, std::cout);

    database_parser p(*this, lex);

    if (p.parse() != 0)
      is.setstate(std::ios::failbit);
    else
      is.clear(is.rdstate() & ~(std::ios::failbit | std::ios::badbit));
  }

} // namespace mli

