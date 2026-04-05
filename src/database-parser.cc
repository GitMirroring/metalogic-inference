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
#line 121 "../../mli-root/src/database-parser.yy"


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

#line 25 "../../mli-root/src/database-parser.yy"
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
      case symbol_kind::S_200_12: // $@12
      case symbol_kind::S_201_compound_proof: // compound-proof
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
      case symbol_kind::S_216_14: // @14
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
      case symbol_kind::S_optional_varied_in_reduction_variable_sequence: // optional_varied_in_reduction_variable_sequence
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
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
      case symbol_kind::S_209_optional_result: // optional-result
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
      case symbol_kind::S_200_12: // $@12
      case symbol_kind::S_201_compound_proof: // compound-proof
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
      case symbol_kind::S_216_14: // @14
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
      case symbol_kind::S_optional_varied_in_reduction_variable_sequence: // optional_varied_in_reduction_variable_sequence
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
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
      case symbol_kind::S_209_optional_result: // optional-result
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
      case symbol_kind::S_200_12: // $@12
      case symbol_kind::S_201_compound_proof: // compound-proof
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
      case symbol_kind::S_216_14: // @14
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
      case symbol_kind::S_optional_varied_in_reduction_variable_sequence: // optional_varied_in_reduction_variable_sequence
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
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
      case symbol_kind::S_209_optional_result: // optional-result
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
      case symbol_kind::S_200_12: // $@12
      case symbol_kind::S_201_compound_proof: // compound-proof
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
      case symbol_kind::S_216_14: // @14
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
      case symbol_kind::S_optional_varied_in_reduction_variable_sequence: // optional_varied_in_reduction_variable_sequence
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
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
      case symbol_kind::S_209_optional_result: // optional-result
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
      case symbol_kind::S_200_12: // $@12
      case symbol_kind::S_201_compound_proof: // compound-proof
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
      case symbol_kind::S_216_14: // @14
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
      case symbol_kind::S_optional_varied_in_reduction_variable_sequence: // optional_varied_in_reduction_variable_sequence
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
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
      case symbol_kind::S_209_optional_result: // optional-result
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
      case symbol_kind::S_200_12: // $@12
      case symbol_kind::S_201_compound_proof: // compound-proof
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
      case symbol_kind::S_216_14: // @14
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
      case symbol_kind::S_optional_varied_in_reduction_variable_sequence: // optional_varied_in_reduction_variable_sequence
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
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
      case symbol_kind::S_209_optional_result: // optional-result
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
#line 35 "../../mli-root/src/database-parser.yy"
{
  yyla.location.initialize(&infile_name); // Initialize the initial location.
}

#line 2023 "../../mli-root/src/database-parser.cc"


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
      case symbol_kind::S_200_12: // $@12
      case symbol_kind::S_201_compound_proof: // compound-proof
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
      case symbol_kind::S_216_14: // @14
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
      case symbol_kind::S_optional_varied_in_reduction_variable_sequence: // optional_varied_in_reduction_variable_sequence
      case symbol_kind::S_varied_in_reduction_variable_conclusions: // varied_in_reduction_variable_conclusions
      case symbol_kind::S_varied_in_reduction_variable_conclusion: // varied_in_reduction_variable_conclusion
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
      case symbol_kind::S_209_optional_result: // optional-result
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
#line 782 "../../mli-root/src/database-parser.yy"
           {}
#line 2386 "../../mli-root/src/database-parser.cc"
    break;

  case 3: // file: file_contents
#line 783 "../../mli-root/src/database-parser.yy"
                  {}
#line 2392 "../../mli-root/src/database-parser.cc"
    break;

  case 4: // file: error
#line 784 "../../mli-root/src/database-parser.yy"
          {
      declaration_context = false;
      bound_variable_type = free_variable_context;
      YYABORT;
    }
#line 2402 "../../mli-root/src/database-parser.cc"
    break;

  case 5: // file_contents: file_contents command
#line 793 "../../mli-root/src/database-parser.yy"
                          {}
#line 2408 "../../mli-root/src/database-parser.cc"
    break;

  case 6: // file_contents: command
#line 794 "../../mli-root/src/database-parser.yy"
                          {}
#line 2414 "../../mli-root/src/database-parser.cc"
    break;

  case 7: // $@1: %empty
#line 799 "../../mli-root/src/database-parser.yy"
    { symbol_table.clear(); }
#line 2420 "../../mli-root/src/database-parser.cc"
    break;

  case 8: // command: $@1 theory
#line 799 "../../mli-root/src/database-parser.yy"
                                     {}
#line 2426 "../../mli-root/src/database-parser.cc"
    break;

  case 9: // metaformula_substitution_sequence: substitution_for_metaformula
#line 804 "../../mli-root/src/database-parser.yy"
                                    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2432 "../../mli-root/src/database-parser.cc"
    break;

  case 10: // metaformula_substitution_sequence: metaformula_substitution_sequence substitution_for_metaformula
#line 805 "../../mli-root/src/database-parser.yy"
                                                                         {
      yylhs.value.as < ref6<unit> > () =  val<substitution>(yystack_[1].value.as < ref6<unit> > ()) * val<substitution>(yystack_[0].value.as < ref6<unit> > ());
    }
#line 2440 "../../mli-root/src/database-parser.cc"
    break;

  case 11: // substitution_for_metaformula: metaformula_substitution
#line 812 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2446 "../../mli-root/src/database-parser.cc"
    break;

  case 12: // substitution_for_metaformula: formula_substitution
#line 813 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2452 "../../mli-root/src/database-parser.cc"
    break;

  case 13: // substitution_for_metaformula: term_substitution
#line 814 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2458 "../../mli-root/src/database-parser.cc"
    break;

  case 14: // metaformula_substitution: "[" "metaformula variable" "⤇" metaformula "]"
#line 819 "../../mli-root/src/database-parser.yy"
                                                       {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2468 "../../mli-root/src/database-parser.cc"
    break;

  case 15: // formula_substitution_sequence: substitution_for_formula
#line 828 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2474 "../../mli-root/src/database-parser.cc"
    break;

  case 16: // formula_substitution_sequence: formula_substitution_sequence substitution_for_formula
#line 829 "../../mli-root/src/database-parser.yy"
                                                                 {
      yylhs.value.as < ref6<unit> > () = val<substitution>(yystack_[1].value.as < ref6<unit> > ()) * val<substitution>(yystack_[0].value.as < ref6<unit> > ());
    }
#line 2482 "../../mli-root/src/database-parser.cc"
    break;

  case 17: // substitution_for_formula: formula_substitution
#line 836 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2488 "../../mli-root/src/database-parser.cc"
    break;

  case 18: // substitution_for_formula: term_substitution
#line 837 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2494 "../../mli-root/src/database-parser.cc"
    break;

  case 19: // formula_substitution: "[" "object formula variable" "⤇" object_formula "]"
#line 842 "../../mli-root/src/database-parser.yy"
                                                             {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2504 "../../mli-root/src/database-parser.cc"
    break;

  case 20: // formula_substitution: "[" "predicate variable" "⤇" predicate "]"
#line 847 "../../mli-root/src/database-parser.yy"
                                                   {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2514 "../../mli-root/src/database-parser.cc"
    break;

  case 21: // formula_substitution: "[" "atom variable" "⤇" "atom constant" "]"
#line 852 "../../mli-root/src/database-parser.yy"
                                                  {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2524 "../../mli-root/src/database-parser.cc"
    break;

  case 22: // term_substitution_sequence: term_substitution
#line 861 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2530 "../../mli-root/src/database-parser.cc"
    break;

  case 23: // term_substitution_sequence: term_substitution_sequence term_substitution
#line 862 "../../mli-root/src/database-parser.yy"
                                                       {
      yylhs.value.as < ref6<unit> > () = val<substitution>(yystack_[1].value.as < ref6<unit> > ()) * val<substitution>(yystack_[0].value.as < ref6<unit> > ());
    }
#line 2538 "../../mli-root/src/database-parser.cc"
    break;

  case 24: // term_substitution: "[" term_identifier "⤇" term "]"
#line 869 "../../mli-root/src/database-parser.yy"
                                           {
      val<variable> v(yystack_[3].value.as < ref6<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2548 "../../mli-root/src/database-parser.cc"
    break;

  case 25: // predicate_function_application: "(" "object variable" "↦" object_formula ")" tuple
#line 878 "../../mli-root/src/database-parser.yy"
                                                              {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[4].value.as < val<unit> > (), yystack_[2].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2556 "../../mli-root/src/database-parser.cc"
    break;

  case 26: // $@2: %empty
#line 881 "../../mli-root/src/database-parser.yy"
                                                           { symbol_table.pop_level(); }
#line 2562 "../../mli-root/src/database-parser.cc"
    break;

  case 27: // predicate_function_application: "(" "𝛌" "function map variable" "↦" object_formula $@2 ")" tuple
#line 881 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[5].value.as < val<unit> > (), yystack_[3].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2570 "../../mli-root/src/database-parser.cc"
    break;

  case 28: // predicate_function_application: "predicate" tuple
#line 884 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = val<function_application>(make, yystack_[1].value.as < val<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 2576 "../../mli-root/src/database-parser.cc"
    break;

  case 29: // term_function_application: "(" "object variable" "↦" term ")" tuple
#line 889 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[4].value.as < val<unit> > (), yystack_[2].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2584 "../../mli-root/src/database-parser.cc"
    break;

  case 30: // $@3: %empty
#line 892 "../../mli-root/src/database-parser.yy"
                                                 { symbol_table.pop_level(); }
#line 2590 "../../mli-root/src/database-parser.cc"
    break;

  case 31: // term_function_application: "(" "𝛌" "function map variable" "↦" term $@3 ")" tuple
#line 892 "../../mli-root/src/database-parser.yy"
                                                                                            {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[5].value.as < val<unit> > (), yystack_[3].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2598 "../../mli-root/src/database-parser.cc"
    break;

  case 32: // term_function_application: "function" tuple
#line 895 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.as < ref6<unit> > () = val<function_application>(make, yystack_[1].value.as < val<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 2604 "../../mli-root/src/database-parser.cc"
    break;

  case 33: // $@4: %empty
#line 901 "../../mli-root/src/database-parser.yy"
        { theory_ = ref1<theory>(make, yystack_[1].value.as < std::string > ());
          yypval.insert(theory_);
          symbol_table.push_level();
    }
#line 2613 "../../mli-root/src/database-parser.cc"
    break;

  case 34: // theory: "theory" statement_name "." $@4 include_theories theory_body "end" "theory" end_theory_name "."
#line 907 "../../mli-root/src/database-parser.yy"
                                          {
      if (yystack_[1].value.as < std::pair<std::string, bool> > ().second && yystack_[8].value.as < std::string > () != yystack_[1].value.as < std::pair<std::string, bool> > ().first) {
        database_parser::error(yystack_[1].location, "warning: Name mismatch, theory " + yystack_[8].value.as < std::string > ()
          + ", end theory " + yystack_[1].value.as < std::pair<std::string, bool> > ().first + ".");
      }

      symbol_table.pop_level();
    }
#line 2626 "../../mli-root/src/database-parser.cc"
    break;

  case 35: // end_theory_name: %empty
#line 919 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < std::pair<std::string, bool> > () = std::make_pair(std::string{}, false); }
#line 2632 "../../mli-root/src/database-parser.cc"
    break;

  case 36: // end_theory_name: statement_name
#line 920 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < std::pair<std::string, bool> > () = std::make_pair(yystack_[0].value.as < std::string > (), true); }
#line 2638 "../../mli-root/src/database-parser.cc"
    break;

  case 37: // include_theories: %empty
#line 925 "../../mli-root/src/database-parser.yy"
           {}
#line 2644 "../../mli-root/src/database-parser.cc"
    break;

  case 38: // include_theories: include_theories include_theory
#line 926 "../../mli-root/src/database-parser.yy"
                                    {}
#line 2650 "../../mli-root/src/database-parser.cc"
    break;

  case 39: // include_theory: "include" "theory" theory_name "."
#line 930 "../../mli-root/src/database-parser.yy"
                                         {
      std::optional<ref1<theory>> th = yypval.find(yystack_[1].value.as < std::string > ());

      if (!th)
        throw syntax_error(yystack_[1].location, "Include theory " + yystack_[1].value.as < std::string > () + " not found.");

      theory_->insert(*th);
    }
#line 2663 "../../mli-root/src/database-parser.cc"
    break;

  case 40: // theory_name: "name"
#line 942 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2669 "../../mli-root/src/database-parser.cc"
    break;

  case 41: // theory_name: "label"
#line 943 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2675 "../../mli-root/src/database-parser.cc"
    break;

  case 42: // theory_body: theory_body_list
#line 948 "../../mli-root/src/database-parser.yy"
                     {}
#line 2681 "../../mli-root/src/database-parser.cc"
    break;

  case 43: // theory_body: formal_system theory_body_list
#line 949 "../../mli-root/src/database-parser.yy"
                                   {}
#line 2687 "../../mli-root/src/database-parser.cc"
    break;

  case 44: // $@5: %empty
#line 955 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(); }
#line 2693 "../../mli-root/src/database-parser.cc"
    break;

  case 45: // formal_system: "system" "name" "{" $@5 formal_system_body "}"
#line 957 "../../mli-root/src/database-parser.yy"
        { symbol_table.pop_level(); }
#line 2699 "../../mli-root/src/database-parser.cc"
    break;

  case 46: // $@6: %empty
#line 959 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(); }
#line 2705 "../../mli-root/src/database-parser.cc"
    break;

  case 47: // formal_system: "formal system" "." $@6 formal_system_body "end" "formal system" "."
#line 961 "../../mli-root/src/database-parser.yy"
                              { symbol_table.pop_level(); }
#line 2711 "../../mli-root/src/database-parser.cc"
    break;

  case 48: // formal_system_body: %empty
#line 966 "../../mli-root/src/database-parser.yy"
           {}
#line 2717 "../../mli-root/src/database-parser.cc"
    break;

  case 49: // formal_system_body: formal_system_body formal_system_body_item
#line 967 "../../mli-root/src/database-parser.yy"
                                               {}
#line 2723 "../../mli-root/src/database-parser.cc"
    break;

  case 50: // formal_system_body_item: identifier_declaration
#line 972 "../../mli-root/src/database-parser.yy"
                           {}
#line 2729 "../../mli-root/src/database-parser.cc"
    break;

  case 51: // formal_system_body_item: postulate
#line 973 "../../mli-root/src/database-parser.yy"
                 { theory_->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 2735 "../../mli-root/src/database-parser.cc"
    break;

  case 52: // formal_system_body_item: definition_labelstatement
#line 974 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref4<statement>(yystack_[0].value.as < val<definition> > ())); }
#line 2741 "../../mli-root/src/database-parser.cc"
    break;

  case 53: // theory_body_list: %empty
#line 979 "../../mli-root/src/database-parser.yy"
           {}
#line 2747 "../../mli-root/src/database-parser.cc"
    break;

  case 54: // theory_body_list: theory_body_list theory_body_item
#line 980 "../../mli-root/src/database-parser.yy"
                                      {}
#line 2753 "../../mli-root/src/database-parser.cc"
    break;

  case 55: // theory_body_item: theorem
#line 990 "../../mli-root/src/database-parser.yy"
               { theory_->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 2759 "../../mli-root/src/database-parser.cc"
    break;

  case 56: // theory_body_item: identifier_declaration
#line 991 "../../mli-root/src/database-parser.yy"
                           {}
#line 2765 "../../mli-root/src/database-parser.cc"
    break;

  case 57: // theory_body_item: conjecture
#line 992 "../../mli-root/src/database-parser.yy"
                  { theory_->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 2771 "../../mli-root/src/database-parser.cc"
    break;

  case 58: // theory_body_item: definition_labelstatement
#line 994 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref4<statement>(yystack_[0].value.as < val<definition> > ())); }
#line 2777 "../../mli-root/src/database-parser.cc"
    break;

  case 59: // $@7: %empty
#line 1000 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2783 "../../mli-root/src/database-parser.cc"
    break;

  case 60: // postulate: "postulate" statement_name "." $@7 statement "."
#line 1001 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::postulate_, yystack_[4].value.as < std::string > (), yystack_[1].value.as < ref6<unit> > (), true);
    }
#line 2792 "../../mli-root/src/database-parser.cc"
    break;

  case 61: // postulate: conjecture
#line 1005 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2798 "../../mli-root/src/database-parser.cc"
    break;

  case 62: // $@8: %empty
#line 1007 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2804 "../../mli-root/src/database-parser.cc"
    break;

  case 63: // postulate: "axiom" statement_name "." $@8 statement "."
#line 1008 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      val<formula> f(yystack_[1].value.as < ref6<unit> > ());

      if (!f->is_axiom())
        throw syntax_error(yystack_[1].location, "Axiom statement not an object formula.");

      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::postulate_, yystack_[4].value.as < std::string > (), f);
    }
#line 2819 "../../mli-root/src/database-parser.cc"
    break;

  case 64: // $@9: %empty
#line 1019 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2825 "../../mli-root/src/database-parser.cc"
    break;

  case 65: // postulate: "rule" statement_name "." $@9 statement "."
#line 1020 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      val<formula> f(yystack_[1].value.as < ref6<unit> > ());

      if (!f->is_rule())
        throw syntax_error(yystack_[1].location, "Rule statement not an inference.");

      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::postulate_, yystack_[4].value.as < std::string > (), f);
    }
#line 2840 "../../mli-root/src/database-parser.cc"
    break;

  case 66: // $@10: %empty
#line 1035 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2846 "../../mli-root/src/database-parser.cc"
    break;

  case 67: // conjecture: "conjecture" statement_name "." $@10 statement "."
#line 1036 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::conjecture_, yystack_[4].value.as < std::string > (), yystack_[1].value.as < ref6<unit> > (), true);
    }
#line 2855 "../../mli-root/src/database-parser.cc"
    break;

  case 68: // $@11: %empty
#line 1044 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2861 "../../mli-root/src/database-parser.cc"
    break;

  case 69: // definition_labelstatement: "definition" statement_name "." $@11 definition_statement "."
#line 1045 "../../mli-root/src/database-parser.yy"
                                {
      symbol_table.pop_level();
      yylhs.value.as < val<definition> > () = val<definition>(make, yystack_[4].value.as < std::string > (), yystack_[1].value.as < ref6<unit> > ());
    }
#line 2870 "../../mli-root/src/database-parser.cc"
    break;

  case 70: // statement_name: "name"
#line 1053 "../../mli-root/src/database-parser.yy"
              { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2876 "../../mli-root/src/database-parser.cc"
    break;

  case 71: // statement_name: "label"
#line 1054 "../../mli-root/src/database-parser.yy"
               { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2882 "../../mli-root/src/database-parser.cc"
    break;

  case 72: // statement_name: "natural number value"
#line 1055 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < std::string > () = yystack_[0].value.as < std::pair<std::string, integer> > ().first; }
#line 2888 "../../mli-root/src/database-parser.cc"
    break;

  case 73: // theorem: theorem_statement proof
#line 1060 "../../mli-root/src/database-parser.yy"
                            {
      yylhs.value.as < ref6<unit> > () = statement_stack_.back();
      ref4<statement> t(yylhs.value.as < ref6<unit> > ()); // The theorem.
      t->prove(proof_count);     // Attempt to prove the theorem.
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
#line 2900 "../../mli-root/src/database-parser.cc"
    break;

  case 74: // theorem_statement: theorem_head statement
#line 1071 "../../mli-root/src/database-parser.yy"
                                 {
      symbol_table_t::table& top = symbol_table.top();
      val<theorem> tr(make,  yystack_[1].value.as < std::pair<theorem::type, std::string> > ().first, yystack_[1].value.as < std::pair<theorem::type, std::string> > ().second, yystack_[0].value.as < ref6<unit> > (), theory_, proof_depth);
      statement_stack_.back() = tr;
      theorem_theory_ = tr->get_theory();
    }
#line 2911 "../../mli-root/src/database-parser.cc"
    break;

  case 75: // theorem_head: "theorem" statement_name "."
#line 1081 "../../mli-root/src/database-parser.yy"
                                       {
      yylhs.value.as < std::pair<theorem::type, std::string> > ().second = yystack_[1].value.as < std::string > ();
      yylhs.value.as < std::pair<theorem::type, std::string> > ().first = yystack_[2].value.as < theorem::type > ();
      symbol_table.push_level();
      statement_stack_.push_back(ref4<statement>());
    }
#line 2922 "../../mli-root/src/database-parser.cc"
    break;

  case 76: // proof: compound-proof
#line 1091 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2928 "../../mli-root/src/database-parser.cc"
    break;

  case 77: // $@12: %empty
#line 1092 "../../mli-root/src/database-parser.yy"
                {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 2938 "../../mli-root/src/database-parser.cc"
    break;

  case 78: // proof: $@12 proof_of_conclusion
#line 1097 "../../mli-root/src/database-parser.yy"
                        {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 2948 "../../mli-root/src/database-parser.cc"
    break;

  case 79: // compound-proof: proof_head proof_lines "∎"
#line 1106 "../../mli-root/src/database-parser.yy"
                               {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 2958 "../../mli-root/src/database-parser.cc"
    break;

  case 80: // compound-proof: "∎"
#line 1111 "../../mli-root/src/database-parser.yy"
        {}
#line 2964 "../../mli-root/src/database-parser.cc"
    break;

  case 81: // proof_head: "proof"
#line 1116 "../../mli-root/src/database-parser.yy"
            {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 2974 "../../mli-root/src/database-parser.cc"
    break;

  case 82: // proof_lines: %empty
#line 1125 "../../mli-root/src/database-parser.yy"
           {}
#line 2980 "../../mli-root/src/database-parser.cc"
    break;

  case 83: // proof_lines: proof_lines proof_line
#line 1126 "../../mli-root/src/database-parser.yy"
                           {}
#line 2986 "../../mli-root/src/database-parser.cc"
    break;

  case 84: // statement_label: statement_name "."
#line 1131 "../../mli-root/src/database-parser.yy"
                          {
      yylhs.value.as < std::string > () = yystack_[1].value.as < std::string > ();
      symbol_table.push_level();
    }
#line 2995 "../../mli-root/src/database-parser.cc"
    break;

  case 85: // proof_line: statement_label statement "by" find_statement "."
#line 1139 "../../mli-root/src/database-parser.yy"
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
#line 3030 "../../mli-root/src/database-parser.cc"
    break;

  case 86: // proof_line: subproof_statement compound-proof
#line 1170 "../../mli-root/src/database-parser.yy"
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
#line 3049 "../../mli-root/src/database-parser.cc"
    break;

  case 87: // $@13: %empty
#line 1185 "../../mli-root/src/database-parser.yy"
    {}
#line 3055 "../../mli-root/src/database-parser.cc"
    break;

  case 88: // proof_line: $@13 identifier_declaration
#line 1185 "../../mli-root/src/database-parser.yy"
                              {}
#line 3061 "../../mli-root/src/database-parser.cc"
    break;

  case 89: // proof_line: definition_labelstatement
#line 1189 "../../mli-root/src/database-parser.yy"
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
#line 3077 "../../mli-root/src/database-parser.cc"
    break;

  case 90: // proof_line: proof_of_conclusion
#line 1200 "../../mli-root/src/database-parser.yy"
                        {}
#line 3083 "../../mli-root/src/database-parser.cc"
    break;

  case 91: // subproof_statement: statement_label statement
#line 1205 "../../mli-root/src/database-parser.yy"
                                    {
      yylhs.value.as < std::string > () = yystack_[1].value.as < std::string > ();
      symbol_table_t::table& top = symbol_table.top();
      val<theorem> tp(make, theorem::claim_, yystack_[1].value.as < std::string > (), yystack_[0].value.as < ref6<unit> > (), theory_, proof_depth);
      statement_stack_.push_back(tp);
    }
#line 3094 "../../mli-root/src/database-parser.cc"
    break;

  case 92: // proof_of_conclusion: optional-result "by" find_statement "."
#line 1215 "../../mli-root/src/database-parser.yy"
                                                  {
      proofline_database_context = false;

      theorem& t = dyn_cast<theorem&>(statement_stack_.back());
      ref4<statement> proof_line =
        t.push_back(yystack_[3].value.as < std::string > (), t.get_formula(), val<database>(yystack_[1].value.as < ref6<unit> > ()), true, proof_depth);
    }
#line 3106 "../../mli-root/src/database-parser.cc"
    break;

  case 93: // optional-result: %empty
#line 1226 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < std::string > () = "result"; }
#line 3112 "../../mli-root/src/database-parser.cc"
    break;

  case 94: // optional-result: "result"
#line 1227 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 3118 "../../mli-root/src/database-parser.cc"
    break;

  case 95: // find_statement: find_statement_list
#line 1232 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = ref5<level_database>(make, val<database>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3124 "../../mli-root/src/database-parser.cc"
    break;

  case 96: // find_statement: find_statement ":" find_statement_list
#line 1233 "../../mli-root/src/database-parser.yy"
                                                 {
      ref5<level_database>(yystack_[2].value.as < ref6<unit> > ())->push_back(val<database>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3133 "../../mli-root/src/database-parser.cc"
    break;

  case 97: // find_statement_list: find_statement_sequence
#line 1241 "../../mli-root/src/database-parser.yy"
                               {
      yylhs.value.as < ref6<unit> > () = ref3<sublevel_database>(make, ref2<sequence_database>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3141 "../../mli-root/src/database-parser.cc"
    break;

  case 98: // find_statement_list: find_statement_list ";" find_statement_sequence
#line 1244 "../../mli-root/src/database-parser.yy"
                                                          {
      ref3<sublevel_database>(yystack_[2].value.as < ref6<unit> > ())->push_back(val<database>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3150 "../../mli-root/src/database-parser.cc"
    break;

  case 99: // find_statement_sequence: %empty
#line 1252 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make); }
#line 3156 "../../mli-root/src/database-parser.cc"
    break;

  case 100: // find_statement_sequence: find_statement_item
#line 1253 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make, ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3163 "../../mli-root/src/database-parser.cc"
    break;

  case 101: // find_statement_sequence: find_statement_item "₍" find_definition_sequence "₎"
#line 1255 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make, ref4<statement>(yystack_[3].value.as < ref6<unit> > ()));
      ref2<sequence_database>(yylhs.value.as < ref6<unit> > ())->insert(ref2<sequence_database>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 3172 "../../mli-root/src/database-parser.cc"
    break;

  case 102: // find_statement_sequence: find_statement_sequence "," find_statement_item
#line 1259 "../../mli-root/src/database-parser.yy"
                                                          {
      ref2<sequence_database>(yystack_[2].value.as < ref6<unit> > ())->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3181 "../../mli-root/src/database-parser.cc"
    break;

  case 103: // find_statement_sequence: find_statement_sequence "," find_statement_item "₍" find_definition_sequence "₎"
#line 1263 "../../mli-root/src/database-parser.yy"
                                                                                              {
      yylhs.value.as < ref6<unit> > () = yystack_[5].value.as < ref6<unit> > ();
      ref2<sequence_database>(yylhs.value.as < ref6<unit> > ())->insert(ref4<statement>(yystack_[3].value.as < ref6<unit> > ()));
      ref2<sequence_database>(yylhs.value.as < ref6<unit> > ())->insert(ref2<sequence_database>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 3191 "../../mli-root/src/database-parser.cc"
    break;

  case 104: // find_definition_sequence: find_statement_item
#line 1272 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make, ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3198 "../../mli-root/src/database-parser.cc"
    break;

  case 105: // find_definition_sequence: find_definition_sequence "," find_statement_item
#line 1274 "../../mli-root/src/database-parser.yy"
                                                           {
      ref2<sequence_database>(yystack_[2].value.as < ref6<unit> > ())->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3207 "../../mli-root/src/database-parser.cc"
    break;

  case 106: // find_statement_item: find_statement_name
#line 1282 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();
    }
#line 3215 "../../mli-root/src/database-parser.cc"
    break;

  case 107: // find_statement_item: "premise"
#line 1285 "../../mli-root/src/database-parser.yy"
              {
      yylhs.value.as < ref6<unit> > () = val<premise>(make, statement_stack_.back());
    }
#line 3223 "../../mli-root/src/database-parser.cc"
    break;

  case 108: // find_statement_item: "premise" statement_name
#line 1288 "../../mli-root/src/database-parser.yy"
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
#line 3241 "../../mli-root/src/database-parser.cc"
    break;

  case 109: // find_statement_item: "premise" statement_name "subscript natural number value"
#line 1301 "../../mli-root/src/database-parser.yy"
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
#line 3260 "../../mli-root/src/database-parser.cc"
    break;

  case 110: // find_statement_item: "premise" "⊢"
#line 1315 "../../mli-root/src/database-parser.yy"
                  {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      yylhs.value.as < ref6<unit> > () = val<premise>(make);
    }
#line 3270 "../../mli-root/src/database-parser.cc"
    break;

  case 111: // find_statement_item: "premise" "⊢" "subscript natural number value"
#line 1320 "../../mli-root/src/database-parser.yy"
                                                    {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      size_type k = (size_type)yystack_[0].value.as < integer > ();
      yylhs.value.as < ref6<unit> > () = val<premise>(make, k);
    }
#line 3281 "../../mli-root/src/database-parser.cc"
    break;

  case 112: // find_statement_name: statement_name
#line 1330 "../../mli-root/src/database-parser.yy"
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
#line 3300 "../../mli-root/src/database-parser.cc"
    break;

  case 113: // @14: %empty
#line 1344 "../../mli-root/src/database-parser.yy"
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
#line 3327 "../../mli-root/src/database-parser.cc"
    break;

  case 114: // find_statement_name: statement_name @14 metaformula_substitution_sequence
#line 1367 "../../mli-root/src/database-parser.yy"
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
#line 3347 "../../mli-root/src/database-parser.cc"
    break;

  case 115: // statement: metaformula
#line 1386 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.as < ref6<unit> > () = dyn_cast<formula&>(yystack_[0].value.as < ref6<unit> > ()).set_bind(); }
#line 3353 "../../mli-root/src/database-parser.cc"
    break;

  case 116: // statement: identifier_declaration metaformula
#line 1387 "../../mli-root/src/database-parser.yy"
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
#line 3398 "../../mli-root/src/database-parser.cc"
    break;

  case 117: // definition_statement: definition
#line 1431 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < ref6<unit> > () = dyn_cast<formula&>(yystack_[0].value.as < ref6<unit> > ()).set_bind(); }
#line 3404 "../../mli-root/src/database-parser.cc"
    break;

  case 118: // definition_statement: identifier_declaration definition
#line 1432 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.as < ref6<unit> > () = dyn_cast<formula&>(yystack_[0].value.as < ref6<unit> > ()).set_bind();
    }
#line 3412 "../../mli-root/src/database-parser.cc"
    break;

  case 119: // identifier_declaration: declarator_list "."
#line 1439 "../../mli-root/src/database-parser.yy"
                        {}
#line 3418 "../../mli-root/src/database-parser.cc"
    break;

  case 120: // declarator_list: declarator_identifier_list
#line 1444 "../../mli-root/src/database-parser.yy"
                               {}
#line 3424 "../../mli-root/src/database-parser.cc"
    break;

  case 121: // declarator_list: declarator_list declarator_identifier_list
#line 1445 "../../mli-root/src/database-parser.yy"
                                               {}
#line 3430 "../../mli-root/src/database-parser.cc"
    break;

  case 122: // declarator_identifier_list: "identifier constant" identifier_constant_list
#line 1450 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 3436 "../../mli-root/src/database-parser.cc"
    break;

  case 123: // declarator_identifier_list: "identifier variable" identifier_variable_list
#line 1451 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 3442 "../../mli-root/src/database-parser.cc"
    break;

  case 124: // declarator_identifier_list: "identifier function" identifier_function_list
#line 1452 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 3448 "../../mli-root/src/database-parser.cc"
    break;

  case 125: // identifier_function_list: identifier_function_name
#line 1457 "../../mli-root/src/database-parser.yy"
                             {}
#line 3454 "../../mli-root/src/database-parser.cc"
    break;

  case 126: // identifier_function_list: identifier_function_list "," identifier_function_name
#line 1458 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 3460 "../../mli-root/src/database-parser.cc"
    break;

  case 127: // $@15: %empty
#line 1469 "../../mli-root/src/database-parser.yy"
              { current_declared_token = declared_token; }
#line 3466 "../../mli-root/src/database-parser.cc"
    break;

  case 128: // $@16: %empty
#line 1470 "../../mli-root/src/database-parser.yy"
        { bound_variable_type = database_parser::token::function_map_variable; }
#line 3472 "../../mli-root/src/database-parser.cc"
    break;

  case 129: // identifier_function_name: "name" $@15 ":" $@16 "function map variable" "↦" object_formula
#line 1471 "../../mli-root/src/database-parser.yy"
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
#line 3488 "../../mli-root/src/database-parser.cc"
    break;

  case 130: // identifier_constant_list: identifier_constant_name
#line 1504 "../../mli-root/src/database-parser.yy"
                             {}
#line 3494 "../../mli-root/src/database-parser.cc"
    break;

  case 131: // identifier_constant_list: identifier_constant_list "," identifier_constant_name
#line 1505 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 3500 "../../mli-root/src/database-parser.cc"
    break;

  case 132: // identifier_constant_name: "name"
#line 1510 "../../mli-root/src/database-parser.yy"
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
#line 3516 "../../mli-root/src/database-parser.cc"
    break;

  case 133: // identifier_variable_list: identifier_variable_name
#line 1525 "../../mli-root/src/database-parser.yy"
                             {}
#line 3522 "../../mli-root/src/database-parser.cc"
    break;

  case 134: // identifier_variable_list: identifier_variable_list "," identifier_variable_name
#line 1526 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 3528 "../../mli-root/src/database-parser.cc"
    break;

  case 135: // identifier_variable_name: "name"
#line 1531 "../../mli-root/src/database-parser.yy"
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
#line 3544 "../../mli-root/src/database-parser.cc"
    break;

  case 136: // identifier_variable_name: "°" "name"
#line 1542 "../../mli-root/src/database-parser.yy"
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
#line 3560 "../../mli-root/src/database-parser.cc"
    break;

  case 137: // identifier_variable_name: "•" "name"
#line 1553 "../../mli-root/src/database-parser.yy"
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
#line 3576 "../../mli-root/src/database-parser.cc"
    break;

  case 138: // definition: metaformula_definition
#line 1568 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3582 "../../mli-root/src/database-parser.cc"
    break;

  case 139: // definition: object_formula_definition
#line 1569 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3588 "../../mli-root/src/database-parser.cc"
    break;

  case 140: // definition: term_definition
#line 1570 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3594 "../../mli-root/src/database-parser.cc"
    break;

  case 141: // metaformula_definition: pure_metaformula "≔" pure_metaformula
#line 1575 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(),
        formula::logic, formula_definition_oprec);
    }
#line 3603 "../../mli-root/src/database-parser.cc"
    break;

  case 142: // metaformula_definition: pure_metaformula "≕" pure_metaformula
#line 1579 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(),
       formula::logic, formula_definition_oprec);
  }
#line 3612 "../../mli-root/src/database-parser.cc"
    break;

  case 143: // object_formula_definition: object_formula "≔" object_formula
#line 1592 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(),
        formula::logic, formula_definition_oprec);
    }
#line 3621 "../../mli-root/src/database-parser.cc"
    break;

  case 144: // object_formula_definition: object_formula "≕" object_formula
#line 1596 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(),
        formula::logic, formula_definition_oprec);
  }
#line 3630 "../../mli-root/src/database-parser.cc"
    break;

  case 145: // term_definition: term "≔" term
#line 1609 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(),
        formula::object, term_definition_oprec);
    }
#line 3639 "../../mli-root/src/database-parser.cc"
    break;

  case 146: // term_definition: term "≕" term
#line 1619 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(),
        formula::object, term_definition_oprec);
  }
#line 3648 "../../mli-root/src/database-parser.cc"
    break;

  case 147: // metaformula: pure_metaformula
#line 1627 "../../mli-root/src/database-parser.yy"
                        { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3654 "../../mli-root/src/database-parser.cc"
    break;

  case 148: // metaformula: object_formula
#line 1628 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3660 "../../mli-root/src/database-parser.cc"
    break;

  case 149: // pure_metaformula: atomic_metaformula
#line 1633 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3666 "../../mli-root/src/database-parser.cc"
    break;

  case 150: // pure_metaformula: special_metaformula
#line 1634 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3672 "../../mli-root/src/database-parser.cc"
    break;

  case 151: // pure_metaformula: "~" metaformula
#line 1635 "../../mli-root/src/database-parser.yy"
                       {
      yylhs.value.as < ref6<unit> > () = val<metanot>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3680 "../../mli-root/src/database-parser.cc"
    break;

  case 152: // pure_metaformula: metaformula ";" metaformula
#line 1638 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.as < ref6<unit> > () = concatenate(val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3688 "../../mli-root/src/database-parser.cc"
    break;

  case 153: // pure_metaformula: metaformula "," metaformula
#line 1641 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.as < ref6<unit> > () = concatenate(val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3696 "../../mli-root/src/database-parser.cc"
    break;

  case 154: // pure_metaformula: metaformula "⊩" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_sequence metaformula
#line 1646 "../../mli-root/src/database-parser.yy"
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
#line 3755 "../../mli-root/src/database-parser.cc"
    break;

  case 155: // pure_metaformula: metaformula "⊢" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_sequence metaformula
#line 1714 "../../mli-root/src/database-parser.yy"
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
#line 3812 "../../mli-root/src/database-parser.cc"
    break;

  case 156: // pure_metaformula: "⊢" metaformula
#line 1773 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = val<inference>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3818 "../../mli-root/src/database-parser.cc"
    break;

  case 157: // pure_metaformula: "(" pure_metaformula ")"
#line 1775 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3824 "../../mli-root/src/database-parser.cc"
    break;

  case 158: // pure_metaformula: simple_metaformula metaformula_substitution_sequence
#line 1776 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.as < ref6<unit> > () = val<substitution_formula>(make, val<substitution>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[1].value.as < ref6<unit> > ())); }
#line 3831 "../../mli-root/src/database-parser.cc"
    break;

  case 159: // optional_varied_variable_matrix: %empty
#line 1782 "../../mli-root/src/database-parser.yy"
           {}
#line 3837 "../../mli-root/src/database-parser.cc"
    break;

  case 160: // optional_varied_variable_matrix: "⁽" varied_variable_conclusions "⁾"
#line 1783 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3843 "../../mli-root/src/database-parser.cc"
    break;

  case 161: // optional_varied_variable_matrix: "⁽" varied_variable_premises "⁾"
#line 1784 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3849 "../../mli-root/src/database-parser.cc"
    break;

  case 162: // optional_varied_variable_matrix: "⁽" varied_variable_set "⁾"
#line 1785 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3855 "../../mli-root/src/database-parser.cc"
    break;

  case 163: // varied_variable_conclusions: varied_variable_conclusion
#line 1789 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3861 "../../mli-root/src/database-parser.cc"
    break;

  case 164: // varied_variable_conclusions: varied_variable_conclusions ";" varied_variable_conclusion
#line 1790 "../../mli-root/src/database-parser.yy"
                                                                      {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& i: x.varied_)
        for (auto& j: i.second)
          xs.varied_[i.first][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3876 "../../mli-root/src/database-parser.cc"
    break;

  case 165: // varied_variable_conclusion: "superscript natural number value" varied_variable_premises
#line 1803 "../../mli-root/src/database-parser.yy"
                                                                     {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_[k].insert(xs.varied_[0].begin(), xs.varied_[0].end());
      yylhs.value.as < ref6<unit> > () = i;

    }
#line 3890 "../../mli-root/src/database-parser.cc"
    break;

  case 166: // varied_variable_premises: varied_variable_premise
#line 1815 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3896 "../../mli-root/src/database-parser.cc"
    break;

  case 167: // varied_variable_premises: varied_variable_premises "," varied_variable_premise
#line 1816 "../../mli-root/src/database-parser.yy"
                                                                {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& j: x.varied_[0])
        xs.varied_[0][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3910 "../../mli-root/src/database-parser.cc"
    break;

  case 168: // varied_variable_premise: "superscript natural number value" varied_variable_set
#line 1828 "../../mli-root/src/database-parser.yy"
                                                                {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_[0][k].insert(xs.varied_[0][0].begin(), xs.varied_[0][0].end());

      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3924 "../../mli-root/src/database-parser.cc"
    break;

  case 169: // varied_variable_set: varied_variable
#line 1840 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3930 "../../mli-root/src/database-parser.cc"
    break;

  case 170: // varied_variable_set: varied_variable_set varied_variable
#line 1841 "../../mli-root/src/database-parser.yy"
                                               {
      inference& xs = dyn_cast<inference&>(yystack_[1].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      xs.varied_[0][0].insert(x.varied_[0][0].begin(), x.varied_[0][0].end());

      yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > ();
    }
#line 3943 "../../mli-root/src/database-parser.cc"
    break;

  case 171: // varied_variable: "object variable"
#line 1852 "../../mli-root/src/database-parser.yy"
                       {
      val<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3953 "../../mli-root/src/database-parser.cc"
    break;

  case 172: // varied_variable: "metaformula variable"
#line 1857 "../../mli-root/src/database-parser.yy"
                            {
      val<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3963 "../../mli-root/src/database-parser.cc"
    break;

  case 173: // optional_varied_in_reduction_variable_sequence: %empty
#line 1867 "../../mli-root/src/database-parser.yy"
           {}
#line 3969 "../../mli-root/src/database-parser.cc"
    break;

  case 174: // optional_varied_in_reduction_variable_sequence: "₍" varied_in_reduction_variable_conclusions "₎"
#line 1868 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3975 "../../mli-root/src/database-parser.cc"
    break;

  case 175: // optional_varied_in_reduction_variable_sequence: "₍" varied_in_reduction_variable_set "₎"
#line 1869 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3981 "../../mli-root/src/database-parser.cc"
    break;

  case 176: // varied_in_reduction_variable_conclusions: varied_in_reduction_variable_conclusion
#line 1873 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3987 "../../mli-root/src/database-parser.cc"
    break;

  case 177: // varied_in_reduction_variable_conclusions: varied_in_reduction_variable_conclusions ";" varied_in_reduction_variable_conclusion
#line 1874 "../../mli-root/src/database-parser.yy"
                                                                                                {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& i: x.varied_in_reduction_)
        xs.varied_in_reduction_[i.first].insert(i.second.begin(), i.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 4001 "../../mli-root/src/database-parser.cc"
    break;

  case 178: // varied_in_reduction_variable_conclusion: "subscript natural number value" varied_in_reduction_variable_set
#line 1886 "../../mli-root/src/database-parser.yy"
                                                                           {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_in_reduction_[k].insert(xs.varied_in_reduction_[0].begin(), xs.varied_in_reduction_[0].end());
      yylhs.value.as < ref6<unit> > () = i;

    }
#line 4015 "../../mli-root/src/database-parser.cc"
    break;

  case 179: // varied_in_reduction_variable_set: varied_in_reduction_variable
#line 1899 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4021 "../../mli-root/src/database-parser.cc"
    break;

  case 180: // varied_in_reduction_variable_set: varied_in_reduction_variable_set varied_in_reduction_variable
#line 1900 "../../mli-root/src/database-parser.yy"
                                                                         {
      inference& xs = dyn_cast<inference&>(yystack_[1].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      xs.varied_in_reduction_[0].insert(x.varied_in_reduction_[0].begin(), x.varied_in_reduction_[0].end());

      yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > ();
    }
#line 4034 "../../mli-root/src/database-parser.cc"
    break;

  case 181: // varied_in_reduction_variable: "object variable"
#line 1911 "../../mli-root/src/database-parser.yy"
                       {
      val<inference> i(make);
      i->varied_in_reduction_[0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 4044 "../../mli-root/src/database-parser.cc"
    break;

  case 182: // varied_in_reduction_variable: "metaformula variable"
#line 1916 "../../mli-root/src/database-parser.yy"
                            {
      val<inference> i(make);
      i->varied_in_reduction_[0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 4054 "../../mli-root/src/database-parser.cc"
    break;

  case 183: // simple_metaformula: "metaformula variable"
#line 1925 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4060 "../../mli-root/src/database-parser.cc"
    break;

  case 184: // simple_metaformula: "(" pure_metaformula ")"
#line 1926 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4066 "../../mli-root/src/database-parser.cc"
    break;

  case 185: // atomic_metaformula: "metaformula variable"
#line 1931 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4072 "../../mli-root/src/database-parser.cc"
    break;

  case 186: // atomic_metaformula: metapredicate
#line 1932 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4078 "../../mli-root/src/database-parser.cc"
    break;

  case 187: // special_metaformula: meta_object_free "≢" meta_object_free
#line 1944 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<objectidentical>(make, val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<variable>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4086 "../../mli-root/src/database-parser.cc"
    break;

  case 188: // special_metaformula: meta_object_free "free in" object_formula
#line 1947 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4094 "../../mli-root/src/database-parser.cc"
    break;

  case 189: // special_metaformula: meta_object_free "free in" term
#line 1950 "../../mli-root/src/database-parser.yy"
                                          {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4102 "../../mli-root/src/database-parser.cc"
    break;

  case 190: // special_metaformula: meta_object_free "not" "free in" object_formula
#line 1953 "../../mli-root/src/database-parser.yy"
                                                          {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[3].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4110 "../../mli-root/src/database-parser.cc"
    break;

  case 191: // special_metaformula: meta_object_free "not" "free in" term
#line 1956 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[3].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4118 "../../mli-root/src/database-parser.cc"
    break;

  case 192: // special_metaformula: term "free for" meta_object_free "in" object_formula
#line 1959 "../../mli-root/src/database-parser.yy"
                                                                  {
      yylhs.value.as < ref6<unit> > () = val<free_for_object>(make, 
        val<formula>(yystack_[4].value.as < ref6<unit> > ()), val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4127 "../../mli-root/src/database-parser.cc"
    break;

  case 193: // special_metaformula: term "free for" meta_object_free "in" term
#line 1963 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.as < ref6<unit> > () = val<free_for_object>(make, 
        val<formula>(yystack_[4].value.as < ref6<unit> > ()), val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4136 "../../mli-root/src/database-parser.cc"
    break;

  case 194: // meta_object_free: "object variable"
#line 1971 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4142 "../../mli-root/src/database-parser.cc"
    break;

  case 195: // metapredicate: metapredicate_function
#line 1976 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4148 "../../mli-root/src/database-parser.cc"
    break;

  case 196: // metapredicate: object_formula "≣" object_formula
#line 1977 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4156 "../../mli-root/src/database-parser.cc"
    break;

  case 197: // metapredicate: object_formula "≣̷" object_formula
#line 1980 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4164 "../../mli-root/src/database-parser.cc"
    break;

  case 198: // metapredicate: term "≣" term
#line 1983 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4172 "../../mli-root/src/database-parser.cc"
    break;

  case 199: // metapredicate: term "≣̷" term
#line 1986 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4180 "../../mli-root/src/database-parser.cc"
    break;

  case 200: // metapredicate_function: "metapredicate constant" metapredicate_argument
#line 1993 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < val<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 4189 "../../mli-root/src/database-parser.cc"
    break;

  case 201: // metapredicate_function: "metaformula variable" metapredicate_argument
#line 1997 "../../mli-root/src/database-parser.yy"
                                                      {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < val<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 4198 "../../mli-root/src/database-parser.cc"
    break;

  case 202: // metapredicate_argument: "(" metapredicate_argument_body ")"
#line 2005 "../../mli-root/src/database-parser.yy"
                                           { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4204 "../../mli-root/src/database-parser.cc"
    break;

  case 203: // metapredicate_argument_body: object_formula
#line 2010 "../../mli-root/src/database-parser.yy"
                      {
      ref0<sequence> vr(make, sequence::tuple);
      yylhs.value.as < ref6<unit> > () = vr;
      vr->push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 4213 "../../mli-root/src/database-parser.cc"
    break;

  case 204: // metapredicate_argument_body: metapredicate_argument_body "," object_formula
#line 2014 "../../mli-root/src/database-parser.yy"
                                                         {
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
      sequence& vr = dyn_cast<sequence&>(yylhs.value.as < ref6<unit> > ());
      vr.push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 4222 "../../mli-root/src/database-parser.cc"
    break;

  case 205: // object_formula: atomic_formula
#line 2022 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4228 "../../mli-root/src/database-parser.cc"
    break;

  case 206: // object_formula: very_simple_formula formula_substitution_sequence
#line 2023 "../../mli-root/src/database-parser.yy"
                                                            {
      yylhs.value.as < ref6<unit> > () = val<substitution_formula>(make, val<substitution>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 4236 "../../mli-root/src/database-parser.cc"
    break;

  case 207: // object_formula: predicate_function_application
#line 2026 "../../mli-root/src/database-parser.yy"
                                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4242 "../../mli-root/src/database-parser.cc"
    break;

  case 208: // object_formula: logic_formula
#line 2027 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4248 "../../mli-root/src/database-parser.cc"
    break;

  case 209: // object_formula: "(" object_formula ")"
#line 2028 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4254 "../../mli-root/src/database-parser.cc"
    break;

  case 210: // object_formula: quantized_formula
#line 2029 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4260 "../../mli-root/src/database-parser.cc"
    break;

  case 211: // object_formula: hoare_triple
#line 2030 "../../mli-root/src/database-parser.yy"
                 {}
#line 4266 "../../mli-root/src/database-parser.cc"
    break;

  case 212: // hoare_triple: "{" object_formula "}" code_sequence "{" object_formula "}"
#line 2035 "../../mli-root/src/database-parser.yy"
                                                              { yylhs.value.as < ref6<unit> > () = val<formula>(); }
#line 4272 "../../mli-root/src/database-parser.cc"
    break;

  case 213: // code_statement: code_term
#line 2046 "../../mli-root/src/database-parser.yy"
              {}
#line 4278 "../../mli-root/src/database-parser.cc"
    break;

  case 214: // code_statement: "{" code_sequence "}"
#line 2047 "../../mli-root/src/database-parser.yy"
                          {}
#line 4284 "../../mli-root/src/database-parser.cc"
    break;

  case 215: // code_sequence: %empty
#line 2052 "../../mli-root/src/database-parser.yy"
           {}
#line 4290 "../../mli-root/src/database-parser.cc"
    break;

  case 216: // code_sequence: code_term
#line 2053 "../../mli-root/src/database-parser.yy"
              {}
#line 4296 "../../mli-root/src/database-parser.cc"
    break;

  case 217: // code_sequence: code_sequence ";" code_term
#line 2054 "../../mli-root/src/database-parser.yy"
                                {}
#line 4302 "../../mli-root/src/database-parser.cc"
    break;

  case 218: // code_term: "code variable"
#line 2059 "../../mli-root/src/database-parser.yy"
                 {}
#line 4308 "../../mli-root/src/database-parser.cc"
    break;

  case 219: // code_term: "∅"
#line 2060 "../../mli-root/src/database-parser.yy"
       {}
#line 4314 "../../mli-root/src/database-parser.cc"
    break;

  case 220: // code_term: "object variable" "≔" term
#line 2061 "../../mli-root/src/database-parser.yy"
                            {}
#line 4320 "../../mli-root/src/database-parser.cc"
    break;

  case 221: // code_term: "if" object_formula "then" code_statement "else" code_statement
#line 2062 "../../mli-root/src/database-parser.yy"
                                                                   {}
#line 4326 "../../mli-root/src/database-parser.cc"
    break;

  case 222: // code_term: "while" object_formula "do" code_statement
#line 2063 "../../mli-root/src/database-parser.yy"
                                              {}
#line 4332 "../../mli-root/src/database-parser.cc"
    break;

  case 223: // very_simple_formula: "object formula variable"
#line 2068 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4338 "../../mli-root/src/database-parser.cc"
    break;

  case 224: // very_simple_formula: "atom variable"
#line 2069 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4344 "../../mli-root/src/database-parser.cc"
    break;

  case 225: // very_simple_formula: "(" object_formula ")"
#line 2070 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4350 "../../mli-root/src/database-parser.cc"
    break;

  case 226: // quantized_formula: quantizer_declaration quantized_body
#line 2075 "../../mli-root/src/database-parser.yy"
                                               {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>(yystack_[1].value.as < ref6<unit> > ());
      val<bound_formula> bf(make, vsr, val<formula>(yystack_[0].value.as < ref6<unit> > ()));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      yylhs.value.as < ref6<unit> > () = bf;
    }
#line 4362 "../../mli-root/src/database-parser.cc"
    break;

  case 227: // quantized_formula: quantizer_declaration optional_in_term ":" object_formula
#line 2082 "../../mli-root/src/database-parser.yy"
                                                                       {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>(yystack_[3].value.as < ref6<unit> > ());
      val<bound_formula> bf(make, vsr, yystack_[2].value.as < ref6<unit> > (), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      yylhs.value.as < ref6<unit> > () = bf;
    }
#line 4374 "../../mli-root/src/database-parser.cc"
    break;

  case 228: // quantized_formula: quantizer_declaration optional_in_term quantized_formula
#line 2089 "../../mli-root/src/database-parser.yy"
                                                                      {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>(yystack_[2].value.as < ref6<unit> > ());
      val<bound_formula> bf(make, vsr, yystack_[1].value.as < ref6<unit> > (), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      yylhs.value.as < ref6<unit> > () = bf;
    }
#line 4386 "../../mli-root/src/database-parser.cc"
    break;

  case 229: // simple_formula: "object formula variable"
#line 2100 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4392 "../../mli-root/src/database-parser.cc"
    break;

  case 230: // simple_formula: "atom variable"
#line 2101 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4398 "../../mli-root/src/database-parser.cc"
    break;

  case 231: // simple_formula: predicate_expression
#line 2102 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4404 "../../mli-root/src/database-parser.cc"
    break;

  case 232: // simple_formula: "(" object_formula ")"
#line 2103 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4410 "../../mli-root/src/database-parser.cc"
    break;

  case 233: // simple_formula: quantized_formula
#line 2104 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4416 "../../mli-root/src/database-parser.cc"
    break;

  case 234: // quantized_body: atomic_formula
#line 2110 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4422 "../../mli-root/src/database-parser.cc"
    break;

  case 235: // quantized_body: "(" object_formula ")"
#line 2111 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4428 "../../mli-root/src/database-parser.cc"
    break;

  case 236: // atomic_formula: "atom constant"
#line 2115 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4434 "../../mli-root/src/database-parser.cc"
    break;

  case 237: // atomic_formula: "object formula variable"
#line 2116 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4440 "../../mli-root/src/database-parser.cc"
    break;

  case 238: // atomic_formula: "atom variable"
#line 2117 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4446 "../../mli-root/src/database-parser.cc"
    break;

  case 239: // atomic_formula: predicate
#line 2118 "../../mli-root/src/database-parser.yy"
                 { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4452 "../../mli-root/src/database-parser.cc"
    break;

  case 240: // predicate: predicate_expression
#line 2124 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4458 "../../mli-root/src/database-parser.cc"
    break;

  case 241: // predicate: term "=" term
#line 2125 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4464 "../../mli-root/src/database-parser.cc"
    break;

  case 242: // predicate: term "≠" term
#line 2126 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4470 "../../mli-root/src/database-parser.cc"
    break;

  case 243: // predicate: term "∣" term
#line 2129 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4476 "../../mli-root/src/database-parser.cc"
    break;

  case 244: // predicate: term "∤" term
#line 2130 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4482 "../../mli-root/src/database-parser.cc"
    break;

  case 245: // predicate: term "<" term
#line 2133 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, less_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4488 "../../mli-root/src/database-parser.cc"
    break;

  case 246: // predicate: term ">" term
#line 2134 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, greater_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4494 "../../mli-root/src/database-parser.cc"
    break;

  case 247: // predicate: term "≤" term
#line 2135 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, less_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4500 "../../mli-root/src/database-parser.cc"
    break;

  case 248: // predicate: term "≥" term
#line 2136 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, greater_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4506 "../../mli-root/src/database-parser.cc"
    break;

  case 249: // predicate: term "≮" term
#line 2137 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_less_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4512 "../../mli-root/src/database-parser.cc"
    break;

  case 250: // predicate: term "≯" term
#line 2138 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_greater_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4518 "../../mli-root/src/database-parser.cc"
    break;

  case 251: // predicate: term "≰" term
#line 2139 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_less_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4524 "../../mli-root/src/database-parser.cc"
    break;

  case 252: // predicate: term "≱" term
#line 2140 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_greater_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4530 "../../mli-root/src/database-parser.cc"
    break;

  case 253: // predicate: term "∈" term
#line 2142 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, in_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4536 "../../mli-root/src/database-parser.cc"
    break;

  case 254: // predicate: term "∉" term
#line 2143 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_in_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4542 "../../mli-root/src/database-parser.cc"
    break;

  case 255: // predicate: term "⊆" term
#line 2144 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, subset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4548 "../../mli-root/src/database-parser.cc"
    break;

  case 256: // predicate: term "⊊" term
#line 2145 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, proper_subset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4554 "../../mli-root/src/database-parser.cc"
    break;

  case 257: // predicate: term "⊇" term
#line 2146 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, superset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4560 "../../mli-root/src/database-parser.cc"
    break;

  case 258: // predicate: term "⊋" term
#line 2147 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, proper_superset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4566 "../../mli-root/src/database-parser.cc"
    break;

  case 259: // $@17: %empty
#line 2148 "../../mli-root/src/database-parser.yy"
          { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 4572 "../../mli-root/src/database-parser.cc"
    break;

  case 260: // $@18: %empty
#line 2149 "../../mli-root/src/database-parser.yy"
                               { bound_variable_type = free_variable_context; }
#line 4578 "../../mli-root/src/database-parser.cc"
    break;

  case 261: // predicate: "Set" $@17 "₍" "Set variable" "₎" $@18 simple_formula
#line 2150 "../../mli-root/src/database-parser.yy"
                       {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<bound_formula>(make,
        val<variable>(yystack_[3].value.as < val<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), bound_formula::is_set_);
    }
#line 4588 "../../mli-root/src/database-parser.cc"
    break;

  case 262: // predicate_expression: predicate_identifier tuple
#line 2159 "../../mli-root/src/database-parser.yy"
                                     {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::predicate, 0_ml, structure::postargument, precedence_t());
    }
#line 4597 "../../mli-root/src/database-parser.cc"
    break;

  case 263: // predicate_identifier: "predicate constant"
#line 2167 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > ();  }
#line 4603 "../../mli-root/src/database-parser.cc"
    break;

  case 264: // predicate_identifier: "predicate variable"
#line 2168 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > ();  }
#line 4609 "../../mli-root/src/database-parser.cc"
    break;

  case 265: // optional_superscript_natural_number_value: %empty
#line 2173 "../../mli-root/src/database-parser.yy"
           {}
#line 4615 "../../mli-root/src/database-parser.cc"
    break;

  case 266: // optional_superscript_natural_number_value: "superscript natural number value"
#line 2174 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < integer > () = yystack_[0].value.as < integer > (); }
#line 4621 "../../mli-root/src/database-parser.cc"
    break;

  case 267: // logic_formula: "¬" optional_superscript_natural_number_value object_formula
#line 2186 "../../mli-root/src/database-parser.yy"
                                                                          {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::prefix, logical_not_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 4632 "../../mli-root/src/database-parser.cc"
    break;

  case 268: // logic_formula: object_formula "∨" optional_superscript_natural_number_value object_formula
#line 2192 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, logical_or_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4643 "../../mli-root/src/database-parser.cc"
    break;

  case 269: // logic_formula: object_formula "∧" optional_superscript_natural_number_value object_formula
#line 2198 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, logical_and_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4654 "../../mli-root/src/database-parser.cc"
    break;

  case 270: // logic_formula: object_formula "⇒" optional_superscript_natural_number_value object_formula
#line 2204 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, implies_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4665 "../../mli-root/src/database-parser.cc"
    break;

  case 271: // logic_formula: object_formula "⇐" optional_superscript_natural_number_value object_formula
#line 2210 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, impliedby_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4676 "../../mli-root/src/database-parser.cc"
    break;

  case 272: // logic_formula: object_formula "⇔" optional_superscript_natural_number_value object_formula
#line 2216 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, equivalent_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4687 "../../mli-root/src/database-parser.cc"
    break;

  case 273: // logic_formula: prefix_logic_formula
#line 2222 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();  }
#line 4693 "../../mli-root/src/database-parser.cc"
    break;

  case 274: // prefix_logic_formula: "prefix formula variable"
#line 2227 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4699 "../../mli-root/src/database-parser.cc"
    break;

  case 275: // prefix_logic_formula: prefix_not_key prefix_logic_formula
#line 2228 "../../mli-root/src/database-parser.yy"
                                              {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "¬", structure::logic, 0_ml,
        structure::prefix, logical_not_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 4708 "../../mli-root/src/database-parser.cc"
    break;

  case 276: // prefix_logic_formula: prefix_or_key prefix_logic_formula prefix_logic_formula
#line 2232 "../../mli-root/src/database-parser.yy"
                                                                     {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "∨", structure::logic, 0_ml,
        structure::infix, logical_or_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4717 "../../mli-root/src/database-parser.cc"
    break;

  case 277: // prefix_logic_formula: prefix_and_key prefix_logic_formula prefix_logic_formula
#line 2236 "../../mli-root/src/database-parser.yy"
                                                                      {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "∧", structure::logic, 0_ml,
        structure::infix, logical_and_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4726 "../../mli-root/src/database-parser.cc"
    break;

  case 278: // prefix_logic_formula: prefix_implies_key prefix_logic_formula prefix_logic_formula
#line 2240 "../../mli-root/src/database-parser.yy"
                                                                          {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "⇒", structure::logic, 0_ml,
        structure::infix, implies_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4735 "../../mli-root/src/database-parser.cc"
    break;

  case 279: // prefix_logic_formula: prefix_equivalent_key prefix_logic_formula prefix_logic_formula
#line 2244 "../../mli-root/src/database-parser.yy"
                                                                             {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "⇔", structure::logic, 0_ml,
        structure::infix, equivalent_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
 }
#line 4744 "../../mli-root/src/database-parser.cc"
    break;

  case 280: // quantizer_declaration: quantized_variable_list
#line 2252 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4750 "../../mli-root/src/database-parser.cc"
    break;

  case 281: // quantized_variable_list: all_variable_list
#line 2256 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4756 "../../mli-root/src/database-parser.cc"
    break;

  case 282: // quantized_variable_list: exist_variable_list
#line 2257 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4762 "../../mli-root/src/database-parser.cc"
    break;

  case 283: // all_variable_list: "∀" exclusion_set all_identifier_list
#line 2262 "../../mli-root/src/database-parser.yy"
                                                 {
      auto bfp = dyn_cast<bound_formula*>(yystack_[1].value.as < ref6<unit> > ());
      if (bfp != nullptr) {
        variable_list& vsr = dyn_cast<variable_list&>(yystack_[0].value.as < ref6<unit> > ());
        vsr.excluded1_.insert(bfp->excluded1_.begin(), bfp->excluded1_.end());
      }
      yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();
    }
#line 4775 "../../mli-root/src/database-parser.cc"
    break;

  case 284: // exist_variable_list: "∃" exclusion_set exist_identifier_list
#line 2274 "../../mli-root/src/database-parser.yy"
                                                   {
      auto bfp = dyn_cast<bound_formula*>(yystack_[1].value.as < ref6<unit> > ());
      if (bfp != nullptr) {
        variable_list& vsr = dyn_cast<variable_list&>(yystack_[0].value.as < ref6<unit> > ());
        vsr.excluded1_.insert(bfp->excluded1_.begin(), bfp->excluded1_.end());
      }
      yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();
    }
#line 4788 "../../mli-root/src/database-parser.cc"
    break;

  case 285: // exclusion_set: %empty
#line 2286 "../../mli-root/src/database-parser.yy"
           {}
#line 4794 "../../mli-root/src/database-parser.cc"
    break;

  case 286: // $@19: %empty
#line 2287 "../../mli-root/src/database-parser.yy"
        { bound_variable_type = free_variable_context; }
#line 4800 "../../mli-root/src/database-parser.cc"
    break;

  case 287: // exclusion_set: "ₓ" $@19 "₍" exclusion_list "₎"
#line 2288 "../../mli-root/src/database-parser.yy"
                               {
      bound_variable_type = database_parser::token::exist_variable;
      yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > ();
    }
#line 4809 "../../mli-root/src/database-parser.cc"
    break;

  case 288: // exclusion_list: "object variable"
#line 2295 "../../mli-root/src/database-parser.yy"
                       { val<bound_formula> vr(make); vr->excluded1_.insert(yystack_[0].value.as < val<unit> > ()); yylhs.value.as < ref6<unit> > () = vr; }
#line 4815 "../../mli-root/src/database-parser.cc"
    break;

  case 289: // exclusion_list: exclusion_list "object variable"
#line 2296 "../../mli-root/src/database-parser.yy"
                                           {
      val<bound_formula> vr = yystack_[1].value.as < ref6<unit> > ();
      vr->excluded1_.insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = vr;
    }
#line 4825 "../../mli-root/src/database-parser.cc"
    break;

  case 290: // all_identifier_list: "all variable"
#line 2306 "../../mli-root/src/database-parser.yy"
                    {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = val<variable_list>(make, val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::all_);
    }
#line 4834 "../../mli-root/src/database-parser.cc"
    break;

  case 291: // $@20: %empty
#line 2310 "../../mli-root/src/database-parser.yy"
                           { bound_variable_type = token::all_variable; }
#line 4840 "../../mli-root/src/database-parser.cc"
    break;

  case 292: // all_identifier_list: all_identifier_list $@20 "," "all variable"
#line 2311 "../../mli-root/src/database-parser.yy"
                          {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = yystack_[3].value.as < ref6<unit> > ();
      dyn_cast<variable_list&>(yylhs.value.as < ref6<unit> > ()).push_back(val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::all_);
    }
#line 4850 "../../mli-root/src/database-parser.cc"
    break;

  case 293: // exist_identifier_list: "exist variable"
#line 2320 "../../mli-root/src/database-parser.yy"
                      {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = val<variable_list>(make, val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::exist_);
    }
#line 4859 "../../mli-root/src/database-parser.cc"
    break;

  case 294: // $@21: %empty
#line 2324 "../../mli-root/src/database-parser.yy"
                             { bound_variable_type = database_parser::token::exist_variable; }
#line 4865 "../../mli-root/src/database-parser.cc"
    break;

  case 295: // exist_identifier_list: exist_identifier_list $@21 "," "exist variable"
#line 2325 "../../mli-root/src/database-parser.yy"
                            {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = yystack_[3].value.as < ref6<unit> > ();
      dyn_cast<variable_list&>(yylhs.value.as < ref6<unit> > ()).push_back(val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::exist_);
    }
#line 4875 "../../mli-root/src/database-parser.cc"
    break;

  case 296: // optional_in_term: %empty
#line 2335 "../../mli-root/src/database-parser.yy"
           { yylhs.value.as < ref6<unit> > () = val<formula>(make); }
#line 4881 "../../mli-root/src/database-parser.cc"
    break;

  case 297: // optional_in_term: "∈" term
#line 2336 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4887 "../../mli-root/src/database-parser.cc"
    break;

  case 298: // tuple: "(" tuple_body ")"
#line 2343 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4893 "../../mli-root/src/database-parser.cc"
    break;

  case 299: // tuple_body: term
#line 2348 "../../mli-root/src/database-parser.yy"
            {
      ref0<sequence> vr(make, sequence::tuple);
      yylhs.value.as < ref6<unit> > () = vr;
      vr->push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 4903 "../../mli-root/src/database-parser.cc"
    break;

  case 300: // tuple_body: tuple_body "," term
#line 2353 "../../mli-root/src/database-parser.yy"
                              {
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
      sequence& vr = dyn_cast<sequence&>(yylhs.value.as < ref6<unit> > ());
      vr.push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 4913 "../../mli-root/src/database-parser.cc"
    break;

  case 301: // term: simple_term
#line 2362 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4919 "../../mli-root/src/database-parser.cc"
    break;

  case 302: // term: function_term
#line 2363 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4925 "../../mli-root/src/database-parser.cc"
    break;

  case 303: // term: simple_term term_substitution_sequence
#line 2364 "../../mli-root/src/database-parser.yy"
                                                 {
      yylhs.value.as < ref6<unit> > () = val<substitution_formula>(make, val<substitution>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 4933 "../../mli-root/src/database-parser.cc"
    break;

  case 304: // term: set_term
#line 2367 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4939 "../../mli-root/src/database-parser.cc"
    break;

  case 305: // simple_term: "term constant"
#line 2372 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4945 "../../mli-root/src/database-parser.cc"
    break;

  case 306: // simple_term: "natural number value"
#line 2373 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = val<integer>(make, yystack_[0].value.as < std::pair<std::string, integer> > ().second); }
#line 4951 "../../mli-root/src/database-parser.cc"
    break;

  case 307: // simple_term: "integer value"
#line 2374 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = val<integer>(make, yystack_[0].value.as < integer > ()); }
#line 4957 "../../mli-root/src/database-parser.cc"
    break;

  case 308: // simple_term: term_identifier
#line 2375 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4963 "../../mli-root/src/database-parser.cc"
    break;

  case 309: // simple_term: "(" term ")"
#line 2376 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4969 "../../mli-root/src/database-parser.cc"
    break;

  case 310: // term_identifier: "object variable" variable_exclusion_set
#line 2381 "../../mli-root/src/database-parser.yy"
                                                    {
      val<variable> xr = yystack_[1].value.as < val<unit> > ();
      val<variable> vr = yystack_[0].value.as < ref6<unit> > ();
      xr->excluded_.insert(vr->excluded_.begin(), vr->excluded_.end());
      yylhs.value.as < ref6<unit> > () = xr;
    }
#line 4980 "../../mli-root/src/database-parser.cc"
    break;

  case 311: // term_identifier: "function variable"
#line 2387 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4986 "../../mli-root/src/database-parser.cc"
    break;

  case 312: // term_identifier: "function map variable"
#line 2388 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4992 "../../mli-root/src/database-parser.cc"
    break;

  case 313: // term_identifier: "all variable"
#line 2389 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4998 "../../mli-root/src/database-parser.cc"
    break;

  case 314: // term_identifier: "exist variable"
#line 2390 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5004 "../../mli-root/src/database-parser.cc"
    break;

  case 315: // term_identifier: "Set variable"
#line 2391 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5010 "../../mli-root/src/database-parser.cc"
    break;

  case 316: // term_identifier: "set variable"
#line 2392 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5016 "../../mli-root/src/database-parser.cc"
    break;

  case 317: // term_identifier: "implicit set variable"
#line 2393 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5022 "../../mli-root/src/database-parser.cc"
    break;

  case 318: // variable_exclusion_set: %empty
#line 2398 "../../mli-root/src/database-parser.yy"
           { yylhs.value.as < ref6<unit> > () = val<variable>(make);  }
#line 5028 "../../mli-root/src/database-parser.cc"
    break;

  case 319: // variable_exclusion_set: "ₓ" "₍" variable_exclusion_list "₎"
#line 2399 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 5034 "../../mli-root/src/database-parser.cc"
    break;

  case 320: // variable_exclusion_list: bound_variable
#line 2404 "../../mli-root/src/database-parser.yy"
                      { val<variable> vr(make); vr->excluded_.insert(yystack_[0].value.as < ref6<unit> > ()); yylhs.value.as < ref6<unit> > () = vr; }
#line 5040 "../../mli-root/src/database-parser.cc"
    break;

  case 321: // variable_exclusion_list: variable_exclusion_list bound_variable
#line 2405 "../../mli-root/src/database-parser.yy"
                                                   {
      val<variable> vr = yystack_[1].value.as < ref6<unit> > ();
      vr->excluded_.insert(yystack_[0].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = vr;
    }
#line 5050 "../../mli-root/src/database-parser.cc"
    break;

  case 322: // bound_variable: "all variable"
#line 2414 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5056 "../../mli-root/src/database-parser.cc"
    break;

  case 323: // bound_variable: "exist variable"
#line 2415 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5062 "../../mli-root/src/database-parser.cc"
    break;

  case 324: // bound_variable: "Set variable"
#line 2416 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5068 "../../mli-root/src/database-parser.cc"
    break;

  case 325: // bound_variable: "set variable"
#line 2417 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5074 "../../mli-root/src/database-parser.cc"
    break;

  case 326: // bound_variable: "implicit set variable"
#line 2418 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5080 "../../mli-root/src/database-parser.cc"
    break;

  case 327: // function_term: function_term_identifier tuple
#line 2423 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::function, 0_ml, structure::postargument, precedence_t()); }
#line 5088 "../../mli-root/src/database-parser.cc"
    break;

  case 328: // function_term: term_function_application
#line 2426 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 5094 "../../mli-root/src/database-parser.cc"
    break;

  case 329: // function_term: term "!"
#line 2427 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[0].value.as < std::string > (), structure::function, 0_ml,
        structure::postfix, factorial_oprec, yystack_[1].value.as < ref6<unit> > ());
    }
#line 5103 "../../mli-root/src/database-parser.cc"
    break;

  case 330: // function_term: term "+" term
#line 2431 "../../mli-root/src/database-parser.yy"
                           { // $$ = val<integer_addition>(make, val<formula>($x), val<formula>($y));
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, plus_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5112 "../../mli-root/src/database-parser.cc"
    break;

  case 331: // function_term: term "-" term
#line 2435 "../../mli-root/src/database-parser.yy"
                           { // $$ = val<integer_addition>(make, val<formula>($x), val<integer_negative>(make, val<formula>($y)));
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, minus_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5121 "../../mli-root/src/database-parser.cc"
    break;

  case 332: // function_term: "-" term
#line 2439 "../../mli-root/src/database-parser.yy"
                                      { // $$ = val<integer_negative>(make, val<formula>($x)); }
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, unary_minus_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5130 "../../mli-root/src/database-parser.cc"
    break;

  case 333: // function_term: term "⋅" term
#line 2443 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, mult_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5139 "../../mli-root/src/database-parser.cc"
    break;

  case 334: // function_term: term "/" term
#line 2447 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, divide_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5148 "../../mli-root/src/database-parser.cc"
    break;

  case 335: // set_term: "{" "}"
#line 2455 "../../mli-root/src/database-parser.yy"
            { yylhs.value.as < ref6<unit> > () = ref0<sequence>(make, sequence::member_list_set); }
#line 5154 "../../mli-root/src/database-parser.cc"
    break;

  case 336: // set_term: "∅"
#line 2456 "../../mli-root/src/database-parser.yy"
        { yylhs.value.as < ref6<unit> > () = val<constant>(make, "∅", constant::object); }
#line 5160 "../../mli-root/src/database-parser.cc"
    break;

  case 337: // set_term: "{" set_member_list "}"
#line 2457 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 5166 "../../mli-root/src/database-parser.cc"
    break;

  case 338: // set_term: "{" "set variable definition" optional_in_term "|" object_formula "}"
#line 2458 "../../mli-root/src/database-parser.yy"
                                                                                 {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<bound_formula>(make, yystack_[4].value.as < val<unit> > (), yystack_[3].value.as < ref6<unit> > (), yystack_[1].value.as < ref6<unit> > (), bound_formula::set_);
    }
#line 5175 "../../mli-root/src/database-parser.cc"
    break;

  case 339: // set_term: "{" "₍" implicit_set_identifier_list optional_in_term "₎" term "|" object_formula "}"
#line 2462 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      symbol_table.pop_level();
      variable_list& vs = dyn_cast<variable_list&>(yystack_[6].value.as < ref6<unit> > ());
      ref0<sequence> sp(make, val<formula>(yystack_[3].value.as < ref6<unit> > ()), sequence::implicit_set);
      sp->push_back(val<formula>(yystack_[1].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () =
        val<bound_formula>(make, vs, yystack_[5].value.as < ref6<unit> > (), val<formula>(sp));
    }
#line 5188 "../../mli-root/src/database-parser.cc"
    break;

  case 340: // set_term: term "∪" term
#line 2470 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, set_union_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5197 "../../mli-root/src/database-parser.cc"
    break;

  case 341: // set_term: term "∩" term
#line 2474 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, set_intersection_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5206 "../../mli-root/src/database-parser.cc"
    break;

  case 342: // set_term: term "∖" term
#line 2478 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, set_difference_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5215 "../../mli-root/src/database-parser.cc"
    break;

  case 343: // set_term: "∁" term
#line 2482 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, set_complement_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5224 "../../mli-root/src/database-parser.cc"
    break;

  case 344: // set_term: "⋃" term
#line 2486 "../../mli-root/src/database-parser.yy"
                   { /* prefix union operator  */
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, set_union_operator_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5233 "../../mli-root/src/database-parser.cc"
    break;

  case 345: // set_term: "∩" term
#line 2490 "../../mli-root/src/database-parser.yy"
                   { /* prefix intersection operator  */
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, set_intersection_operator_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5242 "../../mli-root/src/database-parser.cc"
    break;

  case 346: // $@22: %empty
#line 2498 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 5248 "../../mli-root/src/database-parser.cc"
    break;

  case 347: // implicit_set_identifier_list: $@22 "Set variable"
#line 2499 "../../mli-root/src/database-parser.yy"
                       {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = val<variable_list>(make, val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::implicit_set);
    }
#line 5257 "../../mli-root/src/database-parser.cc"
    break;

  case 348: // $@23: %empty
#line 2503 "../../mli-root/src/database-parser.yy"
                                    { bound_variable_type = database_parser::token::is_set_variable; }
#line 5263 "../../mli-root/src/database-parser.cc"
    break;

  case 349: // implicit_set_identifier_list: implicit_set_identifier_list $@23 "," "Set variable"
#line 2504 "../../mli-root/src/database-parser.yy"
                             {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = yystack_[3].value.as < ref6<unit> > ();
      dyn_cast<variable_list&>(yylhs.value.as < ref6<unit> > ()).push_back(val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::implicit_set);
    }
#line 5273 "../../mli-root/src/database-parser.cc"
    break;

  case 350: // set_member_list: term
#line 2513 "../../mli-root/src/database-parser.yy"
            {
      ref0<sequence> vr(make, sequence::member_list_set);
      yylhs.value.as < ref6<unit> > () = vr;
      vr->push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 5282 "../../mli-root/src/database-parser.cc"
    break;

  case 351: // set_member_list: set_member_list "," term
#line 2517 "../../mli-root/src/database-parser.yy"
                                   {
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
      sequence& vr = dyn_cast<sequence&>(yylhs.value.as < ref6<unit> > ());
      vr.push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 5292 "../../mli-root/src/database-parser.cc"
    break;

  case 352: // function_term_identifier: "function constant"
#line 2526 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5298 "../../mli-root/src/database-parser.cc"
    break;

  case 353: // function_term_identifier: "function variable"
#line 2527 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5304 "../../mli-root/src/database-parser.cc"
    break;


#line 5308 "../../mli-root/src/database-parser.cc"

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


  const short database_parser::yypact_ninf_ = -523;

  const short database_parser::yytable_ninf_ = -354;

  const short
  database_parser::yypact_[] =
  {
     279,  -523,    63,    65,  -523,    89,  -523,  -523,    58,  -523,
    -523,  -523,  -523,   -23,  -523,  -523,   405,   153,    22,   176,
    -523,   184,  -523,   335,   248,  -523,   119,   306,   335,    58,
      58,    58,   289,    87,   297,  -523,  -523,  -523,  -523,   286,
     503,  -523,   142,  -523,  -523,  -523,   221,  -523,  -523,    58,
     232,   241,   282,  -523,   290,  -523,  -523,   370,   372,   292,
    -523,  -523,   300,  -523,  -523,  -523,  -523,   409,  -523,  -523,
     792,   326,   348,   348,  -523,  -523,  -523,  -523,   275,   301,
    -523,   347,  -523,   353,   141,  -523,  -523,  -523,  -523,  -523,
    -523,   338,   338,   379,   592,   592,   592,   592,   592,  -523,
    -523,  1526,  -523,  -523,  1526,  1526,  1526,   692,   992,   792,
    -523,  -523,  -523,   792,    14,  -523,   355,  -523,  -523,   215,
    -523,  -523,   291,  -523,   360,  -523,  -523,  -523,  -523,   348,
    -523,  -523,  1429,  -523,  -523,  -523,   112,   365,  -523,  -523,
    -523,   348,  -523,  -523,  -523,   460,  -523,   380,  -523,  -523,
    -523,  -523,   289,  -523,  -523,    87,   373,   297,  -523,  -523,
     492,    82,   386,  1340,  -523,  1526,  -523,  -523,  -523,   381,
    -523,  -523,   459,   470,  -523,  1340,  -523,   592,   592,   592,
     592,   433,  1454,  1064,  -523,   403,   285,   285,   285,   186,
     482,    14,   413,    17,   899,   432,  1162,  -523,  -523,   227,
    1682,    83,  -523,    14,   379,   379,   792,   792,   634,   355,
    -523,  -523,  -523,  -523,   524,   510,  1340,  1340,  1340,   379,
     379,   379,   379,   379,   722,   360,  -523,  -523,  -523,  -523,
    -523,  -523,  1526,  1251,  -523,  -523,   188,  1682,  1526,  1526,
     510,  1526,  1526,  1526,  1526,  1526,  1526,  1526,  1526,  1526,
    1526,  1526,  1526,  -523,  1526,  1526,  1526,  1526,  1526,  1526,
    1526,  1526,  1526,  1526,  1526,  1526,  1526,   654,   365,  -523,
    -523,   568,    58,    58,    58,  -523,  -523,  -523,  -523,  -523,
      10,  -523,   503,   503,  -523,  -523,  -523,  -523,   145,  -523,
    -523,   466,   503,  -523,   472,   286,  -523,    -9,   534,   223,
     517,   431,   458,  -523,   483,  -523,   487,  -523,  -523,  -523,
    -523,  -523,   198,   537,   398,   517,   538,  1340,   523,   490,
     497,  -523,   489,   247,   284,  1584,   100,   569,    23,  1526,
    -523,   502,   502,    -7,  -523,   548,   549,   552,   553,  -523,
     556,  -523,  1340,  -523,  -523,   534,  1682,   534,   534,  1340,
    1340,  1340,  1340,  1340,  -523,   517,   303,  1340,  -523,   517,
     517,   618,   517,   517,   517,   517,   517,   517,   517,   517,
     517,   517,   517,   517,  -523,   -40,   -40,   517,   517,   532,
     285,   285,   517,   517,   517,   517,  -523,  -523,   526,   527,
     529,   530,  -523,   531,   792,  -523,  -523,  -523,  -523,   358,
     449,   856,   533,   602,    54,   536,   217,   550,   561,   554,
    -523,  -523,   643,  -523,  -523,  1340,  -523,  1526,  -523,  -523,
    -523,  -523,  -523,  -523,   114,  -523,   641,   573,   574,  1526,
     608,   565,   308,  1633,  1340,  1340,   566,   578,  -523,   669,
    -523,  -523,  1340,  1340,   -69,  -523,   517,    18,   580,   580,
     792,  1340,  1136,   664,  1526,   534,  1682,  -523,   649,   516,
     516,   316,  -523,   534,  1340,  -523,  -523,  -523,  -523,  -523,
    -523,   792,   792,  1340,  1340,  1526,  1526,  -523,   627,   620,
     623,   355,   145,  -523,   145,   145,   145,   145,   534,   517,
    -523,  -523,  -523,   -22,   668,   670,   468,  1526,  -523,   348,
     348,   534,  1682,   245,  1526,   666,  1526,    11,   -20,    23,
    1340,  -523,  -523,    77,    80,  -523,   152,  -523,    13,  -523,
     182,   792,   792,    12,   191,   596,   598,   484,   534,  1682,
     503,   503,   503,   603,   621,   534,   534,   517,   517,  1340,
    -523,  -523,   355,   550,   561,   622,    36,  -523,   314,  -523,
    -523,  -523,  -523,   517,   225,  -523,  -523,   625,   628,  -523,
     393,  -523,   517,   -14,   -14,  -523,   254,   -10,   630,   -10,
     659,  -523,   660,  -523,  -523,  -523,  -523,  -523,   103,    85,
    -523,   -12,  -523,    38,   386,  -523,  -523,  -523,  -523,  -523,
     637,   638,   639,   534,   145,   145,  -523,  -523,  -523,  -523,
    1340,  -523,  -523,  -523,   348,   348,  1340,    23,   629,  -523,
    -523,  -523,   660,  -523,  -523,   103,   677,  -523,  -523,  -523,
    -523,  -523,  -523,    42,  -523,   351,  -523,  -523,   262,   -77,
     -14,  -523,  -523,  -523,  -523,  -523,  -523
  };

  const short
  database_parser::yydefact_[] =
  {
       0,     4,     0,     3,     6,     0,     1,     5,     0,     8,
      70,    71,    72,     0,    33,    37,    53,     0,     0,     0,
      38,     0,    53,    42,     0,    46,     0,     0,    43,     0,
       0,     0,     0,     0,     0,    54,    57,    58,    55,    77,
       0,    56,     0,   120,    40,    41,     0,    48,    44,    35,
       0,     0,     0,   132,   122,   130,   135,     0,     0,   123,
     133,   127,   124,   125,    81,    80,    73,    93,    76,    82,
       0,     0,     0,     0,   263,   236,   352,   305,   185,   237,
     264,   238,   274,   311,   318,   313,   314,   312,   315,   316,
     317,   285,   285,   265,     0,     0,     0,     0,     0,   306,
     307,     0,   259,   336,     0,     0,     0,     0,     0,     0,
     207,   328,    74,     0,   115,   147,     0,   149,   150,     0,
     186,   195,   148,   211,     0,   210,   205,   239,   240,     0,
     208,   273,   296,   280,   281,   282,     0,   301,   308,   302,
     304,     0,   119,   121,    39,     0,    48,     0,    36,    68,
      66,    75,     0,   136,   137,     0,     0,     0,    94,    78,
       0,    87,   156,     0,   200,     0,    32,    28,   201,     0,
     310,   286,     0,     0,   266,     0,   275,     0,     0,     0,
       0,   318,     0,     0,   332,     0,   343,   345,   344,   318,
       0,     0,   147,   148,     0,   296,     0,   346,   335,     0,
     350,     0,   151,   116,   265,   265,     0,     0,     0,   158,
       9,    11,    12,    13,     0,     0,     0,     0,     0,   265,
     265,   265,   265,   265,     0,   206,    15,    17,    18,   262,
     237,   238,     0,     0,   226,   234,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   329,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   303,    22,
     327,     0,     0,     0,     0,    49,    51,    61,    52,    50,
       0,    34,     0,     0,   131,   134,   128,   126,    99,    79,
      89,     0,     0,    83,     0,     0,    90,     0,   203,     0,
     299,     0,     0,   290,   283,   293,   284,   267,   277,   276,
     278,   279,   318,     0,     0,   350,     0,     0,     0,   157,
     209,   309,     0,   318,     0,     0,   296,     0,   215,     0,
     337,   159,   159,   152,   153,     0,     0,     0,     0,   311,
       0,    10,     0,   194,   187,   188,   189,   196,   197,     0,
       0,     0,     0,     0,    16,   297,     0,     0,   228,   198,
     199,     0,   245,   246,   247,   248,   249,   250,   251,   252,
     241,   242,   243,   244,   333,   330,   331,   253,   254,   340,
     341,   342,   255,   256,   257,   258,   334,    23,     0,     0,
       0,     0,    45,     0,     0,   117,   138,   139,   140,   147,
     148,     0,     0,     0,   107,   112,     0,    95,    97,   100,
     106,    84,    91,    88,    86,     0,   202,     0,   298,   322,
     323,   324,   325,   326,     0,   320,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   347,     0,
     218,   219,     0,     0,     0,   216,   351,     0,   173,   173,
       0,     0,     0,     0,     0,   190,   191,   269,   268,   270,
     271,   272,   235,   227,     0,    47,    59,    62,    64,    69,
     118,     0,     0,     0,     0,     0,     0,    67,     0,   110,
     108,     0,    99,    92,    99,     0,     0,    99,   204,   300,
     319,   321,   288,     0,     0,     0,     0,     0,   260,     0,
       0,    26,    30,     0,     0,     0,     0,     0,     0,     0,
       0,   172,   171,     0,     0,   163,     0,   166,     0,   169,
       0,     0,     0,     0,     0,     0,     0,     0,   192,   193,
       0,     0,     0,   147,   147,   143,   144,   145,   146,     0,
     111,   109,   114,    96,    98,   102,     0,   104,     0,   289,
     287,   292,   295,    30,     0,    25,    29,     0,     0,   338,
       0,   349,   220,     0,     0,   217,     0,     0,   165,   168,
       0,   160,     0,   161,   162,   170,   182,   181,     0,     0,
     176,     0,   179,   154,   155,    14,    19,    20,    21,    24,
       0,     0,     0,   129,     0,     0,   101,    85,   229,   230,
       0,   233,   261,   231,     0,     0,     0,   215,     0,   213,
     222,   212,     0,   164,   167,   178,     0,   174,   175,   180,
      60,    63,    65,     0,   105,     0,    27,    31,     0,     0,
       0,   177,   103,   232,   339,   214,   221
  };

  const short
  database_parser::yypgoto_[] =
  {
    -523,  -523,  -523,   779,  -523,   305,  -201,  -523,  -523,   559,
    -109,  -523,  -111,  -523,  -523,  -523,  -523,  -523,  -523,  -523,
    -523,  -523,  -523,  -523,  -523,  -523,  -523,   642,  -523,   765,
    -523,  -523,  -523,  -523,  -523,  -135,  -523,  -131,  -523,    -2,
    -523,  -523,  -523,  -523,  -523,   496,  -523,  -523,  -523,  -523,
    -523,  -523,   631,  -523,   307,   311,   312,   201,  -461,  -523,
    -523,  -274,  -523,   -16,  -523,   755,  -523,   645,  -523,  -523,
    -523,   648,  -523,   650,   415,  -523,  -523,  -523,   -54,  -102,
     471,  -523,   237,   363,   239,   366,  -485,   368,  -523,   196,
     236,  -506,  -523,  -523,  -523,    25,  -523,  -523,   737,  -523,
    -106,  -523,  -522,   212,  -324,  -523,  -233,  -523,  -523,   688,
     369,  -523,  -523,   268,  -523,   457,  -523,     9,  -523,  -523,
    -523,  -523,   731,  -523,  -523,  -523,  -523,  -523,  -523,  -184,
     -73,  -523,   199,  -523,    26,  -523,  -523,   400,  -523,  -523,
    -523,  -523,  -523,  -523,  -523
  };

  const short
  database_parser::yydefgoto_[] =
  {
       0,     2,     3,     4,     5,   209,   210,   211,   225,   226,
     212,   268,   213,   110,   557,   111,   558,     9,    15,   147,
      16,    20,    46,    21,    22,   146,    47,   145,   275,    23,
      35,   276,   530,   531,   532,    36,   283,    37,   282,   405,
      38,    39,    40,    66,    67,    68,    69,   161,   292,   293,
     294,   295,   159,   160,   406,   407,   408,   546,   409,   410,
     481,   112,   393,   113,    42,    43,    62,    63,   156,   403,
      54,    55,    59,    60,   395,   396,   397,   398,   114,   115,
     448,   514,   515,   568,   517,   569,   519,   521,   579,   580,
     581,   582,   116,   117,   118,   119,   120,   121,   164,   297,
     122,   123,   608,   444,   609,   124,   125,   602,   234,   126,
     127,   185,   554,   128,   129,   175,   130,   131,   132,   133,
     134,   135,   172,   302,   493,   304,   427,   306,   428,   236,
     166,   299,   237,   137,   138,   170,   424,   425,   139,   140,
     326,   327,   437,   201,   141
  };

  const short
  database_parser::yytable_[] =
  {
     167,   193,   199,   358,   445,   192,    13,    41,   341,   402,
     277,   322,    41,   228,   278,   227,   162,   205,   412,    29,
     272,   273,   274,    30,   545,   547,   269,    50,    51,    52,
     290,   549,   204,   575,   204,   576,   205,   511,   205,   439,
     440,   577,   610,   512,   217,   218,   509,   148,   219,   220,
     221,   222,   223,   191,   509,   202,   229,   298,  -354,   203,
     511,   635,   205,     6,   254,   511,   512,   510,   270,   307,
      -7,   512,    32,    33,    34,   619,   439,   440,   479,   219,
     220,   221,   222,   223,   575,   219,   220,   221,   222,   223,
     324,    29,    10,    11,     8,   441,    10,    11,   289,   -93,
     266,   158,    14,   176,   177,   178,   179,   180,   636,   619,
     345,   347,   348,   550,   228,   415,   227,   207,   416,   513,
      10,    11,   607,   618,   511,    56,   564,   356,   442,   279,
     512,   443,   441,   547,   624,   206,   207,   206,   207,   238,
     239,   585,   436,   240,   320,   277,   574,    25,   392,   278,
     576,    12,   333,   334,   563,    12,   577,   387,    24,   291,
     595,   206,   207,   404,  -194,   442,   595,  -194,   443,   419,
     420,   596,   421,   422,  -194,   423,   400,   632,   567,    12,
     399,    57,    58,    10,    11,   565,   308,   309,   310,   311,
      27,   241,   242,   243,   244,   245,   246,   247,   248,   249,
     250,   251,   252,   570,    32,    33,    34,   329,   616,  -194,
     232,   432,  -194,   571,    26,   253,   254,   255,   256,  -194,
     617,   330,   257,   258,  -348,   259,   260,   261,   191,   576,
     262,   263,   264,   265,   340,   577,   455,   169,   214,   136,
     344,   215,    12,   457,   458,   459,   460,   461,   216,   490,
     340,   463,   266,    91,    92,    48,   590,   591,   592,   219,
     220,   221,   222,   223,   279,   361,   394,   142,    74,   136,
     389,   390,   391,   598,    80,   599,   572,   317,   413,    -2,
       1,   578,   169,   445,    -7,   573,    44,    45,   400,   429,
      91,    92,   399,   340,   169,   219,   220,   221,   222,   223,
     184,    64,    65,   186,   187,   188,   194,   200,   136,   488,
     357,    49,   136,   219,   220,   221,   222,   223,   217,   218,
     586,   601,   219,   220,   221,   222,   223,    53,   501,   503,
     219,   220,   221,   222,   223,    61,   507,   508,   317,   482,
     191,   341,   483,   169,    29,   524,   144,   417,    30,    31,
     418,   600,   219,   220,   221,   222,   223,   149,   528,   219,
     220,   221,   222,   223,   300,   328,   150,   535,   536,   533,
     534,   219,   220,   221,   222,   223,   219,   220,   221,   222,
     223,   314,   315,   559,   219,   220,   221,   222,   253,   254,
     255,   256,   611,   471,   472,   325,   523,    32,    33,    34,
     634,   163,   480,  -183,   566,   136,   136,   151,   153,    17,
     154,   320,    18,    19,   152,   346,   155,   191,   191,   219,
     220,   221,   222,   223,   157,   266,   555,   556,   158,  -223,
     462,   355,   325,   593,   171,   499,   482,   359,   360,   597,
     362,   363,   364,   365,   366,   367,   368,   369,   370,   371,
     372,   373,   163,   374,   375,   376,   377,   378,   379,   380,
     381,   382,   383,   384,   385,   386,   271,   583,   584,    29,
     272,   273,   274,    30,   165,  -224,   217,   218,   633,  -353,
     174,   401,   136,   208,   473,   474,   419,   420,   224,   421,
     422,   136,   423,   267,   625,   286,   253,   254,   255,   256,
     628,   253,   254,   255,   256,   281,   259,   260,   261,   288,
     207,   259,   260,   261,   303,   301,   433,   219,   220,   221,
     222,   223,    32,    33,    34,   321,   305,    70,   446,   169,
     606,   626,   627,   266,    32,    33,    34,   316,   266,   318,
     319,   456,   232,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    82,    83,    84,   342,    85,    86,
      87,    88,    89,   343,    90,    32,    33,    34,    91,    92,
      93,   253,   254,   255,   256,   388,    94,    95,    96,    97,
      98,   259,   260,   261,   219,   220,   221,   253,   254,   255,
     256,   411,   426,   401,   430,   500,   431,   259,   260,   261,
      99,   100,   219,   220,   221,   222,   223,  -291,   266,   101,
     102,  -294,   103,   589,   434,   104,   489,   105,  -184,   106,
     253,   254,   255,   256,   266,  -225,   435,   438,   496,   107,
     259,   260,   261,   502,   447,   253,   254,   255,   256,   108,
     450,   451,   109,    82,   452,   453,   260,   261,   454,   136,
     464,   465,   466,   527,   467,   468,   469,   266,   477,   478,
     487,   331,   332,   529,  -113,    94,    95,    96,    97,    98,
     136,   136,   266,   484,   537,   538,   349,   350,   351,   352,
     353,   335,   336,   337,   338,   485,   339,   181,   486,    85,
      86,    87,    88,    89,   492,    90,   553,   494,   495,   497,
     498,   504,   505,   560,   506,   562,   339,   181,   526,    85,
      86,    87,    88,    89,   520,    90,    70,   219,   539,   540,
     136,   136,   541,   551,   561,   587,   552,   588,  -141,   136,
     136,   136,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    82,    83,   189,  -142,    85,    86,    87,
      88,    89,   604,    90,   572,   605,   594,    91,    92,    93,
     612,   567,   620,   621,   622,    94,    95,    96,    97,    98,
     336,   337,   338,   630,   339,   181,   578,    85,    86,    87,
      88,    89,     7,    90,   354,   190,   542,    28,   280,    99,
     100,   414,   296,   543,   548,   623,   544,   143,   101,   102,
     284,   103,   287,   449,   104,   285,   105,   613,   106,   470,
     516,   614,   631,   518,   615,   168,    70,   522,   107,   629,
     235,   525,   603,   173,   491,     0,     0,     0,   108,     0,
       0,   109,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    82,    83,    84,     0,    85,    86,    87,
      88,    89,     0,    90,     0,     0,     0,    91,    92,    93,
       0,     0,     0,     0,     0,    94,    95,    96,    97,    98,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   238,   239,     0,     0,   240,     0,    99,
     100,   475,   476,     0,     0,     0,     0,     0,   101,   102,
       0,   103,     0,     0,   104,     0,   105,     0,   106,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   107,     0,
       0,     0,     0,     0,     0,     0,   238,   239,   108,     0,
     240,   109,     0,     0,     0,   241,   242,   243,   244,   245,
     246,   247,   248,   249,   250,   251,   252,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   253,
     254,   255,   256,     0,     0,     0,   257,   258,     0,   259,
     260,   261,     0,     0,   262,   263,   264,   265,   241,   242,
     243,   244,   245,   246,   247,   248,   249,   250,   251,   252,
       0,     0,     0,     0,     0,     0,   266,     0,     0,     0,
       0,     0,   253,   254,   255,   256,     0,     0,     0,   257,
     258,     0,   259,   260,   261,     0,     0,   262,   263,   264,
     265,     0,     0,     0,     0,     0,   321,     0,     0,     0,
       0,     0,     0,    72,    73,    74,    75,    76,    77,   266,
      79,    80,    81,    82,    83,   181,     0,    85,    86,    87,
      88,    89,   195,    90,     0,     0,     0,    91,    92,    93,
       0,     0,     0,     0,     0,    94,    95,    96,    97,    98,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    99,
     100,     0,     0,     0,     0,     0,     0,     0,   101,   102,
       0,   103,     0,     0,   104,    72,   105,     0,   106,    76,
      77,     0,     0,     0,     0,     0,    83,   181,   196,    85,
      86,    87,    88,    89,   195,    90,   197,     0,   108,     0,
     198,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    99,   100,     0,     0,     0,     0,     0,     0,     0,
     101,     0,     0,   103,     0,     0,   104,    72,   105,    74,
     106,    76,    77,     0,     0,    80,     0,     0,    83,   181,
     182,    85,    86,    87,    88,    89,     0,    90,   197,     0,
     183,     0,   198,    72,    73,    74,    75,    76,    77,     0,
      79,    80,    81,    82,    83,   323,     0,    85,    86,    87,
      88,    89,     0,    90,     0,     0,     0,    91,    92,    93,
       0,     0,     0,    99,   100,    94,    95,    96,    97,    98,
       0,     0,   101,   102,     0,   103,     0,     0,   104,     0,
     105,     0,   106,     0,     0,   190,     0,     0,     0,    99,
     100,     0,   182,     0,     0,     0,     0,     0,   101,   102,
       0,   103,   183,     0,   104,     0,   105,     0,   106,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   196,     0,
       0,     0,    72,    73,    74,    75,    76,    77,   108,    79,
      80,    81,    82,    83,   312,     0,    85,    86,    87,    88,
      89,     0,    90,     0,     0,     0,    91,    92,    93,     0,
       0,     0,     0,     0,    94,    95,    96,    97,    98,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   313,     0,     0,     0,    99,   100,
       0,     0,     0,     0,     0,     0,     0,   101,   102,     0,
     103,     0,     0,   104,     0,   105,     0,   106,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   196,     0,     0,
       0,    72,    73,    74,    75,    76,    77,   108,    79,    80,
      81,    82,    83,   181,     0,    85,    86,    87,    88,    89,
       0,    90,     0,     0,     0,    91,    92,    93,     0,     0,
       0,     0,     0,    94,    95,    96,    97,    98,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    99,   100,     0,
       0,     0,     0,     0,     0,     0,   101,   102,     0,   103,
       0,     0,   104,     0,   105,     0,   106,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   196,     0,     0,     0,
      72,     0,    74,    75,    76,    77,   108,   230,    80,   231,
       0,    83,   181,     0,    85,    86,    87,    88,    89,     0,
      90,     0,     0,     0,     0,    72,     0,     0,     0,    76,
      77,     0,     0,     0,     0,     0,    83,   312,     0,    85,
      86,    87,    88,    89,     0,    90,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    99,   100,     0,     0,
       0,     0,     0,     0,     0,   101,   102,     0,   103,   232,
       0,   104,     0,   105,     0,   106,     0,   313,     0,     0,
       0,    99,   100,     0,     0,   233,     0,     0,     0,     0,
     101,     0,     0,   103,     0,   183,   104,    72,   105,     0,
     106,    76,    77,     0,     0,     0,     0,     0,    83,   181,
     182,    85,    86,    87,    88,    89,     0,    90,     0,     0,
     183,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    99,   100,     0,     0,     0,     0,     0,
       0,     0,   101,     0,     0,   103,     0,     0,   104,     0,
     105,     0,   106,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   182,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   183,   241,   242,   243,   244,   245,   246,   247,
     248,   249,   250,   251,   252,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   253,   254,   255,
     256,     0,     0,     0,   257,   258,     0,   259,   260,   261,
       0,     0,   262,   263,   264,   265,     0,     0,     0,     0,
       0,   321,   241,   242,   243,   244,   245,   246,   247,   248,
     249,   250,   251,   252,   266,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   253,   254,   255,   256,
       0,     0,     0,   257,   258,     0,   259,   260,   261,     0,
       0,   262,   263,   264,   265,     0,     0,     0,     0,     0,
     500,   241,   242,   243,   244,   245,   246,   247,   248,   249,
     250,   251,   252,   266,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   253,   254,   255,   256,     0,
       0,     0,   257,   258,     0,   259,   260,   261,     0,     0,
     262,   263,   264,   265,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   266
  };

  const short
  database_parser::yycheck_[] =
  {
      73,   107,   108,   236,   328,   107,     8,    23,   209,   283,
     145,   195,    28,   124,   145,   124,    70,    24,   292,     9,
      10,    11,    12,    13,   485,   486,   137,    29,    30,    31,
     161,    53,    20,   518,    20,    47,    24,    47,    24,    53,
      54,    53,   564,    53,    27,    28,   123,    49,    68,    69,
      70,    71,    72,   107,   123,   109,   129,   163,    20,   113,
      47,   138,    24,     0,   104,    47,    53,   136,   141,   175,
       5,    53,    62,    63,    64,   581,    53,    54,    24,    68,
      69,    70,    71,    72,   569,    68,    69,    70,    71,    72,
     196,     9,    38,    39,     5,   109,    38,    39,    16,    17,
     140,    19,   125,    94,    95,    96,    97,    98,   630,   615,
     216,   217,   218,   135,   225,   124,   225,   124,   127,   101,
      38,    39,   136,   135,    47,    38,   146,   233,   142,   145,
      53,   145,   109,   594,   595,   123,   124,   123,   124,    27,
      28,   129,   326,    31,   127,   280,   133,   125,   138,   280,
      47,    97,   206,   207,   143,    97,    53,   268,     5,   161,
     124,   123,   124,    18,    23,   142,   124,    26,   145,    55,
      56,   135,    58,    59,    33,    61,   282,   135,   101,    97,
     282,    94,    95,    38,    39,   509,   177,   178,   179,   180,
       6,    79,    80,    81,    82,    83,    84,    85,    86,    87,
      88,    89,    90,   123,    62,    63,    64,   124,   123,    23,
     110,   317,    26,   133,    38,   103,   104,   105,   106,    33,
     135,   138,   110,   111,   124,   113,   114,   115,   282,    47,
     118,   119,   120,   121,   208,    53,   342,    96,    23,    40,
     215,    26,    97,   349,   350,   351,   352,   353,    33,   135,
     224,   357,   140,    65,    66,   136,   530,   531,   532,    68,
      69,    70,    71,    72,   280,   240,   282,   125,    43,    70,
     272,   273,   274,    48,    49,    50,   124,    91,   294,     0,
       1,    99,    96,   607,     5,   133,    38,    39,   394,    91,
      65,    66,   394,   267,    96,    68,    69,    70,    71,    72,
     101,    15,    16,   104,   105,   106,   107,   108,   109,   415,
     122,     5,   113,    68,    69,    70,    71,    72,    27,    28,
     129,   554,    68,    69,    70,    71,    72,    38,   434,   435,
      68,    69,    70,    71,    72,    38,   442,   443,    91,   122,
     394,   542,   125,    96,     9,   451,   125,   124,    13,    14,
     127,   126,    68,    69,    70,    71,    72,   125,   464,    68,
      69,    70,    71,    72,   165,   138,   125,   473,   474,   471,
     472,    68,    69,    70,    71,    72,    68,    69,    70,    71,
      72,   182,   183,   138,    68,    69,    70,    71,   103,   104,
     105,   106,   138,    35,    36,   196,   450,    62,    63,    64,
     138,   126,   404,   128,   510,   206,   207,   125,    38,     4,
      38,   127,     7,     8,   124,   216,   124,   471,   472,    68,
      69,    70,    71,    72,   124,   140,   499,   500,    19,   128,
     127,   232,   233,   539,    96,   127,   122,   238,   239,   125,
     241,   242,   243,   244,   245,   246,   247,   248,   249,   250,
     251,   252,   126,   254,   255,   256,   257,   258,   259,   260,
     261,   262,   263,   264,   265,   266,     6,   521,   522,     9,
      10,    11,    12,    13,   126,   128,    27,    28,   127,   126,
     101,   282,   283,   128,    35,    36,    55,    56,   128,    58,
      59,   292,    61,   128,   600,   122,   103,   104,   105,   106,
     606,   103,   104,   105,   106,   125,   113,   114,   115,    17,
     124,   113,   114,   115,    55,   134,   317,    68,    69,    70,
      71,    72,    62,    63,    64,   127,    56,    24,   329,    96,
     137,   604,   605,   140,    62,    63,    64,   134,   140,    57,
     127,   342,   110,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,    53,    33,    55,    56,
      57,    58,    59,    53,    61,    62,    63,    64,    65,    66,
      67,   103,   104,   105,   106,     7,    73,    74,    75,    76,
      77,   113,   114,   115,    68,    69,    70,   103,   104,   105,
     106,   125,   134,   394,    57,   127,    58,   113,   114,   115,
      97,    98,    68,    69,    70,    71,    72,   124,   140,   106,
     107,   124,   109,   129,    91,   112,   417,   114,   128,   116,
     103,   104,   105,   106,   140,   128,   137,    58,   429,   126,
     113,   114,   115,   434,   132,   103,   104,   105,   106,   136,
      92,    92,   139,    51,    92,    92,   114,   115,    92,   450,
      32,   125,   125,   454,   125,   125,   125,   140,   125,    57,
      17,   204,   205,   464,   128,    73,    74,    75,    76,    77,
     471,   472,   140,   123,   475,   476,   219,   220,   221,   222,
     223,    47,    48,    49,    50,   124,    52,    53,   134,    55,
      56,    57,    58,    59,    53,    61,   497,   124,   124,    91,
     135,   135,   124,   504,    35,   506,    52,    53,    44,    55,
      56,    57,    58,    59,   134,    61,    24,    68,    91,    99,
     521,   522,    99,    55,    58,   129,    56,   129,   125,   530,
     531,   532,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,   125,    55,    56,    57,
      58,    59,   127,    61,   124,   127,   134,    65,    66,    67,
     101,   101,   125,   125,   125,    73,    74,    75,    76,    77,
      48,    49,    50,   144,    52,    53,    99,    55,    56,    57,
      58,    59,     3,    61,   225,    93,   481,    22,   146,    97,
      98,   295,   161,   482,   487,   594,   484,    42,   106,   107,
     152,   109,   157,   332,   112,   155,   114,   570,   116,   394,
     447,   572,   616,   447,   578,    78,    24,   449,   126,   607,
     132,   452,   554,    92,   424,    -1,    -1,    -1,   136,    -1,
      -1,   139,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    -1,    55,    56,    57,
      58,    59,    -1,    61,    -1,    -1,    -1,    65,    66,    67,
      -1,    -1,    -1,    -1,    -1,    73,    74,    75,    76,    77,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    27,    28,    -1,    -1,    31,    -1,    97,
      98,    35,    36,    -1,    -1,    -1,    -1,    -1,   106,   107,
      -1,   109,    -1,    -1,   112,    -1,   114,    -1,   116,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   126,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    27,    28,   136,    -1,
      31,   139,    -1,    -1,    -1,    79,    80,    81,    82,    83,
      84,    85,    86,    87,    88,    89,    90,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   103,
     104,   105,   106,    -1,    -1,    -1,   110,   111,    -1,   113,
     114,   115,    -1,    -1,   118,   119,   120,   121,    79,    80,
      81,    82,    83,    84,    85,    86,    87,    88,    89,    90,
      -1,    -1,    -1,    -1,    -1,    -1,   140,    -1,    -1,    -1,
      -1,    -1,   103,   104,   105,   106,    -1,    -1,    -1,   110,
     111,    -1,   113,   114,   115,    -1,    -1,   118,   119,   120,
     121,    -1,    -1,    -1,    -1,    -1,   127,    -1,    -1,    -1,
      -1,    -1,    -1,    41,    42,    43,    44,    45,    46,   140,
      48,    49,    50,    51,    52,    53,    -1,    55,    56,    57,
      58,    59,    60,    61,    -1,    -1,    -1,    65,    66,    67,
      -1,    -1,    -1,    -1,    -1,    73,    74,    75,    76,    77,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    97,
      98,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   106,   107,
      -1,   109,    -1,    -1,   112,    41,   114,    -1,   116,    45,
      46,    -1,    -1,    -1,    -1,    -1,    52,    53,   126,    55,
      56,    57,    58,    59,    60,    61,   134,    -1,   136,    -1,
     138,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    97,    98,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     106,    -1,    -1,   109,    -1,    -1,   112,    41,   114,    43,
     116,    45,    46,    -1,    -1,    49,    -1,    -1,    52,    53,
     126,    55,    56,    57,    58,    59,    -1,    61,   134,    -1,
     136,    -1,   138,    41,    42,    43,    44,    45,    46,    -1,
      48,    49,    50,    51,    52,    53,    -1,    55,    56,    57,
      58,    59,    -1,    61,    -1,    -1,    -1,    65,    66,    67,
      -1,    -1,    -1,    97,    98,    73,    74,    75,    76,    77,
      -1,    -1,   106,   107,    -1,   109,    -1,    -1,   112,    -1,
     114,    -1,   116,    -1,    -1,    93,    -1,    -1,    -1,    97,
      98,    -1,   126,    -1,    -1,    -1,    -1,    -1,   106,   107,
      -1,   109,   136,    -1,   112,    -1,   114,    -1,   116,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   126,    -1,
      -1,    -1,    41,    42,    43,    44,    45,    46,   136,    48,
      49,    50,    51,    52,    53,    -1,    55,    56,    57,    58,
      59,    -1,    61,    -1,    -1,    -1,    65,    66,    67,    -1,
      -1,    -1,    -1,    -1,    73,    74,    75,    76,    77,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    93,    -1,    -1,    -1,    97,    98,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   106,   107,    -1,
     109,    -1,    -1,   112,    -1,   114,    -1,   116,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   126,    -1,    -1,
      -1,    41,    42,    43,    44,    45,    46,   136,    48,    49,
      50,    51,    52,    53,    -1,    55,    56,    57,    58,    59,
      -1,    61,    -1,    -1,    -1,    65,    66,    67,    -1,    -1,
      -1,    -1,    -1,    73,    74,    75,    76,    77,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    97,    98,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   106,   107,    -1,   109,
      -1,    -1,   112,    -1,   114,    -1,   116,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   126,    -1,    -1,    -1,
      41,    -1,    43,    44,    45,    46,   136,    48,    49,    50,
      -1,    52,    53,    -1,    55,    56,    57,    58,    59,    -1,
      61,    -1,    -1,    -1,    -1,    41,    -1,    -1,    -1,    45,
      46,    -1,    -1,    -1,    -1,    -1,    52,    53,    -1,    55,
      56,    57,    58,    59,    -1,    61,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    97,    98,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   106,   107,    -1,   109,   110,
      -1,   112,    -1,   114,    -1,   116,    -1,    93,    -1,    -1,
      -1,    97,    98,    -1,    -1,   126,    -1,    -1,    -1,    -1,
     106,    -1,    -1,   109,    -1,   136,   112,    41,   114,    -1,
     116,    45,    46,    -1,    -1,    -1,    -1,    -1,    52,    53,
     126,    55,    56,    57,    58,    59,    -1,    61,    -1,    -1,
     136,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    97,    98,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   106,    -1,    -1,   109,    -1,    -1,   112,    -1,
     114,    -1,   116,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   126,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   136,    79,    80,    81,    82,    83,    84,    85,
      86,    87,    88,    89,    90,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   103,   104,   105,
     106,    -1,    -1,    -1,   110,   111,    -1,   113,   114,   115,
      -1,    -1,   118,   119,   120,   121,    -1,    -1,    -1,    -1,
      -1,   127,    79,    80,    81,    82,    83,    84,    85,    86,
      87,    88,    89,    90,   140,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   103,   104,   105,   106,
      -1,    -1,    -1,   110,   111,    -1,   113,   114,   115,    -1,
      -1,   118,   119,   120,   121,    -1,    -1,    -1,    -1,    -1,
     127,    79,    80,    81,    82,    83,    84,    85,    86,    87,
      88,    89,    90,   140,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   103,   104,   105,   106,    -1,
      -1,    -1,   110,   111,    -1,   113,   114,   115,    -1,    -1,
     118,   119,   120,   121,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   140
  };

  const short
  database_parser::yystos_[] =
  {
       0,     1,   157,   158,   159,   160,     0,   159,     5,   173,
      38,    39,    97,   195,   125,   174,   176,     4,     7,     8,
     177,   179,   180,   185,     5,   125,    38,     6,   185,     9,
      13,    14,    62,    63,    64,   186,   191,   193,   196,   197,
     198,   219,   220,   221,    38,    39,   178,   182,   136,     5,
     195,   195,   195,    38,   226,   227,    38,    94,    95,   228,
     229,    38,   222,   223,    15,    16,   199,   200,   201,   202,
      24,    40,    41,    42,    43,    44,    45,    46,    47,    48,
      49,    50,    51,    52,    53,    55,    56,    57,    58,    59,
      61,    65,    66,    67,    73,    74,    75,    76,    77,    97,
      98,   106,   107,   109,   112,   114,   116,   126,   136,   139,
     169,   171,   217,   219,   234,   235,   248,   249,   250,   251,
     252,   253,   256,   257,   261,   262,   265,   266,   269,   270,
     272,   273,   274,   275,   276,   277,   288,   289,   290,   294,
     295,   300,   125,   221,   125,   183,   181,   175,   195,   125,
     125,   125,   124,    38,    38,   124,   224,   124,    19,   208,
     209,   203,   234,   126,   254,   126,   286,   286,   254,    96,
     291,    96,   278,   278,   101,   271,   273,   273,   273,   273,
     273,    53,   126,   136,   288,   267,   288,   288,   288,    53,
      93,   234,   235,   256,   288,    60,   126,   134,   138,   256,
     288,   299,   234,   234,    20,    24,   123,   124,   128,   161,
     162,   163,   166,   168,    23,    26,    33,    27,    28,    68,
      69,    70,    71,    72,   128,   164,   165,   166,   168,   286,
      48,    50,   110,   126,   264,   265,   285,   288,    27,    28,
      31,    79,    80,    81,    82,    83,    84,    85,    86,    87,
      88,    89,    90,   103,   104,   105,   106,   110,   111,   113,
     114,   115,   118,   119,   120,   121,   140,   128,   167,   168,
     286,     6,    10,    11,    12,   184,   187,   191,   193,   219,
     183,   125,   194,   192,   227,   229,   122,   223,    17,    16,
     193,   195,   204,   205,   206,   207,   208,   255,   256,   287,
     288,   134,   279,    55,   281,    56,   283,   256,   273,   273,
     273,   273,    53,    93,   288,   288,   134,    91,    57,   127,
     127,   127,   285,    53,   256,   288,   296,   297,   138,   124,
     138,   271,   271,   234,   234,    47,    48,    49,    50,    52,
     290,   162,    33,    53,   251,   256,   288,   256,   256,   271,
     271,   271,   271,   271,   165,   288,   256,   122,   262,   288,
     288,   251,   288,   288,   288,   288,   288,   288,   288,   288,
     288,   288,   288,   288,   288,   288,   288,   288,   288,   288,
     288,   288,   288,   288,   288,   288,   288,   168,     7,   195,
     195,   195,   138,   218,   219,   230,   231,   232,   233,   235,
     256,   288,   217,   225,    18,   195,   210,   211,   212,   214,
     215,   125,   217,   219,   201,   124,   127,   124,   127,    55,
      56,    58,    59,    61,   292,   293,   134,   282,   284,    91,
      57,    58,   256,   288,    91,   137,   285,   298,    58,    53,
      54,   109,   142,   145,   259,   260,   288,   132,   236,   236,
      92,    92,    92,    92,    92,   256,   288,   256,   256,   256,
     256,   256,   127,   256,    32,   125,   125,   125,   125,   125,
     230,    35,    36,    35,    36,    35,    36,   125,    57,    24,
     195,   216,   122,   125,   123,   124,   134,    17,   256,   288,
     135,   293,    53,   280,   124,   124,   288,    91,   135,   127,
     127,   256,   288,   256,   135,   124,    35,   256,   256,   123,
     136,    47,    53,   101,   237,   238,   239,   240,   241,   242,
     134,   243,   243,   234,   256,   266,    44,   288,   256,   288,
     188,   189,   190,   235,   235,   256,   256,   288,   288,    91,
      99,    99,   161,   211,   212,   214,   213,   214,   210,    53,
     135,    55,    56,   288,   268,   286,   286,   170,   172,   138,
     288,    58,   288,   143,   146,   260,   256,   101,   239,   241,
     123,   133,   124,   133,   133,   242,    47,    53,    99,   244,
     245,   246,   247,   234,   234,   129,   129,   129,   129,   129,
     217,   217,   217,   256,   134,   124,   135,   125,    48,    50,
     126,   262,   263,   269,   127,   127,   137,   136,   258,   260,
     258,   138,   101,   238,   240,   246,   123,   135,   135,   247,
     125,   125,   125,   213,   214,   256,   286,   286,   256,   259,
     144,   245,   135,   127,   138,   138,   258
  };

  const short
  database_parser::yyr1_[] =
  {
       0,   156,   157,   157,   157,   158,   158,   160,   159,   161,
     161,   162,   162,   162,   163,   164,   164,   165,   165,   166,
     166,   166,   167,   167,   168,   169,   170,   169,   169,   171,
     172,   171,   171,   174,   173,   175,   175,   176,   176,   177,
     178,   178,   179,   179,   181,   180,   182,   180,   183,   183,
     184,   184,   184,   185,   185,   186,   186,   186,   186,   188,
     187,   187,   189,   187,   190,   187,   192,   191,   194,   193,
     195,   195,   195,   196,   197,   198,   199,   200,   199,   201,
     201,   202,   203,   203,   204,   205,   205,   206,   205,   205,
     205,   207,   208,   209,   209,   210,   210,   211,   211,   212,
     212,   212,   212,   212,   213,   213,   214,   214,   214,   214,
     214,   214,   215,   216,   215,   217,   217,   218,   218,   219,
     220,   220,   221,   221,   221,   222,   222,   224,   225,   223,
     226,   226,   227,   228,   228,   229,   229,   229,   230,   230,
     230,   231,   231,   232,   232,   233,   233,   234,   234,   235,
     235,   235,   235,   235,   235,   235,   235,   235,   235,   236,
     236,   236,   236,   237,   237,   238,   239,   239,   240,   241,
     241,   242,   242,   243,   243,   243,   244,   244,   245,   246,
     246,   247,   247,   248,   248,   249,   249,   250,   250,   250,
     250,   250,   250,   250,   251,   252,   252,   252,   252,   252,
     253,   253,   254,   255,   255,   256,   256,   256,   256,   256,
     256,   256,   257,   258,   258,   259,   259,   259,   260,   260,
     260,   260,   260,   261,   261,   261,   262,   262,   262,   263,
     263,   263,   263,   263,   264,   264,   265,   265,   265,   265,
     266,   266,   266,   266,   266,   266,   266,   266,   266,   266,
     266,   266,   266,   266,   266,   266,   266,   266,   266,   267,
     268,   266,   269,   270,   270,   271,   271,   272,   272,   272,
     272,   272,   272,   272,   273,   273,   273,   273,   273,   273,
     274,   275,   275,   276,   277,   278,   279,   278,   280,   280,
     281,   282,   281,   283,   284,   283,   285,   285,   286,   287,
     287,   288,   288,   288,   288,   289,   289,   289,   289,   289,
     290,   290,   290,   290,   290,   290,   290,   290,   291,   291,
     292,   292,   293,   293,   293,   293,   293,   294,   294,   294,
     294,   294,   294,   294,   294,   295,   295,   295,   295,   295,
     295,   295,   295,   295,   295,   295,   297,   296,   298,   296,
     299,   299,   300,   300
  };

  const signed char
  database_parser::yyr2_[] =
  {
       0,     2,     0,     1,     1,     2,     1,     0,     2,     1,
       2,     1,     1,     1,     5,     1,     2,     1,     1,     5,
       5,     5,     1,     2,     5,     6,     0,     8,     2,     6,
       0,     8,     2,     0,    10,     0,     1,     0,     2,     4,
       1,     1,     1,     2,     0,     6,     0,     7,     0,     2,
       1,     1,     1,     0,     2,     1,     1,     1,     1,     0,
       6,     1,     0,     6,     0,     6,     0,     6,     0,     6,
       1,     1,     1,     2,     2,     3,     1,     0,     2,     3,
       1,     1,     0,     2,     2,     5,     2,     0,     2,     1,
       1,     2,     4,     0,     1,     1,     3,     1,     3,     0,
       1,     4,     3,     6,     1,     3,     1,     1,     2,     3,
       2,     3,     1,     0,     3,     1,     2,     1,     2,     2,
       1,     2,     2,     2,     2,     1,     3,     0,     0,     7,
       1,     3,     1,     1,     3,     1,     2,     2,     1,     1,
       1,     3,     3,     3,     3,     3,     3,     1,     1,     1,
       1,     2,     3,     3,     6,     6,     2,     3,     2,     0,
       3,     3,     3,     1,     3,     2,     1,     3,     2,     1,
       2,     1,     1,     0,     3,     3,     1,     3,     2,     1,
       2,     1,     1,     1,     3,     1,     1,     3,     3,     3,
       4,     4,     5,     5,     1,     1,     3,     3,     3,     3,
       2,     2,     3,     1,     3,     1,     2,     1,     1,     3,
       1,     1,     7,     1,     3,     0,     1,     3,     1,     1,
       3,     6,     4,     1,     1,     3,     2,     4,     3,     1,
       1,     1,     3,     1,     1,     3,     1,     1,     1,     1,
       1,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     0,
       0,     7,     2,     1,     1,     0,     1,     3,     4,     4,
       4,     4,     4,     1,     1,     2,     3,     3,     3,     3,
       1,     1,     1,     3,     3,     0,     0,     5,     1,     2,
       1,     0,     4,     1,     0,     4,     0,     2,     3,     1,
       3,     1,     1,     2,     1,     1,     1,     1,     1,     3,
       2,     1,     1,     1,     1,     1,     1,     1,     0,     4,
       1,     2,     1,     1,     1,     1,     1,     2,     1,     2,
       3,     3,     2,     3,     3,     2,     1,     3,     6,     9,
       3,     3,     3,     2,     2,     2,     0,     2,     0,     4,
       1,     3,     1,     1
  };


#if MLIDEBUG || 1
  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a YYNTOKENS, nonterminals.
  const char*
  const database_parser::yytname_[] =
  {
  "\"end of file\"", "error", "\"invalid token\"", "\"token error\"",
  "\"include\"", "\"theory\"", "\"end\"", "\"formal system\"",
  "\"system\"", "\"definition\"", "\"postulate\"", "\"axiom\"", "\"rule\"",
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
  "\"↦\"", "\"⤇\"", "\"𝛌\"", "\"°\"", "\"•\"", "\"ₓ\"",
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
  "formal_system", "$@5", "$@6", "formal_system_body",
  "formal_system_body_item", "theory_body_list", "theory_body_item",
  "postulate", "$@7", "$@8", "$@9", "conjecture", "$@10",
  "definition_labelstatement", "$@11", "statement_name", "theorem",
  "theorem_statement", "theorem_head", "proof", "$@12", "compound-proof",
  "proof_head", "proof_lines", "statement_label", "proof_line", "$@13",
  "subproof_statement", "proof_of_conclusion", "optional-result",
  "find_statement", "find_statement_list", "find_statement_sequence",
  "find_definition_sequence", "find_statement_item", "find_statement_name",
  "@14", "statement", "definition_statement", "identifier_declaration",
  "declarator_list", "declarator_identifier_list",
  "identifier_function_list", "identifier_function_name", "$@15", "$@16",
  "identifier_constant_list", "identifier_constant_name",
  "identifier_variable_list", "identifier_variable_name", "definition",
  "metaformula_definition", "object_formula_definition", "term_definition",
  "metaformula", "pure_metaformula", "optional_varied_variable_matrix",
  "varied_variable_conclusions", "varied_variable_conclusion",
  "varied_variable_premises", "varied_variable_premise",
  "varied_variable_set", "varied_variable",
  "optional_varied_in_reduction_variable_sequence",
  "varied_in_reduction_variable_conclusions",
  "varied_in_reduction_variable_conclusion",
  "varied_in_reduction_variable_set", "varied_in_reduction_variable",
  "simple_metaformula", "atomic_metaformula", "special_metaformula",
  "meta_object_free", "metapredicate", "metapredicate_function",
  "metapredicate_argument", "metapredicate_argument_body",
  "object_formula", "hoare_triple", "code_statement", "code_sequence",
  "code_term", "very_simple_formula", "quantized_formula",
  "simple_formula", "quantized_body", "atomic_formula", "predicate",
  "$@17", "$@18", "predicate_expression", "predicate_identifier",
  "optional_superscript_natural_number_value", "logic_formula",
  "prefix_logic_formula", "quantizer_declaration",
  "quantized_variable_list", "all_variable_list", "exist_variable_list",
  "exclusion_set", "$@19", "exclusion_list", "all_identifier_list", "$@20",
  "exist_identifier_list", "$@21", "optional_in_term", "tuple",
  "tuple_body", "term", "simple_term", "term_identifier",
  "variable_exclusion_set", "variable_exclusion_list", "bound_variable",
  "function_term", "set_term", "implicit_set_identifier_list", "$@22",
  "$@23", "set_member_list", "function_term_identifier", YY_NULLPTR
  };
#endif


#if MLIDEBUG
  const short
  database_parser::yyrline_[] =
  {
       0,   782,   782,   783,   784,   793,   794,   799,   799,   804,
     805,   812,   813,   814,   819,   828,   829,   836,   837,   842,
     847,   852,   861,   862,   869,   878,   881,   881,   884,   889,
     892,   892,   895,   901,   900,   919,   920,   925,   926,   930,
     942,   943,   948,   949,   955,   954,   959,   958,   966,   967,
     972,   973,   974,   979,   980,   990,   991,   992,   994,  1000,
     999,  1005,  1007,  1006,  1019,  1018,  1035,  1034,  1044,  1043,
    1053,  1054,  1055,  1060,  1071,  1081,  1091,  1092,  1092,  1106,
    1111,  1116,  1125,  1126,  1131,  1139,  1170,  1185,  1185,  1189,
    1200,  1205,  1215,  1226,  1227,  1232,  1233,  1241,  1244,  1252,
    1253,  1255,  1259,  1263,  1272,  1274,  1282,  1285,  1288,  1301,
    1315,  1320,  1330,  1344,  1344,  1386,  1387,  1431,  1432,  1439,
    1444,  1445,  1450,  1451,  1452,  1457,  1458,  1469,  1470,  1469,
    1504,  1505,  1510,  1525,  1526,  1531,  1542,  1553,  1568,  1569,
    1570,  1575,  1579,  1592,  1596,  1609,  1619,  1627,  1628,  1633,
    1634,  1635,  1638,  1641,  1644,  1712,  1773,  1775,  1776,  1782,
    1783,  1784,  1785,  1789,  1790,  1803,  1815,  1816,  1828,  1840,
    1841,  1852,  1857,  1867,  1868,  1869,  1873,  1874,  1886,  1899,
    1900,  1911,  1916,  1925,  1926,  1931,  1932,  1944,  1947,  1950,
    1953,  1956,  1959,  1963,  1971,  1976,  1977,  1980,  1983,  1986,
    1993,  1997,  2005,  2010,  2014,  2022,  2023,  2026,  2027,  2028,
    2029,  2030,  2035,  2046,  2047,  2052,  2053,  2054,  2059,  2060,
    2061,  2062,  2063,  2068,  2069,  2070,  2075,  2082,  2089,  2100,
    2101,  2102,  2103,  2104,  2110,  2111,  2115,  2116,  2117,  2118,
    2124,  2125,  2126,  2129,  2130,  2133,  2134,  2135,  2136,  2137,
    2138,  2139,  2140,  2142,  2143,  2144,  2145,  2146,  2147,  2148,
    2149,  2148,  2159,  2167,  2168,  2173,  2174,  2186,  2192,  2198,
    2204,  2210,  2216,  2222,  2227,  2228,  2232,  2236,  2240,  2244,
    2252,  2256,  2257,  2262,  2274,  2286,  2287,  2287,  2295,  2296,
    2306,  2310,  2310,  2320,  2324,  2324,  2335,  2336,  2343,  2348,
    2353,  2362,  2363,  2364,  2367,  2372,  2373,  2374,  2375,  2376,
    2381,  2387,  2388,  2389,  2390,  2391,  2392,  2393,  2398,  2399,
    2404,  2405,  2414,  2415,  2416,  2417,  2418,  2423,  2426,  2427,
    2431,  2435,  2439,  2443,  2447,  2455,  2456,  2457,  2458,  2462,
    2470,  2474,  2478,  2482,  2486,  2490,  2498,  2498,  2503,  2503,
    2513,  2517,  2526,  2527
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
     145,   146,   147,   148,   149,   150,   151,   152,   153,   154,
     155
    };
    // Last valid token kind.
    const int code_max = 410;

    if (t <= 0)
      return symbol_kind::S_YYEOF;
    else if (t <= code_max)
      return static_cast <symbol_kind_type> (translate_table[t]);
    else
      return symbol_kind::S_YYUNDEF;
  }

#line 25 "../../mli-root/src/database-parser.yy"
} // mli
#line 6731 "../../mli-root/src/database-parser.cc"

#line 2531 "../../mli-root/src/database-parser.yy"


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

