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
#line 787 "../../mli-root/src/database-parser.yy"
           {}
#line 2400 "../../mli-root/src/database-parser.cc"
    break;

  case 3: // file: file_contents
#line 788 "../../mli-root/src/database-parser.yy"
                  {}
#line 2406 "../../mli-root/src/database-parser.cc"
    break;

  case 4: // file: error
#line 789 "../../mli-root/src/database-parser.yy"
          {
      declaration_context = false;
      bound_variable_type = free_variable_context;
      YYABORT;
    }
#line 2416 "../../mli-root/src/database-parser.cc"
    break;

  case 5: // file_contents: file_contents command
#line 798 "../../mli-root/src/database-parser.yy"
                          {}
#line 2422 "../../mli-root/src/database-parser.cc"
    break;

  case 6: // file_contents: command
#line 799 "../../mli-root/src/database-parser.yy"
                          {}
#line 2428 "../../mli-root/src/database-parser.cc"
    break;

  case 7: // $@1: %empty
#line 804 "../../mli-root/src/database-parser.yy"
    { symbol_table.clear(); }
#line 2434 "../../mli-root/src/database-parser.cc"
    break;

  case 8: // command: $@1 theory
#line 804 "../../mli-root/src/database-parser.yy"
                                     {}
#line 2440 "../../mli-root/src/database-parser.cc"
    break;

  case 9: // metaformula_substitution_sequence: substitution_for_metaformula
#line 809 "../../mli-root/src/database-parser.yy"
                                    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2446 "../../mli-root/src/database-parser.cc"
    break;

  case 10: // metaformula_substitution_sequence: metaformula_substitution_sequence substitution_for_metaformula
#line 810 "../../mli-root/src/database-parser.yy"
                                                                         {
      yylhs.value.as < ref6<unit> > () =  val<substitution>(yystack_[1].value.as < ref6<unit> > ()) * val<substitution>(yystack_[0].value.as < ref6<unit> > ());
    }
#line 2454 "../../mli-root/src/database-parser.cc"
    break;

  case 11: // substitution_for_metaformula: metaformula_substitution
#line 817 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2460 "../../mli-root/src/database-parser.cc"
    break;

  case 12: // substitution_for_metaformula: formula_substitution
#line 818 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2466 "../../mli-root/src/database-parser.cc"
    break;

  case 13: // substitution_for_metaformula: term_substitution
#line 819 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2472 "../../mli-root/src/database-parser.cc"
    break;

  case 14: // metaformula_substitution: "[" "metaformula variable" "⤇" metaformula "]"
#line 824 "../../mli-root/src/database-parser.yy"
                                                       {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2482 "../../mli-root/src/database-parser.cc"
    break;

  case 15: // formula_substitution_sequence: substitution_for_formula
#line 833 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2488 "../../mli-root/src/database-parser.cc"
    break;

  case 16: // formula_substitution_sequence: formula_substitution_sequence substitution_for_formula
#line 834 "../../mli-root/src/database-parser.yy"
                                                                 {
      yylhs.value.as < ref6<unit> > () = val<substitution>(yystack_[1].value.as < ref6<unit> > ()) * val<substitution>(yystack_[0].value.as < ref6<unit> > ());
    }
#line 2496 "../../mli-root/src/database-parser.cc"
    break;

  case 17: // substitution_for_formula: formula_substitution
#line 841 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2502 "../../mli-root/src/database-parser.cc"
    break;

  case 18: // substitution_for_formula: term_substitution
#line 842 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2508 "../../mli-root/src/database-parser.cc"
    break;

  case 19: // formula_substitution: "[" "object formula variable" "⤇" object_formula "]"
#line 847 "../../mli-root/src/database-parser.yy"
                                                             {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2518 "../../mli-root/src/database-parser.cc"
    break;

  case 20: // formula_substitution: "[" "predicate variable" "⤇" predicate "]"
#line 852 "../../mli-root/src/database-parser.yy"
                                                   {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2528 "../../mli-root/src/database-parser.cc"
    break;

  case 21: // formula_substitution: "[" "atom variable" "⤇" "atom constant" "]"
#line 857 "../../mli-root/src/database-parser.yy"
                                                  {
      val<variable> v(yystack_[3].value.as < val<unit> > ());
      val<formula> f(yystack_[1].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2538 "../../mli-root/src/database-parser.cc"
    break;

  case 22: // term_substitution_sequence: term_substitution
#line 866 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2544 "../../mli-root/src/database-parser.cc"
    break;

  case 23: // term_substitution_sequence: term_substitution_sequence term_substitution
#line 867 "../../mli-root/src/database-parser.yy"
                                                       {
      yylhs.value.as < ref6<unit> > () = val<substitution>(yystack_[1].value.as < ref6<unit> > ()) * val<substitution>(yystack_[0].value.as < ref6<unit> > ());
    }
#line 2552 "../../mli-root/src/database-parser.cc"
    break;

  case 24: // term_substitution: "[" term_identifier "⤇" term "]"
#line 874 "../../mli-root/src/database-parser.yy"
                                           {
      val<variable> v(yystack_[3].value.as < ref6<unit> > ());
      val<formula> f(yystack_[1].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = val<explicit_substitution>(make, v, f);
    }
#line 2562 "../../mli-root/src/database-parser.cc"
    break;

  case 25: // predicate_function_application: "(" "object variable" "↦" object_formula ")" tuple
#line 883 "../../mli-root/src/database-parser.yy"
                                                              {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[4].value.as < val<unit> > (), yystack_[2].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2570 "../../mli-root/src/database-parser.cc"
    break;

  case 26: // $@2: %empty
#line 886 "../../mli-root/src/database-parser.yy"
                                                           { symbol_table.pop_level(); }
#line 2576 "../../mli-root/src/database-parser.cc"
    break;

  case 27: // predicate_function_application: "(" "𝛌" "function map variable" "↦" object_formula $@2 ")" tuple
#line 886 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[5].value.as < val<unit> > (), yystack_[3].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2584 "../../mli-root/src/database-parser.cc"
    break;

  case 28: // predicate_function_application: "predicate" tuple
#line 889 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = val<function_application>(make, yystack_[1].value.as < val<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 2590 "../../mli-root/src/database-parser.cc"
    break;

  case 29: // term_function_application: "(" "object variable" "↦" term ")" tuple
#line 894 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[4].value.as < val<unit> > (), yystack_[2].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2598 "../../mli-root/src/database-parser.cc"
    break;

  case 30: // $@3: %empty
#line 897 "../../mli-root/src/database-parser.yy"
                                                 { symbol_table.pop_level(); }
#line 2604 "../../mli-root/src/database-parser.cc"
    break;

  case 31: // term_function_application: "(" "𝛌" "function map variable" "↦" term $@3 ")" tuple
#line 897 "../../mli-root/src/database-parser.yy"
                                                                                            {
      yylhs.value.as < ref6<unit> > () = val<function_application>(make, val<function_map>(make, yystack_[5].value.as < val<unit> > (), yystack_[3].value.as < ref6<unit> > ()), yystack_[0].value.as < ref6<unit> > ());
    }
#line 2612 "../../mli-root/src/database-parser.cc"
    break;

  case 32: // term_function_application: "function" tuple
#line 900 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.as < ref6<unit> > () = val<function_application>(make, yystack_[1].value.as < val<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 2618 "../../mli-root/src/database-parser.cc"
    break;

  case 33: // $@4: %empty
#line 906 "../../mli-root/src/database-parser.yy"
        { theory_ = ref1<theory>(make, yystack_[1].value.as < std::string > ());
          yypval.insert(theory_);
          symbol_table.push_level();
    }
#line 2627 "../../mli-root/src/database-parser.cc"
    break;

  case 34: // theory: "theory" statement_name "." $@4 include_theories theory_body "end" "theory" end_theory_name "."
#line 912 "../../mli-root/src/database-parser.yy"
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
#line 924 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < std::pair<std::string, bool> > () = std::make_pair(std::string{}, false); }
#line 2646 "../../mli-root/src/database-parser.cc"
    break;

  case 36: // end_theory_name: statement_name
#line 925 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < std::pair<std::string, bool> > () = std::make_pair(yystack_[0].value.as < std::string > (), true); }
#line 2652 "../../mli-root/src/database-parser.cc"
    break;

  case 37: // include_theories: %empty
#line 930 "../../mli-root/src/database-parser.yy"
           {}
#line 2658 "../../mli-root/src/database-parser.cc"
    break;

  case 38: // include_theories: include_theories include_theory
#line 931 "../../mli-root/src/database-parser.yy"
                                    {}
#line 2664 "../../mli-root/src/database-parser.cc"
    break;

  case 39: // include_theory: "include" "theory" theory_name "."
#line 935 "../../mli-root/src/database-parser.yy"
                                         {
      std::optional<ref1<theory>> th = yypval.find(yystack_[1].value.as < std::string > ());

      if (!th)
        throw syntax_error(yystack_[1].location, "Include theory " + yystack_[1].value.as < std::string > () + " not found.");

      theory_->insert(*th);
    }
#line 2677 "../../mli-root/src/database-parser.cc"
    break;

  case 40: // theory_name: "name"
#line 947 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2683 "../../mli-root/src/database-parser.cc"
    break;

  case 41: // theory_name: "label"
#line 948 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2689 "../../mli-root/src/database-parser.cc"
    break;

  case 42: // theory_body: theory_body_list
#line 953 "../../mli-root/src/database-parser.yy"
                     {}
#line 2695 "../../mli-root/src/database-parser.cc"
    break;

  case 43: // theory_body: formal_system theory_body_list
#line 954 "../../mli-root/src/database-parser.yy"
                                   {}
#line 2701 "../../mli-root/src/database-parser.cc"
    break;

  case 44: // $@5: %empty
#line 960 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(); }
#line 2707 "../../mli-root/src/database-parser.cc"
    break;

  case 45: // formal_system: "system" "name" "{" $@5 formal_system_body "}"
#line 962 "../../mli-root/src/database-parser.yy"
        { symbol_table.pop_level(); }
#line 2713 "../../mli-root/src/database-parser.cc"
    break;

  case 46: // $@6: %empty
#line 964 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(); }
#line 2719 "../../mli-root/src/database-parser.cc"
    break;

  case 47: // formal_system: "formal system" "." $@6 formal_system_body "end" "formal system" "."
#line 966 "../../mli-root/src/database-parser.yy"
                              { symbol_table.pop_level(); }
#line 2725 "../../mli-root/src/database-parser.cc"
    break;

  case 48: // formal_system_body: %empty
#line 971 "../../mli-root/src/database-parser.yy"
           {}
#line 2731 "../../mli-root/src/database-parser.cc"
    break;

  case 49: // formal_system_body: formal_system_body formal_system_body_item
#line 972 "../../mli-root/src/database-parser.yy"
                                               {}
#line 2737 "../../mli-root/src/database-parser.cc"
    break;

  case 50: // formal_system_body_item: identifier_declaration
#line 977 "../../mli-root/src/database-parser.yy"
                           {}
#line 2743 "../../mli-root/src/database-parser.cc"
    break;

  case 51: // formal_system_body_item: postulate
#line 978 "../../mli-root/src/database-parser.yy"
                 { theory_->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 2749 "../../mli-root/src/database-parser.cc"
    break;

  case 52: // formal_system_body_item: definition_labelstatement
#line 979 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref4<statement>(yystack_[0].value.as < val<definition> > ())); }
#line 2755 "../../mli-root/src/database-parser.cc"
    break;

  case 53: // theory_body_list: %empty
#line 984 "../../mli-root/src/database-parser.yy"
           {}
#line 2761 "../../mli-root/src/database-parser.cc"
    break;

  case 54: // theory_body_list: theory_body_list theory_body_item
#line 985 "../../mli-root/src/database-parser.yy"
                                      {}
#line 2767 "../../mli-root/src/database-parser.cc"
    break;

  case 55: // theory_body_item: theorem
#line 995 "../../mli-root/src/database-parser.yy"
               { theory_->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 2773 "../../mli-root/src/database-parser.cc"
    break;

  case 56: // theory_body_item: identifier_declaration
#line 996 "../../mli-root/src/database-parser.yy"
                           {}
#line 2779 "../../mli-root/src/database-parser.cc"
    break;

  case 57: // theory_body_item: conjecture
#line 997 "../../mli-root/src/database-parser.yy"
                  { theory_->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 2785 "../../mli-root/src/database-parser.cc"
    break;

  case 58: // theory_body_item: definition_labelstatement
#line 999 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref4<statement>(yystack_[0].value.as < val<definition> > ())); }
#line 2791 "../../mli-root/src/database-parser.cc"
    break;

  case 59: // $@7: %empty
#line 1005 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2797 "../../mli-root/src/database-parser.cc"
    break;

  case 60: // postulate: "postulate" statement_name "." $@7 statement "."
#line 1006 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::postulate_, yystack_[4].value.as < std::string > (), yystack_[1].value.as < ref6<unit> > (), true);
    }
#line 2806 "../../mli-root/src/database-parser.cc"
    break;

  case 61: // postulate: conjecture
#line 1010 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2812 "../../mli-root/src/database-parser.cc"
    break;

  case 62: // $@8: %empty
#line 1012 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2818 "../../mli-root/src/database-parser.cc"
    break;

  case 63: // postulate: "axiom" statement_name "." $@8 statement "."
#line 1013 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      val<formula> f(yystack_[1].value.as < ref6<unit> > ());

      if (!f->is_axiom())
        throw syntax_error(yystack_[1].location, "Axiom statement not an object formula.");

      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::postulate_, yystack_[4].value.as < std::string > (), f);
    }
#line 2833 "../../mli-root/src/database-parser.cc"
    break;

  case 64: // $@9: %empty
#line 1024 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2839 "../../mli-root/src/database-parser.cc"
    break;

  case 65: // postulate: "rule" statement_name "." $@9 statement "."
#line 1025 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      val<formula> f(yystack_[1].value.as < ref6<unit> > ());

      if (!f->is_rule())
        throw syntax_error(yystack_[1].location, "Rule statement not an inference.");

      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::postulate_, yystack_[4].value.as < std::string > (), f);
    }
#line 2854 "../../mli-root/src/database-parser.cc"
    break;

  case 66: // $@10: %empty
#line 1040 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2860 "../../mli-root/src/database-parser.cc"
    break;

  case 67: // conjecture: "conjecture" statement_name "." $@10 statement "."
#line 1041 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<supposition>(make, supposition::conjecture_, yystack_[4].value.as < std::string > (), yystack_[1].value.as < ref6<unit> > (), true);
    }
#line 2869 "../../mli-root/src/database-parser.cc"
    break;

  case 68: // $@11: %empty
#line 1049 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 2875 "../../mli-root/src/database-parser.cc"
    break;

  case 69: // definition_labelstatement: "definition" statement_name "." $@11 definition_statement "."
#line 1050 "../../mli-root/src/database-parser.yy"
                                {
      symbol_table.pop_level();
      yylhs.value.as < val<definition> > () = val<definition>(make, yystack_[4].value.as < std::string > (), yystack_[1].value.as < ref6<unit> > ());
    }
#line 2884 "../../mli-root/src/database-parser.cc"
    break;

  case 70: // statement_name: "name"
#line 1058 "../../mli-root/src/database-parser.yy"
              { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2890 "../../mli-root/src/database-parser.cc"
    break;

  case 71: // statement_name: "label"
#line 1059 "../../mli-root/src/database-parser.yy"
               { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 2896 "../../mli-root/src/database-parser.cc"
    break;

  case 72: // statement_name: "natural number value"
#line 1060 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < std::string > () = yystack_[0].value.as < std::pair<std::string, integer> > ().first; }
#line 2902 "../../mli-root/src/database-parser.cc"
    break;

  case 73: // theorem: theorem_statement proof
#line 1065 "../../mli-root/src/database-parser.yy"
                            {
      yylhs.value.as < ref6<unit> > () = statement_stack_.back();
      ref4<statement> t(yylhs.value.as < ref6<unit> > ()); // The theorem.
      t->prove(proof_count);     // Attempt to prove the theorem.
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
#line 2914 "../../mli-root/src/database-parser.cc"
    break;

  case 74: // theorem_statement: theorem_head statement
#line 1076 "../../mli-root/src/database-parser.yy"
                                 {
      symbol_table_t::table& top = symbol_table.top();
      val<theorem> tr(make,  yystack_[1].value.as < std::pair<theorem::type, std::string> > ().first, yystack_[1].value.as < std::pair<theorem::type, std::string> > ().second, yystack_[0].value.as < ref6<unit> > (), theory_, proof_depth);
      statement_stack_.back() = tr;
      theorem_theory_ = tr->get_theory();
    }
#line 2925 "../../mli-root/src/database-parser.cc"
    break;

  case 75: // theorem_head: "theorem" statement_name "."
#line 1086 "../../mli-root/src/database-parser.yy"
                                       {
      yylhs.value.as < std::pair<theorem::type, std::string> > ().second = yystack_[1].value.as < std::string > ();
      yylhs.value.as < std::pair<theorem::type, std::string> > ().first = yystack_[2].value.as < theorem::type > ();
      symbol_table.push_level();
      statement_stack_.push_back(ref4<statement>());
    }
#line 2936 "../../mli-root/src/database-parser.cc"
    break;

  case 76: // proof: compound-proof
#line 1096 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 2942 "../../mli-root/src/database-parser.cc"
    break;

  case 77: // $@12: %empty
#line 1097 "../../mli-root/src/database-parser.yy"
                {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 2952 "../../mli-root/src/database-parser.cc"
    break;

  case 78: // proof: $@12 proof_of_conclusion
#line 1102 "../../mli-root/src/database-parser.yy"
                        {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 2962 "../../mli-root/src/database-parser.cc"
    break;

  case 79: // compound-proof: proof_head proof_lines "∎"
#line 1111 "../../mli-root/src/database-parser.yy"
                               {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 2972 "../../mli-root/src/database-parser.cc"
    break;

  case 80: // compound-proof: "∎"
#line 1116 "../../mli-root/src/database-parser.yy"
        {}
#line 2978 "../../mli-root/src/database-parser.cc"
    break;

  case 81: // proof_head: "proof"
#line 1121 "../../mli-root/src/database-parser.yy"
            {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 2988 "../../mli-root/src/database-parser.cc"
    break;

  case 82: // proof_lines: %empty
#line 1130 "../../mli-root/src/database-parser.yy"
           {}
#line 2994 "../../mli-root/src/database-parser.cc"
    break;

  case 83: // proof_lines: proof_lines proof_line
#line 1131 "../../mli-root/src/database-parser.yy"
                           {}
#line 3000 "../../mli-root/src/database-parser.cc"
    break;

  case 84: // statement_label: statement_name "."
#line 1136 "../../mli-root/src/database-parser.yy"
                          {
      yylhs.value.as < std::string > () = yystack_[1].value.as < std::string > ();
      symbol_table.push_level();
    }
#line 3009 "../../mli-root/src/database-parser.cc"
    break;

  case 85: // proof_line: statement_label statement "by" find_statement "."
#line 1144 "../../mli-root/src/database-parser.yy"
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
#line 3044 "../../mli-root/src/database-parser.cc"
    break;

  case 86: // proof_line: subproof_statement compound-proof
#line 1175 "../../mli-root/src/database-parser.yy"
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
#line 3063 "../../mli-root/src/database-parser.cc"
    break;

  case 87: // $@13: %empty
#line 1190 "../../mli-root/src/database-parser.yy"
    {}
#line 3069 "../../mli-root/src/database-parser.cc"
    break;

  case 88: // proof_line: $@13 identifier_declaration
#line 1190 "../../mli-root/src/database-parser.yy"
                              {}
#line 3075 "../../mli-root/src/database-parser.cc"
    break;

  case 89: // proof_line: definition_labelstatement
#line 1194 "../../mli-root/src/database-parser.yy"
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
#line 3091 "../../mli-root/src/database-parser.cc"
    break;

  case 90: // proof_line: proof_of_conclusion
#line 1205 "../../mli-root/src/database-parser.yy"
                        {}
#line 3097 "../../mli-root/src/database-parser.cc"
    break;

  case 91: // subproof_statement: statement_label statement
#line 1210 "../../mli-root/src/database-parser.yy"
                                    {
      yylhs.value.as < std::string > () = yystack_[1].value.as < std::string > ();
      symbol_table_t::table& top = symbol_table.top();
      val<theorem> tp(make, theorem::claim_, yystack_[1].value.as < std::string > (), yystack_[0].value.as < ref6<unit> > (), theory_, proof_depth);
      statement_stack_.push_back(tp);
    }
#line 3108 "../../mli-root/src/database-parser.cc"
    break;

  case 92: // proof_of_conclusion: optional-result "by" find_statement "."
#line 1220 "../../mli-root/src/database-parser.yy"
                                                  {
      proofline_database_context = false;

      theorem& t = dyn_cast<theorem&>(statement_stack_.back());
      ref4<statement> proof_line =
        t.push_back(yystack_[3].value.as < std::string > (), t.get_formula(), val<database>(yystack_[1].value.as < ref6<unit> > ()), true, proof_depth);
    }
#line 3120 "../../mli-root/src/database-parser.cc"
    break;

  case 93: // optional-result: %empty
#line 1231 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < std::string > () = "result"; }
#line 3126 "../../mli-root/src/database-parser.cc"
    break;

  case 94: // optional-result: "result"
#line 1232 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < std::string > () = yystack_[0].value.as < std::string > (); }
#line 3132 "../../mli-root/src/database-parser.cc"
    break;

  case 95: // find_statement: find_statement_list
#line 1237 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = ref5<level_database>(make, val<database>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3138 "../../mli-root/src/database-parser.cc"
    break;

  case 96: // find_statement: find_statement ":" find_statement_list
#line 1238 "../../mli-root/src/database-parser.yy"
                                                 {
      ref5<level_database>(yystack_[2].value.as < ref6<unit> > ())->push_back(val<database>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3147 "../../mli-root/src/database-parser.cc"
    break;

  case 97: // find_statement_list: find_statement_sequence
#line 1246 "../../mli-root/src/database-parser.yy"
                               {
      yylhs.value.as < ref6<unit> > () = ref3<sublevel_database>(make, ref2<sequence_database>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3155 "../../mli-root/src/database-parser.cc"
    break;

  case 98: // find_statement_list: find_statement_list ";" find_statement_sequence
#line 1249 "../../mli-root/src/database-parser.yy"
                                                          {
      ref3<sublevel_database>(yystack_[2].value.as < ref6<unit> > ())->push_back(val<database>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3164 "../../mli-root/src/database-parser.cc"
    break;

  case 99: // find_statement_sequence: %empty
#line 1257 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make); }
#line 3170 "../../mli-root/src/database-parser.cc"
    break;

  case 100: // find_statement_sequence: find_statement_item
#line 1258 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make, ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3177 "../../mli-root/src/database-parser.cc"
    break;

  case 101: // find_statement_sequence: find_statement_item "₍" find_definition_sequence "₎"
#line 1260 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make, ref4<statement>(yystack_[3].value.as < ref6<unit> > ()));
      ref2<sequence_database>(yylhs.value.as < ref6<unit> > ())->insert(ref2<sequence_database>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 3186 "../../mli-root/src/database-parser.cc"
    break;

  case 102: // find_statement_sequence: find_statement_sequence "," find_statement_item
#line 1264 "../../mli-root/src/database-parser.yy"
                                                          {
      ref2<sequence_database>(yystack_[2].value.as < ref6<unit> > ())->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3195 "../../mli-root/src/database-parser.cc"
    break;

  case 103: // find_statement_sequence: find_statement_sequence "," find_statement_item "₍" find_definition_sequence "₎"
#line 1268 "../../mli-root/src/database-parser.yy"
                                                                                              {
      yylhs.value.as < ref6<unit> > () = yystack_[5].value.as < ref6<unit> > ();
      ref2<sequence_database>(yylhs.value.as < ref6<unit> > ())->insert(ref4<statement>(yystack_[3].value.as < ref6<unit> > ()));
      ref2<sequence_database>(yylhs.value.as < ref6<unit> > ())->insert(ref2<sequence_database>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 3205 "../../mli-root/src/database-parser.cc"
    break;

  case 104: // find_definition_sequence: find_statement_item
#line 1277 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = ref2<sequence_database>(make, ref4<statement>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3212 "../../mli-root/src/database-parser.cc"
    break;

  case 105: // find_definition_sequence: find_definition_sequence "," find_statement_item
#line 1279 "../../mli-root/src/database-parser.yy"
                                                           {
      ref2<sequence_database>(yystack_[2].value.as < ref6<unit> > ())->insert(ref4<statement>(yystack_[0].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3221 "../../mli-root/src/database-parser.cc"
    break;

  case 106: // find_statement_item: find_statement_name
#line 1287 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();
    }
#line 3229 "../../mli-root/src/database-parser.cc"
    break;

  case 107: // find_statement_item: "premise"
#line 1290 "../../mli-root/src/database-parser.yy"
              {
      yylhs.value.as < ref6<unit> > () = val<premise>(make, statement_stack_.back());
    }
#line 3237 "../../mli-root/src/database-parser.cc"
    break;

  case 108: // find_statement_item: "premise" statement_name
#line 1293 "../../mli-root/src/database-parser.yy"
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
#line 3255 "../../mli-root/src/database-parser.cc"
    break;

  case 109: // find_statement_item: "premise" statement_name "subscript natural number value"
#line 1306 "../../mli-root/src/database-parser.yy"
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
#line 3274 "../../mli-root/src/database-parser.cc"
    break;

  case 110: // find_statement_item: "premise" "⊢"
#line 1320 "../../mli-root/src/database-parser.yy"
                  {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      yylhs.value.as < ref6<unit> > () = val<premise>(make);
    }
#line 3284 "../../mli-root/src/database-parser.cc"
    break;

  case 111: // find_statement_item: "premise" "⊢" "subscript natural number value"
#line 1325 "../../mli-root/src/database-parser.yy"
                                                    {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      size_type k = (size_type)yystack_[0].value.as < integer > ();
      yylhs.value.as < ref6<unit> > () = val<premise>(make, k);
    }
#line 3295 "../../mli-root/src/database-parser.cc"
    break;

  case 112: // find_statement_name: statement_name
#line 1335 "../../mli-root/src/database-parser.yy"
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
#line 3314 "../../mli-root/src/database-parser.cc"
    break;

  case 113: // @14: %empty
#line 1349 "../../mli-root/src/database-parser.yy"
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
#line 3341 "../../mli-root/src/database-parser.cc"
    break;

  case 114: // find_statement_name: statement_name @14 metaformula_substitution_sequence
#line 1372 "../../mli-root/src/database-parser.yy"
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
#line 3361 "../../mli-root/src/database-parser.cc"
    break;

  case 115: // statement: metaformula
#line 1391 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.as < ref6<unit> > () = dyn_cast<formula&>(yystack_[0].value.as < ref6<unit> > ()).set_bind(); }
#line 3367 "../../mli-root/src/database-parser.cc"
    break;

  case 116: // statement: identifier_declaration metaformula
#line 1392 "../../mli-root/src/database-parser.yy"
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
#line 3412 "../../mli-root/src/database-parser.cc"
    break;

  case 117: // definition_statement: definition
#line 1436 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.as < ref6<unit> > () = dyn_cast<formula&>(yystack_[0].value.as < ref6<unit> > ()).set_bind(); }
#line 3418 "../../mli-root/src/database-parser.cc"
    break;

  case 118: // definition_statement: identifier_declaration definition
#line 1437 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.as < ref6<unit> > () = dyn_cast<formula&>(yystack_[0].value.as < ref6<unit> > ()).set_bind();
    }
#line 3426 "../../mli-root/src/database-parser.cc"
    break;

  case 119: // identifier_declaration: declarator_list "."
#line 1444 "../../mli-root/src/database-parser.yy"
                        {}
#line 3432 "../../mli-root/src/database-parser.cc"
    break;

  case 120: // declarator_list: declarator_identifier_list
#line 1449 "../../mli-root/src/database-parser.yy"
                               {}
#line 3438 "../../mli-root/src/database-parser.cc"
    break;

  case 121: // declarator_list: declarator_list declarator_identifier_list
#line 1450 "../../mli-root/src/database-parser.yy"
                                               {}
#line 3444 "../../mli-root/src/database-parser.cc"
    break;

  case 122: // declarator_identifier_list: "identifier constant" identifier_constant_list
#line 1455 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 3450 "../../mli-root/src/database-parser.cc"
    break;

  case 123: // declarator_identifier_list: "identifier variable" identifier_variable_list
#line 1456 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 3456 "../../mli-root/src/database-parser.cc"
    break;

  case 124: // declarator_identifier_list: "identifier function" identifier_function_list
#line 1457 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 3462 "../../mli-root/src/database-parser.cc"
    break;

  case 125: // identifier_function_list: identifier_function_name
#line 1462 "../../mli-root/src/database-parser.yy"
                             {}
#line 3468 "../../mli-root/src/database-parser.cc"
    break;

  case 126: // identifier_function_list: identifier_function_list "," identifier_function_name
#line 1463 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 3474 "../../mli-root/src/database-parser.cc"
    break;

  case 127: // $@15: %empty
#line 1474 "../../mli-root/src/database-parser.yy"
              { current_declared_token = declared_token; }
#line 3480 "../../mli-root/src/database-parser.cc"
    break;

  case 128: // $@16: %empty
#line 1475 "../../mli-root/src/database-parser.yy"
        { bound_variable_type = database_parser::token::function_map_variable; }
#line 3486 "../../mli-root/src/database-parser.cc"
    break;

  case 129: // identifier_function_name: "name" $@15 ":" $@16 "function map variable" "↦" object_formula
#line 1476 "../../mli-root/src/database-parser.yy"
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
#line 3502 "../../mli-root/src/database-parser.cc"
    break;

  case 130: // identifier_constant_list: identifier_constant_name
#line 1509 "../../mli-root/src/database-parser.yy"
                             {}
#line 3508 "../../mli-root/src/database-parser.cc"
    break;

  case 131: // identifier_constant_list: identifier_constant_list "," identifier_constant_name
#line 1510 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 3514 "../../mli-root/src/database-parser.cc"
    break;

  case 132: // identifier_constant_name: "name"
#line 1515 "../../mli-root/src/database-parser.yy"
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
#line 3530 "../../mli-root/src/database-parser.cc"
    break;

  case 133: // identifier_variable_list: identifier_variable_name
#line 1530 "../../mli-root/src/database-parser.yy"
                             {}
#line 3536 "../../mli-root/src/database-parser.cc"
    break;

  case 134: // identifier_variable_list: identifier_variable_list "," identifier_variable_name
#line 1531 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 3542 "../../mli-root/src/database-parser.cc"
    break;

  case 135: // identifier_variable_name: "name"
#line 1536 "../../mli-root/src/database-parser.yy"
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
#line 3558 "../../mli-root/src/database-parser.cc"
    break;

  case 136: // identifier_variable_name: "°" "name"
#line 1547 "../../mli-root/src/database-parser.yy"
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
#line 3574 "../../mli-root/src/database-parser.cc"
    break;

  case 137: // identifier_variable_name: "•" "name"
#line 1558 "../../mli-root/src/database-parser.yy"
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
#line 3590 "../../mli-root/src/database-parser.cc"
    break;

  case 138: // definition: metaformula_definition
#line 1573 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3596 "../../mli-root/src/database-parser.cc"
    break;

  case 139: // definition: object_formula_definition
#line 1574 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3602 "../../mli-root/src/database-parser.cc"
    break;

  case 140: // definition: term_definition
#line 1575 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3608 "../../mli-root/src/database-parser.cc"
    break;

  case 141: // metaformula_definition: pure_metaformula "≔" pure_metaformula
#line 1580 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(),
        formula::logic, formula_definition_oprec);
    }
#line 3617 "../../mli-root/src/database-parser.cc"
    break;

  case 142: // metaformula_definition: pure_metaformula "≕" pure_metaformula
#line 1584 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(),
       formula::logic, formula_definition_oprec);
  }
#line 3626 "../../mli-root/src/database-parser.cc"
    break;

  case 143: // object_formula_definition: object_formula "≔" object_formula
#line 1597 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(),
        formula::logic, formula_definition_oprec);
    }
#line 3635 "../../mli-root/src/database-parser.cc"
    break;

  case 144: // object_formula_definition: object_formula "≕" object_formula
#line 1601 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(),
        formula::logic, formula_definition_oprec);
  }
#line 3644 "../../mli-root/src/database-parser.cc"
    break;

  case 145: // term_definition: term "≔" term
#line 1614 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(),
        formula::object, term_definition_oprec);
    }
#line 3653 "../../mli-root/src/database-parser.cc"
    break;

  case 146: // term_definition: term "≕" term
#line 1624 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<abbreviation>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(),
        formula::object, term_definition_oprec);
  }
#line 3662 "../../mli-root/src/database-parser.cc"
    break;

  case 147: // metaformula: pure_metaformula
#line 1632 "../../mli-root/src/database-parser.yy"
                        { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3668 "../../mli-root/src/database-parser.cc"
    break;

  case 148: // metaformula: object_formula
#line 1633 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3674 "../../mli-root/src/database-parser.cc"
    break;

  case 149: // pure_metaformula: atomic_metaformula
#line 1638 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3680 "../../mli-root/src/database-parser.cc"
    break;

  case 150: // pure_metaformula: special_metaformula
#line 1639 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3686 "../../mli-root/src/database-parser.cc"
    break;

  case 151: // pure_metaformula: "~" metaformula
#line 1640 "../../mli-root/src/database-parser.yy"
                       {
      yylhs.value.as < ref6<unit> > () = val<metanot>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3694 "../../mli-root/src/database-parser.cc"
    break;

  case 152: // pure_metaformula: metaformula ";" metaformula
#line 1643 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.as < ref6<unit> > () = concatenate(val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3702 "../../mli-root/src/database-parser.cc"
    break;

  case 153: // pure_metaformula: metaformula "," metaformula
#line 1646 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.as < ref6<unit> > () = concatenate(val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 3710 "../../mli-root/src/database-parser.cc"
    break;

  case 154: // pure_metaformula: metaformula "⊩" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_matrix metaformula
#line 1651 "../../mli-root/src/database-parser.yy"
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
#line 3769 "../../mli-root/src/database-parser.cc"
    break;

  case 155: // pure_metaformula: metaformula "⊢" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_matrix metaformula
#line 1719 "../../mli-root/src/database-parser.yy"
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
#line 3826 "../../mli-root/src/database-parser.cc"
    break;

  case 156: // pure_metaformula: "⊢" metaformula
#line 1778 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = val<inference>(make, val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 3832 "../../mli-root/src/database-parser.cc"
    break;

  case 157: // pure_metaformula: "(" pure_metaformula ")"
#line 1780 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3838 "../../mli-root/src/database-parser.cc"
    break;

  case 158: // pure_metaformula: simple_metaformula metaformula_substitution_sequence
#line 1781 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.as < ref6<unit> > () = val<substitution_formula>(make, val<substitution>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[1].value.as < ref6<unit> > ())); }
#line 3845 "../../mli-root/src/database-parser.cc"
    break;

  case 159: // optional_varied_variable_matrix: %empty
#line 1787 "../../mli-root/src/database-parser.yy"
           {}
#line 3851 "../../mli-root/src/database-parser.cc"
    break;

  case 160: // optional_varied_variable_matrix: "⁽" varied_variable_conclusions "⁾"
#line 1788 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3857 "../../mli-root/src/database-parser.cc"
    break;

  case 161: // optional_varied_variable_matrix: "⁽" varied_variable_premises "⁾"
#line 1789 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3863 "../../mli-root/src/database-parser.cc"
    break;

  case 162: // optional_varied_variable_matrix: "⁽" varied_variable_set "⁾"
#line 1790 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3869 "../../mli-root/src/database-parser.cc"
    break;

  case 163: // varied_variable_conclusions: varied_variable_conclusion
#line 1794 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3875 "../../mli-root/src/database-parser.cc"
    break;

  case 164: // varied_variable_conclusions: varied_variable_conclusions ";" varied_variable_conclusion
#line 1795 "../../mli-root/src/database-parser.yy"
                                                                      {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& i: x.varied_)
        for (auto& j: i.second)
          xs.varied_[i.first][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3890 "../../mli-root/src/database-parser.cc"
    break;

  case 165: // varied_variable_conclusion: "superscript natural number value" varied_variable_premises
#line 1808 "../../mli-root/src/database-parser.yy"
                                                                     {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_[k].insert(xs.varied_[0].begin(), xs.varied_[0].end());
      yylhs.value.as < ref6<unit> > () = i;

    }
#line 3904 "../../mli-root/src/database-parser.cc"
    break;

  case 166: // varied_variable_premises: varied_variable_premise
#line 1820 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3910 "../../mli-root/src/database-parser.cc"
    break;

  case 167: // varied_variable_premises: varied_variable_premises "," varied_variable_premise
#line 1821 "../../mli-root/src/database-parser.yy"
                                                                {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& j: x.varied_[0])
        xs.varied_[0][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 3924 "../../mli-root/src/database-parser.cc"
    break;

  case 168: // varied_variable_premise: "superscript natural number value" varied_variable_set
#line 1833 "../../mli-root/src/database-parser.yy"
                                                                {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_[0][k].insert(xs.varied_[0][0].begin(), xs.varied_[0][0].end());

      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3938 "../../mli-root/src/database-parser.cc"
    break;

  case 169: // varied_variable_set: varied_variable
#line 1845 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 3944 "../../mli-root/src/database-parser.cc"
    break;

  case 170: // varied_variable_set: varied_variable_set varied_variable
#line 1846 "../../mli-root/src/database-parser.yy"
                                               {
      inference& xs = dyn_cast<inference&>(yystack_[1].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      xs.varied_[0][0].insert(x.varied_[0][0].begin(), x.varied_[0][0].end());

      yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > ();
    }
#line 3957 "../../mli-root/src/database-parser.cc"
    break;

  case 171: // varied_variable: "object variable"
#line 1857 "../../mli-root/src/database-parser.yy"
                       {
      val<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3967 "../../mli-root/src/database-parser.cc"
    break;

  case 172: // varied_variable: "metaformula variable"
#line 1862 "../../mli-root/src/database-parser.yy"
                            {
      val<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 3977 "../../mli-root/src/database-parser.cc"
    break;

  case 173: // optional_varied_in_reduction_variable_matrix: %empty
#line 1872 "../../mli-root/src/database-parser.yy"
           {}
#line 3983 "../../mli-root/src/database-parser.cc"
    break;

  case 174: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_conclusions "₎"
#line 1873 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3989 "../../mli-root/src/database-parser.cc"
    break;

  case 175: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_premises "₎"
#line 1874 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 3995 "../../mli-root/src/database-parser.cc"
    break;

  case 176: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_set "₎"
#line 1875 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4001 "../../mli-root/src/database-parser.cc"
    break;

  case 177: // varied_in_reduction_variable_conclusions: varied_in_reduction_variable_conclusion
#line 1879 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4007 "../../mli-root/src/database-parser.cc"
    break;

  case 178: // varied_in_reduction_variable_conclusions: varied_in_reduction_variable_conclusions ";" varied_in_reduction_variable_conclusion
#line 1880 "../../mli-root/src/database-parser.yy"
                                                                                                {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& i: x.varied_in_reduction_)
        for (auto& j: i.second)
          xs.varied_in_reduction_[i.first][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 4022 "../../mli-root/src/database-parser.cc"
    break;

  case 179: // varied_in_reduction_variable_conclusion: "subscript natural number value" varied_in_reduction_variable_premises
#line 1893 "../../mli-root/src/database-parser.yy"
                                                                                {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_in_reduction_[k].insert(xs.varied_in_reduction_[0].begin(), xs.varied_in_reduction_[0].end());
      yylhs.value.as < ref6<unit> > () = i;

    }
#line 4036 "../../mli-root/src/database-parser.cc"
    break;

  case 180: // varied_in_reduction_variable_premises: varied_in_reduction_variable_premise
#line 1905 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4042 "../../mli-root/src/database-parser.cc"
    break;

  case 181: // varied_in_reduction_variable_premises: varied_in_reduction_variable_premises "," varied_in_reduction_variable_premise
#line 1906 "../../mli-root/src/database-parser.yy"
                                                                                          {
      inference& xs = dyn_cast<inference&>(yystack_[2].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      for (auto& j: x.varied_in_reduction_[0])
        xs.varied_in_reduction_[0][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
    }
#line 4056 "../../mli-root/src/database-parser.cc"
    break;

  case 182: // varied_in_reduction_variable_premise: "subscript natural number value" varied_in_reduction_variable_set
#line 1918 "../../mli-root/src/database-parser.yy"
                                                                           {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      i->varied_in_reduction_[0][k].insert(xs.varied_in_reduction_[0][0].begin(), xs.varied_in_reduction_[0][0].end());

      yylhs.value.as < ref6<unit> > () = i;
    }
#line 4070 "../../mli-root/src/database-parser.cc"
    break;

  case 183: // varied_in_reduction_variable_set: varied_in_reduction_variable
#line 1930 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4076 "../../mli-root/src/database-parser.cc"
    break;

  case 184: // varied_in_reduction_variable_set: varied_in_reduction_variable_set varied_in_reduction_variable
#line 1931 "../../mli-root/src/database-parser.yy"
                                                                         {
      inference& xs = dyn_cast<inference&>(yystack_[1].value.as < ref6<unit> > ());
      inference& x = dyn_cast<inference&>(yystack_[0].value.as < ref6<unit> > ());

      xs.varied_in_reduction_[0][0].insert(x.varied_in_reduction_[0][0].begin(), x.varied_in_reduction_[0][0].end());

      yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > ();
    }
#line 4089 "../../mli-root/src/database-parser.cc"
    break;

  case 185: // varied_in_reduction_variable: "object variable"
#line 1942 "../../mli-root/src/database-parser.yy"
                       {
      val<inference> i(make);
      i->varied_in_reduction_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 4099 "../../mli-root/src/database-parser.cc"
    break;

  case 186: // varied_in_reduction_variable: "metaformula variable"
#line 1947 "../../mli-root/src/database-parser.yy"
                            {
      val<inference> i(make);
      i->varied_in_reduction_[0][0].insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = i;
    }
#line 4109 "../../mli-root/src/database-parser.cc"
    break;

  case 187: // simple_metaformula: "metaformula variable"
#line 2015 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4115 "../../mli-root/src/database-parser.cc"
    break;

  case 188: // simple_metaformula: "(" pure_metaformula ")"
#line 2016 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4121 "../../mli-root/src/database-parser.cc"
    break;

  case 189: // atomic_metaformula: "metaformula variable"
#line 2021 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4127 "../../mli-root/src/database-parser.cc"
    break;

  case 190: // atomic_metaformula: metapredicate
#line 2022 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4133 "../../mli-root/src/database-parser.cc"
    break;

  case 191: // special_metaformula: meta_object_free "≢" meta_object_free
#line 2034 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<objectidentical>(make, val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<variable>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4141 "../../mli-root/src/database-parser.cc"
    break;

  case 192: // special_metaformula: meta_object_free "free in" object_formula
#line 2037 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4149 "../../mli-root/src/database-parser.cc"
    break;

  case 193: // special_metaformula: meta_object_free "free in" term
#line 2040 "../../mli-root/src/database-parser.yy"
                                          {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4157 "../../mli-root/src/database-parser.cc"
    break;

  case 194: // special_metaformula: meta_object_free "not" "free in" object_formula
#line 2043 "../../mli-root/src/database-parser.yy"
                                                          {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[3].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4165 "../../mli-root/src/database-parser.cc"
    break;

  case 195: // special_metaformula: meta_object_free "not" "free in" term
#line 2046 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.as < ref6<unit> > () = val<free_in_object>(make, val<variable>(yystack_[3].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4173 "../../mli-root/src/database-parser.cc"
    break;

  case 196: // special_metaformula: term "free for" meta_object_free "in" object_formula
#line 2049 "../../mli-root/src/database-parser.yy"
                                                                  {
      yylhs.value.as < ref6<unit> > () = val<free_for_object>(make, 
        val<formula>(yystack_[4].value.as < ref6<unit> > ()), val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4182 "../../mli-root/src/database-parser.cc"
    break;

  case 197: // special_metaformula: term "free for" meta_object_free "in" term
#line 2053 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.as < ref6<unit> > () = val<free_for_object>(make, 
        val<formula>(yystack_[4].value.as < ref6<unit> > ()), val<variable>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4191 "../../mli-root/src/database-parser.cc"
    break;

  case 198: // meta_object_free: "object variable"
#line 2061 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4197 "../../mli-root/src/database-parser.cc"
    break;

  case 199: // metapredicate: metapredicate_function
#line 2066 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4203 "../../mli-root/src/database-parser.cc"
    break;

  case 200: // metapredicate: object_formula "≣" object_formula
#line 2067 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4211 "../../mli-root/src/database-parser.cc"
    break;

  case 201: // metapredicate: object_formula "≣̷" object_formula
#line 2070 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4219 "../../mli-root/src/database-parser.cc"
    break;

  case 202: // metapredicate: term "≣" term
#line 2073 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), true);
    }
#line 4227 "../../mli-root/src/database-parser.cc"
    break;

  case 203: // metapredicate: term "≣̷" term
#line 2076 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.as < ref6<unit> > () = val<identical>(make, val<formula>(yystack_[2].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), false);
    }
#line 4235 "../../mli-root/src/database-parser.cc"
    break;

  case 204: // metapredicate_function: "metapredicate constant" metapredicate_argument
#line 2083 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < val<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 4244 "../../mli-root/src/database-parser.cc"
    break;

  case 205: // metapredicate_function: "metaformula variable" metapredicate_argument
#line 2087 "../../mli-root/src/database-parser.yy"
                                                      {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < val<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 4253 "../../mli-root/src/database-parser.cc"
    break;

  case 206: // metapredicate_argument: "(" metapredicate_argument_body ")"
#line 2095 "../../mli-root/src/database-parser.yy"
                                           { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4259 "../../mli-root/src/database-parser.cc"
    break;

  case 207: // metapredicate_argument_body: object_formula
#line 2100 "../../mli-root/src/database-parser.yy"
                      {
      ref0<sequence> vr(make, sequence::tuple);
      yylhs.value.as < ref6<unit> > () = vr;
      vr->push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 4268 "../../mli-root/src/database-parser.cc"
    break;

  case 208: // metapredicate_argument_body: metapredicate_argument_body "," object_formula
#line 2104 "../../mli-root/src/database-parser.yy"
                                                         {
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
      sequence& vr = dyn_cast<sequence&>(yylhs.value.as < ref6<unit> > ());
      vr.push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 4277 "../../mli-root/src/database-parser.cc"
    break;

  case 209: // object_formula: atomic_formula
#line 2112 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4283 "../../mli-root/src/database-parser.cc"
    break;

  case 210: // object_formula: very_simple_formula formula_substitution_sequence
#line 2113 "../../mli-root/src/database-parser.yy"
                                                            {
      yylhs.value.as < ref6<unit> > () = val<substitution_formula>(make, val<substitution>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 4291 "../../mli-root/src/database-parser.cc"
    break;

  case 211: // object_formula: predicate_function_application
#line 2116 "../../mli-root/src/database-parser.yy"
                                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4297 "../../mli-root/src/database-parser.cc"
    break;

  case 212: // object_formula: logic_formula
#line 2117 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4303 "../../mli-root/src/database-parser.cc"
    break;

  case 213: // object_formula: "(" object_formula ")"
#line 2118 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4309 "../../mli-root/src/database-parser.cc"
    break;

  case 214: // object_formula: quantized_formula
#line 2119 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4315 "../../mli-root/src/database-parser.cc"
    break;

  case 215: // object_formula: hoare_triple
#line 2120 "../../mli-root/src/database-parser.yy"
                 {}
#line 4321 "../../mli-root/src/database-parser.cc"
    break;

  case 216: // hoare_triple: "{" object_formula "}" code_sequence "{" object_formula "}"
#line 2125 "../../mli-root/src/database-parser.yy"
                                                              { yylhs.value.as < ref6<unit> > () = val<formula>(); }
#line 4327 "../../mli-root/src/database-parser.cc"
    break;

  case 217: // code_statement: code_term
#line 2136 "../../mli-root/src/database-parser.yy"
              {}
#line 4333 "../../mli-root/src/database-parser.cc"
    break;

  case 218: // code_statement: "{" code_sequence "}"
#line 2137 "../../mli-root/src/database-parser.yy"
                          {}
#line 4339 "../../mli-root/src/database-parser.cc"
    break;

  case 219: // code_sequence: %empty
#line 2142 "../../mli-root/src/database-parser.yy"
           {}
#line 4345 "../../mli-root/src/database-parser.cc"
    break;

  case 220: // code_sequence: code_term
#line 2143 "../../mli-root/src/database-parser.yy"
              {}
#line 4351 "../../mli-root/src/database-parser.cc"
    break;

  case 221: // code_sequence: code_sequence ";" code_term
#line 2144 "../../mli-root/src/database-parser.yy"
                                {}
#line 4357 "../../mli-root/src/database-parser.cc"
    break;

  case 222: // code_term: "code variable"
#line 2149 "../../mli-root/src/database-parser.yy"
                 {}
#line 4363 "../../mli-root/src/database-parser.cc"
    break;

  case 223: // code_term: "∅"
#line 2150 "../../mli-root/src/database-parser.yy"
       {}
#line 4369 "../../mli-root/src/database-parser.cc"
    break;

  case 224: // code_term: "object variable" "≔" term
#line 2151 "../../mli-root/src/database-parser.yy"
                            {}
#line 4375 "../../mli-root/src/database-parser.cc"
    break;

  case 225: // code_term: "if" object_formula "then" code_statement "else" code_statement
#line 2152 "../../mli-root/src/database-parser.yy"
                                                                   {}
#line 4381 "../../mli-root/src/database-parser.cc"
    break;

  case 226: // code_term: "while" object_formula "do" code_statement
#line 2153 "../../mli-root/src/database-parser.yy"
                                              {}
#line 4387 "../../mli-root/src/database-parser.cc"
    break;

  case 227: // very_simple_formula: "object formula variable"
#line 2158 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4393 "../../mli-root/src/database-parser.cc"
    break;

  case 228: // very_simple_formula: "atom variable"
#line 2159 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4399 "../../mli-root/src/database-parser.cc"
    break;

  case 229: // very_simple_formula: "(" object_formula ")"
#line 2160 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4405 "../../mli-root/src/database-parser.cc"
    break;

  case 230: // quantized_formula: quantizer_declaration quantized_body
#line 2165 "../../mli-root/src/database-parser.yy"
                                               {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>(yystack_[1].value.as < ref6<unit> > ());
      val<bound_formula> bf(make, vsr, val<formula>(yystack_[0].value.as < ref6<unit> > ()));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      yylhs.value.as < ref6<unit> > () = bf;
    }
#line 4417 "../../mli-root/src/database-parser.cc"
    break;

  case 231: // quantized_formula: quantizer_declaration optional_in_term ":" object_formula
#line 2172 "../../mli-root/src/database-parser.yy"
                                                                       {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>(yystack_[3].value.as < ref6<unit> > ());
      val<bound_formula> bf(make, vsr, yystack_[2].value.as < ref6<unit> > (), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      yylhs.value.as < ref6<unit> > () = bf;
    }
#line 4429 "../../mli-root/src/database-parser.cc"
    break;

  case 232: // quantized_formula: quantizer_declaration optional_in_term quantized_formula
#line 2179 "../../mli-root/src/database-parser.yy"
                                                                      {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>(yystack_[2].value.as < ref6<unit> > ());
      val<bound_formula> bf(make, vsr, yystack_[1].value.as < ref6<unit> > (), val<formula>(yystack_[0].value.as < ref6<unit> > ()));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      yylhs.value.as < ref6<unit> > () = bf;
    }
#line 4441 "../../mli-root/src/database-parser.cc"
    break;

  case 233: // simple_formula: "object formula variable"
#line 2190 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4447 "../../mli-root/src/database-parser.cc"
    break;

  case 234: // simple_formula: "atom variable"
#line 2191 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4453 "../../mli-root/src/database-parser.cc"
    break;

  case 235: // simple_formula: predicate_expression
#line 2192 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4459 "../../mli-root/src/database-parser.cc"
    break;

  case 236: // simple_formula: "(" object_formula ")"
#line 2193 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4465 "../../mli-root/src/database-parser.cc"
    break;

  case 237: // simple_formula: quantized_formula
#line 2194 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4471 "../../mli-root/src/database-parser.cc"
    break;

  case 238: // quantized_body: atomic_formula
#line 2200 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4477 "../../mli-root/src/database-parser.cc"
    break;

  case 239: // quantized_body: "(" object_formula ")"
#line 2201 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4483 "../../mli-root/src/database-parser.cc"
    break;

  case 240: // atomic_formula: "atom constant"
#line 2205 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4489 "../../mli-root/src/database-parser.cc"
    break;

  case 241: // atomic_formula: "object formula variable"
#line 2206 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4495 "../../mli-root/src/database-parser.cc"
    break;

  case 242: // atomic_formula: "atom variable"
#line 2207 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4501 "../../mli-root/src/database-parser.cc"
    break;

  case 243: // atomic_formula: predicate
#line 2208 "../../mli-root/src/database-parser.yy"
                 { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4507 "../../mli-root/src/database-parser.cc"
    break;

  case 244: // predicate: predicate_expression
#line 2214 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4513 "../../mli-root/src/database-parser.cc"
    break;

  case 245: // predicate: term "=" term
#line 2215 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4519 "../../mli-root/src/database-parser.cc"
    break;

  case 246: // predicate: term "≠" term
#line 2216 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4525 "../../mli-root/src/database-parser.cc"
    break;

  case 247: // predicate: term "∣" term
#line 2219 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4531 "../../mli-root/src/database-parser.cc"
    break;

  case 248: // predicate: term "∤" term
#line 2220 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4537 "../../mli-root/src/database-parser.cc"
    break;

  case 249: // predicate: term "<" term
#line 2223 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, less_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4543 "../../mli-root/src/database-parser.cc"
    break;

  case 250: // predicate: term ">" term
#line 2224 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, greater_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4549 "../../mli-root/src/database-parser.cc"
    break;

  case 251: // predicate: term "≤" term
#line 2225 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, less_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4555 "../../mli-root/src/database-parser.cc"
    break;

  case 252: // predicate: term "≥" term
#line 2226 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, greater_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4561 "../../mli-root/src/database-parser.cc"
    break;

  case 253: // predicate: term "≮" term
#line 2227 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_less_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4567 "../../mli-root/src/database-parser.cc"
    break;

  case 254: // predicate: term "≯" term
#line 2228 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_greater_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4573 "../../mli-root/src/database-parser.cc"
    break;

  case 255: // predicate: term "≰" term
#line 2229 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_less_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4579 "../../mli-root/src/database-parser.cc"
    break;

  case 256: // predicate: term "≱" term
#line 2230 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_greater_or_equal_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4585 "../../mli-root/src/database-parser.cc"
    break;

  case 257: // predicate: term "∈" term
#line 2232 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, in_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4591 "../../mli-root/src/database-parser.cc"
    break;

  case 258: // predicate: term "∉" term
#line 2233 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, not_in_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4597 "../../mli-root/src/database-parser.cc"
    break;

  case 259: // predicate: term "⊆" term
#line 2234 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, subset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4603 "../../mli-root/src/database-parser.cc"
    break;

  case 260: // predicate: term "⊊" term
#line 2235 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, proper_subset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4609 "../../mli-root/src/database-parser.cc"
    break;

  case 261: // predicate: term "⊇" term
#line 2236 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, superset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4615 "../../mli-root/src/database-parser.cc"
    break;

  case 262: // predicate: term "⊋" term
#line 2237 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::predicate, 0_ml, structure::infix, proper_superset_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ()); }
#line 4621 "../../mli-root/src/database-parser.cc"
    break;

  case 263: // $@17: %empty
#line 2238 "../../mli-root/src/database-parser.yy"
          { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 4627 "../../mli-root/src/database-parser.cc"
    break;

  case 264: // $@18: %empty
#line 2239 "../../mli-root/src/database-parser.yy"
                               { bound_variable_type = free_variable_context; }
#line 4633 "../../mli-root/src/database-parser.cc"
    break;

  case 265: // predicate: "Set" $@17 "₍" "Set variable" "₎" $@18 simple_formula
#line 2240 "../../mli-root/src/database-parser.yy"
                       {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<bound_formula>(make,
        val<variable>(yystack_[3].value.as < val<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()), bound_formula::is_set_);
    }
#line 4643 "../../mli-root/src/database-parser.cc"
    break;

  case 266: // predicate_expression: predicate_identifier tuple
#line 2249 "../../mli-root/src/database-parser.yy"
                                     {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::predicate, 0_ml, structure::postargument, precedence_t());
    }
#line 4652 "../../mli-root/src/database-parser.cc"
    break;

  case 267: // predicate_identifier: "predicate constant"
#line 2257 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > ();  }
#line 4658 "../../mli-root/src/database-parser.cc"
    break;

  case 268: // predicate_identifier: "predicate variable"
#line 2258 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > ();  }
#line 4664 "../../mli-root/src/database-parser.cc"
    break;

  case 269: // optional_superscript_natural_number_value: %empty
#line 2263 "../../mli-root/src/database-parser.yy"
           {}
#line 4670 "../../mli-root/src/database-parser.cc"
    break;

  case 270: // optional_superscript_natural_number_value: "superscript natural number value"
#line 2264 "../../mli-root/src/database-parser.yy"
    { yylhs.value.as < integer > () = yystack_[0].value.as < integer > (); }
#line 4676 "../../mli-root/src/database-parser.cc"
    break;

  case 271: // logic_formula: "¬" optional_superscript_natural_number_value object_formula
#line 2276 "../../mli-root/src/database-parser.yy"
                                                                          {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::prefix, logical_not_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 4687 "../../mli-root/src/database-parser.cc"
    break;

  case 272: // logic_formula: object_formula "∨" optional_superscript_natural_number_value object_formula
#line 2282 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, logical_or_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4698 "../../mli-root/src/database-parser.cc"
    break;

  case 273: // logic_formula: object_formula "∧" optional_superscript_natural_number_value object_formula
#line 2288 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, logical_and_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4709 "../../mli-root/src/database-parser.cc"
    break;

  case 274: // logic_formula: object_formula "⇒" optional_superscript_natural_number_value object_formula
#line 2294 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, implies_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4720 "../../mli-root/src/database-parser.cc"
    break;

  case 275: // logic_formula: object_formula "⇐" optional_superscript_natural_number_value object_formula
#line 2300 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, impliedby_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4731 "../../mli-root/src/database-parser.cc"
    break;

  case 276: // logic_formula: object_formula "⇔" optional_superscript_natural_number_value object_formula
#line 2306 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)yystack_[1].value.as < integer > ();

      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[2].value.as < std::string > (), structure::logic, metalevel_t(k),
        structure::infix, equivalent_oprec, yystack_[3].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4742 "../../mli-root/src/database-parser.cc"
    break;

  case 277: // logic_formula: prefix_logic_formula
#line 2312 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();  }
#line 4748 "../../mli-root/src/database-parser.cc"
    break;

  case 278: // prefix_logic_formula: "prefix formula variable"
#line 2317 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 4754 "../../mli-root/src/database-parser.cc"
    break;

  case 279: // prefix_logic_formula: prefix_not_key prefix_logic_formula
#line 2318 "../../mli-root/src/database-parser.yy"
                                              {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "¬", structure::logic, 0_ml,
        structure::prefix, logical_not_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 4763 "../../mli-root/src/database-parser.cc"
    break;

  case 280: // prefix_logic_formula: prefix_or_key prefix_logic_formula prefix_logic_formula
#line 2322 "../../mli-root/src/database-parser.yy"
                                                                     {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "∨", structure::logic, 0_ml,
        structure::infix, logical_or_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4772 "../../mli-root/src/database-parser.cc"
    break;

  case 281: // prefix_logic_formula: prefix_and_key prefix_logic_formula prefix_logic_formula
#line 2326 "../../mli-root/src/database-parser.yy"
                                                                      {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "∧", structure::logic, 0_ml,
        structure::infix, logical_and_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4781 "../../mli-root/src/database-parser.cc"
    break;

  case 282: // prefix_logic_formula: prefix_implies_key prefix_logic_formula prefix_logic_formula
#line 2330 "../../mli-root/src/database-parser.yy"
                                                                          {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "⇒", structure::logic, 0_ml,
        structure::infix, implies_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 4790 "../../mli-root/src/database-parser.cc"
    break;

  case 283: // prefix_logic_formula: prefix_equivalent_key prefix_logic_formula prefix_logic_formula
#line 2334 "../../mli-root/src/database-parser.yy"
                                                                             {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, "⇔", structure::logic, 0_ml,
        structure::infix, equivalent_oprec, yystack_[1].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
 }
#line 4799 "../../mli-root/src/database-parser.cc"
    break;

  case 284: // quantizer_declaration: quantized_variable_list
#line 2342 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4805 "../../mli-root/src/database-parser.cc"
    break;

  case 285: // quantized_variable_list: all_variable_list
#line 2346 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4811 "../../mli-root/src/database-parser.cc"
    break;

  case 286: // quantized_variable_list: exist_variable_list
#line 2347 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4817 "../../mli-root/src/database-parser.cc"
    break;

  case 287: // all_variable_list: "∀" exclusion_set all_identifier_list
#line 2352 "../../mli-root/src/database-parser.yy"
                                                 {
      auto bfp = dyn_cast<bound_formula*>(yystack_[1].value.as < ref6<unit> > ());
      if (bfp != nullptr) {
        variable_list& vsr = dyn_cast<variable_list&>(yystack_[0].value.as < ref6<unit> > ());
        vsr.excluded1_.insert(bfp->excluded1_.begin(), bfp->excluded1_.end());
      }
      yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();
    }
#line 4830 "../../mli-root/src/database-parser.cc"
    break;

  case 288: // exist_variable_list: "∃" exclusion_set exist_identifier_list
#line 2364 "../../mli-root/src/database-parser.yy"
                                                   {
      auto bfp = dyn_cast<bound_formula*>(yystack_[1].value.as < ref6<unit> > ());
      if (bfp != nullptr) {
        variable_list& vsr = dyn_cast<variable_list&>(yystack_[0].value.as < ref6<unit> > ());
        vsr.excluded1_.insert(bfp->excluded1_.begin(), bfp->excluded1_.end());
      }
      yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > ();
    }
#line 4843 "../../mli-root/src/database-parser.cc"
    break;

  case 289: // exclusion_set: %empty
#line 2376 "../../mli-root/src/database-parser.yy"
           {}
#line 4849 "../../mli-root/src/database-parser.cc"
    break;

  case 290: // $@19: %empty
#line 2377 "../../mli-root/src/database-parser.yy"
        { bound_variable_type = free_variable_context; }
#line 4855 "../../mli-root/src/database-parser.cc"
    break;

  case 291: // exclusion_set: "ₓ" $@19 "₍" exclusion_list "₎"
#line 2378 "../../mli-root/src/database-parser.yy"
                               {
      bound_variable_type = database_parser::token::exist_variable;
      yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > ();
    }
#line 4864 "../../mli-root/src/database-parser.cc"
    break;

  case 292: // exclusion_list: "object variable"
#line 2385 "../../mli-root/src/database-parser.yy"
                       { val<bound_formula> vr(make); vr->excluded1_.insert(yystack_[0].value.as < val<unit> > ()); yylhs.value.as < ref6<unit> > () = vr; }
#line 4870 "../../mli-root/src/database-parser.cc"
    break;

  case 293: // exclusion_list: exclusion_list "object variable"
#line 2386 "../../mli-root/src/database-parser.yy"
                                           {
      val<bound_formula> vr = yystack_[1].value.as < ref6<unit> > ();
      vr->excluded1_.insert(yystack_[0].value.as < val<unit> > ());
      yylhs.value.as < ref6<unit> > () = vr;
    }
#line 4880 "../../mli-root/src/database-parser.cc"
    break;

  case 294: // all_identifier_list: "all variable"
#line 2396 "../../mli-root/src/database-parser.yy"
                    {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = val<variable_list>(make, val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::all_);
    }
#line 4889 "../../mli-root/src/database-parser.cc"
    break;

  case 295: // $@20: %empty
#line 2400 "../../mli-root/src/database-parser.yy"
                           { bound_variable_type = token::all_variable; }
#line 4895 "../../mli-root/src/database-parser.cc"
    break;

  case 296: // all_identifier_list: all_identifier_list $@20 "," "all variable"
#line 2401 "../../mli-root/src/database-parser.yy"
                          {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = yystack_[3].value.as < ref6<unit> > ();
      dyn_cast<variable_list&>(yylhs.value.as < ref6<unit> > ()).push_back(val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::all_);
    }
#line 4905 "../../mli-root/src/database-parser.cc"
    break;

  case 297: // exist_identifier_list: "exist variable"
#line 2410 "../../mli-root/src/database-parser.yy"
                      {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = val<variable_list>(make, val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::exist_);
    }
#line 4914 "../../mli-root/src/database-parser.cc"
    break;

  case 298: // $@21: %empty
#line 2414 "../../mli-root/src/database-parser.yy"
                             { bound_variable_type = database_parser::token::exist_variable; }
#line 4920 "../../mli-root/src/database-parser.cc"
    break;

  case 299: // exist_identifier_list: exist_identifier_list $@21 "," "exist variable"
#line 2415 "../../mli-root/src/database-parser.yy"
                            {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = yystack_[3].value.as < ref6<unit> > ();
      dyn_cast<variable_list&>(yylhs.value.as < ref6<unit> > ()).push_back(val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::exist_);
    }
#line 4930 "../../mli-root/src/database-parser.cc"
    break;

  case 300: // optional_in_term: %empty
#line 2425 "../../mli-root/src/database-parser.yy"
           { yylhs.value.as < ref6<unit> > () = val<formula>(make); }
#line 4936 "../../mli-root/src/database-parser.cc"
    break;

  case 301: // optional_in_term: "∈" term
#line 2426 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4942 "../../mli-root/src/database-parser.cc"
    break;

  case 302: // tuple: "(" tuple_body ")"
#line 2433 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 4948 "../../mli-root/src/database-parser.cc"
    break;

  case 303: // tuple_body: term
#line 2438 "../../mli-root/src/database-parser.yy"
            {
      ref0<sequence> vr(make, sequence::tuple);
      yylhs.value.as < ref6<unit> > () = vr;
      vr->push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 4958 "../../mli-root/src/database-parser.cc"
    break;

  case 304: // tuple_body: tuple_body "," term
#line 2443 "../../mli-root/src/database-parser.yy"
                              {
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
      sequence& vr = dyn_cast<sequence&>(yylhs.value.as < ref6<unit> > ());
      vr.push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 4968 "../../mli-root/src/database-parser.cc"
    break;

  case 305: // term: simple_term
#line 2452 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4974 "../../mli-root/src/database-parser.cc"
    break;

  case 306: // term: function_term
#line 2453 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4980 "../../mli-root/src/database-parser.cc"
    break;

  case 307: // term: simple_term term_substitution_sequence
#line 2454 "../../mli-root/src/database-parser.yy"
                                                 {
      yylhs.value.as < ref6<unit> > () = val<substitution_formula>(make, val<substitution>(yystack_[0].value.as < ref6<unit> > ()), val<formula>(yystack_[1].value.as < ref6<unit> > ()));
    }
#line 4988 "../../mli-root/src/database-parser.cc"
    break;

  case 308: // term: set_term
#line 2457 "../../mli-root/src/database-parser.yy"
                { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 4994 "../../mli-root/src/database-parser.cc"
    break;

  case 309: // simple_term: "term constant"
#line 2462 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5000 "../../mli-root/src/database-parser.cc"
    break;

  case 310: // simple_term: "natural number value"
#line 2463 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = val<integer>(make, yystack_[0].value.as < std::pair<std::string, integer> > ().second); }
#line 5006 "../../mli-root/src/database-parser.cc"
    break;

  case 311: // simple_term: "integer value"
#line 2464 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = val<integer>(make, yystack_[0].value.as < integer > ()); }
#line 5012 "../../mli-root/src/database-parser.cc"
    break;

  case 312: // simple_term: term_identifier
#line 2465 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 5018 "../../mli-root/src/database-parser.cc"
    break;

  case 313: // simple_term: "(" term ")"
#line 2466 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 5024 "../../mli-root/src/database-parser.cc"
    break;

  case 314: // term_identifier: "object variable" variable_exclusion_set
#line 2471 "../../mli-root/src/database-parser.yy"
                                                    {
      val<variable> xr = yystack_[1].value.as < val<unit> > ();
      val<variable> vr = yystack_[0].value.as < ref6<unit> > ();
      xr->excluded_.insert(vr->excluded_.begin(), vr->excluded_.end());
      yylhs.value.as < ref6<unit> > () = xr;
    }
#line 5035 "../../mli-root/src/database-parser.cc"
    break;

  case 315: // term_identifier: "function variable"
#line 2477 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5041 "../../mli-root/src/database-parser.cc"
    break;

  case 316: // term_identifier: "function map variable"
#line 2478 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5047 "../../mli-root/src/database-parser.cc"
    break;

  case 317: // term_identifier: "all variable"
#line 2479 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5053 "../../mli-root/src/database-parser.cc"
    break;

  case 318: // term_identifier: "exist variable"
#line 2480 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5059 "../../mli-root/src/database-parser.cc"
    break;

  case 319: // term_identifier: "Set variable"
#line 2481 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5065 "../../mli-root/src/database-parser.cc"
    break;

  case 320: // term_identifier: "set variable"
#line 2482 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5071 "../../mli-root/src/database-parser.cc"
    break;

  case 321: // term_identifier: "implicit set variable"
#line 2483 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5077 "../../mli-root/src/database-parser.cc"
    break;

  case 322: // variable_exclusion_set: %empty
#line 2488 "../../mli-root/src/database-parser.yy"
           { yylhs.value.as < ref6<unit> > () = val<variable>(make);  }
#line 5083 "../../mli-root/src/database-parser.cc"
    break;

  case 323: // variable_exclusion_set: "ₓ" "₍" variable_exclusion_list "₎"
#line 2489 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 5089 "../../mli-root/src/database-parser.cc"
    break;

  case 324: // variable_exclusion_list: bound_variable
#line 2494 "../../mli-root/src/database-parser.yy"
                      { val<variable> vr(make); vr->excluded_.insert(yystack_[0].value.as < ref6<unit> > ()); yylhs.value.as < ref6<unit> > () = vr; }
#line 5095 "../../mli-root/src/database-parser.cc"
    break;

  case 325: // variable_exclusion_list: variable_exclusion_list bound_variable
#line 2495 "../../mli-root/src/database-parser.yy"
                                                   {
      val<variable> vr = yystack_[1].value.as < ref6<unit> > ();
      vr->excluded_.insert(yystack_[0].value.as < ref6<unit> > ());
      yylhs.value.as < ref6<unit> > () = vr;
    }
#line 5105 "../../mli-root/src/database-parser.cc"
    break;

  case 326: // bound_variable: "all variable"
#line 2504 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5111 "../../mli-root/src/database-parser.cc"
    break;

  case 327: // bound_variable: "exist variable"
#line 2505 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5117 "../../mli-root/src/database-parser.cc"
    break;

  case 328: // bound_variable: "Set variable"
#line 2506 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5123 "../../mli-root/src/database-parser.cc"
    break;

  case 329: // bound_variable: "set variable"
#line 2507 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5129 "../../mli-root/src/database-parser.cc"
    break;

  case 330: // bound_variable: "implicit set variable"
#line 2508 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5135 "../../mli-root/src/database-parser.cc"
    break;

  case 331: // function_term: function_term_identifier tuple
#line 2513 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, val<formula>(yystack_[1].value.as < ref6<unit> > ()), val<formula>(yystack_[0].value.as < ref6<unit> > ()),
        structure::function, 0_ml, structure::postargument, precedence_t()); }
#line 5143 "../../mli-root/src/database-parser.cc"
    break;

  case 332: // function_term: term_function_application
#line 2516 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < ref6<unit> > (); }
#line 5149 "../../mli-root/src/database-parser.cc"
    break;

  case 333: // function_term: term "!"
#line 2517 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[0].value.as < std::string > (), structure::function, 0_ml,
        structure::postfix, factorial_oprec, yystack_[1].value.as < ref6<unit> > ());
    }
#line 5158 "../../mli-root/src/database-parser.cc"
    break;

  case 334: // function_term: term "+" term
#line 2521 "../../mli-root/src/database-parser.yy"
                           { // $$ = val<integer_addition>(make, val<formula>($x), val<formula>($y));
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, plus_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5167 "../../mli-root/src/database-parser.cc"
    break;

  case 335: // function_term: term "-" term
#line 2525 "../../mli-root/src/database-parser.yy"
                           { // $$ = val<integer_addition>(make, val<formula>($x), val<integer_negative>(make, val<formula>($y)));
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, minus_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5176 "../../mli-root/src/database-parser.cc"
    break;

  case 336: // function_term: "-" term
#line 2529 "../../mli-root/src/database-parser.yy"
                                      { // $$ = val<integer_negative>(make, val<formula>($x)); }
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, unary_minus_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5185 "../../mli-root/src/database-parser.cc"
    break;

  case 337: // function_term: term "⋅" term
#line 2533 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, mult_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5194 "../../mli-root/src/database-parser.cc"
    break;

  case 338: // function_term: term "/" term
#line 2537 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, divide_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5203 "../../mli-root/src/database-parser.cc"
    break;

  case 339: // set_term: "{" "}"
#line 2545 "../../mli-root/src/database-parser.yy"
            { yylhs.value.as < ref6<unit> > () = ref0<sequence>(make, sequence::member_list_set); }
#line 5209 "../../mli-root/src/database-parser.cc"
    break;

  case 340: // set_term: "∅"
#line 2546 "../../mli-root/src/database-parser.yy"
        { yylhs.value.as < ref6<unit> > () = val<constant>(make, "∅", constant::object); }
#line 5215 "../../mli-root/src/database-parser.cc"
    break;

  case 341: // set_term: "{" set_member_list "}"
#line 2547 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.as < ref6<unit> > () = yystack_[1].value.as < ref6<unit> > (); }
#line 5221 "../../mli-root/src/database-parser.cc"
    break;

  case 342: // set_term: "{" "set variable definition" optional_in_term "|" object_formula "}"
#line 2548 "../../mli-root/src/database-parser.yy"
                                                                                 {
      symbol_table.pop_level();
      yylhs.value.as < ref6<unit> > () = val<bound_formula>(make, yystack_[4].value.as < val<unit> > (), yystack_[3].value.as < ref6<unit> > (), yystack_[1].value.as < ref6<unit> > (), bound_formula::set_);
    }
#line 5230 "../../mli-root/src/database-parser.cc"
    break;

  case 343: // set_term: "{" "₍" implicit_set_identifier_list optional_in_term "₎" term "|" object_formula "}"
#line 2552 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      symbol_table.pop_level();
      variable_list& vs = dyn_cast<variable_list&>(yystack_[6].value.as < ref6<unit> > ());
      ref0<sequence> sp(make, val<formula>(yystack_[3].value.as < ref6<unit> > ()), sequence::implicit_set);
      sp->push_back(val<formula>(yystack_[1].value.as < ref6<unit> > ()));
      yylhs.value.as < ref6<unit> > () =
        val<bound_formula>(make, vs, yystack_[5].value.as < ref6<unit> > (), val<formula>(sp));
    }
#line 5243 "../../mli-root/src/database-parser.cc"
    break;

  case 344: // set_term: term "∪" term
#line 2560 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, set_union_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5252 "../../mli-root/src/database-parser.cc"
    break;

  case 345: // set_term: term "∩" term
#line 2564 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, set_intersection_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5261 "../../mli-root/src/database-parser.cc"
    break;

  case 346: // set_term: term "∖" term
#line 2568 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::infix, set_difference_oprec, yystack_[2].value.as < ref6<unit> > (), yystack_[0].value.as < ref6<unit> > ());
    }
#line 5270 "../../mli-root/src/database-parser.cc"
    break;

  case 347: // set_term: "∁" term
#line 2572 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, set_complement_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5279 "../../mli-root/src/database-parser.cc"
    break;

  case 348: // set_term: "⋃" term
#line 2576 "../../mli-root/src/database-parser.yy"
                   { /* prefix union operator  */
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, set_union_operator_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5288 "../../mli-root/src/database-parser.cc"
    break;

  case 349: // set_term: "∩" term
#line 2580 "../../mli-root/src/database-parser.yy"
                   { /* prefix intersection operator  */
      yylhs.value.as < ref6<unit> > () = val<structure>(make, yystack_[1].value.as < std::string > (), structure::function, 0_ml,
        structure::prefix, set_intersection_operator_oprec, yystack_[0].value.as < ref6<unit> > ());
    }
#line 5297 "../../mli-root/src/database-parser.cc"
    break;

  case 350: // $@22: %empty
#line 2588 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 5303 "../../mli-root/src/database-parser.cc"
    break;

  case 351: // implicit_set_identifier_list: $@22 "Set variable"
#line 2589 "../../mli-root/src/database-parser.yy"
                       {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = val<variable_list>(make, val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::implicit_set);
    }
#line 5312 "../../mli-root/src/database-parser.cc"
    break;

  case 352: // $@23: %empty
#line 2593 "../../mli-root/src/database-parser.yy"
                                    { bound_variable_type = database_parser::token::is_set_variable; }
#line 5318 "../../mli-root/src/database-parser.cc"
    break;

  case 353: // implicit_set_identifier_list: implicit_set_identifier_list $@23 "," "Set variable"
#line 2594 "../../mli-root/src/database-parser.yy"
                             {
      bound_variable_type = free_variable_context;
      yylhs.value.as < ref6<unit> > () = yystack_[3].value.as < ref6<unit> > ();
      dyn_cast<variable_list&>(yylhs.value.as < ref6<unit> > ()).push_back(val<variable>(yystack_[0].value.as < val<unit> > ()), bound_formula::implicit_set);
    }
#line 5328 "../../mli-root/src/database-parser.cc"
    break;

  case 354: // set_member_list: term
#line 2603 "../../mli-root/src/database-parser.yy"
            {
      ref0<sequence> vr(make, sequence::member_list_set);
      yylhs.value.as < ref6<unit> > () = vr;
      vr->push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ())); }
#line 5337 "../../mli-root/src/database-parser.cc"
    break;

  case 355: // set_member_list: set_member_list "," term
#line 2607 "../../mli-root/src/database-parser.yy"
                                   {
      yylhs.value.as < ref6<unit> > () = yystack_[2].value.as < ref6<unit> > ();
      sequence& vr = dyn_cast<sequence&>(yylhs.value.as < ref6<unit> > ());
      vr.push_back(val<formula>(yystack_[0].value.as < ref6<unit> > ()));
    }
#line 5347 "../../mli-root/src/database-parser.cc"
    break;

  case 356: // function_term_identifier: "function constant"
#line 2616 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5353 "../../mli-root/src/database-parser.cc"
    break;

  case 357: // function_term_identifier: "function variable"
#line 2617 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.as < ref6<unit> > () = yystack_[0].value.as < val<unit> > (); }
#line 5359 "../../mli-root/src/database-parser.cc"
    break;


#line 5363 "../../mli-root/src/database-parser.cc"

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


  const short database_parser::yypact_ninf_ = -500;

  const short database_parser::yytable_ninf_ = -358;

  const short
  database_parser::yypact_[] =
  {
      93,  -500,    63,    27,  -500,   129,  -500,  -500,    44,  -500,
    -500,  -500,  -500,    50,  -500,  -500,   246,   203,   149,    80,
    -500,   232,  -500,   460,   144,  -500,   154,   293,   460,    44,
      44,    44,   300,    71,   327,  -500,  -500,  -500,  -500,   295,
     503,  -500,   115,  -500,  -500,  -500,   268,  -500,  -500,    44,
     269,   276,   288,  -500,   279,  -500,  -500,   376,   386,   301,
    -500,  -500,   304,  -500,  -500,  -500,  -500,   410,  -500,  -500,
     792,   310,   313,   313,  -500,  -500,  -500,  -500,   205,   324,
    -500,   342,  -500,   345,    28,  -500,  -500,  -500,  -500,  -500,
    -500,   379,   379,   371,   444,   444,   444,   444,   444,  -500,
    -500,  1526,  -500,  -500,  1526,  1526,  1526,   692,   992,   792,
    -500,  -500,  -500,   792,    14,  -500,   348,  -500,  -500,   333,
    -500,  -500,   316,  -500,   349,  -500,  -500,  -500,  -500,   313,
    -500,  -500,  1429,  -500,  -500,  -500,   112,   360,  -500,  -500,
    -500,   313,  -500,  -500,  -500,   474,  -500,   354,  -500,  -500,
    -500,  -500,   300,  -500,  -500,    71,   367,   327,  -500,  -500,
     473,    61,   368,  1340,  -500,  1526,  -500,  -500,  -500,   359,
    -500,  -500,   439,   441,  -500,  1340,  -500,   444,   444,   444,
     444,   411,  1454,  1064,  -500,   377,   294,   294,   294,   186,
     455,    14,   398,    17,   899,   416,  1162,  -500,  -500,   225,
    1682,   -57,  -500,    14,   371,   371,   792,   792,   723,   348,
    -500,  -500,  -500,  -500,   497,   478,  1340,  1340,  1340,   371,
     371,   371,   371,   371,   864,   349,  -500,  -500,  -500,  -500,
    -500,  -500,  1526,  1251,  -500,  -500,   169,  1682,  1526,  1526,
     478,  1526,  1526,  1526,  1526,  1526,  1526,  1526,  1526,  1526,
    1526,  1526,  1526,  -500,  1526,  1526,  1526,  1526,  1526,  1526,
    1526,  1526,  1526,  1526,  1526,  1526,  1526,   768,   360,  -500,
    -500,   535,    44,    44,    44,  -500,  -500,  -500,  -500,  -500,
      10,  -500,   503,   503,  -500,  -500,  -500,  -500,    57,  -500,
    -500,   414,   503,  -500,   256,   295,  -500,   160,   534,   175,
     551,   634,   423,  -500,   447,  -500,   459,  -500,  -500,  -500,
    -500,  -500,   146,   506,   481,   551,   530,  1340,   500,   464,
     469,  -500,   461,   239,   303,  1584,    36,   541,   -12,  1526,
    -500,   475,   475,    -7,  -500,   519,   521,   522,   526,  -500,
     528,  -500,  1340,  -500,  -500,   534,  1682,   534,   534,  1340,
    1340,  1340,  1340,  1340,  -500,   551,   308,  1340,  -500,   551,
     551,   595,   551,   551,   551,   551,   551,   551,   551,   551,
     551,   551,   551,   551,  -500,   -69,   -69,   551,   551,   573,
     294,   294,   551,   551,   551,   551,  -500,  -500,   505,   507,
     509,   515,  -500,   516,   792,  -500,  -500,  -500,  -500,   326,
     554,   856,   518,   574,    84,   520,   217,   527,   536,   510,
    -500,  -500,   635,  -500,  -500,  1340,  -500,  1526,  -500,  -500,
    -500,  -500,  -500,  -500,   113,  -500,   598,   537,   538,  1526,
     567,   545,   339,  1633,  1340,  1340,   546,   549,  -500,   659,
    -500,  -500,  1340,  1340,   -21,  -500,   551,   167,   563,   563,
     792,  1340,  1136,   625,  1526,   534,  1682,  -500,   630,   321,
     321,   504,  -500,   534,  1340,  -500,  -500,  -500,  -500,  -500,
    -500,   792,   792,  1340,  1340,  1526,  1526,  -500,   608,   601,
     602,   348,    57,  -500,    57,    57,    57,    57,   534,   551,
    -500,  -500,  -500,   -22,   647,   648,   532,  1526,  -500,   313,
     313,   534,  1682,   245,  1526,   649,  1526,   191,   135,   -12,
    1340,  -500,  -500,   226,   142,  -500,   143,  -500,    -1,  -500,
     202,   792,   792,    38,   283,   577,   579,   400,   534,  1682,
     503,   503,   503,   584,   585,   534,   534,   551,   551,  1340,
    -500,  -500,   348,   527,   536,   578,    49,  -500,   235,  -500,
    -500,  -500,  -500,   551,     0,  -500,  -500,   587,   588,  -500,
     395,  -500,   551,   -17,   -17,  -500,   254,   103,   593,   103,
     610,  -500,   617,  -500,  -500,  -500,  -500,  -500,   233,   106,
    -500,    86,  -500,   -14,  -500,    40,   368,  -500,  -500,  -500,
    -500,  -500,   594,   597,   599,   534,    57,    57,  -500,  -500,
    -500,  -500,  1340,  -500,  -500,  -500,   313,   313,  1340,   -12,
     581,  -500,  -500,  -500,   617,  -500,  -500,   236,   603,   236,
     624,  -500,   627,  -500,  -500,  -500,  -500,  -500,  -500,    89,
    -500,   351,  -500,  -500,   278,    32,   -17,   627,  -500,  -500,
    -500,  -500,  -500,  -500,  -500
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
       0,     0,     0,     0,   267,   240,   356,   309,   189,   241,
     268,   242,   278,   315,   322,   317,   318,   316,   319,   320,
     321,   289,   289,   269,     0,     0,     0,     0,     0,   310,
     311,     0,   263,   340,     0,     0,     0,     0,     0,     0,
     211,   332,    74,     0,   115,   147,     0,   149,   150,     0,
     190,   199,   148,   215,     0,   214,   209,   243,   244,     0,
     212,   277,   300,   284,   285,   286,     0,   305,   312,   306,
     308,     0,   119,   121,    39,     0,    48,     0,    36,    68,
      66,    75,     0,   136,   137,     0,     0,     0,    94,    78,
       0,    87,   156,     0,   204,     0,    32,    28,   205,     0,
     314,   290,     0,     0,   270,     0,   279,     0,     0,     0,
       0,   322,     0,     0,   336,     0,   347,   349,   348,   322,
       0,     0,   147,   148,     0,   300,     0,   350,   339,     0,
     354,     0,   151,   116,   269,   269,     0,     0,     0,   158,
       9,    11,    12,    13,     0,     0,     0,     0,     0,   269,
     269,   269,   269,   269,     0,   210,    15,    17,    18,   266,
     241,   242,     0,     0,   230,   238,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   333,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   307,    22,
     331,     0,     0,     0,     0,    49,    51,    61,    52,    50,
       0,    34,     0,     0,   131,   134,   128,   126,    99,    79,
      89,     0,     0,    83,     0,     0,    90,     0,   207,     0,
     303,     0,     0,   294,   287,   297,   288,   271,   281,   280,
     282,   283,   322,     0,     0,   354,     0,     0,     0,   157,
     213,   313,     0,   322,     0,     0,   300,     0,   219,     0,
     341,   159,   159,   152,   153,     0,     0,     0,     0,   315,
       0,    10,     0,   198,   191,   192,   193,   200,   201,     0,
       0,     0,     0,     0,    16,   301,     0,     0,   232,   202,
     203,     0,   249,   250,   251,   252,   253,   254,   255,   256,
     245,   246,   247,   248,   337,   334,   335,   257,   258,   344,
     345,   346,   259,   260,   261,   262,   338,    23,     0,     0,
       0,     0,    45,     0,     0,   117,   138,   139,   140,   147,
     148,     0,     0,     0,   107,   112,     0,    95,    97,   100,
     106,    84,    91,    88,    86,     0,   206,     0,   302,   326,
     327,   328,   329,   330,     0,   324,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   351,     0,
     222,   223,     0,     0,     0,   220,   355,     0,   173,   173,
       0,     0,     0,     0,     0,   194,   195,   273,   272,   274,
     275,   276,   239,   231,     0,    47,    59,    62,    64,    69,
     118,     0,     0,     0,     0,     0,     0,    67,     0,   110,
     108,     0,    99,    92,    99,     0,     0,    99,   208,   304,
     323,   325,   292,     0,     0,     0,     0,     0,   264,     0,
       0,    26,    30,     0,     0,     0,     0,     0,     0,     0,
       0,   172,   171,     0,     0,   163,     0,   166,     0,   169,
       0,     0,     0,     0,     0,     0,     0,     0,   196,   197,
       0,     0,     0,   147,   147,   143,   144,   145,   146,     0,
     111,   109,   114,    96,    98,   102,     0,   104,     0,   293,
     291,   296,   299,    30,     0,    25,    29,     0,     0,   342,
       0,   353,   224,     0,     0,   221,     0,     0,   165,   168,
       0,   160,     0,   161,   162,   170,   186,   185,     0,     0,
     177,     0,   180,     0,   183,   154,   155,    14,    19,    20,
      21,    24,     0,     0,     0,   129,     0,     0,   101,    85,
     233,   234,     0,   237,   265,   235,     0,     0,     0,   219,
       0,   217,   226,   216,     0,   164,   167,     0,   179,   182,
       0,   174,     0,   175,   176,   184,    60,    63,    65,     0,
     105,     0,    27,    31,     0,     0,     0,     0,   178,   181,
     103,   236,   343,   218,   225
  };

  const short
  database_parser::yypgoto_[] =
  {
    -500,  -500,  -500,   725,  -500,   265,  -201,  -500,  -500,   529,
    -109,  -500,  -111,  -500,  -500,  -500,  -500,  -500,  -500,  -500,
    -500,  -500,  -500,  -500,  -500,  -500,  -500,   606,  -500,   733,
    -500,  -500,  -500,  -500,  -500,  -135,  -500,  -131,  -500,    -2,
    -500,  -500,  -500,  -500,  -500,   465,  -500,  -500,  -500,  -500,
    -500,  -500,   600,  -500,   275,   274,   280,   178,  -461,  -500,
    -500,  -274,  -500,   -16,  -500,   721,  -500,   620,  -500,  -500,
    -500,   631,  -500,   632,   392,  -500,  -500,  -500,   -54,  -102,
     456,  -500,   221,   346,   220,   347,  -478,   353,  -500,   176,
     277,   173,   285,  -499,  -500,  -500,  -500,  -139,  -500,  -500,
     722,  -500,  -106,  -500,  -485,   194,  -324,  -500,  -233,  -500,
    -500,   675,   357,  -500,  -500,   257,  -500,   463,  -500,     9,
    -500,  -500,  -500,  -500,   718,  -500,  -500,  -500,  -500,  -500,
    -500,  -184,   -73,  -500,   199,  -500,   -77,  -500,  -500,   388,
    -500,  -500,  -500,  -500,  -500,  -500,  -500
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
     618,   582,   619,   584,   116,   117,   118,   119,   120,   121,
     164,   297,   122,   123,   610,   444,   611,   124,   125,   604,
     234,   126,   127,   185,   554,   128,   129,   175,   130,   131,
     132,   133,   134,   135,   172,   302,   493,   304,   427,   306,
     428,   236,   166,   299,   237,   137,   138,   170,   424,   425,
     139,   140,   326,   327,   437,   201,   141
  };

  const short
  database_parser::yytable_[] =
  {
     167,   193,   199,   358,   445,   192,    13,    41,   341,   402,
     277,   322,    41,   228,   278,   227,   162,   205,   412,    29,
     272,   273,   274,    30,   545,   547,   269,    50,    51,    52,
     290,   549,    -7,   576,   204,   254,   439,   440,   205,   577,
     575,   439,   440,    74,   217,   218,   511,   148,   600,    80,
     601,  -198,   512,   191,  -198,   202,   229,   298,   204,   203,
    -358,  -198,   205,     6,   205,    91,    92,   329,   270,   307,
      29,   266,    32,    33,    34,   404,   344,   289,   -93,   612,
     158,   330,    10,    11,   625,   219,   220,   221,   222,   223,
     324,   575,   441,    -2,     1,    10,    11,   441,    -7,    10,
      11,   361,   509,   176,   177,   178,   179,   180,   479,    56,
     345,   347,   348,   550,   228,   510,   227,   207,    26,   609,
     625,   624,    10,    11,   169,   442,   602,   356,   443,   279,
     442,   340,   574,   443,     8,   547,   630,   206,   207,   238,
     239,    12,   436,   240,   320,   277,   232,   340,   392,   278,
     511,   644,   333,   334,    12,   509,   512,   387,    12,   291,
    -352,   206,   207,   206,   207,    57,    58,   587,   419,   420,
     643,   421,   422,   597,   423,    14,   400,    32,    33,    34,
     399,    12,    44,    45,   598,   565,   308,   309,   310,   311,
     340,   241,   242,   243,   244,   245,   246,   247,   248,   249,
     250,   251,   252,   219,   220,   221,   222,   223,    24,  -198,
     622,   432,  -198,   597,   511,   253,   254,   255,   256,  -198,
     512,   623,   257,   258,   640,   259,   260,   261,   191,   620,
     262,   263,   264,   265,    91,    92,   455,   429,    27,   136,
     142,   621,   169,   457,   458,   459,   460,   461,   490,   576,
      17,   463,   266,    18,    19,   577,   592,   593,   594,   219,
     220,   221,   222,   223,   279,   570,   394,   572,   513,   136,
     389,   390,   391,   511,    25,   571,   573,   317,   413,   512,
     576,   564,   169,   576,   415,   445,   577,   416,   400,   577,
      48,   357,   399,   219,   220,   221,   222,   223,    49,   417,
     184,   578,   418,   186,   187,   188,   194,   200,   136,   488,
      64,    65,   136,   219,   220,   221,   222,   223,    32,    33,
      34,   603,   219,   220,   221,   222,   223,   567,   501,   503,
     317,   163,   617,  -187,   563,   169,   507,   508,    53,   482,
     191,   341,   483,   217,   218,   524,   219,   220,   221,   222,
     223,   219,   220,   221,   222,   223,   214,   482,   528,   215,
     599,   471,   472,   328,   300,    61,   216,   535,   536,   533,
     534,   219,   220,   221,   222,   223,   219,   220,   221,   222,
     223,   314,   315,   559,   219,   220,   221,   222,   223,   219,
     220,   221,   613,   144,   149,   325,   523,   253,   254,   255,
     256,   150,   480,   152,   566,   136,   136,   219,   220,   221,
     222,   223,   588,   151,   153,   346,   642,   191,   191,   219,
     220,   221,   222,   223,   154,   155,   555,   556,   157,   158,
     320,   355,   325,   595,   266,   462,   163,   359,   360,   165,
     362,   363,   364,   365,   366,   367,   368,   369,   370,   371,
     372,   373,  -227,   374,   375,   376,   377,   378,   379,   380,
     381,   382,   383,   384,   385,   386,   499,   585,   586,    29,
    -228,  -357,   174,    30,    31,   171,   208,   224,   641,   281,
     271,   401,   136,    29,   272,   273,   274,    30,   267,   286,
     288,   136,   207,   301,   303,    82,   631,   305,   253,   254,
     255,   256,   634,   253,   254,   255,   256,   169,   259,   260,
     261,   316,   318,   259,   260,   261,   433,    94,    95,    96,
      97,    98,    32,    33,    34,   319,   232,    70,   446,   591,
     342,   343,   608,   632,   633,   266,    32,    33,    34,   411,
     266,   456,   388,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    82,    83,    84,   426,    85,    86,
      87,    88,    89,   430,    90,    32,    33,    34,    91,    92,
      93,  -295,   219,   220,   221,   222,    94,    95,    96,    97,
      98,   217,   218,  -298,   253,   254,   255,   256,   431,   473,
     474,   434,  -188,   401,   259,   260,   261,  -229,   435,   438,
      99,   100,   219,   220,   221,   222,   223,   447,   321,   101,
     102,   450,   103,   451,   452,   104,   489,   105,   453,   106,
     454,   266,   219,   220,   221,   222,   223,   464,   496,   107,
     465,   478,   466,   502,   467,   253,   254,   255,   256,   108,
     468,   469,   109,   477,   486,   259,   260,   261,  -113,   136,
     484,   492,   487,   527,   253,   254,   255,   256,   497,   500,
     485,   494,   495,   529,   259,   260,   261,   331,   332,   526,
     136,   136,   266,   505,   537,   538,   253,   254,   255,   256,
     498,   504,   349,   350,   351,   352,   353,   260,   261,   419,
     420,   266,   421,   422,   506,   423,   553,   520,   219,   539,
     540,   541,   551,   560,   552,   562,   589,   561,   590,  -141,
    -142,   614,   596,   266,   606,   607,    70,   572,   567,   626,
     136,   136,   627,   637,   628,   636,   617,   622,     7,   136,
     136,   136,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    82,    83,   189,   542,    85,    86,    87,
      88,    89,   280,    90,   354,    28,   543,    91,    92,    93,
     414,   296,   548,   143,   544,    94,    95,    96,    97,    98,
     335,   336,   337,   338,   629,   339,   181,   287,    85,    86,
      87,    88,    89,   284,    90,   190,   470,   285,   449,    99,
     100,   615,   616,   516,   518,   639,   638,   581,   101,   102,
     168,   103,   522,   635,   104,   583,   105,   235,   106,   525,
     173,   605,   491,     0,     0,     0,    70,     0,   107,     0,
     339,   181,     0,    85,    86,    87,    88,    89,   108,    90,
       0,   109,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    82,    83,    84,     0,    85,    86,    87,
      88,    89,     0,    90,     0,     0,     0,    91,    92,    93,
       0,     0,     0,     0,     0,    94,    95,    96,    97,    98,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   238,   239,     0,     0,   240,     0,    99,
     100,   475,   476,     0,     0,     0,     0,     0,   101,   102,
       0,   103,     0,     0,   104,     0,   105,     0,   106,     0,
       0,     0,   336,   337,   338,     0,   339,   181,   107,    85,
      86,    87,    88,    89,     0,    90,   238,   239,   108,     0,
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
     161,    53,     5,    47,    20,   104,    53,    54,    24,    53,
     518,    53,    54,    43,    27,    28,    47,    49,    48,    49,
      50,    23,    53,   107,    26,   109,   129,   163,    20,   113,
      20,    33,    24,     0,    24,    65,    66,   124,   141,   175,
       9,   140,    62,    63,    64,    18,   215,    16,    17,   564,
      19,   138,    38,    39,   583,    68,    69,    70,    71,    72,
     196,   569,   109,     0,     1,    38,    39,   109,     5,    38,
      39,   240,   123,    94,    95,    96,    97,    98,    24,    38,
     216,   217,   218,   135,   225,   136,   225,   124,    38,   136,
     619,   135,    38,    39,    96,   142,   126,   233,   145,   145,
     142,   208,   133,   145,     5,   596,   597,   123,   124,    27,
      28,    97,   326,    31,   127,   280,   110,   224,   138,   280,
      47,   636,   206,   207,    97,   123,    53,   268,    97,   161,
     124,   123,   124,   123,   124,    94,    95,   129,    55,    56,
     138,    58,    59,   124,    61,   125,   282,    62,    63,    64,
     282,    97,    38,    39,   135,   509,   177,   178,   179,   180,
     267,    79,    80,    81,    82,    83,    84,    85,    86,    87,
      88,    89,    90,    68,    69,    70,    71,    72,     5,    23,
     124,   317,    26,   124,    47,   103,   104,   105,   106,    33,
      53,   135,   110,   111,   135,   113,   114,   115,   282,   123,
     118,   119,   120,   121,    65,    66,   342,    91,     6,    40,
     125,   135,    96,   349,   350,   351,   352,   353,   135,    47,
       4,   357,   140,     7,     8,    53,   530,   531,   532,    68,
      69,    70,    71,    72,   280,   123,   282,   124,   101,    70,
     272,   273,   274,    47,   125,   133,   133,    91,   294,    53,
      47,   146,    96,    47,   124,   609,    53,   127,   394,    53,
     136,   122,   394,    68,    69,    70,    71,    72,     5,   124,
     101,    99,   127,   104,   105,   106,   107,   108,   109,   415,
      15,    16,   113,    68,    69,    70,    71,    72,    62,    63,
      64,   554,    68,    69,    70,    71,    72,   101,   434,   435,
      91,   126,    99,   128,   143,    96,   442,   443,    38,   122,
     394,   542,   125,    27,    28,   451,    68,    69,    70,    71,
      72,    68,    69,    70,    71,    72,    23,   122,   464,    26,
     125,    35,    36,   138,   165,    38,    33,   473,   474,   471,
     472,    68,    69,    70,    71,    72,    68,    69,    70,    71,
      72,   182,   183,   138,    68,    69,    70,    71,    72,    68,
      69,    70,   138,   125,   125,   196,   450,   103,   104,   105,
     106,   125,   404,   124,   510,   206,   207,    68,    69,    70,
      71,    72,   129,   125,    38,   216,   138,   471,   472,    68,
      69,    70,    71,    72,    38,   124,   499,   500,   124,    19,
     127,   232,   233,   539,   140,   127,   126,   238,   239,   126,
     241,   242,   243,   244,   245,   246,   247,   248,   249,   250,
     251,   252,   128,   254,   255,   256,   257,   258,   259,   260,
     261,   262,   263,   264,   265,   266,   127,   521,   522,     9,
     128,   126,   101,    13,    14,    96,   128,   128,   127,   125,
       6,   282,   283,     9,    10,    11,    12,    13,   128,   122,
      17,   292,   124,   134,    55,    51,   602,    56,   103,   104,
     105,   106,   608,   103,   104,   105,   106,    96,   113,   114,
     115,   134,    57,   113,   114,   115,   317,    73,    74,    75,
      76,    77,    62,    63,    64,   127,   110,    24,   329,   129,
      33,    53,   137,   606,   607,   140,    62,    63,    64,   125,
     140,   342,     7,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,    53,   134,    55,    56,
      57,    58,    59,    57,    61,    62,    63,    64,    65,    66,
      67,   124,    68,    69,    70,    71,    73,    74,    75,    76,
      77,    27,    28,   124,   103,   104,   105,   106,    58,    35,
      36,    91,   128,   394,   113,   114,   115,   128,   137,    58,
      97,    98,    68,    69,    70,    71,    72,   132,   127,   106,
     107,    92,   109,    92,    92,   112,   417,   114,    92,   116,
      92,   140,    68,    69,    70,    71,    72,    32,   429,   126,
     125,    57,   125,   434,   125,   103,   104,   105,   106,   136,
     125,   125,   139,   125,   134,   113,   114,   115,   128,   450,
     123,    53,    17,   454,   103,   104,   105,   106,    91,   127,
     124,   124,   124,   464,   113,   114,   115,   204,   205,    44,
     471,   472,   140,   124,   475,   476,   103,   104,   105,   106,
     135,   135,   219,   220,   221,   222,   223,   114,   115,    55,
      56,   140,    58,    59,    35,    61,   497,   134,    68,    91,
      99,    99,    55,   504,    56,   506,   129,    58,   129,   125,
     125,   101,   134,   140,   127,   127,    24,   124,   101,   125,
     521,   522,   125,    99,   125,   144,    99,   124,     3,   530,
     531,   532,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,   481,    55,    56,    57,
      58,    59,   146,    61,   225,    22,   482,    65,    66,    67,
     295,   161,   487,    42,   484,    73,    74,    75,    76,    77,
      47,    48,    49,    50,   596,    52,    53,   157,    55,    56,
      57,    58,    59,   152,    61,    93,   394,   155,   332,    97,
      98,   570,   572,   447,   447,   622,   620,   520,   106,   107,
      78,   109,   449,   609,   112,   520,   114,   132,   116,   452,
      92,   554,   424,    -1,    -1,    -1,    24,    -1,   126,    -1,
      52,    53,    -1,    55,    56,    57,    58,    59,   136,    61,
      -1,   139,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    -1,    55,    56,    57,
      58,    59,    -1,    61,    -1,    -1,    -1,    65,    66,    67,
      -1,    -1,    -1,    -1,    -1,    73,    74,    75,    76,    77,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    27,    28,    -1,    -1,    31,    -1,    97,
      98,    35,    36,    -1,    -1,    -1,    -1,    -1,   106,   107,
      -1,   109,    -1,    -1,   112,    -1,   114,    -1,   116,    -1,
      -1,    -1,    48,    49,    50,    -1,    52,    53,   126,    55,
      56,    57,    58,    59,    -1,    61,    27,    28,   136,    -1,
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
     169,   171,   217,   219,   234,   235,   250,   251,   252,   253,
     254,   255,   258,   259,   263,   264,   267,   268,   271,   272,
     274,   275,   276,   277,   278,   279,   290,   291,   292,   296,
     297,   302,   125,   221,   125,   183,   181,   175,   195,   125,
     125,   125,   124,    38,    38,   124,   224,   124,    19,   208,
     209,   203,   234,   126,   256,   126,   288,   288,   256,    96,
     293,    96,   280,   280,   101,   273,   275,   275,   275,   275,
     275,    53,   126,   136,   290,   269,   290,   290,   290,    53,
      93,   234,   235,   258,   290,    60,   126,   134,   138,   258,
     290,   301,   234,   234,    20,    24,   123,   124,   128,   161,
     162,   163,   166,   168,    23,    26,    33,    27,    28,    68,
      69,    70,    71,    72,   128,   164,   165,   166,   168,   288,
      48,    50,   110,   126,   266,   267,   287,   290,    27,    28,
      31,    79,    80,    81,    82,    83,    84,    85,    86,    87,
      88,    89,    90,   103,   104,   105,   106,   110,   111,   113,
     114,   115,   118,   119,   120,   121,   140,   128,   167,   168,
     288,     6,    10,    11,    12,   184,   187,   191,   193,   219,
     183,   125,   194,   192,   227,   229,   122,   223,    17,    16,
     193,   195,   204,   205,   206,   207,   208,   257,   258,   289,
     290,   134,   281,    55,   283,    56,   285,   258,   275,   275,
     275,   275,    53,    93,   290,   290,   134,    91,    57,   127,
     127,   127,   287,    53,   258,   290,   298,   299,   138,   124,
     138,   273,   273,   234,   234,    47,    48,    49,    50,    52,
     292,   162,    33,    53,   253,   258,   290,   258,   258,   273,
     273,   273,   273,   273,   165,   290,   258,   122,   264,   290,
     290,   253,   290,   290,   290,   290,   290,   290,   290,   290,
     290,   290,   290,   290,   290,   290,   290,   290,   290,   290,
     290,   290,   290,   290,   290,   290,   290,   168,     7,   195,
     195,   195,   138,   218,   219,   230,   231,   232,   233,   235,
     258,   290,   217,   225,    18,   195,   210,   211,   212,   214,
     215,   125,   217,   219,   201,   124,   127,   124,   127,    55,
      56,    58,    59,    61,   294,   295,   134,   284,   286,    91,
      57,    58,   258,   290,    91,   137,   287,   300,    58,    53,
      54,   109,   142,   145,   261,   262,   290,   132,   236,   236,
      92,    92,    92,    92,    92,   258,   290,   258,   258,   258,
     258,   258,   127,   258,    32,   125,   125,   125,   125,   125,
     230,    35,    36,    35,    36,    35,    36,   125,    57,    24,
     195,   216,   122,   125,   123,   124,   134,    17,   258,   290,
     135,   295,    53,   282,   124,   124,   290,    91,   135,   127,
     127,   258,   290,   258,   135,   124,    35,   258,   258,   123,
     136,    47,    53,   101,   237,   238,   239,   240,   241,   242,
     134,   243,   243,   234,   258,   268,    44,   290,   258,   290,
     188,   189,   190,   235,   235,   258,   258,   290,   290,    91,
      99,    99,   161,   211,   212,   214,   213,   214,   210,    53,
     135,    55,    56,   290,   270,   288,   288,   170,   172,   138,
     290,    58,   290,   143,   146,   262,   258,   101,   239,   241,
     123,   133,   124,   133,   133,   242,    47,    53,    99,   244,
     245,   246,   247,   248,   249,   234,   234,   129,   129,   129,
     129,   129,   217,   217,   217,   258,   134,   124,   135,   125,
      48,    50,   126,   264,   265,   271,   127,   127,   137,   136,
     260,   262,   260,   138,   101,   238,   240,    99,   246,   248,
     123,   135,   124,   135,   135,   249,   125,   125,   125,   213,
     214,   258,   288,   288,   258,   261,   144,    99,   245,   247,
     135,   127,   138,   138,   260
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
     241,   242,   242,   243,   243,   243,   243,   244,   244,   245,
     246,   246,   247,   248,   248,   249,   249,   250,   250,   251,
     251,   252,   252,   252,   252,   252,   252,   252,   253,   254,
     254,   254,   254,   254,   255,   255,   256,   257,   257,   258,
     258,   258,   258,   258,   258,   258,   259,   260,   260,   261,
     261,   261,   262,   262,   262,   262,   262,   263,   263,   263,
     264,   264,   264,   265,   265,   265,   265,   265,   266,   266,
     267,   267,   267,   267,   268,   268,   268,   268,   268,   268,
     268,   268,   268,   268,   268,   268,   268,   268,   268,   268,
     268,   268,   268,   269,   270,   268,   271,   272,   272,   273,
     273,   274,   274,   274,   274,   274,   274,   274,   275,   275,
     275,   275,   275,   275,   276,   277,   277,   278,   279,   280,
     281,   280,   282,   282,   283,   284,   283,   285,   286,   285,
     287,   287,   288,   289,   289,   290,   290,   290,   290,   291,
     291,   291,   291,   291,   292,   292,   292,   292,   292,   292,
     292,   292,   293,   293,   294,   294,   295,   295,   295,   295,
     295,   296,   296,   296,   296,   296,   296,   296,   296,   297,
     297,   297,   297,   297,   297,   297,   297,   297,   297,   297,
     299,   298,   300,   298,   301,   301,   302,   302
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
       2,     1,     1,     0,     3,     3,     3,     1,     3,     2,
       1,     3,     2,     1,     2,     1,     1,     1,     3,     1,
       1,     3,     3,     3,     4,     4,     5,     5,     1,     1,
       3,     3,     3,     3,     2,     2,     3,     1,     3,     1,
       2,     1,     1,     3,     1,     1,     7,     1,     3,     0,
       1,     3,     1,     1,     3,     6,     4,     1,     1,     3,
       2,     4,     3,     1,     1,     1,     3,     1,     1,     3,
       1,     1,     1,     1,     1,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     0,     0,     7,     2,     1,     1,     0,
       1,     3,     4,     4,     4,     4,     4,     1,     1,     2,
       3,     3,     3,     3,     1,     1,     1,     3,     3,     0,
       0,     5,     1,     2,     1,     0,     4,     1,     0,     4,
       0,     2,     3,     1,     3,     1,     1,     2,     1,     1,
       1,     1,     1,     3,     2,     1,     1,     1,     1,     1,
       1,     1,     0,     4,     1,     2,     1,     1,     1,     1,
       1,     2,     1,     2,     3,     3,     2,     3,     3,     2,
       1,     3,     6,     9,     3,     3,     3,     2,     2,     2,
       0,     2,     0,     4,     1,     3,     1,     1
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
       0,   787,   787,   788,   789,   798,   799,   804,   804,   809,
     810,   817,   818,   819,   824,   833,   834,   841,   842,   847,
     852,   857,   866,   867,   874,   883,   886,   886,   889,   894,
     897,   897,   900,   906,   905,   924,   925,   930,   931,   935,
     947,   948,   953,   954,   960,   959,   964,   963,   971,   972,
     977,   978,   979,   984,   985,   995,   996,   997,   999,  1005,
    1004,  1010,  1012,  1011,  1024,  1023,  1040,  1039,  1049,  1048,
    1058,  1059,  1060,  1065,  1076,  1086,  1096,  1097,  1097,  1111,
    1116,  1121,  1130,  1131,  1136,  1144,  1175,  1190,  1190,  1194,
    1205,  1210,  1220,  1231,  1232,  1237,  1238,  1246,  1249,  1257,
    1258,  1260,  1264,  1268,  1277,  1279,  1287,  1290,  1293,  1306,
    1320,  1325,  1335,  1349,  1349,  1391,  1392,  1436,  1437,  1444,
    1449,  1450,  1455,  1456,  1457,  1462,  1463,  1474,  1475,  1474,
    1509,  1510,  1515,  1530,  1531,  1536,  1547,  1558,  1573,  1574,
    1575,  1580,  1584,  1597,  1601,  1614,  1624,  1632,  1633,  1638,
    1639,  1640,  1643,  1646,  1649,  1717,  1778,  1780,  1781,  1787,
    1788,  1789,  1790,  1794,  1795,  1808,  1820,  1821,  1833,  1845,
    1846,  1857,  1862,  1872,  1873,  1874,  1875,  1879,  1880,  1893,
    1905,  1906,  1918,  1930,  1931,  1942,  1947,  2015,  2016,  2021,
    2022,  2034,  2037,  2040,  2043,  2046,  2049,  2053,  2061,  2066,
    2067,  2070,  2073,  2076,  2083,  2087,  2095,  2100,  2104,  2112,
    2113,  2116,  2117,  2118,  2119,  2120,  2125,  2136,  2137,  2142,
    2143,  2144,  2149,  2150,  2151,  2152,  2153,  2158,  2159,  2160,
    2165,  2172,  2179,  2190,  2191,  2192,  2193,  2194,  2200,  2201,
    2205,  2206,  2207,  2208,  2214,  2215,  2216,  2219,  2220,  2223,
    2224,  2225,  2226,  2227,  2228,  2229,  2230,  2232,  2233,  2234,
    2235,  2236,  2237,  2238,  2239,  2238,  2249,  2257,  2258,  2263,
    2264,  2276,  2282,  2288,  2294,  2300,  2306,  2312,  2317,  2318,
    2322,  2326,  2330,  2334,  2342,  2346,  2347,  2352,  2364,  2376,
    2377,  2377,  2385,  2386,  2396,  2400,  2400,  2410,  2414,  2414,
    2425,  2426,  2433,  2438,  2443,  2452,  2453,  2454,  2457,  2462,
    2463,  2464,  2465,  2466,  2471,  2477,  2478,  2479,  2480,  2481,
    2482,  2483,  2488,  2489,  2494,  2495,  2504,  2505,  2506,  2507,
    2508,  2513,  2516,  2517,  2521,  2525,  2529,  2533,  2537,  2545,
    2546,  2547,  2548,  2552,  2560,  2564,  2568,  2572,  2576,  2580,
    2588,  2588,  2593,  2593,  2603,  2607,  2616,  2617
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
#line 6791 "../../mli-root/src/database-parser.cc"

#line 2621 "../../mli-root/src/database-parser.yy"


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

