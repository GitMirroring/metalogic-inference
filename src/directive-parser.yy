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

%skeleton "lalr1.cc"                          /*  -*- C++ -*- */
%require "3.2"
%defines

%define api.namespace {mli}
%define api.prefix {mli}
%define api.parser.class {directive_parser}
%define api.location.type {location_t}

%parse-param {mli::directive_lexer& mlilex} {mli::location_type& loc}


%locations
%initial-action
{
  @$ = loc; // Initialize the initial location.
};

%define parse.trace
%define parse.error verbose

%define api.value.type {mli::semantic_type}

%code requires {
  #include "MLI.hh"
  #include "database.hh"
  #include "basictype.hh"

  #include "location-type.hh"

  // #define YYERROR_VERBOSE 1

  #ifndef yyFlexLexer
    #define yyFlexLexer mliFlexLexer

    #include <FlexLexer.h>
  #endif


  namespace mli {

    class semantic_type {
    public:
      long number = 0;
      std::string text;
      mli::ref<mli::unit> object;

      semantic_type() {}
    };


    class directive_lexer : public yyFlexLexer {
    public:
      mli::semantic_type* yylvalp = nullptr;
      mli::location_type* yyllocp = nullptr;

      directive_lexer() {};

      directive_lexer(std::istream& is, std::ostream& os) : yyFlexLexer(&is, &os) {}

      int yylex(); // Defined in directive-lexer.cc.

      std::istream& in() { return yyin; }

      int operator()(mli::semantic_type* x) { yylvalp = x;  return yylex(); }
      int operator()(mli::semantic_type* x, mli::location_type* y) { yylvalp = x;  yyllocp = y;  return yylex(); }
    };

  } // namespace mli

} // %code requires


%code provides {

  namespace mli {

    // Symbol table: Pushed & popped at lexical environment boundaries.
    // For statements (theorems, definitions), pushed before the symbol declarations
    // (after the label), and if there is a proof, popped where it ends:

    using symbol_table_t = mli::table_stack<std::string, std::pair<mli::directive_parser::token_type, mli::ref<mli::unit>>>;

    extern symbol_table_t directive_symbol_table;


    extern directive_parser::token_type directive_bound_variable_type;

    constexpr directive_parser::token_type free_variable_context = directive_parser::token_type(0);

    directive_parser::token_type directive_define_variable(semantic_type& yylval);

    extern kleenean unused_variable;

  } // namespace mli

} // %code provides


%code {

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

  #include "precedence.hh"

  extern std::string infile_name;

  extern bool declaration_context;
  extern bool maybe_set_declaration_context;
  extern bool proofline_database_context;
  extern bool statement_substitution_context;
  extern int bracket_depth;

  extern mli::directive_parser::token_type declared_token;
  extern int declared_type;
  extern int current_token;


  namespace mli {

    kleenean the_directive_type = false;

    bool set_trace = false;
    trace_type trace_flag = trace_none;


    symbol_table_t directive_symbol_table;



    mli::directive_parser::token_type directive_to_token(variable::type t) {
      switch (t) {
#if USE_VARIABLE_META
        case variable::metaformula_:   return mli::directive_parser::token::metaformula_variable;
#endif
        case variable::formula_:       return mli::directive_parser::token::object_formula_variable;
        case variable::predicate_:     return mli::directive_parser::token::predicate_variable;
        case variable::atom_:          return mli::directive_parser::token::atom_variable;
        case variable::function_:      return mli::directive_parser::token::function_variable;
        case variable::object_:        return mli::directive_parser::token::object_variable;
        default:                       return mli::directive_parser::token::token_error;
      }
    }


    // For bound variable definitions, set to the token type that
    // should be inserted in the symbol table:
    directive_parser::token_type directive_bound_variable_type = directive_parser::token_type(0);



    directive_parser::token_type directive_define_variable(semantic_type& yylval) {
      if (statement_substitution_context) {
        statement_substitution_context = false;
        std::optional<std::pair<directive_parser::token_type, mli::ref<mli::unit>>> x = mli::directive_symbol_table.find_top(yylval.text);
        if (!x)  return mli::directive_parser::token::plain_name;
        yylval.object = x->second;
        yylval.number = x->first;
        return x->first;
      }

      if (declaration_context)
        return mli::directive_parser::token::plain_name;

      std::optional<std::pair<mli::directive_parser::token_type, mli::ref<mli::unit>>> x = mli::directive_symbol_table.find(yylval.text);


      if (!x) {
        // Not a bound variable case:
        if (directive_bound_variable_type == mli::free_variable_context)
          return mli::directive_parser::token::plain_name;

        // Bound variable case: Create a limited variable og bind 1, insert at the secondary
        // (bound variable) stack level.
        ref<variable> v;
        v->bind_ = 1;
        directive_symbol_table.insert(yylval.text, {directive_bound_variable_type, v});

        yylval.object = v;
        yylval.number = directive_bound_variable_type;

        return directive_bound_variable_type;
      }


      mli::variable* vp = mli::ref_cast<mli::variable*>(x->second);

      if (vp != nullptr
        && (vp->depth_ == -1 || directive_bound_variable_type != mli::free_variable_context)) {

        if (directive_bound_variable_type == mli::free_variable_context) {
          // Case definition of a free variable:

          // Check if it is a variable which is declared without definition, in which case make
          // a copy with right proof depth, insert it in the symbol table, and change x->second
          // so subsequently the new copy is used instead of the original lookup value.
          mli::ref<mli::variable> v(make, *vp);

          directive_symbol_table.insert_or_assign(yylval.text, {x->first, v});

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
            mli::ref<mli::variable> v(make, *vp);
            v->metatype_ = variable::limited_;
            v->bind_ = 1;

            directive_symbol_table.insert(yylval.text, {x->first, v});

            x->second = v;
          }
          else if (vp->depth_ == -1) {
            mli::ref<mli::variable> v(make, *vp);

            directive_symbol_table.insert_or_assign(yylval.text, {x->first, v});

            x->second = v;
          }

          yylval.object = x->second;
          yylval.number = x->first;

          return directive_bound_variable_type;
        }
      }

      yylval.object = x->second;
      yylval.number = x->first;

      return x->first;
    }

  } // namespace mli


} // %code


%token token_error "token error"


%token
  diagnostic_key "diagnostic"
  ignored_key "ignored"
  warning_key "warning"
  error_key "error"
;

%token unused_variable_key "unused variable"

%token
  unused_key "unused"
  variable_key "variable"
  type_key "type"
  label_key "label"
;


%token
  all_key   "all"
  none_key  "none"
  no_key    "no"
  use_key    "use"
;


%token
  count_key "count"
  max_key "max"
  level_key "level"
  sublevel_key "sublevel"
;


%token
  proof_key "proof"
  conditional_key "conditional"
  strict_key "strict"
;


%token
  logic_key "logic"
  false_elimination_key "-𝕗"
  false_introduction_key "+𝕗"
  negation_elimination_key "-¬"
  negation_elimination_in_premise_key "-¬⊢"
  double_negation_elimination_key "-¬¬"
  double_negation_elimination_in_premise_key "-¬¬⊢"
  double_negation_introduction_key "+¬¬"
  double_negation_introduction_in_premise_key "+¬¬⊢"
  implication_elimination_key "-⇒"
  implication_elimination_in_premise_key "-⇒⊢"
  conjunction_elimination_key "-∧"
  conjunction_elimination_in_premise_key "-∧⊢"
  disjunction_elimination_key "-∨"
  disjunction_elimination_in_premise_key "-∨⊢"
;

%token
  trace_key "trace"
  untrace_key "untrace"
;


// Write style tokens:
%token
  null_key  "null"
  empty_key "empty"
  result_key "result"
// proof_key  "proof": Defined above.
  solve_key  "solve"
  prooftree_key  "prooftree"
  unify_key  "unify"
  split_key "split"
  substitute_key "substitute"
  statement_key "statement"
  database_key "database"
  formula_key "formula"
  unspecializable_key "unspecializable"
  structure_key "structure"
  thread_key "thread"
// level_key "level": Defined above.
;


%token
  natural_number_value "natural number value"
  integer_value        "integer value"
;


%token include_key "include"
%token end_key "end"


/* Identifiers & labels: */
%token plain_name "name"

/* Metaconstants: */
%token metapredicate_constant "metapredicate constant"

/* Logic (object, non-term) constants: */
%token predicate_constant "predicate constant"
%token atom_constant "atom constant"

/* Terms constants: */
%token function_constant "function constant"
%token term_constant "term constant"

/* Metavariables: */

%token metaformula_variable "metaformula variable"
%token object_formula_variable "object formula variable"
%token predicate_variable "predicate variable"
%token atom_variable "atom variable"

%token prefix_formula_variable "prefix formula variable"

%token function_variable "function variable"
%token constant_variable "constant variable"

/* Object variables: */

%token object_variable "object variable"

/* Hoare logic code variable */
%token code_variable "code variable"


%token all_variable "all variable"
%token exist_variable "exist variable"
%token is_set_variable "Set variable"
%token set_variable "set variable"
%token set_variable_definition "set variable definition"
%token implicit_set_variable "implicit set variable"

/* Declarators: constants and variables. */
  /* Generic tokens, returned for any idenitified constant or variable.
     The exact type is then sorted out by the token type stored lookup table,
     and returned in the semantic value. */
%token identifier_constant_key "identifier constant"
%token identifier_variable_key "identifier variable"
  /* Keys for labeling identifiers constant or variable.
%token constant_key "constant"
%token variable_key "variable"
*/


/* Declarators: quantifiers. */

%token exist_key "∃"


/* Formula logic: */

%token logical_not_key "¬"
%token logical_and_key "∧"
%token logical_or_key "∨"
%token implies_key "⇒"
%token impliedby_key "⇐"
%token equivalent_key "⇔"

/* Prefix logic notation: */
%token prefix_not_key
%token prefix_and_key;
%token prefix_or_key;
%token prefix_implies_key
%token prefix_equivalent_key;


/* Formula functions: */

%token less_key "<"
%token greater_key ">"
%token less_or_equal_key "≤"
%token greater_or_equal_key "≥"

%token not_less_key "≮"
%token not_greater_key "≯"
%token not_less_or_equal_key "≰"
%token not_greater_or_equal_key "≱"

%token equal_key "="
%token not_equal_key "≠"

%token mapsto_key "↦"
%token degree_key "°"



%token factorial_key "!"

%token mult_key "⋅"
%token plus_key "+"
%token minus_key "-"

/* Set theory: */
%token is_set_key "Set"
%token power_set_key "Pow"

%token empty_set_key "∅"

%token in_key "∈"
%token not_in_key "∉"

%token set_complement_key "∁"
%token set_union_key "∪"
%token set_intersection_key "∩"
%token set_difference_key "∖"

/* Set unary prefix operators: */
%token set_union_operator_key "⋃"
%token set_intersection_operator_key "⋂"

%token subset_key "⊆"
%token proper_subset_key "⊊"
%token superset_key "⊇"
%token proper_superset_key "⊋"


/* Miscellaneous symbols: */

%token colon_key ":"
%token semicolon_key ";"
%token comma_key ","
%token period_key "."

%token left_parenthesis_key "("
%token right_parenthesis_key ")"
%token left_bracket_key "["
%token right_bracket_key "]"
%token left_angle_bracket_key "⟨"
%token right_angle_bracket_key "⟩"

%token superscript_left_parenthesis_key "⁽"
%token superscript_right_parenthesis_key "⁾"

%token subscript_left_parenthesis_key "₍"
%token subscript_right_parenthesis_key "₎"

%token left_brace_key "{"
%token vertical_line_key "|"
%token right_brace_key "}"

%token tilde_key "~"

%token slash_key "/"
%token backslash_key "\\"


/* Code keywords */
%token if_key "if"
%token then_key "then"
%token else_key "else"

%token while_key "while"
%token do_key "do"
%token loop_key "loop"
%token for_key "for"

%token break_key "break"
%token continue_key "continue"

%token throw_key "throw"
%token try_key "try"
%token catch_key "catch"



/* Precedence rules: Lower to higher; values used for writing.
   Sign negative <-> non-associative.
   Some precedences are formally unnecessary.
*/

  /* Metalogic. */
%nonassoc "⊩"
%left ";"

%nonassoc "⊣" "⊢"
%left ":"
%left "|"
%left ","
%right "~"

%nonassoc "free in" "free for" "in"
%right "not"

%nonassoc "≔" "≕" "≝"

%nonassoc "≡" "≢" "≣" "≣̷"

%left "⇔"
%nonassoc "⇒" "⇐"

%left "∨"
%left "∧"
%right "¬"

%right prefix_not_key prefix_and_key prefix_or_key prefix_implies_key prefix_equivalent_key

%left superscript_unsigned_integer_value


/* Equality/inequality. */

%left "=" "≠"
%left "<" ">" "≤" "≥"  "≮" "≯" "≰" "≱"


/* Set theory. */

%nonassoc "⊆" "⊊" "⊇" "⊋"

%nonassoc "∈" "∉"

%left "∪"
%left "∩" "∖"

%right "∁"
%right "⋃"
%right "⋂"




%left "!"

%left "+" "-"
%left "⋅" "/"
%right unary_minus


%%

file:
    %empty
  | file_contents {}
  | error {
      declaration_context = false;
      directive_bound_variable_type = free_variable_context;
      YYABORT;
    }
;


file_contents:
    file_contents command {}
  | command               {}
;


command:
    diagnostic_statement {}
  | trace_statement {}
  | proof_strictness {}
  | limits {}
  | logic_simplification {}
  | implicit_logic_simplification {}
;


diagnostic_statement:
    "diagnostic" diagnostic_type diagnostic { unused_variable = the_directive_type; }
;


diagnostic_type:
    "ignored" { the_directive_type = false; }
  | "warning" { the_directive_type = undefined; }
  | "error"   { the_directive_type = true; }
;


diagnostic:
  "unused" "variable"
;


trace_statement:
  trace_qualifier trace_type {
    if (set_trace)
      trace_value |= trace_flag;
    else
      trace_value &= ~trace_flag;
  }
;


trace_qualifier:
    "trace" { set_trace = true; }
  | "untrace" { set_trace = false; }
;


trace_type:
    "all" { trace_flag = trace_all; }
  | "null" { trace_flag = trace_null; }
  | "empty" { trace_flag = trace_empty; }
  | "result" { trace_flag = trace_result; }
  | "proof" { trace_flag = trace_proof; }
  | "solve" { trace_flag = trace_solve; }
  | "prooftree" { trace_flag = trace_prooftree; }
  | "unify" { trace_flag = trace_unify; }
  | "split" { trace_flag = trace_split; }
  | "substitute" { trace_flag = trace_substitute; }
  | "statement" { trace_flag = trace_statement; }
  | "database" { trace_flag = trace_database; }
  | "formula" "type" { trace_flag = trace_formula_type; }
  | "unspecializable" { trace_flag = trace_unspecializable; }
  | "variable" "type" { trace_flag = trace_variable_type; }
  | "variable" "label" { trace_flag = trace_variable_label; }
  | "structure" "type" { trace_flag = trace_structure_type; }
  | "thread" { trace_flag = trace_thread; }
  | "level" { trace_flag = trace_level; }
  | "logic" { trace_flag = trace_logic; }
;


proof_strictness:
    "strict" "proof"      { mli::strict_proof = true; }
  | "conditional" "proof" { mli::strict_proof = false; }
;


limits:
    "thread" "count" integer[k] { thread_count = (difference_type)ref_cast<integer&>($k.object); }
  | "level" "max" natural_number_value[k] { level_max = (size_type)ref_cast<integer&>($k.object); }
  | "sublevel" "max" natural_number_value[k] { sublevel_max = (size_type)ref_cast<integer&>($k.object); }
  | "proof" "count" natural_number_value[k] { proof_count = (size_type)ref_cast<integer&>($k.object); }
  | "unify" "count" "max" natural_number_value[k] { unify_count_max = (size_type)ref_cast<integer&>($k.object); }
;


logic_simplification:
     "no" "logic" "-𝕗"  { false_elimination = false; }
  |  "logic" "+𝕗"  { false_introduction = true; }
  |  "no" "logic" "-¬¬"  { double_negation_elimination = false; }
  |  "logic" "-¬¬"  { double_negation_elimination = true; }
  |  "no" "logic" "-¬¬⊢"  { double_negation_elimination_in_premise = false; }
  |  "logic" "-¬¬⊢"  { double_negation_elimination_in_premise = true; }
  |  "no" "logic" "+¬¬⊢"  { double_negation_introduction_in_premise = false; }
  |  "logic" "+¬¬⊢"  { double_negation_introduction_in_premise = true; }
  |  "no" "logic" "-⇒"   { implication_elimination = false; }
  |  "logic" "-⇒"   { implication_elimination = true; }
  |  "no" "logic" "-⇒⊢"   { implication_elimination_in_premise = false; }
  |  "logic" "-⇒⊢"   { implication_elimination_in_premise = true; }
  |  "no" "logic" "-∧"  { conjunction_elimination = false; }
  |  "logic" "-∧"  { conjunction_elimination = true; }
  |  "no" "logic" "-∧⊢"  { conjunction_elimination_in_premise = false; }
  |  "logic" "-∧⊢"  { conjunction_elimination_in_premise = true; }
  |  "no" "logic" "-∨"  { disjunction_elimination = false; }
  |  "logic" "-∨"  { disjunction_elimination = true; }
  |  "no" "logic" "-∨⊢"  { disjunction_elimination_in_premise = false; }
  |  "logic" "-∨⊢"  { disjunction_elimination_in_premise = true; }
;


implicit_logic_simplification:
  "logic" implicit_logic_simplification_sequence
;


implicit_logic_simplification_sequence:
    implicit_logic_simplification_item
  | implicit_logic_simplification_sequence "," implicit_logic_simplification_item
;


implicit_logic_simplification_item:
  logic_qualifier logic_type logic_name conclusion_or_premise
;


logic_qualifier:
  "no"
;


logic_type:
    "-"
  | "+"
;

logic_name:
  "-⇒⊢"
;


conclusion_or_premise:
  "-∨⊢"
;


integer:
    natural_number_value
  | integer_value
;



%%

#include <sstream>

  extern std::istream* current_istream;
  extern std::istream::pos_type line_position;

namespace mli {

  void directive_parser::error(const location_type& loc, const std::string& errstr) {
    diagnostic(loc, errstr, mlilex.in(), line_position);
  }


  int directive_read(std::istream& is, mli::location_type& loc) {
    mli::directive_lexer lex(is, std::cout);

    mli::directive_parser p(lex, loc);

    int r = p.parse();

    if (r != 0)
      is.setstate(std::ios::failbit);
    else
      is.clear(is.rdstate() & ~(std::ios::failbit | std::ios::badbit));

    return r;
  }

  int directive_read(const std::string& str, mli::location_type& loc) {
    std::stringstream iss(str);

    return directive_read(iss, loc);
  }

} // namespace mli

