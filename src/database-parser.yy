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

%skeleton "lalr1.cc"                          /*  -*- C++ -*- */
%require "3.8"
%defines

%define api.namespace {mli}
%define api.prefix {mli}
%define api.parser.class {database_parser}
%define api.location.type {location_t}

%parse-param {mli::theory_database& yypval} {mli::database_lexer& mlilex}

%define parse.lac full

%locations
%initial-action
{
  @$.initialize(&infile_name); // Initialize the initial location.
};

%define parse.trace
%define parse.error verbose

%define api.value.type variant

%code requires {
  #include "MLI.hh"
  #include "database.hh"
  #include "basictype.hh"
  #include "proposition.hh"

  #include "location-type.hh"


  // #define YYERROR_VERBOSE 1

  #ifndef yyFlexLexer
    #define yyFlexLexer mliFlexLexer

    #include <FlexLexer.h>
  #endif


  namespace mli {

    class database_lexer;

  } // namespace mli

} // %code requires


%code provides {
  namespace mli {
    class database_lexer : public yyFlexLexer {
    public:
      using semantic_value = database_parser::value_type;

      semantic_value* yylvalp = nullptr;
      location_type* yyllocp = nullptr;

      database_lexer() {};

      database_lexer(std::istream& is, std::ostream& os) : yyFlexLexer(&is, &os) {}

      int yylex(); // Defined in database-lexer.cc.

      std::istream& in() { return yyin; }

      int operator()(semantic_value* x) { yylvalp = x;  return yylex(); }
      int operator()(semantic_value* x, location_type* y) { yylvalp = x;  yyllocp = y;  return yylex(); }
    };


    // Symbol table: Pushed & popped at lexical environment boundaries.
    // For statements (theorems, definitions), pushed before the symbol declarations
    // (after the label), and if there is a proof, popped where it ends:

    using symbol_table_data = val<unit>;
    using symbol_table_value = std::pair<database_parser::token_type, symbol_table_data>;
    using symbol_table_t = table_stack<std::string, symbol_table_value>;

    extern symbol_table_t symbol_table;

    extern depth proof_depth;

    extern database_parser::token_type bound_variable_type;

    constexpr database_parser::token_type free_variable_context = database_parser::token_type(0);

    database_parser::token_type define_variable(const std::string& text, database_parser::value_type& yylval);

    extern kleenean unused_variable;

    int directive_read(std::istream& is, location_type& loc);
    int directive_read(const std::string& str, location_type&);

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


} // %code


%token token_error "token error"

%token include_key "include"
%token theory_key "theory"
%token end_key "end"

%token formal_system_key "formal system"

%token definition_key "definition"

%token postulate_key "postulate"
%token axiom_key "axiom"
%token rule_key "rule"
%token conjecture_key "conjecture"

%token <theorem::type> theorem_key "theorem"

%token proof_key "proof"
%token end_of_proof_key "∎"

%token by_key "by"

%token premise_key "premise"
%token <std::string> result_key "result"


/* Metalogic symbols: */

/* Symbols for metastatements */
%token metainfer_key "⊩"
%token metaor_key "or"
%token metaand_key "and"
%token metanot_key "not"

%token infer_key "⊢"

%token object_identical_key "≡"
%token object_not_identical_key "≢"
%token meta_identical_key "≣"
%token meta_not_identical_key "≣̷"

%token fail_key "fail"
%token succeed_key "succeed"

/* Metalogic */
%token free_for_key "free for"
%token metain_key "in"
%token free_in_key "free in"
%token use_key "use"

%token defined_by_key "≔"
%token defines_key "≕"
%token defined_equal_key "≝"


/* Identifiers & labels: */
%token <std::string> plain_name "name"
%token <std::string> label_key "label"

/* Metaconstants: */
%token <val<unit>> metapredicate_constant "metapredicate constant"

/* Functions */
%token <val<unit>> function_key "function"
%token <val<unit>> predicate_key "predicate"

/* Logic (object, non-term) constants: */
%token <val<unit>> predicate_constant "predicate constant"
%token <val<unit>> atom_constant "atom constant"

/* Terms constants: */
%token <val<unit>> function_constant "function constant"
%token <val<unit>> term_constant "term constant"

/* Metavariables: */

%token <val<unit>> metaformula_variable "metaformula variable"
%token <val<unit>> object_formula_variable "object formula variable"
%token <val<unit>> predicate_variable "predicate variable"
%token <val<unit>> atom_variable "atom variable"

%token <val<unit>> prefix_formula_variable "prefix formula variable"

%token <val<unit>> function_variable "function variable"


/* Object variables: */

%token <val<unit>> object_variable "object variable"

/* Hoare logic code variable */
%token <val<unit>> code_variable "code variable"


%token <val<unit>> all_variable "all variable"
%token <val<unit>> exist_variable "exist variable"

/* The function map variable is the 𝒙 in 𝒙 ↦ 𝑨. */
%token <val<unit>> function_map_variable "function map variable"

%token <val<unit>> is_set_variable "Set variable"
%token <val<unit>> set_variable "set variable"
%token <val<unit>> set_variable_definition "set variable definition"
%token <val<unit>> implicit_set_variable "implicit set variable"

/* Declarators: constants and variables. */
  /* Generic tokens, returned for any identified constant or variable.
     The exact type is then sorted out by the token type stored lookup table,
     and returned in the semantic value. */
%token identifier_constant_key "identifier constant"
%token identifier_variable_key "identifier variable"
%token identifier_function_key "identifier function"

  /* Keys for labeling identifiers constant or variable.
%token <val<unit>> constant_key "constant"
%token <val<unit>> variable_key "variable"
*/


/* Declarators: quantifiers. */

%token <std::string> all_key "∀"
%token <std::string> exist_key "∃"


/* Formula logic: */

%token <std::string> logical_not_key "¬"
%token <std::string> logical_and_key "∧"
%token <std::string> logical_or_key "∨"
%token <std::string> implies_key "⇒"
%token <std::string> impliedby_key "⇐"
%token <std::string> equivalent_key "⇔"

/* Prefix logic notation: */
%token prefix_not_key
%token prefix_and_key;
%token prefix_or_key;
%token prefix_implies_key
%token prefix_equivalent_key;


/* Formula functions: */

%token <std::string> natural_number_key "ℕ"

%token <std::string> less_key "<"
%token <std::string> greater_key ">"
%token <std::string> less_or_equal_key "≤"
%token <std::string> greater_or_equal_key "≥"

%token <std::string> not_less_key "≮"
%token <std::string> not_greater_key "≯"
%token <std::string> not_less_or_equal_key "≰"
%token <std::string> not_greater_or_equal_key "≱"

%token <std::string> equal_key "="
%token <std::string> not_equal_key "≠"

%token <std::string> divides_key "∣"
%token <std::string> not_divides_key "∤"

%token <std::string> mapsto_key "↦"
%token <std::string> Mapsto_key "⤇"

/* Boldface 𝛌 for function maps of the form 𝛌 𝒙 ↦ 𝑨 implicitly declaring 𝒙. */
%token function_map_prefix_key "𝛌"

%token degree_key "°"
%token bullet_key "•"

%token subscript_x_key "ₓ"

%token <std::pair<std::string, integer>> natural_number_value "natural number value"
%token <integer> integer_value "integer value"

%token <integer> subscript_natural_number_value "subscript natural number value"
%token <integer> subscript_integer_value "subscript integer value"

%token <integer> superscript_natural_number_value "superscript natural number value"
%token <integer> superscript_integer_value "superscript integer value"


%token <std::string> factorial_key "!"

%token <std::string> mult_key "⋅"
%token <std::string> plus_key "+"
%token <std::string> minus_key "-"

/* Set theory: */
%token is_set_key "Set"
%token power_set_key "Pow"

%token empty_set_key "∅"

%token <std::string> in_key "∈"
%token <std::string> not_in_key "∉"

%token <std::string> set_complement_key "∁"
%token <std::string> set_union_key "∪"
%token <std::string> set_intersection_key "∩"
%token <std::string> set_difference_key "∖"

/* Set unary prefix operators: */
%token <std::string> set_union_operator_key "⋃"
%token <std::string> set_intersection_operator_key "⋂"

%token <std::string> subset_key "⊆"
%token <std::string> proper_subset_key "⊊"
%token <std::string> superset_key "⊇"
%token <std::string> proper_superset_key "⊋"


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

%token <std::string> slash_key "/"
%token <std::string> backslash_key "\\"


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

%nterm file
%nterm file_contents
%nterm command
%nterm <ref6<unit>> metaformula_substitution_sequence
%nterm <ref6<unit>> substitution_for_metaformula
%nterm <ref6<unit>> metaformula_substitution
%nterm <ref6<unit>> formula_substitution_sequence
%nterm <ref6<unit>> substitution_for_formula
%nterm <ref6<unit>> formula_substitution
%nterm <ref6<unit>> term_substitution_sequence
%nterm <ref6<unit>> term_substitution
%nterm <ref6<unit>> predicate_function_application
%nterm <ref6<unit>> term_function_application
%nterm <ref6<unit>> theory
%nterm <std::pair<std::string, bool>> end_theory_name
%nterm <ref6<unit>> include_theories
%nterm <ref6<unit>> include_theory
%nterm <std::string> theory_name
%nterm <ref6<unit>> theory_body
%nterm <ref6<unit>> formal_system
%nterm <ref6<unit>> formal_system_body
%nterm <ref6<unit>> formal_system_body_item
%nterm <ref6<unit>> theory_body_list
%nterm <ref6<unit>> theory_body_item
%nterm <ref6<unit>> postulate
%nterm <ref6<unit>> conjecture
%nterm <val<definition>> definition_labelstatement
%nterm <std::string> statement_name
%nterm <ref6<unit>> theorem
%nterm <ref6<unit>> theorem_statement
%nterm <std::pair<theorem::type, std::string>> theorem_head
%nterm <ref6<unit>> proof
%nterm <ref6<unit>> compound-proof
%nterm <ref6<unit>> proof_head
%nterm <ref6<unit>> proof_lines
%nterm <std::string> statement_label
%nterm <ref6<unit>> proof_line
%nterm <std::string> subproof_statement
%nterm <ref6<unit>> proof_of_conclusion
%nterm <std::string> optional-result
%nterm <ref6<unit>> find_statement
%nterm <ref6<unit>> find_statement_list
%nterm <ref6<unit>> find_statement_sequence
%nterm <ref6<unit>> find_definition_sequence
%nterm <ref6<unit>> find_statement_item
%nterm <ref6<unit>> find_statement_name
%nterm <ref6<unit>> statement
%nterm <ref6<unit>> definition_statement
%nterm <ref6<unit>> identifier_declaration
%nterm <ref6<unit>> declarator_list
%nterm <ref6<unit>> declarator_identifier_list
%nterm <ref6<unit>> identifier_function_list
%nterm <ref6<unit>> identifier_function_name
/*
%nterm <ref6<unit>> constant_identifier_declaration
%nterm <ref6<unit>> constant_declarator_list
%nterm <ref6<unit>> constant_declarator_identifier_list
*/
%nterm <ref6<unit>> identifier_constant_list
%nterm <ref6<unit>> identifier_constant_name
%nterm <ref6<unit>> identifier_variable_list
%nterm <ref6<unit>> identifier_variable_name
%nterm <ref6<unit>> definition
%nterm <ref6<unit>> metaformula_definition
%nterm <ref6<unit>> object_formula_definition
%nterm <ref6<unit>> term_definition
%nterm <ref6<unit>> metaformula
%nterm <ref6<unit>> pure_metaformula
%nterm <ref6<unit>> optional_varied_variable_matrix
%nterm <ref6<unit>> varied_variable_conclusions
%nterm <ref6<unit>> varied_variable_conclusion
%nterm <ref6<unit>> varied_variable_premises
%nterm <ref6<unit>> varied_variable_premise
%nterm <ref6<unit>> varied_variable_set
%nterm <ref6<unit>> varied_variable
%nterm <ref6<unit>> optional_varied_in_reduction_variable_matrix
%nterm <ref6<unit>> varied_in_reduction_variable_conclusions
%nterm <ref6<unit>> varied_in_reduction_variable_conclusion
%nterm <ref6<unit>> varied_in_reduction_variable_premises
%nterm <ref6<unit>> varied_in_reduction_variable_premise
%nterm <ref6<unit>> varied_in_reduction_variable_set
%nterm <ref6<unit>> varied_in_reduction_variable
/*
%nterm <ref6<unit>> optional_varied_in_reduction_variable_sequence
*/
%nterm <ref6<unit>> simple_metaformula
%nterm <ref6<unit>> atomic_metaformula
%nterm <ref6<unit>> special_metaformula
%nterm <ref6<unit>> meta_object_free
%nterm <ref6<unit>> metapredicate
%nterm <ref6<unit>> metapredicate_function
%nterm <ref6<unit>> metapredicate_argument
%nterm <ref6<unit>> metapredicate_argument_body
%nterm <ref6<unit>> object_formula
%nterm <ref6<unit>> hoare_triple
/*
%nterm <ref6<unit>> code
*/
%nterm <ref6<unit>> code_statement
%nterm <ref6<unit>> code_sequence
%nterm <ref6<unit>> code_term
%nterm <ref6<unit>> very_simple_formula
%nterm <ref6<unit>> quantized_formula
%nterm <ref6<unit>> simple_formula
%nterm <ref6<unit>> quantized_body
%nterm <ref6<unit>> atomic_formula
%nterm <ref6<unit>> predicate
%nterm <ref6<unit>> predicate_expression
%nterm <ref6<unit>> predicate_identifier
%nterm <integer> optional_superscript_natural_number_value
/*
%nterm <ref6<unit>> optional_subscript_natural_number_value
*/
%nterm <ref6<unit>> logic_formula
%nterm <ref6<unit>> prefix_logic_formula
%nterm <ref6<unit>> quantizer_declaration
%nterm <ref6<unit>> quantized_variable_list
%nterm <ref6<unit>> all_variable_list
%nterm <ref6<unit>> exist_variable_list
%nterm <ref6<unit>> exclusion_set
%nterm <ref6<unit>> exclusion_list
%nterm <ref6<unit>> all_identifier_list
%nterm <ref6<unit>> exist_identifier_list
%nterm <ref6<unit>> optional_in_term
%nterm <ref6<unit>> tuple
%nterm <ref6<unit>> tuple_body
%nterm <ref6<unit>> term
%nterm <ref6<unit>> simple_term
%nterm <ref6<unit>> term_identifier
%nterm <ref6<unit>> variable_exclusion_set
%nterm <ref6<unit>> variable_exclusion_list
%nterm <ref6<unit>> bound_variable
%nterm <ref6<unit>> function_term
%nterm <ref6<unit>> set_term
%nterm <ref6<unit>> implicit_set_identifier_list
%nterm <ref6<unit>> set_member_list
%nterm <ref6<unit>> function_term_identifier


/* Precedence rules: Lower to higher; values used for writing.
   Sign negative <-> non-associative.
   Some precedences are formally unnecessary.
*/

  /* Metalogic. */
%nonassoc "⊩"
%left ";"

%left "⊣" "⊢"
%left ":"
%left "|"
%left ","
%right "~"

%nonassoc "free in" "free for" "in"
%right "not"

%nonassoc "≔" "≕" "≝"

%nonassoc "≡" "≢" "≣" "≣̷"

%left "⇔"
%left "⇐"
%right "⇒"

%left "∨"
%left "∧"
%right "¬"

%right prefix_not_key prefix_and_key prefix_or_key prefix_implies_key prefix_equivalent_key

%left subscript_natural_number_value
%left superscript_natural_number_value


/* Equality/inequality. */

%left "=" "≠"
%left "<" ">" "≤" "≥"  "≮" "≯" "≰" "≱"

%left "∣" "∤"


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
    %empty {}
  | file_contents {}
  | error {
      declaration_context = false;
      bound_variable_type = free_variable_context;
      YYABORT;
    }
;


file_contents:
    file_contents command {}
  | command               {}
;


command:
    { symbol_table.clear(); } theory {}
;


metaformula_substitution_sequence:
    substitution_for_metaformula[x] { $$ = $x; }
  | metaformula_substitution_sequence[x] substitution_for_metaformula[y] {
      $$ =  val<substitution>($x) * val<substitution>($y);
    }
;


substitution_for_metaformula:
    metaformula_substitution[x] { $$ = $x; }
  | formula_substitution[x] { $$ = $x; }
  | term_substitution[x] { $$ = $x; }
;


metaformula_substitution:
    "[" metaformula_variable[x] "⤇" metaformula[y] "]" {
      val<variable> v($x);
      val<formula> f($y);
      $$ = val<explicit_substitution>(make, v, f);
    }
;


formula_substitution_sequence:
    substitution_for_formula[x] { $$ = $x; }
  | formula_substitution_sequence[x] substitution_for_formula[y] {
      $$ = val<substitution>($x) * val<substitution>($y);
    }
;


substitution_for_formula:
    formula_substitution[x] { $$ = $x; }
  | term_substitution[x] { $$ = $x; }
;


formula_substitution:
    "[" object_formula_variable[x] "⤇" object_formula[y] "]" {
      val<variable> v($x);
      val<formula> f($y);
      $$ = val<explicit_substitution>(make, v, f);
    }
  | "[" predicate_variable[x] "⤇" predicate[y] "]" {
      val<variable> v($x);
      val<formula> f($y);
      $$ = val<explicit_substitution>(make, v, f);
    }
  | "[" atom_variable[x] "⤇" atom_constant[y] "]" {
      val<variable> v($x);
      val<formula> f($y);
      $$ = val<explicit_substitution>(make, v, f);
    }
;


term_substitution_sequence:
    term_substitution[x] { $$ = $x; }
  | term_substitution_sequence[x] term_substitution[y] {
      $$ = val<substitution>($x) * val<substitution>($y);
    }
;


term_substitution:
    "[" term_identifier[x] "⤇" term[y] "]" {
      val<variable> v($x);
      val<formula> f($y);
      $$ = val<explicit_substitution>(make, v, f);
    }
;


predicate_function_application:
    "(" object_variable[x] "↦" object_formula[f] ")" tuple[a] {
      $$ = val<function_application>(make, val<function_map>(make, $x, $f), $a);
    }
  | "(" "𝛌" function_map_variable[x] "↦" object_formula[f] { symbol_table.pop_level(); } ")" tuple[a] {
      $$ = val<function_application>(make, val<function_map>(make, $x, $f), $a);
    }
  | predicate_key[p] tuple[a] { $$ = val<function_application>(make, $p, $a); }
;


term_function_application:
    "(" object_variable[x] "↦" term[f] ")" tuple[a] {
      $$ = val<function_application>(make, val<function_map>(make, $x, $f), $a);
    }
  | "(" "𝛌" function_map_variable[x] "↦" term[f] { symbol_table.pop_level(); } ")" tuple[a] {
      $$ = val<function_application>(make, val<function_map>(make, $x, $f), $a);
    }
  | function_key[p] tuple[a] { $$ = val<function_application>(make, $p, $a); }
;


theory:
    "theory" statement_name[x]
    "." { theory_ = ref1<theory>(make, $x);
          yypval.insert(theory_);
          symbol_table.push_level();
    }
    include_theories
    theory_body
    "end" "theory" end_theory_name[y] "." {
      if ($y.second && $x != $y.first) {
        database_parser::error(@y, "warning: Name mismatch, theory " + $x
          + ", end theory " + $y.first + ".");
      }

      symbol_table.pop_level();
    }
;


end_theory_name:
    %empty             { $$ = std::make_pair(std::string{}, false); }
  | statement_name[x]  { $$ = std::make_pair($x, true); }
;


include_theories:
    %empty {}
  | include_theories include_theory {}
;

include_theory:
   "include" "theory" theory_name[x] "." {
      std::optional<ref1<theory>> th = yypval.find($x);

      if (!th)
        throw syntax_error(@x, "Include theory " + $x + " not found.");

      theory_->insert(*th);
    }
;


theory_name:
    "name"[x]   { $$ = $x; }
  | "label"[x]  { $$ = $x; }
;


theory_body:
    theory_body_list {}
  | formal_system theory_body_list {}
;


formal_system:
    "formal system" "."
    { symbol_table.push_level(); }
    formal_system_body
    "end" "formal system" "." { symbol_table.pop_level(); }
;


formal_system_body:
    %empty {}
  | formal_system_body formal_system_body_item {}
;


formal_system_body_item:
    identifier_declaration {}
  | postulate[x] { theory_->insert(ref4<statement>($x)); }
  | definition_labelstatement[x] { theory_->insert(ref4<statement>($x)); }
;


theory_body_list:
    %empty {}
  | theory_body_list theory_body_item {}
;


/* Postulates are not included here, as metatheorems such as the
   deduction theorem cannot then be localized to the same namespace:
   Such metatheorems are only true with respect to a fixed set of
   postulates, so if more postulates are added after the metatheorem,
   it becomes not true with respect to all postulates in the theory. */
theory_body_item:
    theorem[x] { theory_->insert(ref4<statement>($x)); }
  | identifier_declaration {}
  | conjecture[x] { theory_->insert(ref4<statement>($x)); }
/*| constant_identifier_declaration {} */
  | definition_labelstatement[x] { theory_->insert(ref4<statement>($x)); }
;


postulate:
    "postulate" statement_name[x]
    "." { symbol_table.push_level(); }
    statement[y] "." {
      symbol_table.pop_level();
      $$ = val<supposition>(make, supposition::postulate_, $x, $y, true);
    }
  | conjecture
  | "axiom" statement_name[x]
    "." { symbol_table.push_level(); }
    statement[y] "." {
      symbol_table.pop_level();

      val<formula> f($y);

      if (!f->is_axiom())
        throw syntax_error(@y, "Axiom statement not an object formula.");

      $$ = val<supposition>(make, supposition::postulate_, $x, f);
    }
  | "rule" statement_name[x]
    "." { symbol_table.push_level(); }
    statement[y] "." {
      symbol_table.pop_level();

      val<formula> f($y);

      if (!f->is_rule())
        throw syntax_error(@y, "Rule statement not an inference.");

      $$ = val<supposition>(make, supposition::postulate_, $x, f);
    }
;


conjecture:
    "conjecture" statement_name[x]
    "." { symbol_table.push_level(); }
    statement[y] "." {
      symbol_table.pop_level();
      $$ = val<supposition>(make, supposition::conjecture_, $x, $y, true);
    }
;

definition_labelstatement:
    "definition" statement_name[x]
    "." { symbol_table.push_level(); }
    definition_statement[y] "." {
      symbol_table.pop_level();
      $$ = val<definition>(make, $x, $y);
    }
;


statement_name:
    "name"[x] { $$ = $x; }
  | "label"[x] { $$ = $x; }
  | "natural number value"[x] { $$ = $x.first; }
;


theorem:
    theorem_statement proof {
      $$ = statement_stack_.back();
      ref4<statement> t($$); // The theorem.
      t->prove(proof_count);     // Attempt to prove the theorem.
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
;


theorem_statement:
    theorem_head[x] statement[y] {
      symbol_table_t::table& top = symbol_table.top();
      val<theorem> tr(make,  $x.first, $x.second, $y, theory_, proof_depth);
      statement_stack_.back() = tr;
      theorem_theory_ = tr->get_theory();
    }
;


theorem_head:
    "theorem"[x] statement_name[y] "." {
      $$.second = $y;
      $$.first = $x;
      symbol_table.push_level();
      statement_stack_.push_back(ref4<statement>());
    }
;


proof:
    compound-proof
  | <ref6<unit>>{
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
    proof_of_conclusion {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
;


compound-proof:
    proof_head proof_lines "∎" {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
  | "∎" {}
;


proof_head:
    "proof" {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
;


proof_lines:
    %empty {}
  | proof_lines proof_line {}
;


statement_label:
    statement_name[x] "." {
      $$ = $x;
      symbol_table.push_level();
    }
;


proof_line:
    statement_label[x] statement[y] "by" find_statement[z] "." {
      // Handles explicit find_statement substitutions A[x⤇e].
      proofline_database_context = false;

      theorem& t = dyn_cast<theorem&>(statement_stack_.back());

      bool concluding = false;

      if (t.get_formula() == $y || head(t) == $y)
        concluding = true;

      if (!concluding && $x == "conclusion")
        throw syntax_error(@x, "Proof line name “conclusion” used when not the theorem conclusion.");

      if (!concluding && $x == "result")
        throw syntax_error(@x, "Proof line name “result” used when not the theorem result.");

      ref4<statement> proof_line =
        t.push_back(
          $x, val<formula>($y), val<database>($z), concluding, proof_depth);

      symbol_table.pop_level();

      if (!proofline_stack_.insert($x, proof_line)) {
        if ($x.empty())
          throw syntax_error(@x, "Proof line empty name “” used.");
        else
          throw syntax_error(@x, "Proof line name " + $x  + " already given to a proof line.");
      }
    }

  | subproof_statement[x] compound-proof {
    ref4<statement> top = statement_stack_.back();
    symbol_table.pop_level();
    statement_stack_.pop_back();

    theorem& t = dyn_cast<theorem&>(statement_stack_.back());
      ref4<statement> proof_line = t.push_back(ref4<statement>(top));
      if (!proofline_stack_.insert($x, proof_line)) {
        if ($x.empty())
          throw syntax_error(@x, "Proof line empty name “” used.");
        else
          throw syntax_error(@x, "Proof line name " + $x  + " already given to a proof line.");
      }
    }

  | {} identifier_declaration {}
/* | { proof_depth0 = proof_depth; proof_depth = -1; } identifier_declaration { proof_depth = proof_depth0; } */

/*| constant_identifier_declaration {} */
  | definition_labelstatement[x] {
      theorem& t = dyn_cast<theorem&>(statement_stack_.back());
      ref4<statement> proof_line = t.push_back(ref4<statement>($x));

      if (!proofline_stack_.insert(proof_line->name_, proof_line)) {
        if (proof_line->name_.empty())
          throw syntax_error(@x, "Proof line name “” used.");
        else
          throw syntax_error(@x, "Proof line name " + proof_line->name_  + " already given to a proof line.");
      }
    }
  | proof_of_conclusion {}
;


subproof_statement:
    statement_label[x] statement[y] {
      $$ = $x;
      symbol_table_t::table& top = symbol_table.top();
      val<theorem> tp(make, theorem::claim_, $x, $y, theory_, proof_depth);
      statement_stack_.push_back(tp);
    }
;


proof_of_conclusion:
    optional-result[x] "by" find_statement[y] "." {
      proofline_database_context = false;

      theorem& t = dyn_cast<theorem&>(statement_stack_.back());
      ref4<statement> proof_line =
        t.push_back($x, t.get_formula(), val<database>($y), true, proof_depth);
    }
;


optional-result:
    %empty        { $$ = "result"; }
  | "result"[x]   { $$ = $x; }
;


find_statement:
    find_statement_list[x] { $$ = ref5<level_database>(make, val<database>($x)); }
  | find_statement[x] ":" find_statement_list[y] {
      ref5<level_database>($x)->push_back(val<database>($y));
      $$ = $x;
    }
;


find_statement_list:
    find_statement_sequence[x] {
      $$ = ref3<sublevel_database>(make, ref2<sequence_database>($x));
    }
  | find_statement_list[x] ";" find_statement_sequence[y] {
      ref3<sublevel_database>($x)->push_back(val<database>($y));
      $$ = $x;
    }
;


find_statement_sequence:
    %empty        { $$ = ref2<sequence_database>(make); }
  | find_statement_item[x] {
      $$ = ref2<sequence_database>(make, ref4<statement>($x)); }
  | find_statement_item[x] "₍" find_definition_sequence[y] "₎" {
      $$ = ref2<sequence_database>(make, ref4<statement>($x));
      ref2<sequence_database>($$)->insert(ref2<sequence_database>($y));
    }
  | find_statement_sequence[x] "," find_statement_item[y] {
      ref2<sequence_database>($x)->insert(ref4<statement>($y));
      $$ = $x;
    }
  | find_statement_sequence[x] "," find_statement_item[y] "₍" find_definition_sequence[z] "₎" {
      $$ = $x;
      ref2<sequence_database>($$)->insert(ref4<statement>($y));
      ref2<sequence_database>($$)->insert(ref2<sequence_database>($z));
    }
;


find_definition_sequence:
    find_statement_item[x] {
      $$ = ref2<sequence_database>(make, ref4<statement>($x)); }
  | find_definition_sequence[x] "," find_statement_item[y] {
      ref2<sequence_database>($x)->insert(ref4<statement>($y));
      $$ = $x;
    }
;


find_statement_item:
    find_statement_name[x] {
      $$ = $x;
    }
  | "premise" {
      $$ = val<premise>(make, statement_stack_.back());
    }
  | "premise" statement_name[x] {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == $x) {
          $$ = val<premise>(make, *i);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(@x, "Proof line premise " + $x  + " not found.");
    }
  | "premise" statement_name[x] subscript_natural_number_value[k] {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == $x) {
          size_type k = (size_type)$k;
          $$ = val<premise>(make, *i, k);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(@x, "Proof line premise " + $x  + " not found.");
    }
  | "premise" "⊢" {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      $$ = val<premise>(make);
    }
  | "premise" "⊢" subscript_natural_number_value[k] {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      size_type k = (size_type)$k;
      $$ = val<premise>(make, k);
    }
;


find_statement_name:
    statement_name[x] {
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref4<statement>> st;
      st = proofline_stack_.find($x);

      if (!st)
        st = theorem_theory_->find($x, 0);

      if (!st)
        throw syntax_error(@x,
          "statement name " + $x + " not found earlier in proof, in premises or theory.");

      $$ = *st;
    }
  | statement_name[x] <ref6<unit>>{
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref4<statement>> st;
      st = proofline_stack_.find($x);
      if (!st)
        st = theorem_theory_->find($x, 0);

      if (!st)
        throw syntax_error(@x,
          "statement name " + $x + " not found earlier in proof, in premises or theory.");

      $$ = *st;
      // Find the variables of *st and record them for use in the substitution domain checks:
      ref4<statement> pr = *st;
      statement_variables_.clear();
      pr->declared(statement_variables_);
      // Then push the declared *st variables & constants onto symbol_table
      // making them usable in substitution codomains:
      symbol_table.push_level();
      for (auto& i: statement_variables_)
        symbol_table.insert(i->name, {to_token(i->type_), i});
    }[y] // End of grammar mid-rule action.

    metaformula_substitution_sequence[z] {
      // The try-catch checks whether the statement-substitution is legal:
      ref4<statement> p($y);
      val<substitution> s($z);
      try {
        $$ = val<statement_substitution>(make, p, s);
      } catch (illegal_substitution&) {
        database_parser::error(@z, "Proposition substitute error.");
        p->write(std::cerr,
          write_style(write_name | write_type | write_statement));
        std::cerr << "\n  " << s << std::endl;
        YYERROR;        
      }
      symbol_table.pop_level();
    }
;


statement:
    metaformula[x] { $$ = dyn_cast<formula&>($x).set_bind(); }
  | identifier_declaration metaformula[x] {
      val<formula> f($x);
      $$ = f->set_bind();

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
          database_parser::error(@x, "warning: " + ds);
        else
          throw syntax_error(@x, ds);
        }
      }
    }
;


definition_statement:
    definition[x] { $$ = dyn_cast<formula&>($x).set_bind(); }
  | identifier_declaration definition[x] {
      $$ = dyn_cast<formula&>($x).set_bind();
    }
;


identifier_declaration:
    declarator_list "." {}
;


declarator_list:
    declarator_identifier_list {}
  | declarator_list declarator_identifier_list {}
;


declarator_identifier_list: /* Declarator followed by an identifier list. */
    identifier_constant_key identifier_constant_list {}
  | identifier_variable_key identifier_variable_list {}
  | identifier_function_key identifier_function_list {}
;


identifier_function_list:
    identifier_function_name {}
  | identifier_function_list "," identifier_function_name {}
;


/* When the object_formula is read, token lookahead may change the declared_token value
  if followed by another declaration, so therefore the current declared_token value is
  saved in a mid-action before this occurs.
  Also, the token ":" sets declaration_context to false, enabling the following formula
  to be read.
*/
identifier_function_name:
    "name"[x] { current_declared_token = declared_token; }
    ":" { bound_variable_type = database_parser::token::function_map_variable; }
    function_map_variable[y] "↦" object_formula[f] {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top($x);
      if (x0) {
        throw syntax_error(@x, "Name " + $x + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x, {current_declared_token,
        val<function_map>(make, $y, $f)});
    }
;

/*
constant_identifier_declaration:
    constant_declarator_list "." {}
;


constant_declarator_list:
    constant_declarator_identifier_list {}
  | constant_declarator_list constant_declarator_identifier_list {}
;


// Constant declarator followed by a constant identifier list.
constant_declarator_identifier_list:
    identifier_constant_key identifier_constant_list {}
;
*/


identifier_constant_list:
    identifier_constant_name {}
  | identifier_constant_list "," identifier_constant_name {}
;


identifier_constant_name:
    "name"[x] {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top($x);
      if (x0) {
        throw syntax_error(@x, "Name " + $x + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x, {declared_token,
        val<constant>(make, $x, constant::type(declared_type))});
    }
;


identifier_variable_list:
    identifier_variable_name {}
  | identifier_variable_list "," identifier_variable_name {}
;


identifier_variable_name:
    "name"[x] {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top($x);
      if (x0) {
        throw syntax_error(@x, "Name " + $x + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x, {declared_token,
       val<variable>(make, $x, variable::ordinary_, variable::type(declared_type), -1)});
    }
  | "°" "name"[x] {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top($x);
      if (x0) {
        throw syntax_error(@x, "Name " + $x + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x, {declared_token,
        val<variable>(make, $x, variable::limited_, variable::type(declared_type), -1)});
    }
  | "•" "name"[x] {
      // Check if name already has top level definition:
      std::optional<symbol_table_value> x0 = symbol_table.find_top($x);
      if (x0) {
        throw syntax_error(@x, "Name " + $x + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x, {declared_token,
        val<variable>(make, $x, variable::term_, variable::type(declared_type), -1)});
    }
;


definition:
    metaformula_definition[x] { $$ = $x; }
  | object_formula_definition[x] { $$ = $x; }
  | term_definition[x] { $$ = $x; }
;


metaformula_definition:
    pure_metaformula[x] "≔" pure_metaformula[y] {
      $$ = val<abbreviation>(make, val<formula>($x), val<formula>($y), val<formula>(),
        formula::logic, formula_definition_oprec);
    }
  | pure_metaformula[x] "≕" pure_metaformula[y] {
      $$ = val<abbreviation>(make, val<formula>($y), val<formula>($x), val<formula>(),
       formula::logic, formula_definition_oprec);
  }
/*
  | metaformula[x] "⊢" metaformula[y] "≔" metaformula[z] {
      $$ = val<abbreviation>(make, val<formula>($y), val<formula>($z), val<formula>($x),
        object_formula_type_, formula_definition_oprec); }
*/
;


object_formula_definition:
    object_formula[x] "≔" object_formula[y] {
      $$ = val<abbreviation>(make, val<formula>($x), val<formula>($y), val<formula>(),
        formula::logic, formula_definition_oprec);
    }
  | object_formula[x] "≕" object_formula[y] {
      $$ = val<abbreviation>(make, val<formula>($y), val<formula>($x), val<formula>(),
        formula::logic, formula_definition_oprec);
  }
/*
  | metaformula[x] "⊢" object_formula[y] "≔" object_formula[z] {
      $$ = val<abbreviation>(make, val<formula>($y), val<formula>($z), val<formula>($x),
        object_formula_type_, formula_definition_oprec); }
*/
;


term_definition:
    term[x] "≔" term[y] {
      $$ = val<abbreviation>(make, val<formula>($x), val<formula>($y), val<formula>(),
        formula::object, term_definition_oprec);
    }
/*
  // Causes conflicts with the general "⊢" rules.
  | metaformula[x] "⊢" term[y] "≔" term[z] {
      $$ = val<abbreviation>(make, val<formula>($y), val<formula>($z), val<formula>($x),
        term_type_, term_definition_oprec); }
*/
  | term[x] "≕" term[y] {
      $$ = val<abbreviation>(make, val<formula>($y), val<formula>($x), val<formula>(),
        formula::object, term_definition_oprec);
  }
;


metaformula:
    pure_metaformula[x] { $$ = $x; }
  | object_formula[x] { $$ = $x; }
;


pure_metaformula:
    atomic_metaformula[x] { $$ = $x; }
  | special_metaformula[x] { $$ = $x; }
  | "~" metaformula[x] {
      $$ = val<metanot>(make, val<formula>($x));
    }
  | metaformula[x] ";" metaformula[y] {
      $$ = concatenate(val<formula>($x), val<formula>($y));
    }
  | metaformula[x] "," metaformula[y] {
      $$ = concatenate(val<formula>($x), val<formula>($y));
    }
  | metaformula[x] "⊩" optional_superscript_natural_number_value[k]
      optional_varied_variable_matrix[m] optional_varied_in_reduction_variable_matrix[mr]
      metaformula[y] {
      size_type k = (size_type)$k;

      if (k < 1)
        k = 2;
      else
        k += 2;

      val<inference> i(make, val<formula>($y), val<formula>($x), metalevel_t(k));

      inference* mp = dyn_cast<inference*>($m);
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = dyn_cast<inference*>($mr);
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
          throw syntax_error(@m,
            "inference varied variable conclusion index " + std::to_string(vc_max)
            + " must be less than the number of conclusions " + std::to_string(n_head) + ".");

        if (vp_max >= n_body)
          throw syntax_error(@m,
            "inference varied variable premise index " + std::to_string(vp_max)
            + " must be less than the number of premises " + std::to_string(n_body) + ".");
      }

      $$ = i;
    }
/*
  | metaformula[x] "⊢" superscript_natural_number_value[k] metaformula[y] {
      size_type k = (size_type)$k;

      if (k < 1)
        throw syntax_error(@x,
          "inference ⊢" + $k + ": metalevel " + std::to_string(k) + " < 1.");

      $$ =
        val<inference>(make, val<formula>($y), val<formula>($x), metalevel_t(k));
    }
*/
  | metaformula[x] "⊢" optional_superscript_natural_number_value[k]
      optional_varied_variable_matrix[m] optional_varied_in_reduction_variable_matrix[mr]
      metaformula[y] {
      size_type k = (size_type)$k;

      if (k < 1)
        k = 1;

      val<inference> i(make, val<formula>($y), val<formula>($x), metalevel_t(k));

      inference* mp = dyn_cast<inference*>($m);
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = dyn_cast<inference*>($mr);
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
          throw syntax_error(@m,
            "inference varied variable conclusion index " + std::to_string(vc_max)
            + " must be less than the number of conclusions " + std::to_string(n_head) + ".");

        if (vp_max >= n_body)
          throw syntax_error(@m,
            "inference varied variable premise index " + std::to_string(vp_max)
            + " must be less than the number of premises " + std::to_string(n_body) + ".");
      }

      $$ = i;
    }
/*
  | metaformula[x] "⊢" metaformula[y] {
      val<inference> i(make, val<formula>($y), val<formula>($x), 1_ml);

      $$ = i;
    }
*/
  | "⊢" metaformula[x] { $$ = val<inference>(make, val<formula>($x)); }

  | "(" pure_metaformula[x] ")" { $$ = $x; }
  | simple_metaformula[x] metaformula_substitution_sequence[y] {
      $$ = val<substitution_formula>(make, val<substitution>($y), val<formula>($x)); }
;


optional_varied_variable_matrix:
    %empty {}
  | "⁽" varied_variable_conclusions[cs] "⁾" { $$ = $cs; }
  | "⁽" varied_variable_premises[ps] "⁾"    { $$ = $ps; }
  | "⁽" varied_variable_set[vs] "⁾"         { $$ = $vs; }
;

varied_variable_conclusions:
    varied_variable_conclusion
  | varied_variable_conclusions[xs] ";" varied_variable_conclusion[x] {
      inference& xs = dyn_cast<inference&>($xs);
      inference& x = dyn_cast<inference&>($x);

      for (auto& i: x.varied_)
        for (auto& j: i.second)
          xs.varied_[i.first][j.first].insert(j.second.begin(), j.second.end());

      $$ = $xs;
    }
;

varied_variable_conclusion:
    superscript_natural_number_value[k] varied_variable_premises[xs] {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>($xs);
      size_type k = (size_type)$k;

      i->varied_[k].insert(xs.varied_[0].begin(), xs.varied_[0].end());
      $$ = i;

    }
;

varied_variable_premises:
    varied_variable_premise
  | varied_variable_premises[xs] "," varied_variable_premise[x] {
      inference& xs = dyn_cast<inference&>($xs);
      inference& x = dyn_cast<inference&>($x);

      for (auto& j: x.varied_[0])
        xs.varied_[0][j.first].insert(j.second.begin(), j.second.end());

      $$ = $xs;
    }
;

varied_variable_premise:
    superscript_natural_number_value[k] varied_variable_set[xs] {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>($xs);
      size_type k = (size_type)$k;

      i->varied_[0][k].insert(xs.varied_[0][0].begin(), xs.varied_[0][0].end());

      $$ = i;
    }
;

varied_variable_set:
    varied_variable
  | varied_variable_set[xs] varied_variable[x] {
      inference& xs = dyn_cast<inference&>($xs);
      inference& x = dyn_cast<inference&>($x);

      xs.varied_[0][0].insert(x.varied_[0][0].begin(), x.varied_[0][0].end());

      $$ = $xs;
    }
;

varied_variable:
    object_variable[x] {
      val<inference> i(make);
      i->varied_[0][0].insert($x);
      $$ = i;
    }
  | metaformula_variable[x] {
      val<inference> i(make);
      i->varied_[0][0].insert($x);
      $$ = i;
    }
;



optional_varied_in_reduction_variable_matrix:
    %empty {}
  | "₍" varied_in_reduction_variable_conclusions[cs] "₎" { $$ = $cs; }
  | "₍" varied_in_reduction_variable_premises[ps] "₎"    { $$ = $ps; }
  | "₍" varied_in_reduction_variable_set[vs] "₎"         { $$ = $vs; }
;

varied_in_reduction_variable_conclusions:
    varied_in_reduction_variable_conclusion
  | varied_in_reduction_variable_conclusions[xs] ";" varied_in_reduction_variable_conclusion[x] {
      inference& xs = dyn_cast<inference&>($xs);
      inference& x = dyn_cast<inference&>($x);

      for (auto& i: x.varied_in_reduction_)
        for (auto& j: i.second)
          xs.varied_in_reduction_[i.first][j.first].insert(j.second.begin(), j.second.end());

      $$ = $xs;
    }
;

varied_in_reduction_variable_conclusion:
    subscript_natural_number_value[k] varied_in_reduction_variable_premises[xs] {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>($xs);
      size_type k = (size_type)$k;

      i->varied_in_reduction_[k].insert(xs.varied_in_reduction_[0].begin(), xs.varied_in_reduction_[0].end());
      $$ = i;

    }
;

varied_in_reduction_variable_premises:
    varied_in_reduction_variable_premise
  | varied_in_reduction_variable_premises[xs] "," varied_in_reduction_variable_premise[x] {
      inference& xs = dyn_cast<inference&>($xs);
      inference& x = dyn_cast<inference&>($x);

      for (auto& j: x.varied_in_reduction_[0])
        xs.varied_in_reduction_[0][j.first].insert(j.second.begin(), j.second.end());

      $$ = $xs;
    }
;

varied_in_reduction_variable_premise:
    subscript_natural_number_value[k] varied_in_reduction_variable_set[xs] {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>($xs);
      size_type k = (size_type)$k;

      i->varied_in_reduction_[0][k].insert(xs.varied_in_reduction_[0][0].begin(), xs.varied_in_reduction_[0][0].end());

      $$ = i;
    }
;

varied_in_reduction_variable_set:
    varied_in_reduction_variable
  | varied_in_reduction_variable_set[xs] varied_in_reduction_variable[x] {
      inference& xs = dyn_cast<inference&>($xs);
      inference& x = dyn_cast<inference&>($x);

      xs.varied_in_reduction_[0][0].insert(x.varied_in_reduction_[0][0].begin(), x.varied_in_reduction_[0][0].end());

      $$ = $xs;
    }
;

varied_in_reduction_variable:
    object_variable[x] {
      val<inference> i(make);
      i->varied_in_reduction_[0][0].insert($x);
      $$ = i;
    }
  | metaformula_variable[x] {
      val<inference> i(make);
      i->varied_in_reduction_[0][0].insert($x);
      $$ = i;
    }
;


/*
optional_varied_in_reduction_variable_sequence:
    %empty
  | "₍" varied_in_reduction_variable_conclusions[ps] "₎"    { $$ = $ps; }
  | "₍" varied_in_reduction_variable_set[vs] "₎"         { $$ = $vs; }
;

varied_in_reduction_variable_conclusions:
    varied_in_reduction_variable_conclusion
  | varied_in_reduction_variable_conclusion[xs] "," varied_in_reduction_variable_conclusion[x] {
      inference& xs = dyn_cast<inference&>($xs);
      inference& x = dyn_cast<inference&>($x);

      for (auto& j: x.varied_in_reduction_)
        xs.varied_in_reduction_[j.first].insert(j.second.begin(), j.second.end());

      $$ = $xs;
    }
;

varied_in_reduction_variable_conclusion:
    subscript_natural_number_value[k] varied_in_reduction_variable_set[xs] {
      val<inference> i(make);
      inference& xs = dyn_cast<inference&>($xs);
      size_type k = (size_type)$k;

      i->varied_in_reduction_[k].insert(xs.varied_in_reduction_[0].begin(), xs.varied_in_reduction_[0].end());

      $$ = i;
    }
;

varied_in_reduction_variable_set:
    varied_in_reduction_variable
  | varied_in_reduction_variable_set[xs] varied_in_reduction_variable[x] {
      inference& xs = dyn_cast<inference&>($xs);
      inference& x = dyn_cast<inference&>($x);

      xs.varied_in_reduction_[0].insert(x.varied_in_reduction_[0].begin(), x.varied_in_reduction_[0].end());

      $$ = $xs;
    }
;

varied_in_reduction_variable:
    object_variable[x] {
      val<inference> i(make);
      i->varied_in_reduction_[0].insert($x);
      $$ = i;
    }
  | metaformula_variable[x] {
      val<inference> i(make);
      i->varied_in_reduction_[0].insert($x);
      $$ = i;
    }
;
*/


simple_metaformula:
    metaformula_variable[x] { $$ = $x; }
  | "(" pure_metaformula[x] ")" { $$ = $x; }
;


atomic_metaformula:
    metaformula_variable[x] { $$ = $x; }
  | metapredicate[x] { $$ = $x; }
;


special_metaformula:
/*
  |  "fail"[x] { $$ = val<succeed_fail>(make, false); }
  | "succeed"[x] { $$ = val<succeed_fail>(make, true); }
   meta_object_free[x] "≡" meta_object_free[y] {
      $$ = val<objectidentical>(make, val<variable>($x), val<variable>($y), true);
    }
*/
    meta_object_free[x] "≢" meta_object_free[y] {
      $$ = val<objectidentical>(make, val<variable>($x), val<variable>($y), false);
    }
  | meta_object_free[x] "free in" object_formula[y] {
      $$ = val<free_in_object>(make, val<variable>($x), val<formula>($y), true);
    }
  | meta_object_free[x] "free in" term[y] {
      $$ = val<free_in_object>(make, val<variable>($x), val<formula>($y), true);
    }
  | meta_object_free[x] "not" "free in" object_formula[y] {
      $$ = val<free_in_object>(make, val<variable>($x), val<formula>($y), false);
    }
  | meta_object_free[x] "not" "free in" term[y] {
      $$ = val<free_in_object>(make, val<variable>($x), val<formula>($y), false);
    }
  | term[x] "free for" meta_object_free[y] "in" object_formula[z] {
      $$ = val<free_for_object>(make, 
        val<formula>($x), val<variable>($y), val<formula>($z), true);
    }
  | term[x] "free for" meta_object_free[y] "in" term[z] {
      $$ = val<free_for_object>(make, 
        val<formula>($x), val<variable>($y), val<formula>($z), true);
    }
;


meta_object_free:
    object_variable[x] { $$ = $x; }
;


metapredicate:
    metapredicate_function[x] { $$ = $x; }
  | object_formula[x] "≣" object_formula[y] {
      $$ = val<identical>(make, val<formula>($x), val<formula>($y), true);
    }
  | object_formula[x] "≣̷" object_formula[y] {
      $$ = val<identical>(make, val<formula>($x), val<formula>($y), false);
    }
  | term[x] "≣" term[y] {
      $$ = val<identical>(make, val<formula>($x), val<formula>($y), true);
    }
  | term[x] "≣̷" term[y] {
      $$ = val<identical>(make, val<formula>($x), val<formula>($y), false);
    }
;


metapredicate_function:
    metapredicate_constant[x] metapredicate_argument[y] {
      $$ = val<structure>(make, val<formula>($x), val<formula>($y),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
  | metaformula_variable[x] metapredicate_argument[y] {
      $$ = val<structure>(make, val<formula>($x), val<formula>($y),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
;


metapredicate_argument:
    "(" metapredicate_argument_body[x] ")" { $$ = $x; }
;


metapredicate_argument_body:
    object_formula[x] {
      ref0<sequence> vr(make, sequence::tuple);
      $$ = vr;
      vr->push_back(val<formula>($x)); }
  | metapredicate_argument_body[x] "," object_formula[y] {
      $$ = $x;
      sequence& vr = dyn_cast<sequence&>($$);
      vr.push_back(val<formula>($y)); }
;


object_formula:
    atomic_formula[x] { $$ = $x; }
  | very_simple_formula[x] formula_substitution_sequence[y] {
      $$ = val<substitution_formula>(make, val<substitution>($y), val<formula>($x));
    }
  | predicate_function_application[x] { $$ = $x; }
  | logic_formula[x] { $$ = $x; }
  | "(" object_formula[x] ")" { $$ = $x; }
  | quantized_formula[x] { $$ = $x; }
  | hoare_triple {}
;


hoare_triple:
  "{" object_formula "}" code_sequence "{" object_formula "}" { $$ = val<formula>(); }
;

/*
code:
    %empty {}
  | code_statement {}
;
*/

code_statement:
    code_term {}
  | "{" code_sequence "}" {}
;


code_sequence:
    %empty {}
  | code_term {}
  | code_sequence ";" code_term {}
;


code_term:
   code_variable {}
 | "∅" {}
 | object_variable "≔" term {}
 | "if" object_formula "then" code_statement "else" code_statement {}
 | "while" object_formula "do" code_statement {}
;


very_simple_formula:
    object_formula_variable[x] { $$ = $x; }
  | atom_variable[x] { $$ = $x; }
  | "(" object_formula[x] ")" { $$ = $x; }
;


quantized_formula:
    quantizer_declaration[x] quantized_body[y] {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>($x);
      val<bound_formula> bf(make, vsr, val<formula>($y));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      $$ = bf;
    }
  | quantizer_declaration[x] optional_in_term[s] ":" object_formula[y] {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>($x);
      val<bound_formula> bf(make, vsr, $s, val<formula>($y));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      $$ = bf;
    }
  | quantizer_declaration[x] optional_in_term[s] quantized_formula[y] {
      symbol_table.pop_level();
      variable_list& vsr = dyn_cast<variable_list&>($x);
      val<bound_formula> bf(make, vsr, $s, val<formula>($y));
      bf->excluded1_.insert(vsr.excluded1_.begin(), vsr.excluded1_.end());
      $$ = bf;
    }
;


simple_formula:
    object_formula_variable[x] { $$ = $x; }
  | atom_variable[x] { $$ = $x; }
  | predicate_expression[x] { $$ = $x; }
  | "(" object_formula[x] ")" { $$ = $x; }
  | quantized_formula[x] { $$ = $x; }
;


// No quantizer or logic in top level.
quantized_body:
    atomic_formula[x] { $$ = $x; }
  | "(" object_formula[x] ")" { $$ = $x; }
;

atomic_formula:
    atom_constant[x] { $$ = $x; }
  | object_formula_variable[x] { $$ = $x; }
  | atom_variable[x] { $$ = $x; }
  | predicate[x] { $$ = $x; }
;


    /* Predicates */
predicate:
    predicate_expression[x] { $$ = $x; }
  | term[x] "="[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, equal_oprec, $x, $y); }
  | term[x] "≠"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, not_equal_oprec, $x, $y); }

  /* Divisibility */
  | term[x] "∣"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, equal_oprec, $x, $y); }
  | term[x] "∤"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, not_equal_oprec, $x, $y); }

  /* Inequalities and their negations. */
  | term[x] "<"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, less_oprec, $x, $y); }
  | term[x] ">"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, greater_oprec, $x, $y); }
  | term[x] "≤"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, less_or_equal_oprec, $x, $y); }
  | term[x] "≥"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, greater_or_equal_oprec, $x, $y); }
  | term[x] "≮"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, not_less_oprec, $x, $y); }
  | term[x] "≯"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, not_greater_oprec, $x, $y); }
  | term[x] "≰"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, not_less_or_equal_oprec, $x, $y); }
  | term[x] "≱"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, not_greater_or_equal_oprec, $x, $y); }
  /* Set predicates. */
  | term[x] "∈"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, in_oprec, $x, $y); }
  | term[x] "∉"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, not_in_oprec, $x, $y); }
  | term[x] "⊆"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, subset_oprec, $x, $y); }
  | term[x] "⊊"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, proper_subset_oprec, $x, $y); }
  | term[x] "⊇"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, superset_oprec, $x, $y); }
  | term[x] "⊋"[a] term[y] { $$ = val<structure>(make, $a, structure::predicate, 0_ml, structure::infix, proper_superset_oprec, $x, $y); }
  | "Set" { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
    "₍" is_set_variable[x] "₎" { bound_variable_type = free_variable_context; }
     simple_formula[y] {
      symbol_table.pop_level();
      $$ = val<bound_formula>(make,
        val<variable>($x), val<formula>($y), bound_formula::is_set_);
    }
;


predicate_expression:
    predicate_identifier[x] tuple[y] {
      $$ = val<structure>(make, val<formula>($x), val<formula>($y),
        structure::predicate, 0_ml, structure::postargument, precedence_t());
    }
;


predicate_identifier:
    predicate_constant[x] { $$ = $x;  }
  | predicate_variable[x] { $$ = $x;  }
;


optional_superscript_natural_number_value:
    %empty {}
  | superscript_natural_number_value
;

/*
optional_subscript_natural_number_value:
    %empty { $$ = val<integer>(make); }
  | subscript_natural_number_value
;
*/

    /* Logic */
logic_formula:
    "¬"[a] optional_superscript_natural_number_value[k] object_formula[x] {
      size_type k = (size_type)$k;

      $$ = val<structure>(make, $a, structure::logic, metalevel_t(k),
        structure::prefix, logical_not_oprec, $x);
    }
  | object_formula[x] "∨"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)$k;

      $$ = val<structure>(make, $a, structure::logic, metalevel_t(k),
        structure::infix, logical_or_oprec, $x, $y);
    }
  | object_formula[x] "∧"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)$k;

      $$ = val<structure>(make, $a, structure::logic, metalevel_t(k),
        structure::infix, logical_and_oprec, $x, $y);
    }
  | object_formula[x] "⇒"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)$k;

      $$ = val<structure>(make, $a, structure::logic, metalevel_t(k),
        structure::infix, implies_oprec, $x, $y);
    }
  | object_formula[x] "⇐"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)$k;

      $$ = val<structure>(make, $a, structure::logic, metalevel_t(k),
        structure::infix, impliedby_oprec, $x, $y);
    }
  | object_formula[x] "⇔"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)$k;

      $$ = val<structure>(make, $a, structure::logic, metalevel_t(k),
        structure::infix, equivalent_oprec, $x, $y);
    }
  | prefix_logic_formula[x] { $$ = $x;  }
;


prefix_logic_formula:
    prefix_formula_variable[x] { $$ = $x; }
  | prefix_not_key[a] prefix_logic_formula[x] {
      $$ = val<structure>(make, "¬", structure::logic, 0_ml,
        structure::prefix, logical_not_oprec, $x);
    }
  | prefix_or_key[a] prefix_logic_formula[x] prefix_logic_formula[y] {
      $$ = val<structure>(make, "∨", structure::logic, 0_ml,
        structure::infix, logical_or_oprec, $x, $y);
    }
  | prefix_and_key[a] prefix_logic_formula[x] prefix_logic_formula[y] {
      $$ = val<structure>(make, "∧", structure::logic, 0_ml,
        structure::infix, logical_and_oprec, $x, $y);
    }
  | prefix_implies_key[a] prefix_logic_formula[x] prefix_logic_formula[y] {
      $$ = val<structure>(make, "⇒", structure::logic, 0_ml,
        structure::infix, implies_oprec, $x, $y);
    }
  | prefix_equivalent_key[a] prefix_logic_formula[x] prefix_logic_formula[y] {
      $$ = val<structure>(make, "⇔", structure::logic, 0_ml,
        structure::infix, equivalent_oprec, $x, $y);
 }
;


quantizer_declaration:
    quantized_variable_list[x] { $$ = $x; }
;

quantized_variable_list:
    all_variable_list[x] { $$ = $x; }
  | exist_variable_list[x] { $$ = $x; }
;


all_variable_list:
    "∀" exclusion_set[vs] all_identifier_list[x] {
      auto bfp = dyn_cast<bound_formula*>($vs);
      if (bfp != nullptr) {
        variable_list& vsr = dyn_cast<variable_list&>($x);
        vsr.excluded1_.insert(bfp->excluded1_.begin(), bfp->excluded1_.end());
      }
      $$ = $x;
    }
;


exist_variable_list:
    "∃" exclusion_set[vs] exist_identifier_list[x] {
      auto bfp = dyn_cast<bound_formula*>($vs);
      if (bfp != nullptr) {
        variable_list& vsr = dyn_cast<variable_list&>($x);
        vsr.excluded1_.insert(bfp->excluded1_.begin(), bfp->excluded1_.end());
      }
      $$ = $x;
    }
;


exclusion_set:
    %empty {}
  | "ₓ" { bound_variable_type = free_variable_context; }
    "₍" exclusion_list[vs] "₎" {
      bound_variable_type = database_parser::token::exist_variable;
      $$ = $vs;
    }
;

exclusion_list:
    object_variable[x] { val<bound_formula> vr(make); vr->excluded1_.insert($x); $$ = vr; }
  | exclusion_list[vs] object_variable [x] {
      val<bound_formula> vr = $vs;
      vr->excluded1_.insert($x);
      $$ = vr;
    }
;



all_identifier_list:
    all_variable[x] {
      bound_variable_type = free_variable_context;
      $$ = val<variable_list>(make, val<variable>($x), bound_formula::all_);
    }
  | all_identifier_list[x] { bound_variable_type = token::all_variable; }
      "," all_variable[y] {
      bound_variable_type = free_variable_context;
      $$ = $x;
      dyn_cast<variable_list&>($$).push_back(val<variable>($y), bound_formula::all_);
    }
;


exist_identifier_list:
    exist_variable[x] {
      bound_variable_type = free_variable_context;
      $$ = val<variable_list>(make, val<variable>($x), bound_formula::exist_);
    }
  | exist_identifier_list[x] { bound_variable_type = database_parser::token::exist_variable; }
      "," exist_variable[y] {
      bound_variable_type = free_variable_context;
      $$ = $x;
      dyn_cast<variable_list&>($$).push_back(val<variable>($y), bound_formula::exist_);
    }
;


// Specifying domain 𝒙 ∈ 𝑆 for binders:
optional_in_term:
    %empty { $$ = val<formula>(make); }
  | "∈" term[s] { $$ = $s; }
;


    /* Terms */

tuple:
    "(" tuple_body[x] ")" { $$ = $x; }
;


tuple_body:
    term[x] {
      ref0<sequence> vr(make, sequence::tuple);
      $$ = vr;
      vr->push_back(val<formula>($x));
    }
  | tuple_body[x] "," term[y] {
      $$ = $x;
      sequence& vr = dyn_cast<sequence&>($$);
      vr.push_back(val<formula>($y));
    }
;


term:
    simple_term[x] { $$ = $x; }
  | function_term[x] { $$ = $x; }
  | simple_term[x] term_substitution_sequence[y] {
      $$ = val<substitution_formula>(make, val<substitution>($y), val<formula>($x));
    }
  | set_term[x] { $$ = $x; }
;


simple_term:
    term_constant[x]   { $$ = $x; }
  | "natural number value"[x] { $$ = val<integer>(make, $x.second); }
  | "integer value"[x] { $$ = val<integer>(make, $x); }
  | term_identifier[x] { $$ = $x; }
  | "(" term[x] ")"    { $$ = $x; }
;


term_identifier:
    object_variable[x] variable_exclusion_set[vs]   {
      val<variable> xr = $x;
      val<variable> vr = $vs;
      xr->excluded_.insert(vr->excluded_.begin(), vr->excluded_.end());
      $$ = xr;
    }
  | function_variable[x]  { $$ = $x; }
  | function_map_variable[x]  { $$ = $x; }
  | all_variable[x]       { $$ = $x; }
  | exist_variable[x]     { $$ = $x; }
  | is_set_variable[x]    { $$ = $x; }
  | set_variable[x]       { $$ = $x; }
  | implicit_set_variable[x] { $$ = $x; }
;


variable_exclusion_set:
    %empty { $$ = val<variable>(make);  }
  | "ₓ" "₍" variable_exclusion_list[vs] "₎" { $$ = $vs; }
;


variable_exclusion_list:
    bound_variable[x] { val<variable> vr(make); vr->excluded_.insert($x); $$ = vr; }
  | variable_exclusion_list[vs] bound_variable [x] {
      val<variable> vr = $vs;
      vr->excluded_.insert($x);
      $$ = vr;
    }
;


bound_variable:
    all_variable[x]       { $$ = $x; }
  | exist_variable[x]     { $$ = $x; }
  | is_set_variable[x]    { $$ = $x; }
  | set_variable[x]       { $$ = $x; }
  | implicit_set_variable[x] { $$ = $x; }
;


function_term:
    function_term_identifier[x] tuple[y] {
      $$ = val<structure>(make, val<formula>($x), val<formula>($y),
        structure::function, 0_ml, structure::postargument, precedence_t()); }
  | term_function_application[x] { $$ = $x; }
  | term[x] "!"[a] {
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::postfix, factorial_oprec, $x);
    }
  | term[x] "+"[a] term[y] { // $$ = val<integer_addition>(make, val<formula>($x), val<formula>($y));
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::infix, plus_oprec, $x, $y);
    }
  | term[x] "-"[a] term[y] { // $$ = val<integer_addition>(make, val<formula>($x), val<integer_negative>(make, val<formula>($y)));
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::infix, minus_oprec, $x, $y);
    }
  | "-"[a] term[x]  %prec unary_minus { // $$ = val<integer_negative>(make, val<formula>($x)); }
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::prefix, unary_minus_oprec, $x);
    }
  | term[x] "⋅"[a] term[y] {
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::infix, mult_oprec, $x, $y);
    }
  | term[x] "/"[a] term[y] {
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::infix, divide_oprec, $x, $y);
    }
;


set_term:
    "{" "}" { $$ = ref0<sequence>(make, sequence::member_list_set); }
  | "∅" { $$ = val<constant>(make, "∅", constant::object); }
  | "{" set_member_list[x] "}" { $$ = $x; }
  | "{" set_variable_definition[x] optional_in_term[s] "|" object_formula[y] "}" {
      symbol_table.pop_level();
      $$ = val<bound_formula>(make, $x, $s, $y, bound_formula::set_);
    }
  | "{" "₍" implicit_set_identifier_list[x] optional_in_term[s] "₎" term[y] "|" object_formula[z] "}" {
      symbol_table.pop_level();
      variable_list& vs = dyn_cast<variable_list&>($x);
      ref0<sequence> sp(make, val<formula>($y), sequence::implicit_set);
      sp->push_back(val<formula>($z));
      $$ =
        val<bound_formula>(make, vs, $s, val<formula>(sp));
    }
  | term[x] "∪"[a] term[y] {
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::infix, set_union_oprec, $x, $y);
    }
  | term[x] "∩"[a] term[y] {
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::infix, set_intersection_oprec, $x, $y);
    }
  | term[x] "∖"[a] term[y] {
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::infix, set_difference_oprec, $x, $y);
    }
  | "∁"[a] term[x] {
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::prefix, set_complement_oprec, $x);
    }
  | "⋃"[a] term[x] { /* prefix union operator  */
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::prefix, set_union_operator_oprec, $x);
    }
  | "∩"[a] term[x] { /* prefix intersection operator  */
      $$ = val<structure>(make, $a, structure::function, 0_ml,
        structure::prefix, set_intersection_operator_oprec, $x);
    }
;


implicit_set_identifier_list:
    { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
    is_set_variable[x] {
      bound_variable_type = free_variable_context;
      $$ = val<variable_list>(make, val<variable>($x), bound_formula::implicit_set);
    }
  | implicit_set_identifier_list[x] { bound_variable_type = database_parser::token::is_set_variable; }
      "," is_set_variable[y] {
      bound_variable_type = free_variable_context;
      $$ = $x;
      dyn_cast<variable_list&>($$).push_back(val<variable>($y), bound_formula::implicit_set);
    }
;


set_member_list:
    term[x] {
      ref0<sequence> vr(make, sequence::member_list_set);
      $$ = vr;
      vr->push_back(val<formula>($x)); }
  | set_member_list[x] "," term[y] {
      $$ = $x;
      sequence& vr = dyn_cast<sequence&>($$);
      vr.push_back(val<formula>($y));
    }
;


function_term_identifier:
    function_constant[x] { $$ = $x; }
  | function_variable[x] { $$ = $x; }
;


%%

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

