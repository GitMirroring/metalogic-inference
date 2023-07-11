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


    class database_lexer : public yyFlexLexer {
    public:
      mli::semantic_type* yylvalp = nullptr;
      mli::location_type* yyllocp = nullptr;

      database_lexer() {};

      database_lexer(std::istream& is, std::ostream& os) : yyFlexLexer(&is, &os) {}

      int yylex(); // Defined in database-lexer.cc.

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

    using symbol_table_t = mli::table_stack<std::string, std::pair<mli::database_parser::token_type, mli::ref<mli::unit>>>;

    extern symbol_table_t symbol_table;

    extern depth proof_depth;

    extern database_parser::token_type bound_variable_type;

    constexpr database_parser::token_type free_variable_context = database_parser::token_type(0);

    database_parser::token_type define_variable(semantic_type& yylval);

    extern kleenean unused_variable;

    int directive_read(std::istream& is, mli::location_type& loc);
    int directive_read(const std::string& str, mli::location_type&);

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

    std::set<ref<variable>> statement_variables_;

    ref<theory> theory_;  // Theory to enter propositions into.
    ref<database> theorem_theory_;  // Theory used for a theorem proof.

    // Stacks to handle nested statements and their proofs:
    std::vector<ref<statement>> statement_stack_; // Pushed & popped at statement boundaries.


    // Pushed & popped at proof boundaries:
    mli::table_stack<std::string, ref<statement>> proofline_stack_; // Proof line table.

    // The proofe depth is used for nested proof variable renumbering.
    // Incremented at the beginning of a theorem or subtheorem, and decremented at the proof end.
    depth proof_depth = 0, proof_depth0 = 0;


    mli::database_parser::token_type to_token(variable::type t) {
      switch (t) {
        case variable::formula_:       return mli::database_parser::token::object_formula_variable;
        case variable::predicate_:     return mli::database_parser::token::predicate_variable;
        case variable::atom_:          return mli::database_parser::token::atom_variable;
        case variable::function_:      return mli::database_parser::token::function_variable;
        case variable::object_:        return mli::database_parser::token::object_variable;
        default:                       return mli::database_parser::token::token_error;
      }
    }


    // For bound variable definitions, set to the token type that
    // should be inserted in the symbol table:
    database_parser::token_type bound_variable_type = database_parser::token_type(0);

    ref<formula> head(const statement& x) {
      auto xp = ref_cast<inference*>(x.statement_);
      if (xp != nullptr)
        return xp->head_;
      return x.statement_;
    }


    database_parser::token_type define_variable(semantic_type& yylval) {
      if (statement_substitution_context) {
        statement_substitution_context = false;
        std::optional<std::pair<database_parser::token_type, mli::ref<mli::unit>>> x = mli::symbol_table.find_top(yylval.text);
        if (!x)  return mli::database_parser::token::plain_name;
        yylval.object = x->second;
        yylval.number = x->first;
        return x->first;
      }

      if (declaration_context)
        return mli::database_parser::token::plain_name;

      std::optional<std::pair<mli::database_parser::token_type, mli::ref<mli::unit>>> x = mli::symbol_table.find(yylval.text);


      if (!x) {
        // Not a bound variable case:
        if (bound_variable_type == mli::free_variable_context)
          return mli::database_parser::token::plain_name;

        // Bound variable case: Create a limited variable of bind 1, insert at the secondary
        // (bound variable) stack level.
        ref<variable> v = ref<variable>(make, yylval.text, variable::limited_, variable::object_, proof_depth);

        v->bind_ = 1;
        symbol_table.insert(yylval.text, {bound_variable_type, v});

        yylval.object = v;
        yylval.number = bound_variable_type;

        return bound_variable_type;
      }


      mli::variable* vp = mli::ref_cast<mli::variable*>(x->second);

      if (vp != nullptr
        && (vp->depth_ == -1 || bound_variable_type != mli::free_variable_context)) {

        if (bound_variable_type == mli::free_variable_context) {
          // Case definition of a free variable:

          // Check if it is a variable which is declared without definition, in which case make
          // a copy with right proof depth, insert it in the symbol table, and change x->second
          // so subsequently the new copy is used instead of the original lookup value.
          mli::ref<mli::variable> v(make, *vp);
          v->depth_ = proof_depth;

          symbol_table.insert_or_assign(yylval.text, {x->first, v});

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
            v->depth_ = proof_depth;
            v->metatype_ = variable::limited_;
            v->bind_ = 1;

            symbol_table.insert(yylval.text, {x->first, v});

            x->second = v;
          }
          else if (vp->depth_ == -1) {
            mli::ref<mli::variable> v(make, *vp);
            v->depth_ = proof_depth;

            symbol_table.insert_or_assign(yylval.text, {x->first, v});

            x->second = v;
          }

          yylval.object = x->second;
          yylval.number = x->first;

          return bound_variable_type;
        }
      }

      yylval.object = x->second;
      yylval.number = x->first;

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

%token theorem_key "theorem"

%token proof_key "proof"
%token end_of_proof_key "∎"

%token by_key "by"

%token premise_key "premise"
%token result_key "result"


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
%token plain_name "name"
%token label_key "label"

/* Metaconstants: */
%token metapredicate_constant "metapredicate constant"

/* Functions */
%token function_key "function"
%token predicate_key "predicate"

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


/* Object variables: */

%token object_variable "object variable"

/* Hoare logic code variable */
%token code_variable "code variable"


%token all_variable "all variable"
%token exist_variable "exist variable"

/* The function map variable is the 𝒙 in 𝒙 ↦ 𝑨. */
%token function_map_variable "function map variable"

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
%token identifier_function_key "identifier function"

  /* Keys for labeling identifiers constant or variable.
%token constant_key "constant"
%token variable_key "variable"
*/


/* Declarators: quantifiers. */

%token all_key "∀"
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

%token natural_numner_key "ℕ"

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

%token divides_key "∣"
%token not_divides_key "∤"

%token mapsto_key "↦"
%token Mapsto_key "⤇"

/* Boldface 𝛌 for function maps of the form 𝛌 𝒙 ↦ 𝑨 implicitly declaring 𝒙. */
%token function_map_prefix_key "𝛌"

%token degree_key "°"
%token bullet_key "•"

%token subscript_x_key "ₓ"

%token natural_number_value "natural number value"
%token integer_value   "integer value"

%token subscript_natural_number_value "subscript natural number value"
%token subscript_integer_value   "subscript integer value"

%token superscript_natural_number_value "superscript natural number value"
%token superscript_integer_value   "superscript integer value"


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
    %empty
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
    substitution_for_metaformula[x] { $$.object = $x.object; }
  | metaformula_substitution_sequence[x] substitution_for_metaformula[y] {
      $$.object =  ref<substitution>($x.object) * ref<substitution>($y.object);
    }
;


substitution_for_metaformula:
    metaformula_substitution[x] { $$.object = $x.object; }
  | formula_substitution[x] { $$.object = $x.object; }
  | term_substitution[x] { $$.object = $x.object; }
;


metaformula_substitution:
    "[" metaformula_variable[x] "⤇" metaformula[y] "]" {
      ref<variable> v($x.object);
      ref<formula> f($y.object);
      $$.object = ref<explicit_substitution>(make, v, f);
    }
;


formula_substitution_sequence:
    substitution_for_formula[x] { $$.object = $x.object; }
  | formula_substitution_sequence[x] substitution_for_formula[y] {
      $$.object = ref<substitution>($x.object) * ref<substitution>($y.object);
    }
;


substitution_for_formula:
    formula_substitution[x] { $$.object = $x.object; }
  | term_substitution[x] { $$.object = $x.object; }
;


formula_substitution:
    "[" object_formula_variable[x] "⤇" object_formula[y] "]" {
      ref<variable> v($x.object);
      ref<formula> f($y.object);
      $$.object = ref<explicit_substitution>(make, v, f);
    }
  | "[" predicate_variable[x] "⤇" predicate[y] "]" {
      ref<variable> v($x.object);
      ref<formula> f($y.object);
      $$.object = ref<explicit_substitution>(make, v, f);
    }
  | "[" atom_variable[x] "⤇" atom_constant[y] "]" {
      ref<variable> v($x.object);
      ref<formula> f($y.object);
      $$.object = ref<explicit_substitution>(make, v, f);
    }
;


term_substitution_sequence:
    term_substitution[x] { $$.object = $x.object; }
  | term_substitution_sequence[x] term_substitution[y] {
      $$.object = ref<substitution>($x.object) * ref<substitution>($y.object);
    }
;


term_substitution:
    "[" term_identifier[x] "⤇" term[y] "]" {
      ref<variable> v($x.object);
      ref<formula> f($y.object);
      $$.object = ref<explicit_substitution>(make, v, f);
    }
;


predicate_function_application:
    "(" object_variable[x] "↦" object_formula[f] ")" tuple[a] {
      $$.object = ref<function_application>(make, ref<function_map>(make, $x.object, $f.object), $a.object);
    }
  | "(" "𝛌" function_map_variable[x] "↦" object_formula[f] { symbol_table.pop_level(); } ")" tuple[a] {
      $$.object = ref<function_application>(make, ref<function_map>(make, $x.object, $f.object), $a.object);
    }
  | predicate_key[p] tuple[a] { $$.object = ref<function_application>(make, $p.object, $a.object); }
;


term_function_application:
    "(" object_variable[x] "↦" term[f] ")" tuple[a] {
      $$.object = ref<function_application>(make, ref<function_map>(make, $x.object, $f.object), $a.object);
    }
  | "(" "𝛌" function_map_variable[x] "↦" term[f] { symbol_table.pop_level(); } ")" tuple[a] {
      $$.object = ref<function_application>(make, ref<function_map>(make, $x.object, $f.object), $a.object);
    }
  | function_key[p] tuple[a] { $$.object = ref<function_application>(make, $p.object, $a.object); }
;


theory:
    "theory" statement_name[x]
    "." { theory_ = ref<theory>(make, $x.text);
          yypval.insert(theory_);
          symbol_table.push_level();
    }
    include_theories
    theory_body
    "end" "theory" end_theory_name[y] "." {
      if ($y.number != 0 && $x.text != $y.text) {
        mli::database_parser::error(@y, "warning: Name mismatch, theory " + $x.text
          + ", end theory " + $y.text + ".");
      }

      symbol_table.pop_level();
    }
;


end_theory_name:
    %empty             { $$.number = 0; }
  | statement_name[x]  { $$.text = $x.text; $$.number = 1; }
;


include_theories:
    %empty
  | include_theories include_theory {}
;

include_theory:
   "include" "theory" theory_name[x] "." {
      std::optional<ref<theory>> th = yypval.find($x.text);

      if (!th)
        throw syntax_error(@x, "Include theory " + $x.text + " not found.");

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
    %empty
  | formal_system_body formal_system_body_item {}
;


formal_system_body_item:
    identifier_declaration {}
  | postulate[x] { theory_->insert(ref<statement>($x.object)); }
  | definition_labelstatement[x] { theory_->insert(ref<statement>($x.object)); }
;


theory_body_list:
    %empty
  | theory_body_list theory_body_item {}
;


/* Postulates are not included here, as metatheorems such as the
   deduction theorem cannot then be localized to the same namespace:
   Such metatheorems are only true with respect to a fixed set of
   postulates, so if more postulates are added after the metatheorem,
   it becomes not true with respect to all postulates in the theory. */
theory_body_item:
    theorem[x] { theory_->insert(ref<statement>($x.object)); }
  | identifier_declaration {}
  | conjecture[x] { theory_->insert(ref<statement>($x.object)); }
/*| constant_identifier_declaration {} */
  | definition_labelstatement[x] { theory_->insert(ref<statement>($x.object)); }
;


postulate:
    "postulate" statement_name[x]
    "." { symbol_table.push_level(); }
    statement[y] "." {
      symbol_table.pop_level();
      $$.object = ref<supposition>(make, supposition::postulate_, $x.text, $y.object, true);
    }
  | conjecture
  | "axiom" statement_name[x]
    "." { symbol_table.push_level(); }
    statement[y] "." {
      symbol_table.pop_level();

      ref<formula> f($y.object);

      if (!f->is_axiom())
        throw syntax_error(@y, "Axiom statement not an object formula.");

      $$.object = ref<supposition>(make, supposition::postulate_, $x.text, f);
    }
  | "rule" statement_name[x]
    "." { symbol_table.push_level(); }
    statement[y] "." {
      symbol_table.pop_level();

      ref<formula> f($y.object);

      if (!f->is_rule())
        throw syntax_error(@y, "Rule statement not an inference.");

      $$.object = ref<supposition>(make, supposition::postulate_, $x.text, f);
    }
;


conjecture:
    "conjecture" statement_name[x]
    "." { symbol_table.push_level(); }
    statement[y] "." {
      symbol_table.pop_level();
      $$.object = ref<supposition>(make, supposition::conjecture_, $x.text, $y.object, true);
    }
;

definition_labelstatement:
    "definition" statement_name[x]
    "." { symbol_table.push_level(); }
    definition_statement[y] "." {
      symbol_table.pop_level();
      $$.text = $x.text;
      $$.object = ref<definition>(make, $x.text, $y.object);
    }
;


statement_name:
    "name"[x] { $$.text = $x.text; }
  | "label"[x] { $$.text = $x.text; }
  | "natural number value"[x] { $$.text = $x.text; }
;


theorem:
    theorem_statement proof {
      $$.object = statement_stack_.back();
      ref<statement> t($$.object); // The theorem.
      t->prove(proof_count);     // Attempt to prove the theorem.
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
;


theorem_statement:
    theorem_head[x] statement[y] {
      symbol_table_t::table& top = symbol_table.top();
      ref<theorem> tr(make,
        theorem::type($x.number), $x.text, $y.object, theory_, proof_depth);
      statement_stack_.back() = tr;
      theorem_theory_ = tr->get_theory();
    }
;


theorem_head:
    "theorem"[x] statement_name[y] "." {
      $$.text = $y.text;
      $$.number = $x.number;
      symbol_table.push_level();
      statement_stack_.push_back(ref<statement>());
    }
;


proof:
    compound-proof
  | {
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
  | "∎"
;


proof_head:
    "proof" {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
;


proof_lines:
    %empty
  | proof_lines proof_line {}
;


statement_label:
    statement_name[x] "." {
      $$.text = $x.text;
      symbol_table.push_level();
    }
;


proof_line:
    statement_label[x] statement[y] "by" find_statement[z] "." {
      // Handles explicit find_statement substitutions A[x⤇e].
      proofline_database_context = false;

      theorem& t = ref_cast<theorem&>(statement_stack_.back());

      bool concluding = false;

      if (t.get_formula() == $y.object || head(t) == $y.object)
        concluding = true;

      if (!concluding && $x.text == "conclusion")
        throw syntax_error(@x, "Proof line name “conclusion” used when not the theorem conclusion.");

      if (!concluding && $x.text == "result")
        throw syntax_error(@x, "Proof line name “result” used when not the theorem result.");

      symbol_table_t::table& top = symbol_table.top();

      ref<statement> proof_line =
        t.push_back(
          $x.text, ref<formula>($y.object), ref<database>($z.object), concluding, proof_depth);

      symbol_table.pop_level();

      if (!proofline_stack_.insert($x.text, proof_line)) {
        if ($x.text.empty())
          throw syntax_error(@x, "Proof line empty name “” used.");
        else
          throw syntax_error(@x, "Proof line name " + $x.text  + " already given to a proof line.");
      }
    }
  | subproof[x] {
      theorem& t = ref_cast<theorem&>(statement_stack_.back());
      ref<statement> proof_line = t.push_back(ref<statement>($x.object));
      if (!proofline_stack_.insert($x.text, proof_line)) {
        if ($x.text.empty())
          throw syntax_error(@x, "Proof line empty name “” used.");
        else
          throw syntax_error(@x, "Proof line name " + $x.text  + " already given to a proof line.");
      }
    }
  | {} identifier_declaration {}
/* | { proof_depth0 = proof_depth; proof_depth = -1; } identifier_declaration { proof_depth = proof_depth0; } */

/*| constant_identifier_declaration {} */
  | definition_labelstatement[x] {
      theorem& t = ref_cast<theorem&>(statement_stack_.back());
      ref<statement> proof_line = t.push_back(ref<statement>($x.object));

      if (!proofline_stack_.insert($x.text, proof_line)) {
        if ($x.text.empty())
          throw syntax_error(@x, "Proof line name “” used.");
        else
          throw syntax_error(@x, "Proof line name " + $x.text  + " already given to a proof line.");
      }
    }
  | proof_of_conclusion {}
;


subproof:
    subproof_statement[x] compound-proof {
      $$.text = $x.text;
      $$.object = statement_stack_.back();
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
;


subproof_statement:
    statement_label[x] statement[y] {
      $$.text = $x.text;
      symbol_table_t::table& top = symbol_table.top();
      ref<theorem> tp(make, theorem::claim_, $x.text, $y.object, theory_, proof_depth);
      statement_stack_.push_back(tp);
    }
;


proof_of_conclusion:
    optional-result[x] "by" find_statement[y] "." {
      proofline_database_context = false;

      theorem& t = ref_cast<theorem&>(statement_stack_.back());
      ref<statement> proof_line =
        t.push_back($x.text, t.get_formula(), ref<database>($y.object), true, proof_depth);
    }
;


optional-result:
    %empty        { $$.text = "result"; }
  | "result"[x]   { $$ = $x; }
;


find_statement:
    find_statement_list[x] { $$.object = ref<level_database>(make, ref<database>($x.object)); }
  | find_statement[x] ":" find_statement_list[y] {
      ref<level_database>($x.object)->push_back(ref<database>($y.object));
      $$.object = $x.object;
    }
;


find_statement_list:
    find_statement_sequence[x] {
      $$.object = ref<sublevel_database>(make, ref<sequence_database>($x.object));
    }
  | find_statement_list[x] ";" find_statement_sequence[y] {
      ref<sublevel_database>($x.object)->push_back(ref<database>($y.object));
      $$.object = $x.object;
    }
;


find_statement_sequence:
    %empty        { $$.object = ref<sequence_database>(make); }
  | find_statement_item[x] {
      $$.object = ref<sequence_database>(make, ref<statement>($x.object)); }
  | find_statement_item[x] "₍" find_definition_sequence[y] "₎" {
      $$.object = ref<sequence_database>(make, ref<statement>($x.object));
      ref<sequence_database>($$.object)->insert(ref<sequence_database>($y.object));
    }
  | find_statement_sequence[x] "," find_statement_item[y] {
      ref<sequence_database>($x.object)->insert(ref<statement>($y.object));
      $$.object = $x.object;
    }
  | find_statement_sequence[x] "," find_statement_item[y] "₍" find_definition_sequence[z] "₎" {
      $$.object = $x.object;
      ref<sequence_database>($$.object)->insert(ref<statement>($y.object));
      ref<sequence_database>($$.object)->insert(ref<sequence_database>($z.object));
    }
;


find_definition_sequence:
    find_statement_item[x] {
      $$.object = ref<sequence_database>(make, ref<statement>($x.object)); }
  | find_definition_sequence[x] "," find_statement_item[y] {
      ref<sequence_database>($x.object)->insert(ref<statement>($y.object));
      $$.object = $x.object;
    }
;


find_statement_item:
    find_statement_name[x] {
      $$.object = $x.object;
    }
  | "premise" {
      $$.object = ref<premise>(make, statement_stack_.back());
    }
  | "premise" statement_name[x] {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == $x.text) {
          $$.object = ref<premise>(make, *i);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(@x, "Proof line premise " + $x.text  + " not found.");
    }
  | "premise" statement_name[x] subscript_natural_number_value[k] {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == $x.text) {
          size_type k = (size_type)ref_cast<integer&>($k.object);
          $$.object = ref<premise>(make, *i, k);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(@x, "Proof line premise " + $x.text  + " not found.");
    }
  | "premise" "⊢" {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      $$.object = ref<premise>(make);
    }
  | "premise" "⊢" subscript_natural_number_value[k] {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      size_type k = (size_type)ref_cast<integer&>($k.object);
      $$.object = ref<premise>(make, k);
    }
;


find_statement_name:
    statement_name[x] {
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref<statement>> st;
      st = proofline_stack_.find($x.text);

      if (!st)
        st = theorem_theory_->find($x.text, 0);

      if (!st)
        throw syntax_error(@x,
          "statement name " + $x.text + " not found earlier in proof, in premises or theory.");

      $$.object = *st;
    }
  | statement_name[x] {
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref<statement>> st;
      st = proofline_stack_.find($x.text);
      if (!st)
        st = theorem_theory_->find($x.text, 0);

      if (!st)
        throw syntax_error(@x,
          "statement name " + $x.text + " not found earlier in proof, in premises or theory.");

      $$.object = *st;
      // Find the variables of *st and record them for use in the substitution domain checks:
      ref<statement> pr = *st;
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
      ref<statement> p($y.object);
      ref<substitution> s($z.object);
      try {
        $$.object = ref<statement_substitution>(make, p, s);
      } catch (illegal_substitution&) {
        mli::database_parser::error(@z, "Proposition substitute error.");
        p->write(std::cerr,
          write_style(write_name | write_type | write_statement));
        std::cerr << "\n  " << s << std::endl;
        YYERROR;        
      }
      symbol_table.pop_level();
    }
;


statement:
    metaformula[x] { $$.object = ref<formula>($x.object)->set_bind(); }
  | identifier_declaration metaformula[x] {
      ref<formula> f($x.object);
      $$.object = f->set_bind();

      if (unused_variable != false) {
        std::set<ref<variable>> vs;
        f->contains(vs, occurrence::declared);

        std::set<ref<variable>> vr;  // Redundant variables.

        for (auto& i: symbol_table.top()) {
          try {
            ref<variable> v(i.second.second);
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
          mli::database_parser::error(@x, "warning: " + ds);
        else
          throw syntax_error(@x, ds);
        }
      }
    }
;


definition_statement:
    definition[x] { $$.object = ref<formula>($x.object)->set_bind(); }
  | identifier_declaration definition[x] {
      $$.object = ref<formula>($x.object)->set_bind();
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
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top($x.text);
      if (x0) {
        throw syntax_error(@x, "Name " + $x.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x.text, {current_declared_token,
        ref<function_map>(make, $y.object, $f.object)});
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
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top($x.text);
      if (x0) {
        throw syntax_error(@x, "Name " + $x.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x.text, {declared_token,
        ref<constant>(make, $x.text, constant::type(declared_type))});
    }
;


identifier_variable_list:
    identifier_variable_name {}
  | identifier_variable_list "," identifier_variable_name {}
;


identifier_variable_name:
    "name"[x] {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top($x.text);
      if (x0) {
        throw syntax_error(@x, "Name " + $x.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x.text, {declared_token,
       ref<variable>(make, $x.text, variable::ordinary_, variable::type(declared_type), -1)});
    }
  | "°" "name"[x] {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top($x.text);
      if (x0) {
        throw syntax_error(@x, "Name " + $x.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x.text, {declared_token,
        ref<variable>(make, $x.text, variable::limited_, variable::type(declared_type), -1)});
    }
  | "•" "name"[x] {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top($x.text);
      if (x0) {
        throw syntax_error(@x, "Name " + $x.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert($x.text, {declared_token,
        ref<variable>(make, $x.text, variable::term_, variable::type(declared_type), -1)});
    }
;


definition:
    metaformula_definition[x] { $$.object = $x.object; }
  | object_formula_definition[x] { $$.object = $x.object; }
  | term_definition[x] { $$.object = $x.object; }
;


metaformula_definition:
    pure_metaformula[x] "≔" pure_metaformula[y] {
      $$.object = ref<abbreviation>(make, ref<formula>($x.object), ref<formula>($y.object), ref<formula>(),
        formula::logic, formula_definition_oprec);
    }
  | pure_metaformula[x] "≕" pure_metaformula[y] {
      $$.object = ref<abbreviation>(make, ref<formula>($y.object), ref<formula>($x.object), ref<formula>(),
       formula::logic, formula_definition_oprec);
  }
/*
  | metaformula[x] "⊢" metaformula[y] "≔" metaformula[z] {
      $$.object = ref<abbreviation>(make, ref<formula>($y.object), ref<formula>($z.object), ref<formula>($x.object),
        object_formula_type_, formula_definition_oprec); }
*/
;


object_formula_definition:
    object_formula[x] "≔" object_formula[y] {
      $$.object = ref<abbreviation>(make, ref<formula>($x.object), ref<formula>($y.object), ref<formula>(),
        formula::logic, formula_definition_oprec);
    }
  | object_formula[x] "≕" object_formula[y] {
      $$.object = ref<abbreviation>(make, ref<formula>($y.object), ref<formula>($x.object), ref<formula>(),
        formula::logic, formula_definition_oprec);
  }
/*
  | metaformula[x] "⊢" object_formula[y] "≔" object_formula[z] {
      $$.object = ref<abbreviation>(make, ref<formula>($y.object), ref<formula>($z.object), ref<formula>($x.object),
        object_formula_type_, formula_definition_oprec); }
*/
;


term_definition:
    term[x] "≔" term[y] {
      $$.object = ref<abbreviation>(make, ref<formula>($x.object), ref<formula>($y.object), ref<formula>(),
        formula::object, term_definition_oprec);
    }
/*
  // Causes conflicts with the general "⊢" rules.
  | metaformula[x] "⊢" term[y] "≔" term[z] {
      $$.object = ref<abbreviation>(make, ref<formula>($y.object), ref<formula>($z.object), ref<formula>($x.object),
        term_type_, term_definition_oprec); }
*/
  | term[x] "≕" term[y] {
      $$.object = ref<abbreviation>(make, ref<formula>($y.object), ref<formula>($x.object), ref<formula>(),
        formula::object, term_definition_oprec);
  }
;


metaformula:
    pure_metaformula[x] { $$.object = $x.object; }
  | object_formula[x] { $$.object = $x.object; }
;


pure_metaformula:
    atomic_metaformula[x] { $$.object = $x.object; }
  | special_metaformula[x] { $$.object = $x.object; }
  | "~" metaformula[x] {
      $$.object = ref<metanot>(make, ref<formula>($x.object));
    }
  | metaformula[x] ";" metaformula[y] {
      $$.object = mli::concatenate(ref<formula>($x.object), ref<formula>($y.object));
    }
  | metaformula[x] "," metaformula[y] {
      $$.object = mli::concatenate(ref<formula>($x.object), ref<formula>($y.object));
    }
  | metaformula[x] "⊩" optional_superscript_natural_number_value[k]
      optional_varied_variable_matrix[m] optional_varied_in_reduction_variable_matrix[mr]
      metaformula[y] {
      size_type k = (size_type)ref_cast<integer&>($k.object);

      if (k < 1)
        k = 2;
      else
        k += 2;

      ref<inference> i(make, ref<formula>($y.object), ref<formula>($x.object), metalevel_t(k));

      inference* mp = ref_cast<inference*>($m.object);
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = ref_cast<inference*>($mr.object);
      if (mrp != nullptr)
        i->varied_in_reduction_ = mrp->varied_in_reduction_;


      // Check that varied and invariable indices given do not exceed
      // exceed the conclusion (head) and premise (body) sizes:

      formula_sequence* hp = ref_cast<formula_sequence*>(i->head_);
      size_type n_head = (hp == nullptr)? 1 : hp->formulas_.size();

      formula_sequence* bp = ref_cast<formula_sequence*>(i->body_);
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

      $$.object = i;
    }
/*
  | metaformula[x] "⊢" superscript_natural_number_value[k] metaformula[y] {
      size_type k = (size_type)ref_cast<integer&>($k.object);

      if (k < 1)
        throw syntax_error(@x,
          "inference ⊢" + $k.text + ": metalevel " + std::to_string(k) + " < 1.");

      $$.object =
        ref<inference>(make, ref<formula>($y.object), ref<formula>($x.object), metalevel_t(k));
    }
*/
  | metaformula[x] "⊢" optional_superscript_natural_number_value[k]
      optional_varied_variable_matrix[m] optional_varied_in_reduction_variable_matrix[mr]
      metaformula[y] {
      size_type k = (size_type)ref_cast<integer&>($k.object);

      if (k < 1)
        k = 1;

      ref<inference> i(make, ref<formula>($y.object), ref<formula>($x.object), metalevel_t(k));

      inference* mp = ref_cast<inference*>($m.object);
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = ref_cast<inference*>($mr.object);
      if (mrp != nullptr)
        i->varied_in_reduction_ = mrp->varied_in_reduction_;


      // Check that varied and invariable indices given do not exceed
      // exceed the conclusion (head) and premise (body) sizes:

      formula_sequence* hp = ref_cast<formula_sequence*>(i->head_);
      size_type n_head = (hp == nullptr)? 1 : hp->formulas_.size();

      formula_sequence* bp = ref_cast<formula_sequence*>(i->body_);
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

      $$.object = i;
    }
/*
  | metaformula[x] "⊢" metaformula[y] {
      ref<inference> i(make, ref<formula>($y.object), ref<formula>($x.object), 1_ml);

      $$.object = i;
    }
*/
  | "⊢" metaformula[x] { $$.object = ref<inference>(make, ref<formula>($x.object)); }

  | "(" pure_metaformula[x] ")" { $$.object = $x.object; }
  | simple_metaformula[x] metaformula_substitution_sequence[y] {
      $$.object = ref<substitution_formula>(make, ref<substitution>($y.object), ref<formula>($x.object)); }
;


optional_varied_variable_matrix:
    %empty
  | "⁽" varied_variable_conclusions[cs] "⁾" { $$.object = $cs.object; }
  | "⁽" varied_variable_premises[ps] "⁾"    { $$.object = $ps.object; }
  | "⁽" varied_variable_set[vs] "⁾"         { $$.object = $vs.object; }
;

varied_variable_conclusions:
    varied_variable_conclusion
  | varied_variable_conclusions[xs] ";" varied_variable_conclusion[x] {
      inference& xs = ref_cast<inference&>($xs.object);
      inference& x = ref_cast<inference&>($x.object);

      for (auto& i: x.varied_)
        for (auto& j: i.second)
          xs.varied_[i.first][j.first].insert(j.second.begin(), j.second.end());

      $$.object = $xs.object;
    }
;

varied_variable_conclusion:
    superscript_natural_number_value[k] varied_variable_premises[xs] {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>($xs.object);
      size_type k = (size_type)ref_cast<integer&>($k.object);

      i->varied_[k].insert(xs.varied_[0].begin(), xs.varied_[0].end());
      $$.object = i;

    }
;

varied_variable_premises:
    varied_variable_premise
  | varied_variable_premises[xs] "," varied_variable_premise[x] {
      inference& xs = ref_cast<inference&>($xs.object);
      inference& x = ref_cast<inference&>($x.object);

      for (auto& j: x.varied_[0])
        xs.varied_[0][j.first].insert(j.second.begin(), j.second.end());

      $$.object = $xs.object;
    }
;

varied_variable_premise:
    superscript_natural_number_value[k] varied_variable_set[xs] {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>($xs.object);
      size_type k = (size_type)ref_cast<integer&>($k.object);

      i->varied_[0][k].insert(xs.varied_[0][0].begin(), xs.varied_[0][0].end());

      $$.object = i;
    }
;

varied_variable_set:
    varied_variable
  | varied_variable_set[xs] varied_variable[x] {
      inference& xs = ref_cast<inference&>($xs.object);
      inference& x = ref_cast<inference&>($x.object);

      xs.varied_[0][0].insert(x.varied_[0][0].begin(), x.varied_[0][0].end());

      $$.object = $xs.object;
    }
;

varied_variable:
    object_variable[x] {
      ref<inference> i(make);
      i->varied_[0][0].insert($x.object);
      $$.object = i;
    }
  | metaformula_variable[x] {
      ref<inference> i(make);
      i->varied_[0][0].insert($x.object);
      $$.object = i;
    }
;



optional_varied_in_reduction_variable_matrix:
    %empty
  | "₍" varied_in_reduction_variable_conclusions[cs] "₎" { $$.object = $cs.object; }
  | "₍" varied_in_reduction_variable_premises[ps] "₎"    { $$.object = $ps.object; }
  | "₍" varied_in_reduction_variable_set[vs] "₎"         { $$.object = $vs.object; }
;

varied_in_reduction_variable_conclusions:
    varied_in_reduction_variable_conclusion
  | varied_in_reduction_variable_conclusions[xs] ";" varied_in_reduction_variable_conclusion[x] {
      inference& xs = ref_cast<inference&>($xs.object);
      inference& x = ref_cast<inference&>($x.object);

      for (auto& i: x.varied_in_reduction_)
        for (auto& j: i.second)
          xs.varied_in_reduction_[i.first][j.first].insert(j.second.begin(), j.second.end());

      $$.object = $xs.object;
    }
;

varied_in_reduction_variable_conclusion:
    subscript_natural_number_value[k] varied_in_reduction_variable_premises[xs] {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>($xs.object);
      size_type k = (size_type)ref_cast<integer&>($k.object);

      i->varied_in_reduction_[k].insert(xs.varied_in_reduction_[0].begin(), xs.varied_in_reduction_[0].end());
      $$.object = i;

    }
;

varied_in_reduction_variable_premises:
    varied_in_reduction_variable_premise
  | varied_in_reduction_variable_premises[xs] "," varied_in_reduction_variable_premise[x] {
      inference& xs = ref_cast<inference&>($xs.object);
      inference& x = ref_cast<inference&>($x.object);

      for (auto& j: x.varied_in_reduction_[0])
        xs.varied_in_reduction_[0][j.first].insert(j.second.begin(), j.second.end());

      $$.object = $xs.object;
    }
;

varied_in_reduction_variable_premise:
    subscript_natural_number_value[k] varied_in_reduction_variable_set[xs] {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>($xs.object);
      size_type k = (size_type)ref_cast<integer&>($k.object);

      i->varied_in_reduction_[0][k].insert(xs.varied_in_reduction_[0][0].begin(), xs.varied_in_reduction_[0][0].end());

      $$.object = i;
    }
;

varied_in_reduction_variable_set:
    varied_in_reduction_variable
  | varied_in_reduction_variable_set[xs] varied_in_reduction_variable[x] {
      inference& xs = ref_cast<inference&>($xs.object);
      inference& x = ref_cast<inference&>($x.object);

      xs.varied_in_reduction_[0][0].insert(x.varied_in_reduction_[0][0].begin(), x.varied_in_reduction_[0][0].end());

      $$.object = $xs.object;
    }
;

varied_in_reduction_variable:
    object_variable[x] {
      ref<inference> i(make);
      i->varied_in_reduction_[0][0].insert($x.object);
      $$.object = i;
    }
  | metaformula_variable[x] {
      ref<inference> i(make);
      i->varied_in_reduction_[0][0].insert($x.object);
      $$.object = i;
    }
;


/*
optional_varied_in_reduction_variable_sequence:
    %empty
  | "₍" varied_in_reduction_variable_conclusions[ps] "₎"    { $$.object = $ps.object; }
  | "₍" varied_in_reduction_variable_set[vs] "₎"         { $$.object = $vs.object; }
;

varied_in_reduction_variable_conclusions:
    varied_in_reduction_variable_conclusion
  | varied_in_reduction_variable_conclusion[xs] "," varied_in_reduction_variable_conclusion[x] {
      inference& xs = ref_cast<inference&>($xs.object);
      inference& x = ref_cast<inference&>($x.object);

      for (auto& j: x.varied_in_reduction_)
        xs.varied_in_reduction_[j.first].insert(j.second.begin(), j.second.end());

      $$.object = $xs.object;
    }
;

varied_in_reduction_variable_conclusion:
    subscript_natural_number_value[k] varied_in_reduction_variable_set[xs] {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>($xs.object);
      size_type k = (size_type)ref_cast<integer&>($k.object);

      i->varied_in_reduction_[k].insert(xs.varied_in_reduction_[0].begin(), xs.varied_in_reduction_[0].end());

      $$.object = i;
    }
;

varied_in_reduction_variable_set:
    varied_in_reduction_variable
  | varied_in_reduction_variable_set[xs] varied_in_reduction_variable[x] {
      inference& xs = ref_cast<inference&>($xs.object);
      inference& x = ref_cast<inference&>($x.object);

      xs.varied_in_reduction_[0].insert(x.varied_in_reduction_[0].begin(), x.varied_in_reduction_[0].end());

      $$.object = $xs.object;
    }
;

varied_in_reduction_variable:
    object_variable[x] {
      ref<inference> i(make);
      i->varied_in_reduction_[0].insert($x.object);
      $$.object = i;
    }
  | metaformula_variable[x] {
      ref<inference> i(make);
      i->varied_in_reduction_[0].insert($x.object);
      $$.object = i;
    }
;
*/


simple_metaformula:
    metaformula_variable[x] { $$.object = $x.object; }
  | "(" pure_metaformula[x] ")" { $$.object = $x.object; }
;


atomic_metaformula:
    metaformula_variable[x] { $$.object = $x.object; }
  | metapredicate[x] { $$.object = $x.object; }
;


special_metaformula:
/*
  |  "fail"[x] { $$.object = ref<succeed_fail>(make, false); }
  | "succeed"[x] { $$.object = ref<succeed_fail>(make, true); }
   meta_object_free[x] "≡" meta_object_free[y] {
      $$.object = ref<objectidentical>(make, ref<variable>($x.object), ref<variable>($y.object), true);
    }
*/
    meta_object_free[x] "≢" meta_object_free[y] {
      $$.object = ref<objectidentical>(make, ref<variable>($x.object), ref<variable>($y.object), false);
    }
  | meta_object_free[x] "free in" object_formula[y] {
      $$.object = ref<free_in_object>(make, ref<variable>($x.object), ref<formula>($y.object), true);
    }
  | meta_object_free[x] "free in" term[y] {
      $$.object = ref<free_in_object>(make, ref<variable>($x.object), ref<formula>($y.object), true);
    }
  | meta_object_free[x] "not" "free in" object_formula[y] {
      $$.object = ref<free_in_object>(make, ref<variable>($x.object), ref<formula>($y.object), false);
    }
  | meta_object_free[x] "not" "free in" term[y] {
      $$.object = ref<free_in_object>(make, ref<variable>($x.object), ref<formula>($y.object), false);
    }
  | term[x] "free for" meta_object_free[y] "in" object_formula[z] {
      $$.object = ref<free_for_object>(make, 
        ref<formula>($x.object), ref<variable>($y.object), ref<formula>($z.object), true);
    }
  | term[x] "free for" meta_object_free[y] "in" term[z] {
      $$.object = ref<free_for_object>(make, 
        ref<formula>($x.object), ref<variable>($y.object), ref<formula>($z.object), true);
    }
;


meta_object_free:
    object_variable[x] { $$.object = $x.object; }
;


metapredicate:
    metapredicate_function[x] { $$.object = $x.object; }
  | object_formula[x] "≣" object_formula[y] {
      $$.object = ref<identical>(make, ref<formula>($x.object), ref<formula>($y.object), true);
    }
  | object_formula[x] "≣̷" object_formula[y] {
      $$.object = ref<identical>(make, ref<formula>($x.object), ref<formula>($y.object), false);
    }
  | term[x] "≣" term[y] {
      $$.object = ref<identical>(make, ref<formula>($x.object), ref<formula>($y.object), true);
    }
  | term[x] "≣̷" term[y] {
      $$.object = ref<identical>(make, ref<formula>($x.object), ref<formula>($y.object), false);
    }
;


metapredicate_function:
    metapredicate_constant[x] metapredicate_argument[y] {
      $$.object = ref<structure>(make, ref<formula>($x.object), ref<formula>($y.object),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
  | metaformula_variable[x] metapredicate_argument[y] {
      $$.object = ref<structure>(make, ref<formula>($x.object), ref<formula>($y.object),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
;


metapredicate_argument:
    "(" metapredicate_argument_body[x] ")" { $$.object = $x.object; }
;


metapredicate_argument_body:
    object_formula[x] {
      ref<sequence> vr(make, sequence::tuple);
      $$.object = vr;
      vr->push_back(ref<formula>($x.object)); }
  | metapredicate_argument_body[x] "," object_formula[y] {
      $$.object = $x.object;
      sequence& vr = ref_cast<sequence&>($$.object);
      vr.push_back(ref<formula>($y.object)); }
;


object_formula:
    atomic_formula[x] { $$.object = $x.object; }
  | very_simple_formula[x] formula_substitution_sequence[y] {
      $$.object = ref<substitution_formula>(make, ref<substitution>($y.object), ref<formula>($x.object));
    }
  | predicate_function_application[x] { $$.object = $x.object; }
  | logic_formula[x] { $$.object = $x.object; }
  | "(" object_formula[x] ")" { $$.object = $x.object; }
  | quantized_formula[x] { $$.object = $x.object; }
  | hoare_triple {}
;


hoare_triple:
  "{" object_formula "}" code_sequence "{" object_formula "}" { $$.object = ref<formula>(); }
;

/*
code:
    %empty {}
  | code_statement {}
;
*/

code_statement:
    code_term {}
  | "{" code_sequence  "}"
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
    object_formula_variable[x] { $$.object = $x.object; }
  | atom_variable[x] { $$.object = $x.object; }
  | "(" object_formula[x] ")" { $$.object = $x.object; }
;


quantized_formula:
    quantizer_declaration[x] quantized_body[y] {
      symbol_table.pop_level();
      variable_list& vsr = ref_cast<variable_list&>($x.object);
      $$.object = ref<bound_formula>(make, vsr, ref<formula>($y.object));
    }
  | quantizer_declaration[x] optional_in_term[s] ":" object_formula[y] {
      symbol_table.pop_level();
      variable_list& vsr = ref_cast<variable_list&>($x.object);
      $$.object = ref<bound_formula>(make, vsr, $s.object, ref<formula>($y.object));
    }
  | quantizer_declaration[x] optional_in_term[s] quantized_formula[y] {
      symbol_table.pop_level();
      variable_list& vsr = ref_cast<variable_list&>($x.object);
      $$.object = ref<bound_formula>(make, vsr, $s.object, ref<formula>($y.object));
    }
;


simple_formula:
    object_formula_variable[x] { $$.object = $x.object; }
  | atom_variable[x] { $$.object = $x.object; }
  | predicate_expression[x] { $$.object = $x.object; }
  | "(" object_formula[x] ")" { $$.object = $x.object; }
  | quantized_formula[x] { $$.object = $x.object; }
;


// No quantizer or logic in top level.
quantized_body:
    atomic_formula[x] { $$.object = $x.object; }
  | "(" object_formula[x] ")" { $$.object = $x.object; }
;

atomic_formula:
    atom_constant[x] { $$.object = $x.object; }
  | object_formula_variable[x] { $$.object = $x.object; }
  | atom_variable[x] { $$.object = $x.object; }
  | predicate[x] { $$.object = $x.object; }
;


    /* Predicates */
predicate:
    predicate_expression[x] { $$.object = $x.object; }
  | term[x] "="[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, equal_oprec, $x.object, $y.object); }
  | term[x] "≠"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, not_equal_oprec, $x.object, $y.object); }

  /* Divisibility */
  | term[x] "∣"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, equal_oprec, $x.object, $y.object); }
  | term[x] "∤"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, not_equal_oprec, $x.object, $y.object); }

  /* Inequalities and their negations. */
  | term[x] "<"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, less_oprec, $x.object, $y.object); }
  | term[x] ">"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, greater_oprec, $x.object, $y.object); }
  | term[x] "≤"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, less_or_equal_oprec, $x.object, $y.object); }
  | term[x] "≥"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, greater_or_equal_oprec, $x.object, $y.object); }
  | term[x] "≮"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, not_less_oprec, $x.object, $y.object); }
  | term[x] "≯"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, not_greater_oprec, $x.object, $y.object); }
  | term[x] "≰"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, not_less_or_equal_oprec, $x.object, $y.object); }
  | term[x] "≱"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, not_greater_or_equal_oprec, $x.object, $y.object); }
  /* Set predicates. */
  | term[x] "∈"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, in_oprec, $x.object, $y.object); }
  | term[x] "∉"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, not_in_oprec, $x.object, $y.object); }
  | term[x] "⊆"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, subset_oprec, $x.object, $y.object); }
  | term[x] "⊊"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, proper_subset_oprec, $x.object, $y.object); }
  | term[x] "⊇"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, superset_oprec, $x.object, $y.object); }
  | term[x] "⊋"[a] term[y] { $$.object = ref<structure>(make, $a.text, structure::predicate, 0_ml, structure::infix, proper_superset_oprec, $x.object, $y.object); }
  | "Set" { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
    "₍" is_set_variable[x] "₎" { bound_variable_type = free_variable_context; }
     simple_formula[y] {
      symbol_table.pop_level();
      $$.object = ref<bound_formula>(make,
        ref<variable>($x.object), ref<formula>($y.object), bound_formula::is_set_);
    }
;


predicate_expression:
    predicate_identifier[x] tuple[y] {
      $$.object = ref<structure>(make, ref<formula>($x.object), ref<formula>($y.object),
        structure::predicate, 0_ml, structure::postargument, precedence_t());
    }
;


predicate_identifier:
    predicate_constant[x] { $$.object = $x.object;  }
  | predicate_variable[x] { $$.object = $x.object;  }
;


optional_superscript_natural_number_value:
    %empty { $$.object = ref<mli::integer>(make); $$.text = ""; }
  | superscript_natural_number_value
;

/*
optional_subscript_natural_number_value:
    %empty { $$.object = ref<mli::integer>(make); $$.text = ""; }
  | subscript_natural_number_value
;
*/

    /* Logic */
logic_formula:
    "¬"[a] optional_superscript_natural_number_value[k] object_formula[x] {
      size_type k = (size_type)ref_cast<integer&>($k.object);

      $$.object = ref<structure>(make, $a.text, structure::logic, metalevel_t(k),
        structure::prefix, logical_not_oprec, $x.object);
    }
  | object_formula[x] "∨"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)ref_cast<integer&>($k.object);

      $$.object = ref<structure>(make, $a.text, structure::logic, metalevel_t(k),
        structure::infix, logical_or_oprec, $x.object, $y.object);
    }
  | object_formula[x] "∧"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)ref_cast<integer&>($k.object);

      $$.object = ref<structure>(make, $a.text, structure::logic, metalevel_t(k),
        structure::infix, logical_and_oprec, $x.object, $y.object);
    }
  | object_formula[x] "⇒"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)ref_cast<integer&>($k.object);

      $$.object = ref<structure>(make, $a.text, structure::logic, metalevel_t(k),
        structure::infix, implies_oprec, $x.object, $y.object);
    }
  | object_formula[x] "⇐"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)ref_cast<integer&>($k.object);

      $$.object = ref<structure>(make, $a.text, structure::logic, metalevel_t(k),
        structure::infix, impliedby_oprec, $x.object, $y.object);
    }
  | object_formula[x] "⇔"[a] optional_superscript_natural_number_value[k] object_formula[y] {
      size_type k = (size_type)ref_cast<integer&>($k.object);

      $$.object = ref<structure>(make, $a.text, structure::logic, metalevel_t(k),
        structure::infix, equivalent_oprec, $x.object, $y.object);
    }
  | prefix_logic_formula[x] { $$.object = $x.object;  }
;


prefix_logic_formula:
    prefix_formula_variable[x] { $$.object = $x.object; }
  | prefix_not_key[a] prefix_logic_formula[x] {
      $$.object = ref<structure>(make, "¬", structure::logic, 0_ml,
        structure::prefix, logical_not_oprec, $x.object);
    }
  | prefix_or_key[a] prefix_logic_formula[x] prefix_logic_formula[y] {
      $$.object = ref<structure>(make, "∨", structure::logic, 0_ml,
        structure::infix, logical_or_oprec, $x.object, $y.object);
    }
  | prefix_and_key[a] prefix_logic_formula[x] prefix_logic_formula[y] {
      $$.object = ref<structure>(make, "∧", structure::logic, 0_ml,
        structure::infix, logical_and_oprec, $x.object, $y.object);
    }
  | prefix_implies_key[a] prefix_logic_formula[x] prefix_logic_formula[y] {
      $$.object = ref<structure>(make, "⇒", structure::logic, 0_ml,
        structure::infix, implies_oprec, $x.object, $y.object);
    }
  | prefix_equivalent_key[a] prefix_logic_formula[x] prefix_logic_formula[y] {
      $$.object = ref<structure>(make, "⇔", structure::logic, 0_ml,
        structure::infix, equivalent_oprec, $x.object, $y.object);
 }
;


quantizer_declaration:
    quantized_variable_list[x] { $$.object = $x.object; }
;

quantized_variable_list:
    all_variable_list[x] { $$.object = $x.object; }
  | exist_variable_list[x] { $$.object = $x.object; }
;


all_variable_list:
    "∀" all_identifier_list[x] { $$.object = $x.object; }
;


exist_variable_list:
    "∃" exist_identifier_list[x] { $$.object = $x.object; }
;


all_identifier_list:
    all_variable[x] {
      bound_variable_type = free_variable_context;
      $$.object = ref<variable_list>(make, ref<variable>($x.object), bound_formula::all_);
    }
  | all_identifier_list[x] { bound_variable_type = token::all_variable; }
      "," all_variable[y] {
      bound_variable_type = free_variable_context;
      $$.object = $x.object;
      ref_cast<variable_list&>($$.object).push_back(ref<variable>($y.object), bound_formula::all_);
    }
;


exist_identifier_list:
    exist_variable[x] {
      bound_variable_type = free_variable_context;
      $$.object = ref<variable_list>(make, ref<variable>($x.object), bound_formula::exist_);
    }
  | exist_identifier_list[x] { bound_variable_type = database_parser::token::exist_variable; }
      "," exist_variable[y] {
      bound_variable_type = free_variable_context;
      $$.object = $x.object;
      ref_cast<variable_list&>($$.object).push_back(ref<variable>($y.object), bound_formula::exist_);
    }
;


// Specifying domain 𝒙 ∈ 𝑆 for binders:
optional_in_term:
    %empty { $$.object = ref<formula>(make); }
  | "∈" term[s] { $$.object = $s.object; }
;


    /* Terms */

tuple:
    "(" tuple_body[x] ")" { $$.object = $x.object; }
;


tuple_body:
    term[x] {
      ref<sequence> vr(make, sequence::tuple);
      $$.object = vr;
      vr->push_back(ref<formula>($x.object));
    }
  | tuple_body[x] "," term[y] {
      $$.object = $x.object;
      sequence& vr = ref_cast<sequence&>($$.object);
      vr.push_back(ref<formula>($y.object));
    }
;


term:
    simple_term[x] { $$.object = $x.object; }
  | function_term[x] { $$.object = $x.object; }
  | simple_term[x] term_substitution_sequence[y] {
      $$.object = ref<substitution_formula>(make, ref<substitution>($y.object), ref<formula>($x.object));
    }
  | set_term[x] { $$.object = $x.object; }
;


simple_term:
    term_constant[x]   { $$.object = $x.object; }
  | "natural number value"[x] { $$.object = $x.object; }
  | "integer value"[x] { $$.object = $x.object; }
  | term_identifier[x] { $$.object = $x.object; }
  | "(" term[x] ")"    { $$.object = $x.object; }
;


term_identifier:
    object_variable[x] variable_exclusion_set[vs]   {
      ref<variable> xr = $x.object;
      ref<variable> vr = $vs.object;
      xr->excluded_.insert(vr->excluded_.begin(), vr->excluded_.end());
      $$.object = $x.object;
    }
  | function_variable[x]  { $$.object = $x.object; }
  | function_map_variable[x]  { $$.object = $x.object; }
  | all_variable[x]       { $$.object = $x.object; }
  | exist_variable[x]     { $$.object = $x.object; }
  | is_set_variable[x]    { $$.object = $x.object; }
  | set_variable[x]       { $$.object = $x.object; }
  | implicit_set_variable[x] { $$.object = $x.object; }
;


variable_exclusion_set:
    %empty { $$.object = ref<variable>(make);  }
  | "ₓ" "₍" variable_exclusion_list[vs] "₎" { $$.object = $vs.object; }
;


variable_exclusion_list:
    bound_variable[x] { ref<variable> vr(make); vr->excluded_.insert($x.object); $$.object = vr; }
  | variable_exclusion_list[vs] bound_variable [x] {
      ref<variable> vr = $vs.object;
      vr->excluded_.insert($x.object);
      $$.object = vr;
    }
;


bound_variable:
    all_variable[x]       { $$.object = $x.object; }
  | exist_variable[x]     { $$.object = $x.object; }
  | is_set_variable[x]    { $$.object = $x.object; }
  | set_variable[x]       { $$.object = $x.object; }
  | implicit_set_variable[x] { $$.object = $x.object; }
;


function_term:
    function_term_identifier[x] tuple[y] {
      $$.object = ref<structure>(make, ref<formula>($x.object), ref<formula>($y.object),
        structure::function, 0_ml, structure::postargument, precedence_t()); }
  | term_function_application[x] { $$.object = $x.object; }
  | term[x] "!"[a] {
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::postfix, factorial_oprec, $x.object);
    }
  | term[x] "+"[a] term[y] { // $$.object = ref<integer_addition>(make, ref<formula>($x.object), ref<formula>($y.object));
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::infix, plus_oprec, $x.object, $y.object);
    }
  | term[x] "-"[a] term[y] { // $$.object = ref<integer_addition>(make, ref<formula>($x.object), ref<integer_negative>(make, ref<formula>($y.object)));
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::infix, minus_oprec, $x.object, $y.object);
    }
  | "-"[a] term[x]  %prec unary_minus { // $$.object = ref<integer_negative>(make, ref<formula>($x.object)); }
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::prefix, unary_minus_oprec, $x.object);
    }
  | term[x] "⋅"[a] term[y] {
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::infix, mult_oprec, $x.object, $y.object);
    }
  | term[x] "/"[a] term[y] {
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::infix, divide_oprec, $x.object, $y.object);
    }
;


set_term:
    "{" "}" { $$.object = ref<sequence>(make, sequence::member_list_set); }
  | "∅" { $$.object = ref<constant>(make, "∅", constant::object); }
  | "{" set_member_list[x] "}" { $$.object = $x.object; }
  | "{" set_variable_definition[x] optional_in_term[s] "|" object_formula[y] "}" {
      symbol_table.pop_level();
      $$.object = ref<bound_formula>(make, $x.object, $s.object, $y.object, bound_formula::set_);
    }
  | "{" "₍" implicit_set_identifier_list[x] optional_in_term[s] "₎" term[y] "|" object_formula[z] "}" {
      symbol_table.pop_level();
      variable_list& vs = ref_cast<variable_list&>($x.object);
      ref<sequence> sp(make, ref<formula>($y.object), sequence::implicit_set);
      sp->push_back(ref<formula>($z.object));
      $$.object =
        ref<bound_formula>(make, vs, $s.object, ref<formula>(sp));
    }
  | term[x] "∪"[a] term[y] {
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::infix, set_union_oprec, $x.object, $y.object);
    }
  | term[x] "∩"[a] term[y] {
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::infix, set_intersection_oprec, $x.object, $y.object);
    }
  | term[x] "∖"[a] term[y] {
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::infix, set_difference_oprec, $x.object, $y.object);
    }
  | "∁"[a] term[x] {
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::prefix, set_complement_oprec, $x.object);
    }
  | "⋃"[a] term[x] { /* prefix union operator  */
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::prefix, set_union_operator_oprec, $x.object);
    }
  | "∩"[a] term[x] { /* prefix intersection operator  */
      $$.object = ref<structure>(make, $a.text, structure::function, 0_ml,
        structure::prefix, set_intersection_operator_oprec, $x.object);
    }
;


implicit_set_identifier_list:
    { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
    is_set_variable[x] {
      bound_variable_type = free_variable_context;
      $$.object = ref<variable_list>(make, ref<variable>($x.object), bound_formula::implicit_set);
    }
  | implicit_set_identifier_list[x] { bound_variable_type = database_parser::token::is_set_variable; }
      "," is_set_variable[y] {
      bound_variable_type = free_variable_context;
      $$.object = $x.object;
      ref_cast<variable_list&>($$.object).push_back(ref<variable>($y.object), bound_formula::implicit_set);
    }
;


set_member_list:
    term[x] {
      ref<sequence> vr(make, sequence::member_list_set);
      $$.object = vr;
      vr->push_back(ref<formula>($x.object)); }
  | set_member_list[x] "," term[y] {
      $$.object = $x.object;
      sequence& vr = ref_cast<sequence&>($$.object);
      vr.push_back(ref<formula>($y.object));
    }
;


function_term_identifier:
    function_constant[x] { $$.object = $x.object; }
  | function_variable[x] { $$.object = $x.object; }
;


%%

  extern std::istream::pos_type line_position;

namespace mli {

  void database_parser::error(const location_type& loc, const std::string& errstr) {
    diagnostic(loc, errstr, mlilex.in(), line_position);
  }


  void theory_database::read(std::istream& is) {
    mli::database_lexer lex(is, std::cout);

    mli::database_parser p(*this, lex);

    if (p.parse() != 0)
      is.setstate(std::ios::failbit);
    else
      is.clear(is.rdstate() & ~(std::ios::failbit | std::ios::badbit));
  }

} // namespace mli

