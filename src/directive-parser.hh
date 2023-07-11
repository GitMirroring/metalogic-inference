// A Bison parser, made by GNU Bison 3.8.2.

// Skeleton interface for Bison LALR(1) parsers in C++

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


/**
 ** \file ../../mli-root/src/directive-parser.hh
 ** Define the mli::parser class.
 */

// C++ LALR(1) parser skeleton written by Akim Demaille.

// DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
// especially those whose name start with YY_ or yy_.  They are
// private implementation details that can be changed or removed.

#ifndef YY_MLI_MLI_ROOT_SRC_DIRECTIVE_PARSER_HH_INCLUDED
# define YY_MLI_MLI_ROOT_SRC_DIRECTIVE_PARSER_HH_INCLUDED
// "%code requires" blocks.
#line 41 "../../mli-root/src/directive-parser.yy"

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


#line 98 "../../mli-root/src/directive-parser.hh"


# include <cstdlib> // std::abort
# include <iostream>
# include <stdexcept>
# include <string>
# include <vector>

#if defined __cplusplus
# define YY_CPLUSPLUS __cplusplus
#else
# define YY_CPLUSPLUS 199711L
#endif

// Support move semantics when possible.
#if 201103L <= YY_CPLUSPLUS
# define YY_MOVE           std::move
# define YY_MOVE_OR_COPY   move
# define YY_MOVE_REF(Type) Type&&
# define YY_RVREF(Type)    Type&&
# define YY_COPY(Type)     Type
#else
# define YY_MOVE
# define YY_MOVE_OR_COPY   copy
# define YY_MOVE_REF(Type) Type&
# define YY_RVREF(Type)    const Type&
# define YY_COPY(Type)     const Type&
#endif

// Support noexcept when possible.
#if 201103L <= YY_CPLUSPLUS
# define YY_NOEXCEPT noexcept
# define YY_NOTHROW
#else
# define YY_NOEXCEPT
# define YY_NOTHROW throw ()
#endif

// Support constexpr when possible.
#if 201703 <= YY_CPLUSPLUS
# define YY_CONSTEXPR constexpr
#else
# define YY_CONSTEXPR
#endif



#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

/* Debug traces.  */
#ifndef MLIDEBUG
# if defined YYDEBUG
#if YYDEBUG
#   define MLIDEBUG 1
#  else
#   define MLIDEBUG 0
#  endif
# else /* ! defined YYDEBUG */
#  define MLIDEBUG 1
# endif /* ! defined YYDEBUG */
#endif  /* ! defined MLIDEBUG */

#line 22 "../../mli-root/src/directive-parser.yy"
namespace mli {
#line 242 "../../mli-root/src/directive-parser.hh"




  /// A Bison parser.
  class directive_parser
  {
  public:
#ifdef MLISTYPE
# ifdef __GNUC__
#  pragma GCC message "bison: do not #define MLISTYPE in C++, use %define api.value.type"
# endif
    typedef MLISTYPE value_type;
#else
    /// Symbol semantic values.
    typedef mli::semantic_type value_type;
#endif
    /// Backward compatibility (Bison 3.8).
    typedef value_type semantic_type;

    /// Symbol locations.
    typedef location_t location_type;

    /// Syntax errors thrown from user actions.
    struct syntax_error : std::runtime_error
    {
      syntax_error (const location_type& l, const std::string& m)
        : std::runtime_error (m)
        , location (l)
      {}

      syntax_error (const syntax_error& s)
        : std::runtime_error (s.what ())
        , location (s.location)
      {}

      ~syntax_error () YY_NOEXCEPT YY_NOTHROW;

      location_type location;
    };

    /// Token kinds.
    struct token
    {
      enum token_kind_type
      {
        MLIEMPTY = -2,
    MLIEOF = 0,                    // "end of file"
    MLIerror = 256,                // error
    MLIUNDEF = 257,                // "invalid token"
    token_error = 258,             // "token error"
    diagnostic_key = 259,          // "diagnostic"
    ignored_key = 260,             // "ignored"
    warning_key = 261,             // "warning"
    error_key = 262,               // "error"
    unused_variable_key = 263,     // "unused variable"
    unused_key = 264,              // "unused"
    variable_key = 265,            // "variable"
    type_key = 266,                // "type"
    label_key = 267,               // "label"
    all_key = 268,                 // "all"
    none_key = 269,                // "none"
    no_key = 270,                  // "no"
    use_key = 271,                 // "use"
    count_key = 272,               // "count"
    max_key = 273,                 // "max"
    level_key = 274,               // "level"
    sublevel_key = 275,            // "sublevel"
    proof_key = 276,               // "proof"
    conditional_key = 277,         // "conditional"
    strict_key = 278,              // "strict"
    logic_key = 279,               // "logic"
    false_elimination_key = 280,   // "-𝕗"
    false_introduction_key = 281,  // "+𝕗"
    negation_elimination_key = 282, // "-¬"
    negation_elimination_in_premise_key = 283, // "-¬⊢"
    double_negation_elimination_key = 284, // "-¬¬"
    double_negation_elimination_in_premise_key = 285, // "-¬¬⊢"
    double_negation_introduction_key = 286, // "+¬¬"
    double_negation_introduction_in_premise_key = 287, // "+¬¬⊢"
    implication_elimination_key = 288, // "-⇒"
    implication_elimination_in_premise_key = 289, // "-⇒⊢"
    conjunction_elimination_key = 290, // "-∧"
    conjunction_elimination_in_premise_key = 291, // "-∧⊢"
    disjunction_elimination_key = 292, // "-∨"
    disjunction_elimination_in_premise_key = 293, // "-∨⊢"
    trace_key = 294,               // "trace"
    untrace_key = 295,             // "untrace"
    null_key = 296,                // "null"
    empty_key = 297,               // "empty"
    result_key = 298,              // "result"
    solve_key = 299,               // "solve"
    prooftree_key = 300,           // "prooftree"
    unify_key = 301,               // "unify"
    split_key = 302,               // "split"
    substitute_key = 303,          // "substitute"
    statement_key = 304,           // "statement"
    database_key = 305,            // "database"
    formula_key = 306,             // "formula"
    unspecializable_key = 307,     // "unspecializable"
    structure_key = 308,           // "structure"
    thread_key = 309,              // "thread"
    natural_number_value = 310,    // "natural number value"
    integer_value = 311,           // "integer value"
    include_key = 312,             // "include"
    end_key = 313,                 // "end"
    plain_name = 314,              // "name"
    metapredicate_constant = 315,  // "metapredicate constant"
    predicate_constant = 316,      // "predicate constant"
    atom_constant = 317,           // "atom constant"
    function_constant = 318,       // "function constant"
    term_constant = 319,           // "term constant"
    metaformula_variable = 320,    // "metaformula variable"
    object_formula_variable = 321, // "object formula variable"
    predicate_variable = 322,      // "predicate variable"
    atom_variable = 323,           // "atom variable"
    prefix_formula_variable = 324, // "prefix formula variable"
    function_variable = 325,       // "function variable"
    constant_variable = 326,       // "constant variable"
    object_variable = 327,         // "object variable"
    code_variable = 328,           // "code variable"
    all_variable = 329,            // "all variable"
    exist_variable = 330,          // "exist variable"
    is_set_variable = 331,         // "Set variable"
    set_variable = 332,            // "set variable"
    set_variable_definition = 333, // "set variable definition"
    implicit_set_variable = 334,   // "implicit set variable"
    identifier_constant_key = 335, // "identifier constant"
    identifier_variable_key = 336, // "identifier variable"
    exist_key = 337,               // "∃"
    logical_not_key = 338,         // "¬"
    logical_and_key = 339,         // "∧"
    logical_or_key = 340,          // "∨"
    implies_key = 341,             // "⇒"
    impliedby_key = 342,           // "⇐"
    equivalent_key = 343,          // "⇔"
    prefix_not_key = 344,          // prefix_not_key
    prefix_and_key = 345,          // prefix_and_key
    prefix_or_key = 346,           // prefix_or_key
    prefix_implies_key = 347,      // prefix_implies_key
    prefix_equivalent_key = 348,   // prefix_equivalent_key
    less_key = 349,                // "<"
    greater_key = 350,             // ">"
    less_or_equal_key = 351,       // "≤"
    greater_or_equal_key = 352,    // "≥"
    not_less_key = 353,            // "≮"
    not_greater_key = 354,         // "≯"
    not_less_or_equal_key = 355,   // "≰"
    not_greater_or_equal_key = 356, // "≱"
    equal_key = 357,               // "="
    not_equal_key = 358,           // "≠"
    mapsto_key = 359,              // "↦"
    degree_key = 360,              // "°"
    factorial_key = 361,           // "!"
    mult_key = 362,                // "⋅"
    plus_key = 363,                // "+"
    minus_key = 364,               // "-"
    is_set_key = 365,              // "Set"
    power_set_key = 366,           // "Pow"
    empty_set_key = 367,           // "∅"
    in_key = 368,                  // "∈"
    not_in_key = 369,              // "∉"
    set_complement_key = 370,      // "∁"
    set_union_key = 371,           // "∪"
    set_intersection_key = 372,    // "∩"
    set_difference_key = 373,      // "∖"
    set_union_operator_key = 374,  // "⋃"
    set_intersection_operator_key = 375, // "⋂"
    subset_key = 376,              // "⊆"
    proper_subset_key = 377,       // "⊊"
    superset_key = 378,            // "⊇"
    proper_superset_key = 379,     // "⊋"
    colon_key = 380,               // ":"
    semicolon_key = 381,           // ";"
    comma_key = 382,               // ","
    period_key = 383,              // "."
    left_parenthesis_key = 384,    // "("
    right_parenthesis_key = 385,   // ")"
    left_bracket_key = 386,        // "["
    right_bracket_key = 387,       // "]"
    left_angle_bracket_key = 388,  // "⟨"
    right_angle_bracket_key = 389, // "⟩"
    superscript_left_parenthesis_key = 390, // "⁽"
    superscript_right_parenthesis_key = 391, // "⁾"
    subscript_left_parenthesis_key = 392, // "₍"
    subscript_right_parenthesis_key = 393, // "₎"
    left_brace_key = 394,          // "{"
    vertical_line_key = 395,       // "|"
    right_brace_key = 396,         // "}"
    tilde_key = 397,               // "~"
    slash_key = 398,               // "/"
    backslash_key = 399,           // "\\"
    if_key = 400,                  // "if"
    then_key = 401,                // "then"
    else_key = 402,                // "else"
    while_key = 403,               // "while"
    do_key = 404,                  // "do"
    loop_key = 405,                // "loop"
    for_key = 406,                 // "for"
    break_key = 407,               // "break"
    continue_key = 408,            // "continue"
    throw_key = 409,               // "throw"
    try_key = 410,                 // "try"
    catch_key = 411,               // "catch"
    superscript_unsigned_integer_value = 426, // superscript_unsigned_integer_value
    unary_minus = 427              // unary_minus
      };
      /// Backward compatibility alias (Bison 3.6).
      typedef token_kind_type yytokentype;
    };

    /// Token kind, as returned by yylex.
    typedef token::token_kind_type token_kind_type;

    /// Backward compatibility alias (Bison 3.6).
    typedef token_kind_type token_type;

    /// Symbol kinds.
    struct symbol_kind
    {
      enum symbol_kind_type
      {
        YYNTOKENS = 173, ///< Number of tokens.
        S_YYEMPTY = -2,
        S_YYEOF = 0,                             // "end of file"
        S_YYerror = 1,                           // error
        S_YYUNDEF = 2,                           // "invalid token"
        S_token_error = 3,                       // "token error"
        S_diagnostic_key = 4,                    // "diagnostic"
        S_ignored_key = 5,                       // "ignored"
        S_warning_key = 6,                       // "warning"
        S_error_key = 7,                         // "error"
        S_unused_variable_key = 8,               // "unused variable"
        S_unused_key = 9,                        // "unused"
        S_variable_key = 10,                     // "variable"
        S_type_key = 11,                         // "type"
        S_label_key = 12,                        // "label"
        S_all_key = 13,                          // "all"
        S_none_key = 14,                         // "none"
        S_no_key = 15,                           // "no"
        S_use_key = 16,                          // "use"
        S_count_key = 17,                        // "count"
        S_max_key = 18,                          // "max"
        S_level_key = 19,                        // "level"
        S_sublevel_key = 20,                     // "sublevel"
        S_proof_key = 21,                        // "proof"
        S_conditional_key = 22,                  // "conditional"
        S_strict_key = 23,                       // "strict"
        S_logic_key = 24,                        // "logic"
        S_false_elimination_key = 25,            // "-𝕗"
        S_false_introduction_key = 26,           // "+𝕗"
        S_negation_elimination_key = 27,         // "-¬"
        S_negation_elimination_in_premise_key = 28, // "-¬⊢"
        S_double_negation_elimination_key = 29,  // "-¬¬"
        S_double_negation_elimination_in_premise_key = 30, // "-¬¬⊢"
        S_double_negation_introduction_key = 31, // "+¬¬"
        S_double_negation_introduction_in_premise_key = 32, // "+¬¬⊢"
        S_implication_elimination_key = 33,      // "-⇒"
        S_implication_elimination_in_premise_key = 34, // "-⇒⊢"
        S_conjunction_elimination_key = 35,      // "-∧"
        S_conjunction_elimination_in_premise_key = 36, // "-∧⊢"
        S_disjunction_elimination_key = 37,      // "-∨"
        S_disjunction_elimination_in_premise_key = 38, // "-∨⊢"
        S_trace_key = 39,                        // "trace"
        S_untrace_key = 40,                      // "untrace"
        S_null_key = 41,                         // "null"
        S_empty_key = 42,                        // "empty"
        S_result_key = 43,                       // "result"
        S_solve_key = 44,                        // "solve"
        S_prooftree_key = 45,                    // "prooftree"
        S_unify_key = 46,                        // "unify"
        S_split_key = 47,                        // "split"
        S_substitute_key = 48,                   // "substitute"
        S_statement_key = 49,                    // "statement"
        S_database_key = 50,                     // "database"
        S_formula_key = 51,                      // "formula"
        S_unspecializable_key = 52,              // "unspecializable"
        S_structure_key = 53,                    // "structure"
        S_thread_key = 54,                       // "thread"
        S_natural_number_value = 55,             // "natural number value"
        S_integer_value = 56,                    // "integer value"
        S_include_key = 57,                      // "include"
        S_end_key = 58,                          // "end"
        S_plain_name = 59,                       // "name"
        S_metapredicate_constant = 60,           // "metapredicate constant"
        S_predicate_constant = 61,               // "predicate constant"
        S_atom_constant = 62,                    // "atom constant"
        S_function_constant = 63,                // "function constant"
        S_term_constant = 64,                    // "term constant"
        S_metaformula_variable = 65,             // "metaformula variable"
        S_object_formula_variable = 66,          // "object formula variable"
        S_predicate_variable = 67,               // "predicate variable"
        S_atom_variable = 68,                    // "atom variable"
        S_prefix_formula_variable = 69,          // "prefix formula variable"
        S_function_variable = 70,                // "function variable"
        S_constant_variable = 71,                // "constant variable"
        S_object_variable = 72,                  // "object variable"
        S_code_variable = 73,                    // "code variable"
        S_all_variable = 74,                     // "all variable"
        S_exist_variable = 75,                   // "exist variable"
        S_is_set_variable = 76,                  // "Set variable"
        S_set_variable = 77,                     // "set variable"
        S_set_variable_definition = 78,          // "set variable definition"
        S_implicit_set_variable = 79,            // "implicit set variable"
        S_identifier_constant_key = 80,          // "identifier constant"
        S_identifier_variable_key = 81,          // "identifier variable"
        S_exist_key = 82,                        // "∃"
        S_logical_not_key = 83,                  // "¬"
        S_logical_and_key = 84,                  // "∧"
        S_logical_or_key = 85,                   // "∨"
        S_implies_key = 86,                      // "⇒"
        S_impliedby_key = 87,                    // "⇐"
        S_equivalent_key = 88,                   // "⇔"
        S_prefix_not_key = 89,                   // prefix_not_key
        S_prefix_and_key = 90,                   // prefix_and_key
        S_prefix_or_key = 91,                    // prefix_or_key
        S_prefix_implies_key = 92,               // prefix_implies_key
        S_prefix_equivalent_key = 93,            // prefix_equivalent_key
        S_less_key = 94,                         // "<"
        S_greater_key = 95,                      // ">"
        S_less_or_equal_key = 96,                // "≤"
        S_greater_or_equal_key = 97,             // "≥"
        S_not_less_key = 98,                     // "≮"
        S_not_greater_key = 99,                  // "≯"
        S_not_less_or_equal_key = 100,           // "≰"
        S_not_greater_or_equal_key = 101,        // "≱"
        S_equal_key = 102,                       // "="
        S_not_equal_key = 103,                   // "≠"
        S_mapsto_key = 104,                      // "↦"
        S_degree_key = 105,                      // "°"
        S_factorial_key = 106,                   // "!"
        S_mult_key = 107,                        // "⋅"
        S_plus_key = 108,                        // "+"
        S_minus_key = 109,                       // "-"
        S_is_set_key = 110,                      // "Set"
        S_power_set_key = 111,                   // "Pow"
        S_empty_set_key = 112,                   // "∅"
        S_in_key = 113,                          // "∈"
        S_not_in_key = 114,                      // "∉"
        S_set_complement_key = 115,              // "∁"
        S_set_union_key = 116,                   // "∪"
        S_set_intersection_key = 117,            // "∩"
        S_set_difference_key = 118,              // "∖"
        S_set_union_operator_key = 119,          // "⋃"
        S_set_intersection_operator_key = 120,   // "⋂"
        S_subset_key = 121,                      // "⊆"
        S_proper_subset_key = 122,               // "⊊"
        S_superset_key = 123,                    // "⊇"
        S_proper_superset_key = 124,             // "⊋"
        S_colon_key = 125,                       // ":"
        S_semicolon_key = 126,                   // ";"
        S_comma_key = 127,                       // ","
        S_period_key = 128,                      // "."
        S_left_parenthesis_key = 129,            // "("
        S_right_parenthesis_key = 130,           // ")"
        S_left_bracket_key = 131,                // "["
        S_right_bracket_key = 132,               // "]"
        S_left_angle_bracket_key = 133,          // "⟨"
        S_right_angle_bracket_key = 134,         // "⟩"
        S_superscript_left_parenthesis_key = 135, // "⁽"
        S_superscript_right_parenthesis_key = 136, // "⁾"
        S_subscript_left_parenthesis_key = 137,  // "₍"
        S_subscript_right_parenthesis_key = 138, // "₎"
        S_left_brace_key = 139,                  // "{"
        S_vertical_line_key = 140,               // "|"
        S_right_brace_key = 141,                 // "}"
        S_tilde_key = 142,                       // "~"
        S_slash_key = 143,                       // "/"
        S_backslash_key = 144,                   // "\\"
        S_if_key = 145,                          // "if"
        S_then_key = 146,                        // "then"
        S_else_key = 147,                        // "else"
        S_while_key = 148,                       // "while"
        S_do_key = 149,                          // "do"
        S_loop_key = 150,                        // "loop"
        S_for_key = 151,                         // "for"
        S_break_key = 152,                       // "break"
        S_continue_key = 153,                    // "continue"
        S_throw_key = 154,                       // "throw"
        S_try_key = 155,                         // "try"
        S_catch_key = 156,                       // "catch"
        S_157_ = 157,                            // "⊩"
        S_158_ = 158,                            // "⊣"
        S_159_ = 159,                            // "⊢"
        S_160_free_in_ = 160,                    // "free in"
        S_161_free_for_ = 161,                   // "free for"
        S_162_in_ = 162,                         // "in"
        S_163_not_ = 163,                        // "not"
        S_164_ = 164,                            // "≔"
        S_165_ = 165,                            // "≕"
        S_166_ = 166,                            // "≝"
        S_167_ = 167,                            // "≡"
        S_168_ = 168,                            // "≢"
        S_169_ = 169,                            // "≣"
        S_170_ = 170,                            // "≣̷"
        S_superscript_unsigned_integer_value = 171, // superscript_unsigned_integer_value
        S_unary_minus = 172,                     // unary_minus
        S_YYACCEPT = 173,                        // $accept
        S_file = 174,                            // file
        S_file_contents = 175,                   // file_contents
        S_command = 176,                         // command
        S_diagnostic_statement = 177,            // diagnostic_statement
        S_diagnostic_type = 178,                 // diagnostic_type
        S_diagnostic = 179,                      // diagnostic
        S_trace_statement = 180,                 // trace_statement
        S_trace_qualifier = 181,                 // trace_qualifier
        S_trace_type = 182,                      // trace_type
        S_proof_strictness = 183,                // proof_strictness
        S_limits = 184,                          // limits
        S_logic_simplification = 185,            // logic_simplification
        S_implicit_logic_simplification = 186,   // implicit_logic_simplification
        S_implicit_logic_simplification_sequence = 187, // implicit_logic_simplification_sequence
        S_implicit_logic_simplification_item = 188, // implicit_logic_simplification_item
        S_logic_qualifier = 189,                 // logic_qualifier
        S_logic_type = 190,                      // logic_type
        S_logic_name = 191,                      // logic_name
        S_conclusion_or_premise = 192,           // conclusion_or_premise
        S_integer = 193                          // integer
      };
    };

    /// (Internal) symbol kind.
    typedef symbol_kind::symbol_kind_type symbol_kind_type;

    /// The number of tokens.
    static const symbol_kind_type YYNTOKENS = symbol_kind::YYNTOKENS;

    /// A complete symbol.
    ///
    /// Expects its Base type to provide access to the symbol kind
    /// via kind ().
    ///
    /// Provide access to semantic value and location.
    template <typename Base>
    struct basic_symbol : Base
    {
      /// Alias to Base.
      typedef Base super_type;

      /// Default constructor.
      basic_symbol () YY_NOEXCEPT
        : value ()
        , location ()
      {}

#if 201103L <= YY_CPLUSPLUS
      /// Move constructor.
      basic_symbol (basic_symbol&& that)
        : Base (std::move (that))
        , value (std::move (that.value))
        , location (std::move (that.location))
      {}
#endif

      /// Copy constructor.
      basic_symbol (const basic_symbol& that);
      /// Constructor for valueless symbols.
      basic_symbol (typename Base::kind_type t,
                    YY_MOVE_REF (location_type) l);

      /// Constructor for symbols with semantic value.
      basic_symbol (typename Base::kind_type t,
                    YY_RVREF (value_type) v,
                    YY_RVREF (location_type) l);

      /// Destroy the symbol.
      ~basic_symbol ()
      {
        clear ();
      }



      /// Destroy contents, and record that is empty.
      void clear () YY_NOEXCEPT
      {
        Base::clear ();
      }

      /// The user-facing name of this symbol.
      std::string name () const YY_NOEXCEPT
      {
        return directive_parser::symbol_name (this->kind ());
      }

      /// Backward compatibility (Bison 3.6).
      symbol_kind_type type_get () const YY_NOEXCEPT;

      /// Whether empty.
      bool empty () const YY_NOEXCEPT;

      /// Destructive move, \a s is emptied into this.
      void move (basic_symbol& s);

      /// The semantic value.
      value_type value;

      /// The location.
      location_type location;

    private:
#if YY_CPLUSPLUS < 201103L
      /// Assignment operator.
      basic_symbol& operator= (const basic_symbol& that);
#endif
    };

    /// Type access provider for token (enum) based symbols.
    struct by_kind
    {
      /// The symbol kind as needed by the constructor.
      typedef token_kind_type kind_type;

      /// Default constructor.
      by_kind () YY_NOEXCEPT;

#if 201103L <= YY_CPLUSPLUS
      /// Move constructor.
      by_kind (by_kind&& that) YY_NOEXCEPT;
#endif

      /// Copy constructor.
      by_kind (const by_kind& that) YY_NOEXCEPT;

      /// Constructor from (external) token numbers.
      by_kind (kind_type t) YY_NOEXCEPT;



      /// Record that this symbol is empty.
      void clear () YY_NOEXCEPT;

      /// Steal the symbol kind from \a that.
      void move (by_kind& that);

      /// The (internal) type number (corresponding to \a type).
      /// \a empty when empty.
      symbol_kind_type kind () const YY_NOEXCEPT;

      /// Backward compatibility (Bison 3.6).
      symbol_kind_type type_get () const YY_NOEXCEPT;

      /// The symbol kind.
      /// \a S_YYEMPTY when empty.
      symbol_kind_type kind_;
    };

    /// Backward compatibility for a private implementation detail (Bison 3.6).
    typedef by_kind by_type;

    /// "External" symbols: returned by the scanner.
    struct symbol_type : basic_symbol<by_kind>
    {};

    /// Build a parser object.
    directive_parser (mli::directive_lexer& mlilex_yyarg, mli::location_type& loc_yyarg);
    virtual ~directive_parser ();

#if 201103L <= YY_CPLUSPLUS
    /// Non copyable.
    directive_parser (const directive_parser&) = delete;
    /// Non copyable.
    directive_parser& operator= (const directive_parser&) = delete;
#endif

    /// Parse.  An alias for parse ().
    /// \returns  0 iff parsing succeeded.
    int operator() ();

    /// Parse.
    /// \returns  0 iff parsing succeeded.
    virtual int parse ();

#if MLIDEBUG
    /// The current debugging stream.
    std::ostream& debug_stream () const YY_ATTRIBUTE_PURE;
    /// Set the current debugging stream.
    void set_debug_stream (std::ostream &);

    /// Type for debugging levels.
    typedef int debug_level_type;
    /// The current debugging level.
    debug_level_type debug_level () const YY_ATTRIBUTE_PURE;
    /// Set the current debugging level.
    void set_debug_level (debug_level_type l);
#endif

    /// Report a syntax error.
    /// \param loc    where the syntax error is found.
    /// \param msg    a description of the syntax error.
    virtual void error (const location_type& loc, const std::string& msg);

    /// Report a syntax error.
    void error (const syntax_error& err);

    /// The user-facing name of the symbol whose (internal) number is
    /// YYSYMBOL.  No bounds checking.
    static std::string symbol_name (symbol_kind_type yysymbol);



    class context
    {
    public:
      context (const directive_parser& yyparser, const symbol_type& yyla);
      const symbol_type& lookahead () const YY_NOEXCEPT { return yyla_; }
      symbol_kind_type token () const YY_NOEXCEPT { return yyla_.kind (); }
      const location_type& location () const YY_NOEXCEPT { return yyla_.location; }

      /// Put in YYARG at most YYARGN of the expected tokens, and return the
      /// number of tokens stored in YYARG.  If YYARG is null, return the
      /// number of expected tokens (guaranteed to be less than YYNTOKENS).
      int expected_tokens (symbol_kind_type yyarg[], int yyargn) const;

    private:
      const directive_parser& yyparser_;
      const symbol_type& yyla_;
    };

  private:
#if YY_CPLUSPLUS < 201103L
    /// Non copyable.
    directive_parser (const directive_parser&);
    /// Non copyable.
    directive_parser& operator= (const directive_parser&);
#endif


    /// Stored state numbers (used for stacks).
    typedef signed char state_type;

    /// The arguments of the error message.
    int yy_syntax_error_arguments_ (const context& yyctx,
                                    symbol_kind_type yyarg[], int yyargn) const;

    /// Generate an error message.
    /// \param yyctx     the context in which the error occurred.
    virtual std::string yysyntax_error_ (const context& yyctx) const;
    /// Compute post-reduction state.
    /// \param yystate   the current state
    /// \param yysym     the nonterminal to push on the stack
    static state_type yy_lr_goto_state_ (state_type yystate, int yysym);

    /// Whether the given \c yypact_ value indicates a defaulted state.
    /// \param yyvalue   the value to check
    static bool yy_pact_value_is_default_ (int yyvalue) YY_NOEXCEPT;

    /// Whether the given \c yytable_ value indicates a syntax error.
    /// \param yyvalue   the value to check
    static bool yy_table_value_is_error_ (int yyvalue) YY_NOEXCEPT;

    static const signed char yypact_ninf_;
    static const signed char yytable_ninf_;

    /// Convert a scanner token kind \a t to a symbol kind.
    /// In theory \a t should be a token_kind_type, but character literals
    /// are valid, yet not members of the token_kind_type enum.
    static symbol_kind_type yytranslate_ (int t) YY_NOEXCEPT;

    /// Convert the symbol name \a n to a form suitable for a diagnostic.
    static std::string yytnamerr_ (const char *yystr);

    /// For a symbol, its name in clear.
    static const char* const yytname_[];


    // Tables.
    // YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
    // STATE-NUM.
    static const signed char yypact_[];

    // YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
    // Performed when YYTABLE does not specify something else to do.  Zero
    // means the default is an error.
    static const signed char yydefact_[];

    // YYPGOTO[NTERM-NUM].
    static const signed char yypgoto_[];

    // YYDEFGOTO[NTERM-NUM].
    static const signed char yydefgoto_[];

    // YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
    // positive, shift that token.  If negative, reduce the rule whose
    // number is the opposite.  If YYTABLE_NINF, syntax error.
    static const signed char yytable_[];

    static const signed char yycheck_[];

    // YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
    // state STATE-NUM.
    static const unsigned char yystos_[];

    // YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.
    static const unsigned char yyr1_[];

    // YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.
    static const signed char yyr2_[];


#if MLIDEBUG
    // YYRLINE[YYN] -- Source line where rule number YYN was defined.
    static const short yyrline_[];
    /// Report on the debug stream that the rule \a r is going to be reduced.
    virtual void yy_reduce_print_ (int r) const;
    /// Print the state stack on the debug stream.
    virtual void yy_stack_print_ () const;

    /// Debugging level.
    int yydebug_;
    /// Debug stream.
    std::ostream* yycdebug_;

    /// \brief Display a symbol kind, value and location.
    /// \param yyo    The output stream.
    /// \param yysym  The symbol.
    template <typename Base>
    void yy_print_ (std::ostream& yyo, const basic_symbol<Base>& yysym) const;
#endif

    /// \brief Reclaim the memory associated to a symbol.
    /// \param yymsg     Why this token is reclaimed.
    ///                  If null, print nothing.
    /// \param yysym     The symbol.
    template <typename Base>
    void yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const;

  private:
    /// Type access provider for state based symbols.
    struct by_state
    {
      /// Default constructor.
      by_state () YY_NOEXCEPT;

      /// The symbol kind as needed by the constructor.
      typedef state_type kind_type;

      /// Constructor.
      by_state (kind_type s) YY_NOEXCEPT;

      /// Copy constructor.
      by_state (const by_state& that) YY_NOEXCEPT;

      /// Record that this symbol is empty.
      void clear () YY_NOEXCEPT;

      /// Steal the symbol kind from \a that.
      void move (by_state& that);

      /// The symbol kind (corresponding to \a state).
      /// \a symbol_kind::S_YYEMPTY when empty.
      symbol_kind_type kind () const YY_NOEXCEPT;

      /// The state number used to denote an empty symbol.
      /// We use the initial state, as it does not have a value.
      enum { empty_state = 0 };

      /// The state.
      /// \a empty when empty.
      state_type state;
    };

    /// "Internal" symbol: element of the stack.
    struct stack_symbol_type : basic_symbol<by_state>
    {
      /// Superclass.
      typedef basic_symbol<by_state> super_type;
      /// Construct an empty symbol.
      stack_symbol_type ();
      /// Move or copy construction.
      stack_symbol_type (YY_RVREF (stack_symbol_type) that);
      /// Steal the contents from \a sym to build this.
      stack_symbol_type (state_type s, YY_MOVE_REF (symbol_type) sym);
#if YY_CPLUSPLUS < 201103L
      /// Assignment, needed by push_back by some old implementations.
      /// Moves the contents of that.
      stack_symbol_type& operator= (stack_symbol_type& that);

      /// Assignment, needed by push_back by other implementations.
      /// Needed by some other old implementations.
      stack_symbol_type& operator= (const stack_symbol_type& that);
#endif
    };

    /// A stack with random access from its top.
    template <typename T, typename S = std::vector<T> >
    class stack
    {
    public:
      // Hide our reversed order.
      typedef typename S::iterator iterator;
      typedef typename S::const_iterator const_iterator;
      typedef typename S::size_type size_type;
      typedef typename std::ptrdiff_t index_type;

      stack (size_type n = 200) YY_NOEXCEPT
        : seq_ (n)
      {}

#if 201103L <= YY_CPLUSPLUS
      /// Non copyable.
      stack (const stack&) = delete;
      /// Non copyable.
      stack& operator= (const stack&) = delete;
#endif

      /// Random access.
      ///
      /// Index 0 returns the topmost element.
      const T&
      operator[] (index_type i) const
      {
        return seq_[size_type (size () - 1 - i)];
      }

      /// Random access.
      ///
      /// Index 0 returns the topmost element.
      T&
      operator[] (index_type i)
      {
        return seq_[size_type (size () - 1 - i)];
      }

      /// Steal the contents of \a t.
      ///
      /// Close to move-semantics.
      void
      push (YY_MOVE_REF (T) t)
      {
        seq_.push_back (T ());
        operator[] (0).move (t);
      }

      /// Pop elements from the stack.
      void
      pop (std::ptrdiff_t n = 1) YY_NOEXCEPT
      {
        for (; 0 < n; --n)
          seq_.pop_back ();
      }

      /// Pop all elements from the stack.
      void
      clear () YY_NOEXCEPT
      {
        seq_.clear ();
      }

      /// Number of elements on the stack.
      index_type
      size () const YY_NOEXCEPT
      {
        return index_type (seq_.size ());
      }

      /// Iterator on top of the stack (going downwards).
      const_iterator
      begin () const YY_NOEXCEPT
      {
        return seq_.begin ();
      }

      /// Bottom of the stack.
      const_iterator
      end () const YY_NOEXCEPT
      {
        return seq_.end ();
      }

      /// Present a slice of the top of a stack.
      class slice
      {
      public:
        slice (const stack& stack, index_type range) YY_NOEXCEPT
          : stack_ (stack)
          , range_ (range)
        {}

        const T&
        operator[] (index_type i) const
        {
          return stack_[range_ - i];
        }

      private:
        const stack& stack_;
        index_type range_;
      };

    private:
#if YY_CPLUSPLUS < 201103L
      /// Non copyable.
      stack (const stack&);
      /// Non copyable.
      stack& operator= (const stack&);
#endif
      /// The wrapped container.
      S seq_;
    };


    /// Stack type.
    typedef stack<stack_symbol_type> stack_type;

    /// The stack.
    stack_type yystack_;

    /// Push a new state on the stack.
    /// \param m    a debug message to display
    ///             if null, no trace is output.
    /// \param sym  the symbol
    /// \warning the contents of \a s.value is stolen.
    void yypush_ (const char* m, YY_MOVE_REF (stack_symbol_type) sym);

    /// Push a new look ahead token on the state on the stack.
    /// \param m    a debug message to display
    ///             if null, no trace is output.
    /// \param s    the state
    /// \param sym  the symbol (for its value and location).
    /// \warning the contents of \a sym.value is stolen.
    void yypush_ (const char* m, state_type s, YY_MOVE_REF (symbol_type) sym);

    /// Pop \a n symbols from the stack.
    void yypop_ (int n = 1) YY_NOEXCEPT;

    /// Constants.
    enum
    {
      yylast_ = 102,     ///< Last index in yytable_.
      yynnts_ = 21,  ///< Number of nonterminal symbols.
      yyfinal_ = 50 ///< Termination state number.
    };


    // User arguments.
    mli::directive_lexer& mlilex;
    mli::location_type& loc;

  };


#line 22 "../../mli-root/src/directive-parser.yy"
} // mli
#line 1187 "../../mli-root/src/directive-parser.hh"


// "%code provides" blocks.
#line 91 "../../mli-root/src/directive-parser.yy"


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


#line 1216 "../../mli-root/src/directive-parser.hh"


#endif // !YY_MLI_MLI_ROOT_SRC_DIRECTIVE_PARSER_HH_INCLUDED
