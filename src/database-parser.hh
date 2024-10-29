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
 ** \file ../../mli-root/src/database-parser.hh
 ** Define the mli::parser class.
 */

// C++ LALR(1) parser skeleton written by Akim Demaille.

// DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
// especially those whose name start with YY_ or yy_.  They are
// private implementation details that can be changed or removed.

#ifndef YY_MLI_MLI_ROOT_SRC_DATABASE_PARSER_HH_INCLUDED
# define YY_MLI_MLI_ROOT_SRC_DATABASE_PARSER_HH_INCLUDED
// "%code requires" blocks.
#line 42 "../../mli-root/src/database-parser.yy"

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


#line 75 "../../mli-root/src/database-parser.hh"


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

#line 22 "../../mli-root/src/database-parser.yy"
namespace mli {
#line 219 "../../mli-root/src/database-parser.hh"




  /// A Bison parser.
  class database_parser
  {
  public:
#ifdef MLISTYPE
# ifdef __GNUC__
#  pragma GCC message "bison: do not #define MLISTYPE in C++, use %define api.value.type"
# endif
    typedef MLISTYPE value_type;
#else
  /// A buffer to store and retrieve objects.
  ///
  /// Sort of a variant, but does not keep track of the nature
  /// of the stored data, since that knowledge is available
  /// via the current parser state.
  class value_type
  {
  public:
    /// Type of *this.
    typedef value_type self_type;

    /// Empty construction.
    value_type () YY_NOEXCEPT
      : yyraw_ ()
    {}

    /// Construct and fill.
    template <typename T>
    value_type (YY_RVREF (T) t)
    {
      new (yyas_<T> ()) T (YY_MOVE (t));
    }

#if 201103L <= YY_CPLUSPLUS
    /// Non copyable.
    value_type (const self_type&) = delete;
    /// Non copyable.
    self_type& operator= (const self_type&) = delete;
#endif

    /// Destruction, allowed only if empty.
    ~value_type () YY_NOEXCEPT
    {}

# if 201103L <= YY_CPLUSPLUS
    /// Instantiate a \a T in here from \a t.
    template <typename T, typename... U>
    T&
    emplace (U&&... u)
    {
      return *new (yyas_<T> ()) T (std::forward <U>(u)...);
    }
# else
    /// Instantiate an empty \a T in here.
    template <typename T>
    T&
    emplace ()
    {
      return *new (yyas_<T> ()) T ();
    }

    /// Instantiate a \a T in here from \a t.
    template <typename T>
    T&
    emplace (const T& t)
    {
      return *new (yyas_<T> ()) T (t);
    }
# endif

    /// Instantiate an empty \a T in here.
    /// Obsolete, use emplace.
    template <typename T>
    T&
    build ()
    {
      return emplace<T> ();
    }

    /// Instantiate a \a T in here from \a t.
    /// Obsolete, use emplace.
    template <typename T>
    T&
    build (const T& t)
    {
      return emplace<T> (t);
    }

    /// Accessor to a built \a T.
    template <typename T>
    T&
    as () YY_NOEXCEPT
    {
      return *yyas_<T> ();
    }

    /// Const accessor to a built \a T (for %printer).
    template <typename T>
    const T&
    as () const YY_NOEXCEPT
    {
      return *yyas_<T> ();
    }

    /// Swap the content with \a that, of same type.
    ///
    /// Both variants must be built beforehand, because swapping the actual
    /// data requires reading it (with as()), and this is not possible on
    /// unconstructed variants: it would require some dynamic testing, which
    /// should not be the variant's responsibility.
    /// Swapping between built and (possibly) non-built is done with
    /// self_type::move ().
    template <typename T>
    void
    swap (self_type& that) YY_NOEXCEPT
    {
      std::swap (as<T> (), that.as<T> ());
    }

    /// Move the content of \a that to this.
    ///
    /// Destroys \a that.
    template <typename T>
    void
    move (self_type& that)
    {
# if 201103L <= YY_CPLUSPLUS
      emplace<T> (std::move (that.as<T> ()));
# else
      emplace<T> ();
      swap<T> (that);
# endif
      that.destroy<T> ();
    }

# if 201103L <= YY_CPLUSPLUS
    /// Move the content of \a that to this.
    template <typename T>
    void
    move (self_type&& that)
    {
      emplace<T> (std::move (that.as<T> ()));
      that.destroy<T> ();
    }
#endif

    /// Copy the content of \a that to this.
    template <typename T>
    void
    copy (const self_type& that)
    {
      emplace<T> (that.as<T> ());
    }

    /// Destroy the stored \a T.
    template <typename T>
    void
    destroy ()
    {
      as<T> ().~T ();
    }

  private:
#if YY_CPLUSPLUS < 201103L
    /// Non copyable.
    value_type (const self_type&);
    /// Non copyable.
    self_type& operator= (const self_type&);
#endif

    /// Accessor to raw memory as \a T.
    template <typename T>
    T*
    yyas_ () YY_NOEXCEPT
    {
      void *yyp = yyraw_;
      return static_cast<T*> (yyp);
     }

    /// Const accessor to raw memory as \a T.
    template <typename T>
    const T*
    yyas_ () const YY_NOEXCEPT
    {
      const void *yyp = yyraw_;
      return static_cast<const T*> (yyp);
     }

    /// An auxiliary type to compute the largest semantic type.
    union union_type
    {
      // "integer value"
      // "subscript natural number value"
      // "subscript integer value"
      // "superscript natural number value"
      // "superscript integer value"
      // optional_superscript_natural_number_value
      char dummy1[sizeof (integer)];

      // metaformula_substitution_sequence
      // substitution_for_metaformula
      // metaformula_substitution
      // formula_substitution_sequence
      // substitution_for_formula
      // formula_substitution
      // term_substitution_sequence
      // term_substitution
      // predicate_function_application
      // term_function_application
      // theory
      // include_theories
      // include_theory
      // theory_body
      // formal_system
      // formal_system_body
      // formal_system_body_item
      // theory_body_list
      // theory_body_item
      // postulate
      // conjecture
      // theorem
      // theorem_statement
      // proof
      // $@11
      // compound-proof
      // proof_head
      // proof_lines
      // proof_line
      // proof_of_conclusion
      // find_statement
      // find_statement_list
      // find_statement_sequence
      // find_definition_sequence
      // find_statement_item
      // find_statement_name
      // @13
      // statement
      // definition_statement
      // identifier_declaration
      // declarator_list
      // declarator_identifier_list
      // identifier_function_list
      // identifier_function_name
      // identifier_constant_list
      // identifier_constant_name
      // identifier_variable_list
      // identifier_variable_name
      // definition
      // metaformula_definition
      // object_formula_definition
      // term_definition
      // metaformula
      // pure_metaformula
      // optional_varied_variable_matrix
      // varied_variable_conclusions
      // varied_variable_conclusion
      // varied_variable_premises
      // varied_variable_premise
      // varied_variable_set
      // varied_variable
      // optional_varied_in_reduction_variable_matrix
      // varied_in_reduction_variable_conclusions
      // varied_in_reduction_variable_conclusion
      // varied_in_reduction_variable_premises
      // varied_in_reduction_variable_premise
      // varied_in_reduction_variable_set
      // varied_in_reduction_variable
      // simple_metaformula
      // atomic_metaformula
      // special_metaformula
      // meta_object_free
      // metapredicate
      // metapredicate_function
      // metapredicate_argument
      // metapredicate_argument_body
      // object_formula
      // hoare_triple
      // code_statement
      // code_sequence
      // code_term
      // very_simple_formula
      // quantized_formula
      // simple_formula
      // quantized_body
      // atomic_formula
      // predicate
      // predicate_expression
      // predicate_identifier
      // logic_formula
      // prefix_logic_formula
      // quantizer_declaration
      // quantized_variable_list
      // all_variable_list
      // exist_variable_list
      // exclusion_set
      // exclusion_list
      // all_identifier_list
      // exist_identifier_list
      // optional_in_term
      // tuple
      // tuple_body
      // term
      // simple_term
      // term_identifier
      // variable_exclusion_set
      // variable_exclusion_list
      // bound_variable
      // function_term
      // set_term
      // implicit_set_identifier_list
      // set_member_list
      // function_term_identifier
      char dummy2[sizeof (ref6<unit>)];

      // end_theory_name
      char dummy3[sizeof (std::pair<std::string, bool>)];

      // "natural number value"
      char dummy4[sizeof (std::pair<std::string, integer>)];

      // theorem_head
      char dummy5[sizeof (std::pair<theorem::type, std::string>)];

      // "result"
      // "name"
      // "label"
      // "∀"
      // "∃"
      // "¬"
      // "∧"
      // "∨"
      // "⇒"
      // "⇐"
      // "⇔"
      // "ℕ"
      // "<"
      // ">"
      // "≤"
      // "≥"
      // "≮"
      // "≯"
      // "≰"
      // "≱"
      // "="
      // "≠"
      // "∣"
      // "∤"
      // "↦"
      // "⤇"
      // "!"
      // "⋅"
      // "+"
      // "-"
      // "∈"
      // "∉"
      // "∁"
      // "∪"
      // "∩"
      // "∖"
      // "⋃"
      // "⋂"
      // "⊆"
      // "⊊"
      // "⊇"
      // "⊋"
      // "/"
      // "\\"
      // theory_name
      // statement_name
      // statement_label
      // subproof_statement
      // optional-result
      char dummy6[sizeof (std::string)];

      // "theorem"
      char dummy7[sizeof (theorem::type)];

      // definition_labelstatement
      char dummy8[sizeof (val<definition>)];

      // "metapredicate constant"
      // "function"
      // "predicate"
      // "predicate constant"
      // "atom constant"
      // "function constant"
      // "term constant"
      // "metaformula variable"
      // "object formula variable"
      // "predicate variable"
      // "atom variable"
      // "prefix formula variable"
      // "function variable"
      // "object variable"
      // "code variable"
      // "all variable"
      // "exist variable"
      // "function map variable"
      // "Set variable"
      // "set variable"
      // "set variable definition"
      // "implicit set variable"
      char dummy9[sizeof (val<unit>)];
    };

    /// The size of the largest semantic type.
    enum { size = sizeof (union_type) };

    /// A buffer to store semantic values.
    union
    {
      /// Strongest alignment constraints.
      long double yyalign_me_;
      /// A buffer large enough to store any of the semantic values.
      char yyraw_[size];
    };
  };

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
    include_key = 259,             // "include"
    theory_key = 260,              // "theory"
    end_key = 261,                 // "end"
    formal_system_key = 262,       // "formal system"
    definition_key = 263,          // "definition"
    postulate_key = 264,           // "postulate"
    axiom_key = 265,               // "axiom"
    rule_key = 266,                // "rule"
    conjecture_key = 267,          // "conjecture"
    theorem_key = 268,             // "theorem"
    proof_key = 269,               // "proof"
    end_of_proof_key = 270,        // "∎"
    by_key = 271,                  // "by"
    premise_key = 272,             // "premise"
    result_key = 273,              // "result"
    metainfer_key = 274,           // "⊩"
    metaor_key = 275,              // "or"
    metaand_key = 276,             // "and"
    metanot_key = 277,             // "not"
    infer_key = 278,               // "⊢"
    object_identical_key = 279,    // "≡"
    object_not_identical_key = 280, // "≢"
    meta_identical_key = 281,      // "≣"
    meta_not_identical_key = 282,  // "≣̷"
    fail_key = 283,                // "fail"
    succeed_key = 284,             // "succeed"
    free_for_key = 285,            // "free for"
    metain_key = 286,              // "in"
    free_in_key = 287,             // "free in"
    use_key = 288,                 // "use"
    defined_by_key = 289,          // "≔"
    defines_key = 290,             // "≕"
    defined_equal_key = 291,       // "≝"
    plain_name = 292,              // "name"
    label_key = 293,               // "label"
    metapredicate_constant = 294,  // "metapredicate constant"
    function_key = 295,            // "function"
    predicate_key = 296,           // "predicate"
    predicate_constant = 297,      // "predicate constant"
    atom_constant = 298,           // "atom constant"
    function_constant = 299,       // "function constant"
    term_constant = 300,           // "term constant"
    metaformula_variable = 301,    // "metaformula variable"
    object_formula_variable = 302, // "object formula variable"
    predicate_variable = 303,      // "predicate variable"
    atom_variable = 304,           // "atom variable"
    prefix_formula_variable = 305, // "prefix formula variable"
    function_variable = 306,       // "function variable"
    object_variable = 307,         // "object variable"
    code_variable = 308,           // "code variable"
    all_variable = 309,            // "all variable"
    exist_variable = 310,          // "exist variable"
    function_map_variable = 311,   // "function map variable"
    is_set_variable = 312,         // "Set variable"
    set_variable = 313,            // "set variable"
    set_variable_definition = 314, // "set variable definition"
    implicit_set_variable = 315,   // "implicit set variable"
    identifier_constant_key = 316, // "identifier constant"
    identifier_variable_key = 317, // "identifier variable"
    identifier_function_key = 318, // "identifier function"
    all_key = 319,                 // "∀"
    exist_key = 320,               // "∃"
    logical_not_key = 321,         // "¬"
    logical_and_key = 322,         // "∧"
    logical_or_key = 323,          // "∨"
    implies_key = 324,             // "⇒"
    impliedby_key = 325,           // "⇐"
    equivalent_key = 326,          // "⇔"
    prefix_not_key = 327,          // prefix_not_key
    prefix_and_key = 328,          // prefix_and_key
    prefix_or_key = 329,           // prefix_or_key
    prefix_implies_key = 330,      // prefix_implies_key
    prefix_equivalent_key = 331,   // prefix_equivalent_key
    natural_number_key = 332,      // "ℕ"
    less_key = 333,                // "<"
    greater_key = 334,             // ">"
    less_or_equal_key = 335,       // "≤"
    greater_or_equal_key = 336,    // "≥"
    not_less_key = 337,            // "≮"
    not_greater_key = 338,         // "≯"
    not_less_or_equal_key = 339,   // "≰"
    not_greater_or_equal_key = 340, // "≱"
    equal_key = 341,               // "="
    not_equal_key = 342,           // "≠"
    divides_key = 343,             // "∣"
    not_divides_key = 344,         // "∤"
    mapsto_key = 345,              // "↦"
    Mapsto_key = 346,              // "⤇"
    function_map_prefix_key = 347, // "𝛌"
    degree_key = 348,              // "°"
    bullet_key = 349,              // "•"
    subscript_x_key = 350,         // "ₓ"
    natural_number_value = 351,    // "natural number value"
    integer_value = 352,           // "integer value"
    subscript_natural_number_value = 353, // "subscript natural number value"
    subscript_integer_value = 354, // "subscript integer value"
    superscript_natural_number_value = 355, // "superscript natural number value"
    superscript_integer_value = 356, // "superscript integer value"
    factorial_key = 357,           // "!"
    mult_key = 358,                // "⋅"
    plus_key = 359,                // "+"
    minus_key = 360,               // "-"
    is_set_key = 361,              // "Set"
    power_set_key = 362,           // "Pow"
    empty_set_key = 363,           // "∅"
    in_key = 364,                  // "∈"
    not_in_key = 365,              // "∉"
    set_complement_key = 366,      // "∁"
    set_union_key = 367,           // "∪"
    set_intersection_key = 368,    // "∩"
    set_difference_key = 369,      // "∖"
    set_union_operator_key = 370,  // "⋃"
    set_intersection_operator_key = 371, // "⋂"
    subset_key = 372,              // "⊆"
    proper_subset_key = 373,       // "⊊"
    superset_key = 374,            // "⊇"
    proper_superset_key = 375,     // "⊋"
    colon_key = 376,               // ":"
    semicolon_key = 377,           // ";"
    comma_key = 378,               // ","
    period_key = 379,              // "."
    left_parenthesis_key = 380,    // "("
    right_parenthesis_key = 381,   // ")"
    left_bracket_key = 382,        // "["
    right_bracket_key = 383,       // "]"
    left_angle_bracket_key = 384,  // "⟨"
    right_angle_bracket_key = 385, // "⟩"
    superscript_left_parenthesis_key = 386, // "⁽"
    superscript_right_parenthesis_key = 387, // "⁾"
    subscript_left_parenthesis_key = 388, // "₍"
    subscript_right_parenthesis_key = 389, // "₎"
    left_brace_key = 390,          // "{"
    vertical_line_key = 391,       // "|"
    right_brace_key = 392,         // "}"
    tilde_key = 393,               // "~"
    slash_key = 394,               // "/"
    backslash_key = 395,           // "\\"
    if_key = 396,                  // "if"
    then_key = 397,                // "then"
    else_key = 398,                // "else"
    while_key = 399,               // "while"
    do_key = 400,                  // "do"
    loop_key = 401,                // "loop"
    for_key = 402,                 // "for"
    break_key = 403,               // "break"
    continue_key = 404,            // "continue"
    throw_key = 405,               // "throw"
    try_key = 406,                 // "try"
    catch_key = 407,               // "catch"
    unary_minus = 409              // unary_minus
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
        YYNTOKENS = 155, ///< Number of tokens.
        S_YYEMPTY = -2,
        S_YYEOF = 0,                             // "end of file"
        S_YYerror = 1,                           // error
        S_YYUNDEF = 2,                           // "invalid token"
        S_token_error = 3,                       // "token error"
        S_include_key = 4,                       // "include"
        S_theory_key = 5,                        // "theory"
        S_end_key = 6,                           // "end"
        S_formal_system_key = 7,                 // "formal system"
        S_definition_key = 8,                    // "definition"
        S_postulate_key = 9,                     // "postulate"
        S_axiom_key = 10,                        // "axiom"
        S_rule_key = 11,                         // "rule"
        S_conjecture_key = 12,                   // "conjecture"
        S_theorem_key = 13,                      // "theorem"
        S_proof_key = 14,                        // "proof"
        S_end_of_proof_key = 15,                 // "∎"
        S_by_key = 16,                           // "by"
        S_premise_key = 17,                      // "premise"
        S_result_key = 18,                       // "result"
        S_metainfer_key = 19,                    // "⊩"
        S_metaor_key = 20,                       // "or"
        S_metaand_key = 21,                      // "and"
        S_metanot_key = 22,                      // "not"
        S_infer_key = 23,                        // "⊢"
        S_object_identical_key = 24,             // "≡"
        S_object_not_identical_key = 25,         // "≢"
        S_meta_identical_key = 26,               // "≣"
        S_meta_not_identical_key = 27,           // "≣̷"
        S_fail_key = 28,                         // "fail"
        S_succeed_key = 29,                      // "succeed"
        S_free_for_key = 30,                     // "free for"
        S_metain_key = 31,                       // "in"
        S_free_in_key = 32,                      // "free in"
        S_use_key = 33,                          // "use"
        S_defined_by_key = 34,                   // "≔"
        S_defines_key = 35,                      // "≕"
        S_defined_equal_key = 36,                // "≝"
        S_plain_name = 37,                       // "name"
        S_label_key = 38,                        // "label"
        S_metapredicate_constant = 39,           // "metapredicate constant"
        S_function_key = 40,                     // "function"
        S_predicate_key = 41,                    // "predicate"
        S_predicate_constant = 42,               // "predicate constant"
        S_atom_constant = 43,                    // "atom constant"
        S_function_constant = 44,                // "function constant"
        S_term_constant = 45,                    // "term constant"
        S_metaformula_variable = 46,             // "metaformula variable"
        S_object_formula_variable = 47,          // "object formula variable"
        S_predicate_variable = 48,               // "predicate variable"
        S_atom_variable = 49,                    // "atom variable"
        S_prefix_formula_variable = 50,          // "prefix formula variable"
        S_function_variable = 51,                // "function variable"
        S_object_variable = 52,                  // "object variable"
        S_code_variable = 53,                    // "code variable"
        S_all_variable = 54,                     // "all variable"
        S_exist_variable = 55,                   // "exist variable"
        S_function_map_variable = 56,            // "function map variable"
        S_is_set_variable = 57,                  // "Set variable"
        S_set_variable = 58,                     // "set variable"
        S_set_variable_definition = 59,          // "set variable definition"
        S_implicit_set_variable = 60,            // "implicit set variable"
        S_identifier_constant_key = 61,          // "identifier constant"
        S_identifier_variable_key = 62,          // "identifier variable"
        S_identifier_function_key = 63,          // "identifier function"
        S_all_key = 64,                          // "∀"
        S_exist_key = 65,                        // "∃"
        S_logical_not_key = 66,                  // "¬"
        S_logical_and_key = 67,                  // "∧"
        S_logical_or_key = 68,                   // "∨"
        S_implies_key = 69,                      // "⇒"
        S_impliedby_key = 70,                    // "⇐"
        S_equivalent_key = 71,                   // "⇔"
        S_prefix_not_key = 72,                   // prefix_not_key
        S_prefix_and_key = 73,                   // prefix_and_key
        S_prefix_or_key = 74,                    // prefix_or_key
        S_prefix_implies_key = 75,               // prefix_implies_key
        S_prefix_equivalent_key = 76,            // prefix_equivalent_key
        S_natural_number_key = 77,               // "ℕ"
        S_less_key = 78,                         // "<"
        S_greater_key = 79,                      // ">"
        S_less_or_equal_key = 80,                // "≤"
        S_greater_or_equal_key = 81,             // "≥"
        S_not_less_key = 82,                     // "≮"
        S_not_greater_key = 83,                  // "≯"
        S_not_less_or_equal_key = 84,            // "≰"
        S_not_greater_or_equal_key = 85,         // "≱"
        S_equal_key = 86,                        // "="
        S_not_equal_key = 87,                    // "≠"
        S_divides_key = 88,                      // "∣"
        S_not_divides_key = 89,                  // "∤"
        S_mapsto_key = 90,                       // "↦"
        S_Mapsto_key = 91,                       // "⤇"
        S_function_map_prefix_key = 92,          // "𝛌"
        S_degree_key = 93,                       // "°"
        S_bullet_key = 94,                       // "•"
        S_subscript_x_key = 95,                  // "ₓ"
        S_natural_number_value = 96,             // "natural number value"
        S_integer_value = 97,                    // "integer value"
        S_subscript_natural_number_value = 98,   // "subscript natural number value"
        S_subscript_integer_value = 99,          // "subscript integer value"
        S_superscript_natural_number_value = 100, // "superscript natural number value"
        S_superscript_integer_value = 101,       // "superscript integer value"
        S_factorial_key = 102,                   // "!"
        S_mult_key = 103,                        // "⋅"
        S_plus_key = 104,                        // "+"
        S_minus_key = 105,                       // "-"
        S_is_set_key = 106,                      // "Set"
        S_power_set_key = 107,                   // "Pow"
        S_empty_set_key = 108,                   // "∅"
        S_in_key = 109,                          // "∈"
        S_not_in_key = 110,                      // "∉"
        S_set_complement_key = 111,              // "∁"
        S_set_union_key = 112,                   // "∪"
        S_set_intersection_key = 113,            // "∩"
        S_set_difference_key = 114,              // "∖"
        S_set_union_operator_key = 115,          // "⋃"
        S_set_intersection_operator_key = 116,   // "⋂"
        S_subset_key = 117,                      // "⊆"
        S_proper_subset_key = 118,               // "⊊"
        S_superset_key = 119,                    // "⊇"
        S_proper_superset_key = 120,             // "⊋"
        S_colon_key = 121,                       // ":"
        S_semicolon_key = 122,                   // ";"
        S_comma_key = 123,                       // ","
        S_period_key = 124,                      // "."
        S_left_parenthesis_key = 125,            // "("
        S_right_parenthesis_key = 126,           // ")"
        S_left_bracket_key = 127,                // "["
        S_right_bracket_key = 128,               // "]"
        S_left_angle_bracket_key = 129,          // "⟨"
        S_right_angle_bracket_key = 130,         // "⟩"
        S_superscript_left_parenthesis_key = 131, // "⁽"
        S_superscript_right_parenthesis_key = 132, // "⁾"
        S_subscript_left_parenthesis_key = 133,  // "₍"
        S_subscript_right_parenthesis_key = 134, // "₎"
        S_left_brace_key = 135,                  // "{"
        S_vertical_line_key = 136,               // "|"
        S_right_brace_key = 137,                 // "}"
        S_tilde_key = 138,                       // "~"
        S_slash_key = 139,                       // "/"
        S_backslash_key = 140,                   // "\\"
        S_if_key = 141,                          // "if"
        S_then_key = 142,                        // "then"
        S_else_key = 143,                        // "else"
        S_while_key = 144,                       // "while"
        S_do_key = 145,                          // "do"
        S_loop_key = 146,                        // "loop"
        S_for_key = 147,                         // "for"
        S_break_key = 148,                       // "break"
        S_continue_key = 149,                    // "continue"
        S_throw_key = 150,                       // "throw"
        S_try_key = 151,                         // "try"
        S_catch_key = 152,                       // "catch"
        S_153_ = 153,                            // "⊣"
        S_unary_minus = 154,                     // unary_minus
        S_YYACCEPT = 155,                        // $accept
        S_file = 156,                            // file
        S_file_contents = 157,                   // file_contents
        S_command = 158,                         // command
        S_159_1 = 159,                           // $@1
        S_metaformula_substitution_sequence = 160, // metaformula_substitution_sequence
        S_substitution_for_metaformula = 161,    // substitution_for_metaformula
        S_metaformula_substitution = 162,        // metaformula_substitution
        S_formula_substitution_sequence = 163,   // formula_substitution_sequence
        S_substitution_for_formula = 164,        // substitution_for_formula
        S_formula_substitution = 165,            // formula_substitution
        S_term_substitution_sequence = 166,      // term_substitution_sequence
        S_term_substitution = 167,               // term_substitution
        S_predicate_function_application = 168,  // predicate_function_application
        S_169_2 = 169,                           // $@2
        S_term_function_application = 170,       // term_function_application
        S_171_3 = 171,                           // $@3
        S_theory = 172,                          // theory
        S_173_4 = 173,                           // $@4
        S_end_theory_name = 174,                 // end_theory_name
        S_include_theories = 175,                // include_theories
        S_include_theory = 176,                  // include_theory
        S_theory_name = 177,                     // theory_name
        S_theory_body = 178,                     // theory_body
        S_formal_system = 179,                   // formal_system
        S_180_5 = 180,                           // $@5
        S_formal_system_body = 181,              // formal_system_body
        S_formal_system_body_item = 182,         // formal_system_body_item
        S_theory_body_list = 183,                // theory_body_list
        S_theory_body_item = 184,                // theory_body_item
        S_postulate = 185,                       // postulate
        S_186_6 = 186,                           // $@6
        S_187_7 = 187,                           // $@7
        S_188_8 = 188,                           // $@8
        S_conjecture = 189,                      // conjecture
        S_190_9 = 190,                           // $@9
        S_definition_labelstatement = 191,       // definition_labelstatement
        S_192_10 = 192,                          // $@10
        S_statement_name = 193,                  // statement_name
        S_theorem = 194,                         // theorem
        S_theorem_statement = 195,               // theorem_statement
        S_theorem_head = 196,                    // theorem_head
        S_proof = 197,                           // proof
        S_198_11 = 198,                          // $@11
        S_199_compound_proof = 199,              // compound-proof
        S_proof_head = 200,                      // proof_head
        S_proof_lines = 201,                     // proof_lines
        S_statement_label = 202,                 // statement_label
        S_proof_line = 203,                      // proof_line
        S_204_12 = 204,                          // $@12
        S_subproof_statement = 205,              // subproof_statement
        S_proof_of_conclusion = 206,             // proof_of_conclusion
        S_207_optional_result = 207,             // optional-result
        S_find_statement = 208,                  // find_statement
        S_find_statement_list = 209,             // find_statement_list
        S_find_statement_sequence = 210,         // find_statement_sequence
        S_find_definition_sequence = 211,        // find_definition_sequence
        S_find_statement_item = 212,             // find_statement_item
        S_find_statement_name = 213,             // find_statement_name
        S_214_13 = 214,                          // @13
        S_statement = 215,                       // statement
        S_definition_statement = 216,            // definition_statement
        S_identifier_declaration = 217,          // identifier_declaration
        S_declarator_list = 218,                 // declarator_list
        S_declarator_identifier_list = 219,      // declarator_identifier_list
        S_identifier_function_list = 220,        // identifier_function_list
        S_identifier_function_name = 221,        // identifier_function_name
        S_222_14 = 222,                          // $@14
        S_223_15 = 223,                          // $@15
        S_identifier_constant_list = 224,        // identifier_constant_list
        S_identifier_constant_name = 225,        // identifier_constant_name
        S_identifier_variable_list = 226,        // identifier_variable_list
        S_identifier_variable_name = 227,        // identifier_variable_name
        S_definition = 228,                      // definition
        S_metaformula_definition = 229,          // metaformula_definition
        S_object_formula_definition = 230,       // object_formula_definition
        S_term_definition = 231,                 // term_definition
        S_metaformula = 232,                     // metaformula
        S_pure_metaformula = 233,                // pure_metaformula
        S_optional_varied_variable_matrix = 234, // optional_varied_variable_matrix
        S_varied_variable_conclusions = 235,     // varied_variable_conclusions
        S_varied_variable_conclusion = 236,      // varied_variable_conclusion
        S_varied_variable_premises = 237,        // varied_variable_premises
        S_varied_variable_premise = 238,         // varied_variable_premise
        S_varied_variable_set = 239,             // varied_variable_set
        S_varied_variable = 240,                 // varied_variable
        S_optional_varied_in_reduction_variable_matrix = 241, // optional_varied_in_reduction_variable_matrix
        S_varied_in_reduction_variable_conclusions = 242, // varied_in_reduction_variable_conclusions
        S_varied_in_reduction_variable_conclusion = 243, // varied_in_reduction_variable_conclusion
        S_varied_in_reduction_variable_premises = 244, // varied_in_reduction_variable_premises
        S_varied_in_reduction_variable_premise = 245, // varied_in_reduction_variable_premise
        S_varied_in_reduction_variable_set = 246, // varied_in_reduction_variable_set
        S_varied_in_reduction_variable = 247,    // varied_in_reduction_variable
        S_simple_metaformula = 248,              // simple_metaformula
        S_atomic_metaformula = 249,              // atomic_metaformula
        S_special_metaformula = 250,             // special_metaformula
        S_meta_object_free = 251,                // meta_object_free
        S_metapredicate = 252,                   // metapredicate
        S_metapredicate_function = 253,          // metapredicate_function
        S_metapredicate_argument = 254,          // metapredicate_argument
        S_metapredicate_argument_body = 255,     // metapredicate_argument_body
        S_object_formula = 256,                  // object_formula
        S_hoare_triple = 257,                    // hoare_triple
        S_code_statement = 258,                  // code_statement
        S_code_sequence = 259,                   // code_sequence
        S_code_term = 260,                       // code_term
        S_very_simple_formula = 261,             // very_simple_formula
        S_quantized_formula = 262,               // quantized_formula
        S_simple_formula = 263,                  // simple_formula
        S_quantized_body = 264,                  // quantized_body
        S_atomic_formula = 265,                  // atomic_formula
        S_predicate = 266,                       // predicate
        S_267_16 = 267,                          // $@16
        S_268_17 = 268,                          // $@17
        S_predicate_expression = 269,            // predicate_expression
        S_predicate_identifier = 270,            // predicate_identifier
        S_optional_superscript_natural_number_value = 271, // optional_superscript_natural_number_value
        S_logic_formula = 272,                   // logic_formula
        S_prefix_logic_formula = 273,            // prefix_logic_formula
        S_quantizer_declaration = 274,           // quantizer_declaration
        S_quantized_variable_list = 275,         // quantized_variable_list
        S_all_variable_list = 276,               // all_variable_list
        S_exist_variable_list = 277,             // exist_variable_list
        S_exclusion_set = 278,                   // exclusion_set
        S_279_18 = 279,                          // $@18
        S_exclusion_list = 280,                  // exclusion_list
        S_all_identifier_list = 281,             // all_identifier_list
        S_282_19 = 282,                          // $@19
        S_exist_identifier_list = 283,           // exist_identifier_list
        S_284_20 = 284,                          // $@20
        S_optional_in_term = 285,                // optional_in_term
        S_tuple = 286,                           // tuple
        S_tuple_body = 287,                      // tuple_body
        S_term = 288,                            // term
        S_simple_term = 289,                     // simple_term
        S_term_identifier = 290,                 // term_identifier
        S_variable_exclusion_set = 291,          // variable_exclusion_set
        S_variable_exclusion_list = 292,         // variable_exclusion_list
        S_bound_variable = 293,                  // bound_variable
        S_function_term = 294,                   // function_term
        S_set_term = 295,                        // set_term
        S_implicit_set_identifier_list = 296,    // implicit_set_identifier_list
        S_297_21 = 297,                          // $@21
        S_298_22 = 298,                          // $@22
        S_set_member_list = 299,                 // set_member_list
        S_function_term_identifier = 300         // function_term_identifier
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
        , value ()
        , location (std::move (that.location))
      {
        switch (this->kind ())
    {
      case symbol_kind::S_integer_value: // "integer value"
      case symbol_kind::S_subscript_natural_number_value: // "subscript natural number value"
      case symbol_kind::S_subscript_integer_value: // "subscript integer value"
      case symbol_kind::S_superscript_natural_number_value: // "superscript natural number value"
      case symbol_kind::S_superscript_integer_value: // "superscript integer value"
      case symbol_kind::S_optional_superscript_natural_number_value: // optional_superscript_natural_number_value
        value.move< integer > (std::move (that.value));
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
        value.move< ref6<unit> > (std::move (that.value));
        break;

      case symbol_kind::S_end_theory_name: // end_theory_name
        value.move< std::pair<std::string, bool> > (std::move (that.value));
        break;

      case symbol_kind::S_natural_number_value: // "natural number value"
        value.move< std::pair<std::string, integer> > (std::move (that.value));
        break;

      case symbol_kind::S_theorem_head: // theorem_head
        value.move< std::pair<theorem::type, std::string> > (std::move (that.value));
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
        value.move< std::string > (std::move (that.value));
        break;

      case symbol_kind::S_theorem_key: // "theorem"
        value.move< theorem::type > (std::move (that.value));
        break;

      case symbol_kind::S_definition_labelstatement: // definition_labelstatement
        value.move< val<definition> > (std::move (that.value));
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
        value.move< val<unit> > (std::move (that.value));
        break;

      default:
        break;
    }

      }
#endif

      /// Copy constructor.
      basic_symbol (const basic_symbol& that);

      /// Constructors for typed symbols.
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, location_type&& l)
        : Base (t)
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const location_type& l)
        : Base (t)
        , location (l)
      {}
#endif

#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, integer&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const integer& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, ref6<unit>&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const ref6<unit>& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, std::pair<std::string, bool>&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const std::pair<std::string, bool>& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, std::pair<std::string, integer>&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const std::pair<std::string, integer>& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, std::pair<theorem::type, std::string>&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const std::pair<theorem::type, std::string>& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, std::string&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const std::string& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, theorem::type&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const theorem::type& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, val<definition>&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const val<definition>& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, val<unit>&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const val<unit>& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

      /// Destroy the symbol.
      ~basic_symbol ()
      {
        clear ();
      }



      /// Destroy contents, and record that is empty.
      void clear () YY_NOEXCEPT
      {
        // User destructor.
        symbol_kind_type yykind = this->kind ();
        basic_symbol<Base>& yysym = *this;
        (void) yysym;
        switch (yykind)
        {
       default:
          break;
        }

        // Value type destructor.
switch (yykind)
    {
      case symbol_kind::S_integer_value: // "integer value"
      case symbol_kind::S_subscript_natural_number_value: // "subscript natural number value"
      case symbol_kind::S_subscript_integer_value: // "subscript integer value"
      case symbol_kind::S_superscript_natural_number_value: // "superscript natural number value"
      case symbol_kind::S_superscript_integer_value: // "superscript integer value"
      case symbol_kind::S_optional_superscript_natural_number_value: // optional_superscript_natural_number_value
        value.template destroy< integer > ();
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
        value.template destroy< ref6<unit> > ();
        break;

      case symbol_kind::S_end_theory_name: // end_theory_name
        value.template destroy< std::pair<std::string, bool> > ();
        break;

      case symbol_kind::S_natural_number_value: // "natural number value"
        value.template destroy< std::pair<std::string, integer> > ();
        break;

      case symbol_kind::S_theorem_head: // theorem_head
        value.template destroy< std::pair<theorem::type, std::string> > ();
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
        value.template destroy< std::string > ();
        break;

      case symbol_kind::S_theorem_key: // "theorem"
        value.template destroy< theorem::type > ();
        break;

      case symbol_kind::S_definition_labelstatement: // definition_labelstatement
        value.template destroy< val<definition> > ();
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
        value.template destroy< val<unit> > ();
        break;

      default:
        break;
    }

        Base::clear ();
      }

      /// The user-facing name of this symbol.
      std::string name () const YY_NOEXCEPT
      {
        return database_parser::symbol_name (this->kind ());
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
    {
      /// Superclass.
      typedef basic_symbol<by_kind> super_type;

      /// Empty symbol.
      symbol_type () YY_NOEXCEPT {}

      /// Constructor for valueless symbols, and symbols from each type.
#if 201103L <= YY_CPLUSPLUS
      symbol_type (int tok, location_type l)
        : super_type (token_kind_type (tok), std::move (l))
#else
      symbol_type (int tok, const location_type& l)
        : super_type (token_kind_type (tok), l)
#endif
      {}
#if 201103L <= YY_CPLUSPLUS
      symbol_type (int tok, integer v, location_type l)
        : super_type (token_kind_type (tok), std::move (v), std::move (l))
#else
      symbol_type (int tok, const integer& v, const location_type& l)
        : super_type (token_kind_type (tok), v, l)
#endif
      {}
#if 201103L <= YY_CPLUSPLUS
      symbol_type (int tok, std::pair<std::string, integer> v, location_type l)
        : super_type (token_kind_type (tok), std::move (v), std::move (l))
#else
      symbol_type (int tok, const std::pair<std::string, integer>& v, const location_type& l)
        : super_type (token_kind_type (tok), v, l)
#endif
      {}
#if 201103L <= YY_CPLUSPLUS
      symbol_type (int tok, std::string v, location_type l)
        : super_type (token_kind_type (tok), std::move (v), std::move (l))
#else
      symbol_type (int tok, const std::string& v, const location_type& l)
        : super_type (token_kind_type (tok), v, l)
#endif
      {}
#if 201103L <= YY_CPLUSPLUS
      symbol_type (int tok, theorem::type v, location_type l)
        : super_type (token_kind_type (tok), std::move (v), std::move (l))
#else
      symbol_type (int tok, const theorem::type& v, const location_type& l)
        : super_type (token_kind_type (tok), v, l)
#endif
      {}
#if 201103L <= YY_CPLUSPLUS
      symbol_type (int tok, val<unit> v, location_type l)
        : super_type (token_kind_type (tok), std::move (v), std::move (l))
#else
      symbol_type (int tok, const val<unit>& v, const location_type& l)
        : super_type (token_kind_type (tok), v, l)
#endif
      {}
    };

    /// Build a parser object.
    database_parser (mli::theory_database& yypval_yyarg, mli::database_lexer& mlilex_yyarg);
    virtual ~database_parser ();

#if 201103L <= YY_CPLUSPLUS
    /// Non copyable.
    database_parser (const database_parser&) = delete;
    /// Non copyable.
    database_parser& operator= (const database_parser&) = delete;
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

    // Implementation of make_symbol for each token kind.
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_MLIEOF (location_type l)
      {
        return symbol_type (token::MLIEOF, std::move (l));
      }
#else
      static
      symbol_type
      make_MLIEOF (const location_type& l)
      {
        return symbol_type (token::MLIEOF, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_MLIerror (location_type l)
      {
        return symbol_type (token::MLIerror, std::move (l));
      }
#else
      static
      symbol_type
      make_MLIerror (const location_type& l)
      {
        return symbol_type (token::MLIerror, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_MLIUNDEF (location_type l)
      {
        return symbol_type (token::MLIUNDEF, std::move (l));
      }
#else
      static
      symbol_type
      make_MLIUNDEF (const location_type& l)
      {
        return symbol_type (token::MLIUNDEF, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_token_error (location_type l)
      {
        return symbol_type (token::token_error, std::move (l));
      }
#else
      static
      symbol_type
      make_token_error (const location_type& l)
      {
        return symbol_type (token::token_error, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_include_key (location_type l)
      {
        return symbol_type (token::include_key, std::move (l));
      }
#else
      static
      symbol_type
      make_include_key (const location_type& l)
      {
        return symbol_type (token::include_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_theory_key (location_type l)
      {
        return symbol_type (token::theory_key, std::move (l));
      }
#else
      static
      symbol_type
      make_theory_key (const location_type& l)
      {
        return symbol_type (token::theory_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_end_key (location_type l)
      {
        return symbol_type (token::end_key, std::move (l));
      }
#else
      static
      symbol_type
      make_end_key (const location_type& l)
      {
        return symbol_type (token::end_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_formal_system_key (location_type l)
      {
        return symbol_type (token::formal_system_key, std::move (l));
      }
#else
      static
      symbol_type
      make_formal_system_key (const location_type& l)
      {
        return symbol_type (token::formal_system_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_definition_key (location_type l)
      {
        return symbol_type (token::definition_key, std::move (l));
      }
#else
      static
      symbol_type
      make_definition_key (const location_type& l)
      {
        return symbol_type (token::definition_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_postulate_key (location_type l)
      {
        return symbol_type (token::postulate_key, std::move (l));
      }
#else
      static
      symbol_type
      make_postulate_key (const location_type& l)
      {
        return symbol_type (token::postulate_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_axiom_key (location_type l)
      {
        return symbol_type (token::axiom_key, std::move (l));
      }
#else
      static
      symbol_type
      make_axiom_key (const location_type& l)
      {
        return symbol_type (token::axiom_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_rule_key (location_type l)
      {
        return symbol_type (token::rule_key, std::move (l));
      }
#else
      static
      symbol_type
      make_rule_key (const location_type& l)
      {
        return symbol_type (token::rule_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_conjecture_key (location_type l)
      {
        return symbol_type (token::conjecture_key, std::move (l));
      }
#else
      static
      symbol_type
      make_conjecture_key (const location_type& l)
      {
        return symbol_type (token::conjecture_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_theorem_key (theorem::type v, location_type l)
      {
        return symbol_type (token::theorem_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_theorem_key (const theorem::type& v, const location_type& l)
      {
        return symbol_type (token::theorem_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_proof_key (location_type l)
      {
        return symbol_type (token::proof_key, std::move (l));
      }
#else
      static
      symbol_type
      make_proof_key (const location_type& l)
      {
        return symbol_type (token::proof_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_end_of_proof_key (location_type l)
      {
        return symbol_type (token::end_of_proof_key, std::move (l));
      }
#else
      static
      symbol_type
      make_end_of_proof_key (const location_type& l)
      {
        return symbol_type (token::end_of_proof_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_by_key (location_type l)
      {
        return symbol_type (token::by_key, std::move (l));
      }
#else
      static
      symbol_type
      make_by_key (const location_type& l)
      {
        return symbol_type (token::by_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_premise_key (location_type l)
      {
        return symbol_type (token::premise_key, std::move (l));
      }
#else
      static
      symbol_type
      make_premise_key (const location_type& l)
      {
        return symbol_type (token::premise_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_result_key (std::string v, location_type l)
      {
        return symbol_type (token::result_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_result_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::result_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_metainfer_key (location_type l)
      {
        return symbol_type (token::metainfer_key, std::move (l));
      }
#else
      static
      symbol_type
      make_metainfer_key (const location_type& l)
      {
        return symbol_type (token::metainfer_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_metaor_key (location_type l)
      {
        return symbol_type (token::metaor_key, std::move (l));
      }
#else
      static
      symbol_type
      make_metaor_key (const location_type& l)
      {
        return symbol_type (token::metaor_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_metaand_key (location_type l)
      {
        return symbol_type (token::metaand_key, std::move (l));
      }
#else
      static
      symbol_type
      make_metaand_key (const location_type& l)
      {
        return symbol_type (token::metaand_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_metanot_key (location_type l)
      {
        return symbol_type (token::metanot_key, std::move (l));
      }
#else
      static
      symbol_type
      make_metanot_key (const location_type& l)
      {
        return symbol_type (token::metanot_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_infer_key (location_type l)
      {
        return symbol_type (token::infer_key, std::move (l));
      }
#else
      static
      symbol_type
      make_infer_key (const location_type& l)
      {
        return symbol_type (token::infer_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_object_identical_key (location_type l)
      {
        return symbol_type (token::object_identical_key, std::move (l));
      }
#else
      static
      symbol_type
      make_object_identical_key (const location_type& l)
      {
        return symbol_type (token::object_identical_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_object_not_identical_key (location_type l)
      {
        return symbol_type (token::object_not_identical_key, std::move (l));
      }
#else
      static
      symbol_type
      make_object_not_identical_key (const location_type& l)
      {
        return symbol_type (token::object_not_identical_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_meta_identical_key (location_type l)
      {
        return symbol_type (token::meta_identical_key, std::move (l));
      }
#else
      static
      symbol_type
      make_meta_identical_key (const location_type& l)
      {
        return symbol_type (token::meta_identical_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_meta_not_identical_key (location_type l)
      {
        return symbol_type (token::meta_not_identical_key, std::move (l));
      }
#else
      static
      symbol_type
      make_meta_not_identical_key (const location_type& l)
      {
        return symbol_type (token::meta_not_identical_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_fail_key (location_type l)
      {
        return symbol_type (token::fail_key, std::move (l));
      }
#else
      static
      symbol_type
      make_fail_key (const location_type& l)
      {
        return symbol_type (token::fail_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_succeed_key (location_type l)
      {
        return symbol_type (token::succeed_key, std::move (l));
      }
#else
      static
      symbol_type
      make_succeed_key (const location_type& l)
      {
        return symbol_type (token::succeed_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_free_for_key (location_type l)
      {
        return symbol_type (token::free_for_key, std::move (l));
      }
#else
      static
      symbol_type
      make_free_for_key (const location_type& l)
      {
        return symbol_type (token::free_for_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_metain_key (location_type l)
      {
        return symbol_type (token::metain_key, std::move (l));
      }
#else
      static
      symbol_type
      make_metain_key (const location_type& l)
      {
        return symbol_type (token::metain_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_free_in_key (location_type l)
      {
        return symbol_type (token::free_in_key, std::move (l));
      }
#else
      static
      symbol_type
      make_free_in_key (const location_type& l)
      {
        return symbol_type (token::free_in_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_use_key (location_type l)
      {
        return symbol_type (token::use_key, std::move (l));
      }
#else
      static
      symbol_type
      make_use_key (const location_type& l)
      {
        return symbol_type (token::use_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_defined_by_key (location_type l)
      {
        return symbol_type (token::defined_by_key, std::move (l));
      }
#else
      static
      symbol_type
      make_defined_by_key (const location_type& l)
      {
        return symbol_type (token::defined_by_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_defines_key (location_type l)
      {
        return symbol_type (token::defines_key, std::move (l));
      }
#else
      static
      symbol_type
      make_defines_key (const location_type& l)
      {
        return symbol_type (token::defines_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_defined_equal_key (location_type l)
      {
        return symbol_type (token::defined_equal_key, std::move (l));
      }
#else
      static
      symbol_type
      make_defined_equal_key (const location_type& l)
      {
        return symbol_type (token::defined_equal_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_plain_name (std::string v, location_type l)
      {
        return symbol_type (token::plain_name, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_plain_name (const std::string& v, const location_type& l)
      {
        return symbol_type (token::plain_name, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_label_key (std::string v, location_type l)
      {
        return symbol_type (token::label_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_label_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::label_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_metapredicate_constant (val<unit> v, location_type l)
      {
        return symbol_type (token::metapredicate_constant, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_metapredicate_constant (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::metapredicate_constant, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_function_key (val<unit> v, location_type l)
      {
        return symbol_type (token::function_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_function_key (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::function_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_predicate_key (val<unit> v, location_type l)
      {
        return symbol_type (token::predicate_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_predicate_key (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::predicate_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_predicate_constant (val<unit> v, location_type l)
      {
        return symbol_type (token::predicate_constant, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_predicate_constant (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::predicate_constant, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_atom_constant (val<unit> v, location_type l)
      {
        return symbol_type (token::atom_constant, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_atom_constant (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::atom_constant, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_function_constant (val<unit> v, location_type l)
      {
        return symbol_type (token::function_constant, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_function_constant (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::function_constant, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_term_constant (val<unit> v, location_type l)
      {
        return symbol_type (token::term_constant, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_term_constant (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::term_constant, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_metaformula_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::metaformula_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_metaformula_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::metaformula_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_object_formula_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::object_formula_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_object_formula_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::object_formula_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_predicate_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::predicate_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_predicate_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::predicate_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_atom_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::atom_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_atom_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::atom_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_prefix_formula_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::prefix_formula_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_prefix_formula_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::prefix_formula_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_function_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::function_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_function_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::function_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_object_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::object_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_object_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::object_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_code_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::code_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_code_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::code_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_all_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::all_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_all_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::all_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_exist_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::exist_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_exist_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::exist_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_function_map_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::function_map_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_function_map_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::function_map_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_is_set_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::is_set_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_is_set_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::is_set_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_set_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::set_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_set_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::set_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_set_variable_definition (val<unit> v, location_type l)
      {
        return symbol_type (token::set_variable_definition, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_set_variable_definition (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::set_variable_definition, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_implicit_set_variable (val<unit> v, location_type l)
      {
        return symbol_type (token::implicit_set_variable, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_implicit_set_variable (const val<unit>& v, const location_type& l)
      {
        return symbol_type (token::implicit_set_variable, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_identifier_constant_key (location_type l)
      {
        return symbol_type (token::identifier_constant_key, std::move (l));
      }
#else
      static
      symbol_type
      make_identifier_constant_key (const location_type& l)
      {
        return symbol_type (token::identifier_constant_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_identifier_variable_key (location_type l)
      {
        return symbol_type (token::identifier_variable_key, std::move (l));
      }
#else
      static
      symbol_type
      make_identifier_variable_key (const location_type& l)
      {
        return symbol_type (token::identifier_variable_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_identifier_function_key (location_type l)
      {
        return symbol_type (token::identifier_function_key, std::move (l));
      }
#else
      static
      symbol_type
      make_identifier_function_key (const location_type& l)
      {
        return symbol_type (token::identifier_function_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_all_key (std::string v, location_type l)
      {
        return symbol_type (token::all_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_all_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::all_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_exist_key (std::string v, location_type l)
      {
        return symbol_type (token::exist_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_exist_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::exist_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_logical_not_key (std::string v, location_type l)
      {
        return symbol_type (token::logical_not_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_logical_not_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::logical_not_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_logical_and_key (std::string v, location_type l)
      {
        return symbol_type (token::logical_and_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_logical_and_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::logical_and_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_logical_or_key (std::string v, location_type l)
      {
        return symbol_type (token::logical_or_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_logical_or_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::logical_or_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_implies_key (std::string v, location_type l)
      {
        return symbol_type (token::implies_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_implies_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::implies_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_impliedby_key (std::string v, location_type l)
      {
        return symbol_type (token::impliedby_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_impliedby_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::impliedby_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_equivalent_key (std::string v, location_type l)
      {
        return symbol_type (token::equivalent_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_equivalent_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::equivalent_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_prefix_not_key (location_type l)
      {
        return symbol_type (token::prefix_not_key, std::move (l));
      }
#else
      static
      symbol_type
      make_prefix_not_key (const location_type& l)
      {
        return symbol_type (token::prefix_not_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_prefix_and_key (location_type l)
      {
        return symbol_type (token::prefix_and_key, std::move (l));
      }
#else
      static
      symbol_type
      make_prefix_and_key (const location_type& l)
      {
        return symbol_type (token::prefix_and_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_prefix_or_key (location_type l)
      {
        return symbol_type (token::prefix_or_key, std::move (l));
      }
#else
      static
      symbol_type
      make_prefix_or_key (const location_type& l)
      {
        return symbol_type (token::prefix_or_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_prefix_implies_key (location_type l)
      {
        return symbol_type (token::prefix_implies_key, std::move (l));
      }
#else
      static
      symbol_type
      make_prefix_implies_key (const location_type& l)
      {
        return symbol_type (token::prefix_implies_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_prefix_equivalent_key (location_type l)
      {
        return symbol_type (token::prefix_equivalent_key, std::move (l));
      }
#else
      static
      symbol_type
      make_prefix_equivalent_key (const location_type& l)
      {
        return symbol_type (token::prefix_equivalent_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_natural_number_key (std::string v, location_type l)
      {
        return symbol_type (token::natural_number_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_natural_number_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::natural_number_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_less_key (std::string v, location_type l)
      {
        return symbol_type (token::less_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_less_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::less_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_greater_key (std::string v, location_type l)
      {
        return symbol_type (token::greater_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_greater_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::greater_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_less_or_equal_key (std::string v, location_type l)
      {
        return symbol_type (token::less_or_equal_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_less_or_equal_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::less_or_equal_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_greater_or_equal_key (std::string v, location_type l)
      {
        return symbol_type (token::greater_or_equal_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_greater_or_equal_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::greater_or_equal_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_not_less_key (std::string v, location_type l)
      {
        return symbol_type (token::not_less_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_not_less_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::not_less_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_not_greater_key (std::string v, location_type l)
      {
        return symbol_type (token::not_greater_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_not_greater_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::not_greater_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_not_less_or_equal_key (std::string v, location_type l)
      {
        return symbol_type (token::not_less_or_equal_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_not_less_or_equal_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::not_less_or_equal_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_not_greater_or_equal_key (std::string v, location_type l)
      {
        return symbol_type (token::not_greater_or_equal_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_not_greater_or_equal_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::not_greater_or_equal_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_equal_key (std::string v, location_type l)
      {
        return symbol_type (token::equal_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_equal_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::equal_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_not_equal_key (std::string v, location_type l)
      {
        return symbol_type (token::not_equal_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_not_equal_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::not_equal_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_divides_key (std::string v, location_type l)
      {
        return symbol_type (token::divides_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_divides_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::divides_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_not_divides_key (std::string v, location_type l)
      {
        return symbol_type (token::not_divides_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_not_divides_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::not_divides_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_mapsto_key (std::string v, location_type l)
      {
        return symbol_type (token::mapsto_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_mapsto_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::mapsto_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_Mapsto_key (std::string v, location_type l)
      {
        return symbol_type (token::Mapsto_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_Mapsto_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::Mapsto_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_function_map_prefix_key (location_type l)
      {
        return symbol_type (token::function_map_prefix_key, std::move (l));
      }
#else
      static
      symbol_type
      make_function_map_prefix_key (const location_type& l)
      {
        return symbol_type (token::function_map_prefix_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_degree_key (location_type l)
      {
        return symbol_type (token::degree_key, std::move (l));
      }
#else
      static
      symbol_type
      make_degree_key (const location_type& l)
      {
        return symbol_type (token::degree_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_bullet_key (location_type l)
      {
        return symbol_type (token::bullet_key, std::move (l));
      }
#else
      static
      symbol_type
      make_bullet_key (const location_type& l)
      {
        return symbol_type (token::bullet_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_subscript_x_key (location_type l)
      {
        return symbol_type (token::subscript_x_key, std::move (l));
      }
#else
      static
      symbol_type
      make_subscript_x_key (const location_type& l)
      {
        return symbol_type (token::subscript_x_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_natural_number_value (std::pair<std::string, integer> v, location_type l)
      {
        return symbol_type (token::natural_number_value, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_natural_number_value (const std::pair<std::string, integer>& v, const location_type& l)
      {
        return symbol_type (token::natural_number_value, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_integer_value (integer v, location_type l)
      {
        return symbol_type (token::integer_value, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_integer_value (const integer& v, const location_type& l)
      {
        return symbol_type (token::integer_value, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_subscript_natural_number_value (integer v, location_type l)
      {
        return symbol_type (token::subscript_natural_number_value, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_subscript_natural_number_value (const integer& v, const location_type& l)
      {
        return symbol_type (token::subscript_natural_number_value, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_subscript_integer_value (integer v, location_type l)
      {
        return symbol_type (token::subscript_integer_value, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_subscript_integer_value (const integer& v, const location_type& l)
      {
        return symbol_type (token::subscript_integer_value, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_superscript_natural_number_value (integer v, location_type l)
      {
        return symbol_type (token::superscript_natural_number_value, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_superscript_natural_number_value (const integer& v, const location_type& l)
      {
        return symbol_type (token::superscript_natural_number_value, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_superscript_integer_value (integer v, location_type l)
      {
        return symbol_type (token::superscript_integer_value, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_superscript_integer_value (const integer& v, const location_type& l)
      {
        return symbol_type (token::superscript_integer_value, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_factorial_key (std::string v, location_type l)
      {
        return symbol_type (token::factorial_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_factorial_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::factorial_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_mult_key (std::string v, location_type l)
      {
        return symbol_type (token::mult_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_mult_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::mult_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_plus_key (std::string v, location_type l)
      {
        return symbol_type (token::plus_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_plus_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::plus_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_minus_key (std::string v, location_type l)
      {
        return symbol_type (token::minus_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_minus_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::minus_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_is_set_key (location_type l)
      {
        return symbol_type (token::is_set_key, std::move (l));
      }
#else
      static
      symbol_type
      make_is_set_key (const location_type& l)
      {
        return symbol_type (token::is_set_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_power_set_key (location_type l)
      {
        return symbol_type (token::power_set_key, std::move (l));
      }
#else
      static
      symbol_type
      make_power_set_key (const location_type& l)
      {
        return symbol_type (token::power_set_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_empty_set_key (location_type l)
      {
        return symbol_type (token::empty_set_key, std::move (l));
      }
#else
      static
      symbol_type
      make_empty_set_key (const location_type& l)
      {
        return symbol_type (token::empty_set_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_in_key (std::string v, location_type l)
      {
        return symbol_type (token::in_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_in_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::in_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_not_in_key (std::string v, location_type l)
      {
        return symbol_type (token::not_in_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_not_in_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::not_in_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_set_complement_key (std::string v, location_type l)
      {
        return symbol_type (token::set_complement_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_set_complement_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::set_complement_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_set_union_key (std::string v, location_type l)
      {
        return symbol_type (token::set_union_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_set_union_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::set_union_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_set_intersection_key (std::string v, location_type l)
      {
        return symbol_type (token::set_intersection_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_set_intersection_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::set_intersection_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_set_difference_key (std::string v, location_type l)
      {
        return symbol_type (token::set_difference_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_set_difference_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::set_difference_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_set_union_operator_key (std::string v, location_type l)
      {
        return symbol_type (token::set_union_operator_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_set_union_operator_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::set_union_operator_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_set_intersection_operator_key (std::string v, location_type l)
      {
        return symbol_type (token::set_intersection_operator_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_set_intersection_operator_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::set_intersection_operator_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_subset_key (std::string v, location_type l)
      {
        return symbol_type (token::subset_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_subset_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::subset_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_proper_subset_key (std::string v, location_type l)
      {
        return symbol_type (token::proper_subset_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_proper_subset_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::proper_subset_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_superset_key (std::string v, location_type l)
      {
        return symbol_type (token::superset_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_superset_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::superset_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_proper_superset_key (std::string v, location_type l)
      {
        return symbol_type (token::proper_superset_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_proper_superset_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::proper_superset_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_colon_key (location_type l)
      {
        return symbol_type (token::colon_key, std::move (l));
      }
#else
      static
      symbol_type
      make_colon_key (const location_type& l)
      {
        return symbol_type (token::colon_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_semicolon_key (location_type l)
      {
        return symbol_type (token::semicolon_key, std::move (l));
      }
#else
      static
      symbol_type
      make_semicolon_key (const location_type& l)
      {
        return symbol_type (token::semicolon_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_comma_key (location_type l)
      {
        return symbol_type (token::comma_key, std::move (l));
      }
#else
      static
      symbol_type
      make_comma_key (const location_type& l)
      {
        return symbol_type (token::comma_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_period_key (location_type l)
      {
        return symbol_type (token::period_key, std::move (l));
      }
#else
      static
      symbol_type
      make_period_key (const location_type& l)
      {
        return symbol_type (token::period_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_left_parenthesis_key (location_type l)
      {
        return symbol_type (token::left_parenthesis_key, std::move (l));
      }
#else
      static
      symbol_type
      make_left_parenthesis_key (const location_type& l)
      {
        return symbol_type (token::left_parenthesis_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_right_parenthesis_key (location_type l)
      {
        return symbol_type (token::right_parenthesis_key, std::move (l));
      }
#else
      static
      symbol_type
      make_right_parenthesis_key (const location_type& l)
      {
        return symbol_type (token::right_parenthesis_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_left_bracket_key (location_type l)
      {
        return symbol_type (token::left_bracket_key, std::move (l));
      }
#else
      static
      symbol_type
      make_left_bracket_key (const location_type& l)
      {
        return symbol_type (token::left_bracket_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_right_bracket_key (location_type l)
      {
        return symbol_type (token::right_bracket_key, std::move (l));
      }
#else
      static
      symbol_type
      make_right_bracket_key (const location_type& l)
      {
        return symbol_type (token::right_bracket_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_left_angle_bracket_key (location_type l)
      {
        return symbol_type (token::left_angle_bracket_key, std::move (l));
      }
#else
      static
      symbol_type
      make_left_angle_bracket_key (const location_type& l)
      {
        return symbol_type (token::left_angle_bracket_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_right_angle_bracket_key (location_type l)
      {
        return symbol_type (token::right_angle_bracket_key, std::move (l));
      }
#else
      static
      symbol_type
      make_right_angle_bracket_key (const location_type& l)
      {
        return symbol_type (token::right_angle_bracket_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_superscript_left_parenthesis_key (location_type l)
      {
        return symbol_type (token::superscript_left_parenthesis_key, std::move (l));
      }
#else
      static
      symbol_type
      make_superscript_left_parenthesis_key (const location_type& l)
      {
        return symbol_type (token::superscript_left_parenthesis_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_superscript_right_parenthesis_key (location_type l)
      {
        return symbol_type (token::superscript_right_parenthesis_key, std::move (l));
      }
#else
      static
      symbol_type
      make_superscript_right_parenthesis_key (const location_type& l)
      {
        return symbol_type (token::superscript_right_parenthesis_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_subscript_left_parenthesis_key (location_type l)
      {
        return symbol_type (token::subscript_left_parenthesis_key, std::move (l));
      }
#else
      static
      symbol_type
      make_subscript_left_parenthesis_key (const location_type& l)
      {
        return symbol_type (token::subscript_left_parenthesis_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_subscript_right_parenthesis_key (location_type l)
      {
        return symbol_type (token::subscript_right_parenthesis_key, std::move (l));
      }
#else
      static
      symbol_type
      make_subscript_right_parenthesis_key (const location_type& l)
      {
        return symbol_type (token::subscript_right_parenthesis_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_left_brace_key (location_type l)
      {
        return symbol_type (token::left_brace_key, std::move (l));
      }
#else
      static
      symbol_type
      make_left_brace_key (const location_type& l)
      {
        return symbol_type (token::left_brace_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_vertical_line_key (location_type l)
      {
        return symbol_type (token::vertical_line_key, std::move (l));
      }
#else
      static
      symbol_type
      make_vertical_line_key (const location_type& l)
      {
        return symbol_type (token::vertical_line_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_right_brace_key (location_type l)
      {
        return symbol_type (token::right_brace_key, std::move (l));
      }
#else
      static
      symbol_type
      make_right_brace_key (const location_type& l)
      {
        return symbol_type (token::right_brace_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_tilde_key (location_type l)
      {
        return symbol_type (token::tilde_key, std::move (l));
      }
#else
      static
      symbol_type
      make_tilde_key (const location_type& l)
      {
        return symbol_type (token::tilde_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_slash_key (std::string v, location_type l)
      {
        return symbol_type (token::slash_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_slash_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::slash_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_backslash_key (std::string v, location_type l)
      {
        return symbol_type (token::backslash_key, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_backslash_key (const std::string& v, const location_type& l)
      {
        return symbol_type (token::backslash_key, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_if_key (location_type l)
      {
        return symbol_type (token::if_key, std::move (l));
      }
#else
      static
      symbol_type
      make_if_key (const location_type& l)
      {
        return symbol_type (token::if_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_then_key (location_type l)
      {
        return symbol_type (token::then_key, std::move (l));
      }
#else
      static
      symbol_type
      make_then_key (const location_type& l)
      {
        return symbol_type (token::then_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_else_key (location_type l)
      {
        return symbol_type (token::else_key, std::move (l));
      }
#else
      static
      symbol_type
      make_else_key (const location_type& l)
      {
        return symbol_type (token::else_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_while_key (location_type l)
      {
        return symbol_type (token::while_key, std::move (l));
      }
#else
      static
      symbol_type
      make_while_key (const location_type& l)
      {
        return symbol_type (token::while_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_do_key (location_type l)
      {
        return symbol_type (token::do_key, std::move (l));
      }
#else
      static
      symbol_type
      make_do_key (const location_type& l)
      {
        return symbol_type (token::do_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_loop_key (location_type l)
      {
        return symbol_type (token::loop_key, std::move (l));
      }
#else
      static
      symbol_type
      make_loop_key (const location_type& l)
      {
        return symbol_type (token::loop_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_for_key (location_type l)
      {
        return symbol_type (token::for_key, std::move (l));
      }
#else
      static
      symbol_type
      make_for_key (const location_type& l)
      {
        return symbol_type (token::for_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_break_key (location_type l)
      {
        return symbol_type (token::break_key, std::move (l));
      }
#else
      static
      symbol_type
      make_break_key (const location_type& l)
      {
        return symbol_type (token::break_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_continue_key (location_type l)
      {
        return symbol_type (token::continue_key, std::move (l));
      }
#else
      static
      symbol_type
      make_continue_key (const location_type& l)
      {
        return symbol_type (token::continue_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_throw_key (location_type l)
      {
        return symbol_type (token::throw_key, std::move (l));
      }
#else
      static
      symbol_type
      make_throw_key (const location_type& l)
      {
        return symbol_type (token::throw_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_try_key (location_type l)
      {
        return symbol_type (token::try_key, std::move (l));
      }
#else
      static
      symbol_type
      make_try_key (const location_type& l)
      {
        return symbol_type (token::try_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_catch_key (location_type l)
      {
        return symbol_type (token::catch_key, std::move (l));
      }
#else
      static
      symbol_type
      make_catch_key (const location_type& l)
      {
        return symbol_type (token::catch_key, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_unary_minus (location_type l)
      {
        return symbol_type (token::unary_minus, std::move (l));
      }
#else
      static
      symbol_type
      make_unary_minus (const location_type& l)
      {
        return symbol_type (token::unary_minus, l);
      }
#endif


    class context
    {
    public:
      context (const database_parser& yyparser, const symbol_type& yyla);
      const symbol_type& lookahead () const YY_NOEXCEPT { return yyla_; }
      symbol_kind_type token () const YY_NOEXCEPT { return yyla_.kind (); }
      const location_type& location () const YY_NOEXCEPT { return yyla_.location; }

      /// Put in YYARG at most YYARGN of the expected tokens, and return the
      /// number of tokens stored in YYARG.  If YYARG is null, return the
      /// number of expected tokens (guaranteed to be less than YYNTOKENS).
      int expected_tokens (symbol_kind_type yyarg[], int yyargn) const;

    private:
      const database_parser& yyparser_;
      const symbol_type& yyla_;
    };

  private:
#if YY_CPLUSPLUS < 201103L
    /// Non copyable.
    database_parser (const database_parser&);
    /// Non copyable.
    database_parser& operator= (const database_parser&);
#endif

    /// Check the lookahead yytoken.
    /// \returns  true iff the token will be eventually shifted.
    bool yy_lac_check_ (symbol_kind_type yytoken) const;
    /// Establish the initial context if no initial context currently exists.
    /// \returns  true iff the token will be eventually shifted.
    bool yy_lac_establish_ (symbol_kind_type yytoken);
    /// Discard any previous initial lookahead context because of event.
    /// \param event  the event which caused the lookahead to be discarded.
    ///               Only used for debbuging output.
    void yy_lac_discard_ (const char* event);

    /// Stored state numbers (used for stacks).
    typedef short state_type;

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

    static const short yypact_ninf_;
    static const short yytable_ninf_;

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
    static const short yypact_[];

    // YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
    // Performed when YYTABLE does not specify something else to do.  Zero
    // means the default is an error.
    static const short yydefact_[];

    // YYPGOTO[NTERM-NUM].
    static const short yypgoto_[];

    // YYDEFGOTO[NTERM-NUM].
    static const short yydefgoto_[];

    // YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
    // positive, shift that token.  If negative, reduce the rule whose
    // number is the opposite.  If YYTABLE_NINF, syntax error.
    static const short yytable_[];

    static const short yycheck_[];

    // YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
    // state STATE-NUM.
    static const short yystos_[];

    // YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.
    static const short yyr1_[];

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
    /// The stack for LAC.
    /// Logically, the yy_lac_stack's lifetime is confined to the function
    /// yy_lac_check_. We just store it as a member of this class to hold
    /// on to the memory and to avoid frequent reallocations.
    /// Since yy_lac_check_ is const, this member must be mutable.
    mutable std::vector<state_type> yylac_stack_;
    /// Whether an initial LAC context was established.
    bool yy_lac_established_;


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
      yylast_ = 1765,     ///< Last index in yytable_.
      yynnts_ = 146,  ///< Number of nonterminal symbols.
      yyfinal_ = 6 ///< Termination state number.
    };


    // User arguments.
    mli::theory_database& yypval;
    mli::database_lexer& mlilex;

  };


#line 22 "../../mli-root/src/database-parser.yy"
} // mli
#line 4657 "../../mli-root/src/database-parser.hh"


// "%code provides" blocks.
#line 69 "../../mli-root/src/database-parser.yy"

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


#line 4710 "../../mli-root/src/database-parser.hh"


#endif // !YY_MLI_MLI_ROOT_SRC_DATABASE_PARSER_HH_INCLUDED
