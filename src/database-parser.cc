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
#line 123 "../../mli-root/src/database-parser.yy"


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



#line 241 "../../mli-root/src/database-parser.cc"


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
#line 334 "../../mli-root/src/database-parser.cc"

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
    , value (that.value)
    , location (that.location)
  {}


  /// Constructor for valueless symbols.
  template <typename Base>
  database_parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, YY_MOVE_REF (location_type) l)
    : Base (t)
    , value ()
    , location (l)
  {}

  template <typename Base>
  database_parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, YY_RVREF (value_type) v, YY_RVREF (location_type) l)
    : Base (t)
    , value (YY_MOVE (v))
    , location (YY_MOVE (l))
  {}


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
    value = YY_MOVE (s.value);
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
    : super_type (YY_MOVE (that.state), YY_MOVE (that.value), YY_MOVE (that.location))
  {
#if 201103L <= YY_CPLUSPLUS
    // that is emptied.
    that.state = empty_state;
#endif
  }

  database_parser::stack_symbol_type::stack_symbol_type (state_type s, YY_MOVE_REF (symbol_type) that)
    : super_type (s, YY_MOVE (that.value), YY_MOVE (that.location))
  {
    // that is emptied.
    that.kind_ = symbol_kind::S_YYEMPTY;
  }

#if YY_CPLUSPLUS < 201103L
  database_parser::stack_symbol_type&
  database_parser::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
    value = that.value;
    location = that.location;
    return *this;
  }

  database_parser::stack_symbol_type&
  database_parser::stack_symbol_type::operator= (stack_symbol_type& that)
  {
    state = that.state;
    value = that.value;
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

    // User destructor.
    YY_USE (yysym.kind ());
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

#line 684 "../../mli-root/src/database-parser.cc"


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
      /* If YYLEN is nonzero, implement the default value of the
         action: '$$ = $1'.  Otherwise, use the top of the stack.

         Otherwise, the following line sets YYLHS.VALUE to garbage.
         This behavior is undocumented and Bison users should not rely
         upon it.  */
      if (yylen)
        yylhs.value = yystack_[yylen - 1].value;
      else
        yylhs.value = yystack_[0].value;

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
  case 3: // file: file_contents
#line 650 "../../mli-root/src/database-parser.yy"
                  {}
#line 828 "../../mli-root/src/database-parser.cc"
    break;

  case 4: // file: error
#line 651 "../../mli-root/src/database-parser.yy"
          {
      declaration_context = false;
      bound_variable_type = free_variable_context;
      YYABORT;
    }
#line 838 "../../mli-root/src/database-parser.cc"
    break;

  case 5: // file_contents: file_contents command
#line 660 "../../mli-root/src/database-parser.yy"
                          {}
#line 844 "../../mli-root/src/database-parser.cc"
    break;

  case 6: // file_contents: command
#line 661 "../../mli-root/src/database-parser.yy"
                          {}
#line 850 "../../mli-root/src/database-parser.cc"
    break;

  case 7: // $@1: %empty
#line 666 "../../mli-root/src/database-parser.yy"
    { symbol_table.clear(); }
#line 856 "../../mli-root/src/database-parser.cc"
    break;

  case 8: // command: $@1 theory
#line 666 "../../mli-root/src/database-parser.yy"
                                     {}
#line 862 "../../mli-root/src/database-parser.cc"
    break;

  case 9: // metaformula_substitution_sequence: substitution_for_metaformula
#line 671 "../../mli-root/src/database-parser.yy"
                                    { yylhs.value.object = yystack_[0].value.object; }
#line 868 "../../mli-root/src/database-parser.cc"
    break;

  case 10: // metaformula_substitution_sequence: metaformula_substitution_sequence substitution_for_metaformula
#line 672 "../../mli-root/src/database-parser.yy"
                                                                         {
      yylhs.value.object =  ref<substitution>(yystack_[1].value.object) * ref<substitution>(yystack_[0].value.object);
    }
#line 876 "../../mli-root/src/database-parser.cc"
    break;

  case 11: // substitution_for_metaformula: metaformula_substitution
#line 679 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.object = yystack_[0].value.object; }
#line 882 "../../mli-root/src/database-parser.cc"
    break;

  case 12: // substitution_for_metaformula: formula_substitution
#line 680 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 888 "../../mli-root/src/database-parser.cc"
    break;

  case 13: // substitution_for_metaformula: term_substitution
#line 681 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 894 "../../mli-root/src/database-parser.cc"
    break;

  case 14: // metaformula_substitution: "[" "metaformula variable" "⤇" metaformula "]"
#line 686 "../../mli-root/src/database-parser.yy"
                                                       {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 904 "../../mli-root/src/database-parser.cc"
    break;

  case 15: // formula_substitution_sequence: substitution_for_formula
#line 695 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.object = yystack_[0].value.object; }
#line 910 "../../mli-root/src/database-parser.cc"
    break;

  case 16: // formula_substitution_sequence: formula_substitution_sequence substitution_for_formula
#line 696 "../../mli-root/src/database-parser.yy"
                                                                 {
      yylhs.value.object = ref<substitution>(yystack_[1].value.object) * ref<substitution>(yystack_[0].value.object);
    }
#line 918 "../../mli-root/src/database-parser.cc"
    break;

  case 17: // substitution_for_formula: formula_substitution
#line 703 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 924 "../../mli-root/src/database-parser.cc"
    break;

  case 18: // substitution_for_formula: term_substitution
#line 704 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 930 "../../mli-root/src/database-parser.cc"
    break;

  case 19: // formula_substitution: "[" "object formula variable" "⤇" object_formula "]"
#line 709 "../../mli-root/src/database-parser.yy"
                                                             {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 940 "../../mli-root/src/database-parser.cc"
    break;

  case 20: // formula_substitution: "[" "predicate variable" "⤇" predicate "]"
#line 714 "../../mli-root/src/database-parser.yy"
                                                   {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 950 "../../mli-root/src/database-parser.cc"
    break;

  case 21: // formula_substitution: "[" "atom variable" "⤇" "atom constant" "]"
#line 719 "../../mli-root/src/database-parser.yy"
                                                  {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 960 "../../mli-root/src/database-parser.cc"
    break;

  case 22: // term_substitution_sequence: term_substitution
#line 728 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 966 "../../mli-root/src/database-parser.cc"
    break;

  case 23: // term_substitution_sequence: term_substitution_sequence term_substitution
#line 729 "../../mli-root/src/database-parser.yy"
                                                       {
      yylhs.value.object = ref<substitution>(yystack_[1].value.object) * ref<substitution>(yystack_[0].value.object);
    }
#line 974 "../../mli-root/src/database-parser.cc"
    break;

  case 24: // term_substitution: "[" term_identifier "⤇" term "]"
#line 736 "../../mli-root/src/database-parser.yy"
                                           {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 984 "../../mli-root/src/database-parser.cc"
    break;

  case 25: // predicate_function_application: "(" "object variable" "↦" object_formula ")" tuple
#line 745 "../../mli-root/src/database-parser.yy"
                                                              {
      yylhs.value.object = ref<function_application>(make, ref<function_map>(make, yystack_[4].value.object, yystack_[2].value.object), yystack_[0].value.object);
    }
#line 992 "../../mli-root/src/database-parser.cc"
    break;

  case 26: // $@2: %empty
#line 748 "../../mli-root/src/database-parser.yy"
                                                           { symbol_table.pop_level(); }
#line 998 "../../mli-root/src/database-parser.cc"
    break;

  case 27: // predicate_function_application: "(" "𝛌" "function map variable" "↦" object_formula $@2 ")" tuple
#line 748 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      yylhs.value.object = ref<function_application>(make, ref<function_map>(make, yystack_[5].value.object, yystack_[3].value.object), yystack_[0].value.object);
    }
#line 1006 "../../mli-root/src/database-parser.cc"
    break;

  case 28: // predicate_function_application: "predicate" tuple
#line 751 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = ref<function_application>(make, yystack_[1].value.object, yystack_[0].value.object); }
#line 1012 "../../mli-root/src/database-parser.cc"
    break;

  case 29: // term_function_application: "(" "object variable" "↦" term ")" tuple
#line 756 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.object = ref<function_application>(make, ref<function_map>(make, yystack_[4].value.object, yystack_[2].value.object), yystack_[0].value.object);
    }
#line 1020 "../../mli-root/src/database-parser.cc"
    break;

  case 30: // $@3: %empty
#line 759 "../../mli-root/src/database-parser.yy"
                                                 { symbol_table.pop_level(); }
#line 1026 "../../mli-root/src/database-parser.cc"
    break;

  case 31: // term_function_application: "(" "𝛌" "function map variable" "↦" term $@3 ")" tuple
#line 759 "../../mli-root/src/database-parser.yy"
                                                                                            {
      yylhs.value.object = ref<function_application>(make, ref<function_map>(make, yystack_[5].value.object, yystack_[3].value.object), yystack_[0].value.object);
    }
#line 1034 "../../mli-root/src/database-parser.cc"
    break;

  case 32: // term_function_application: "function" tuple
#line 762 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.object = ref<function_application>(make, yystack_[1].value.object, yystack_[0].value.object); }
#line 1040 "../../mli-root/src/database-parser.cc"
    break;

  case 33: // $@4: %empty
#line 768 "../../mli-root/src/database-parser.yy"
        { theory_ = ref<theory>(make, yystack_[1].value.text);
          yypval.insert(theory_);
          symbol_table.push_level();
    }
#line 1049 "../../mli-root/src/database-parser.cc"
    break;

  case 34: // theory: "theory" statement_name "." $@4 include_theories theory_body "end" "theory" end_theory_name "."
#line 774 "../../mli-root/src/database-parser.yy"
                                          {
      if (yystack_[1].value.number != 0 && yystack_[8].value.text != yystack_[1].value.text) {
        mli::database_parser::error(yystack_[1].location, "warning: Name mismatch, theory " + yystack_[8].value.text
          + ", end theory " + yystack_[1].value.text + ".");
      }

      symbol_table.pop_level();
    }
#line 1062 "../../mli-root/src/database-parser.cc"
    break;

  case 35: // end_theory_name: %empty
#line 786 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.number = 0; }
#line 1068 "../../mli-root/src/database-parser.cc"
    break;

  case 36: // end_theory_name: statement_name
#line 787 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.text = yystack_[0].value.text; yylhs.value.number = 1; }
#line 1074 "../../mli-root/src/database-parser.cc"
    break;

  case 38: // include_theories: include_theories include_theory
#line 793 "../../mli-root/src/database-parser.yy"
                                    {}
#line 1080 "../../mli-root/src/database-parser.cc"
    break;

  case 39: // include_theory: "include" "theory" theory_name "."
#line 797 "../../mli-root/src/database-parser.yy"
                                         {
      std::optional<ref<theory>> th = yypval.find(yystack_[1].value.text);

      if (!th)
        throw syntax_error(yystack_[1].location, "Include theory " + yystack_[1].value.text + " not found.");

      theory_->insert(*th);
    }
#line 1093 "../../mli-root/src/database-parser.cc"
    break;

  case 40: // theory_name: "name"
#line 809 "../../mli-root/src/database-parser.yy"
                { yylhs.value = yystack_[0].value; }
#line 1099 "../../mli-root/src/database-parser.cc"
    break;

  case 41: // theory_name: "label"
#line 810 "../../mli-root/src/database-parser.yy"
                { yylhs.value = yystack_[0].value; }
#line 1105 "../../mli-root/src/database-parser.cc"
    break;

  case 42: // theory_body: theory_body_list
#line 815 "../../mli-root/src/database-parser.yy"
                     {}
#line 1111 "../../mli-root/src/database-parser.cc"
    break;

  case 43: // theory_body: formal_system theory_body_list
#line 816 "../../mli-root/src/database-parser.yy"
                                   {}
#line 1117 "../../mli-root/src/database-parser.cc"
    break;

  case 44: // $@5: %empty
#line 822 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(); }
#line 1123 "../../mli-root/src/database-parser.cc"
    break;

  case 45: // formal_system: "formal system" "." $@5 formal_system_body "end" "formal system" "."
#line 824 "../../mli-root/src/database-parser.yy"
                              { symbol_table.pop_level(); }
#line 1129 "../../mli-root/src/database-parser.cc"
    break;

  case 47: // formal_system_body: formal_system_body formal_system_body_item
#line 830 "../../mli-root/src/database-parser.yy"
                                               {}
#line 1135 "../../mli-root/src/database-parser.cc"
    break;

  case 48: // formal_system_body_item: identifier_declaration
#line 835 "../../mli-root/src/database-parser.yy"
                           {}
#line 1141 "../../mli-root/src/database-parser.cc"
    break;

  case 49: // formal_system_body_item: postulate
#line 836 "../../mli-root/src/database-parser.yy"
                 { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1147 "../../mli-root/src/database-parser.cc"
    break;

  case 50: // formal_system_body_item: definition_labelstatement
#line 837 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1153 "../../mli-root/src/database-parser.cc"
    break;

  case 52: // theory_body_list: theory_body_list theory_body_item
#line 843 "../../mli-root/src/database-parser.yy"
                                      {}
#line 1159 "../../mli-root/src/database-parser.cc"
    break;

  case 53: // theory_body_item: theorem
#line 853 "../../mli-root/src/database-parser.yy"
               { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1165 "../../mli-root/src/database-parser.cc"
    break;

  case 54: // theory_body_item: identifier_declaration
#line 854 "../../mli-root/src/database-parser.yy"
                           {}
#line 1171 "../../mli-root/src/database-parser.cc"
    break;

  case 55: // theory_body_item: conjecture
#line 855 "../../mli-root/src/database-parser.yy"
                  { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1177 "../../mli-root/src/database-parser.cc"
    break;

  case 56: // theory_body_item: definition_labelstatement
#line 857 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1183 "../../mli-root/src/database-parser.cc"
    break;

  case 57: // $@6: %empty
#line 863 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1189 "../../mli-root/src/database-parser.cc"
    break;

  case 58: // postulate: "postulate" statement_name "." $@6 statement "."
#line 864 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.object = ref<supposition>(make, supposition::postulate_, yystack_[4].value.text, yystack_[1].value.object, true);
    }
#line 1198 "../../mli-root/src/database-parser.cc"
    break;

  case 60: // $@7: %empty
#line 870 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1204 "../../mli-root/src/database-parser.cc"
    break;

  case 61: // postulate: "axiom" statement_name "." $@7 statement "."
#line 871 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      ref<formula> f(yystack_[1].value.object);

      if (!f->is_axiom())
        throw syntax_error(yystack_[1].location, "Axiom statement not an object formula.");

      yylhs.value.object = ref<supposition>(make, supposition::postulate_, yystack_[4].value.text, f);
    }
#line 1219 "../../mli-root/src/database-parser.cc"
    break;

  case 62: // $@8: %empty
#line 882 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1225 "../../mli-root/src/database-parser.cc"
    break;

  case 63: // postulate: "rule" statement_name "." $@8 statement "."
#line 883 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      ref<formula> f(yystack_[1].value.object);

      if (!f->is_rule())
        throw syntax_error(yystack_[1].location, "Rule statement not an inference.");

      yylhs.value.object = ref<supposition>(make, supposition::postulate_, yystack_[4].value.text, f);
    }
#line 1240 "../../mli-root/src/database-parser.cc"
    break;

  case 64: // $@9: %empty
#line 898 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1246 "../../mli-root/src/database-parser.cc"
    break;

  case 65: // conjecture: "conjecture" statement_name "." $@9 statement "."
#line 899 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.object = ref<supposition>(make, supposition::conjecture_, yystack_[4].value.text, yystack_[1].value.object, true);
    }
#line 1255 "../../mli-root/src/database-parser.cc"
    break;

  case 66: // $@10: %empty
#line 907 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1261 "../../mli-root/src/database-parser.cc"
    break;

  case 67: // definition_labelstatement: "definition" statement_name "." $@10 definition_statement "."
#line 908 "../../mli-root/src/database-parser.yy"
                                {
      symbol_table.pop_level();
      yylhs.value.text = yystack_[4].value.text;
      yylhs.value.object = ref<definition>(make, yystack_[4].value.text, yystack_[1].value.object);
    }
#line 1271 "../../mli-root/src/database-parser.cc"
    break;

  case 68: // statement_name: "name"
#line 917 "../../mli-root/src/database-parser.yy"
              { yylhs.value.text = yystack_[0].value.text; }
#line 1277 "../../mli-root/src/database-parser.cc"
    break;

  case 69: // statement_name: "label"
#line 918 "../../mli-root/src/database-parser.yy"
               { yylhs.value.text = yystack_[0].value.text; }
#line 1283 "../../mli-root/src/database-parser.cc"
    break;

  case 70: // statement_name: "natural number value"
#line 919 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.text = yystack_[0].value.text; }
#line 1289 "../../mli-root/src/database-parser.cc"
    break;

  case 71: // theorem: theorem_statement proof
#line 924 "../../mli-root/src/database-parser.yy"
                            {
      yylhs.value.object = statement_stack_.back();
      ref<statement> t(yylhs.value.object); // The theorem.
      t->prove(proof_count);     // Attempt to prove the theorem.
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
#line 1301 "../../mli-root/src/database-parser.cc"
    break;

  case 72: // theorem_statement: theorem_head statement
#line 935 "../../mli-root/src/database-parser.yy"
                                 {
      symbol_table_t::table& top = symbol_table.top();
      ref<theorem> tr(make,
        theorem::type(yystack_[1].value.number), yystack_[1].value.text, yystack_[0].value.object, theory_, proof_depth);
      statement_stack_.back() = tr;
      theorem_theory_ = tr->get_theory();
    }
#line 1313 "../../mli-root/src/database-parser.cc"
    break;

  case 73: // theorem_head: "theorem" statement_name "."
#line 946 "../../mli-root/src/database-parser.yy"
                                       {
      yylhs.value.text = yystack_[1].value.text;
      yylhs.value.number = yystack_[2].value.number;
      symbol_table.push_level();
      statement_stack_.push_back(ref<statement>());
    }
#line 1324 "../../mli-root/src/database-parser.cc"
    break;

  case 75: // $@11: %empty
#line 957 "../../mli-root/src/database-parser.yy"
    {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 1334 "../../mli-root/src/database-parser.cc"
    break;

  case 76: // proof: $@11 proof_of_conclusion
#line 962 "../../mli-root/src/database-parser.yy"
                        {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 1344 "../../mli-root/src/database-parser.cc"
    break;

  case 77: // compound-proof: proof_head proof_lines "∎"
#line 971 "../../mli-root/src/database-parser.yy"
                               {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 1354 "../../mli-root/src/database-parser.cc"
    break;

  case 79: // proof_head: "proof"
#line 981 "../../mli-root/src/database-parser.yy"
            {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 1364 "../../mli-root/src/database-parser.cc"
    break;

  case 81: // proof_lines: proof_lines proof_line
#line 991 "../../mli-root/src/database-parser.yy"
                           {}
#line 1370 "../../mli-root/src/database-parser.cc"
    break;

  case 82: // statement_label: statement_name "."
#line 996 "../../mli-root/src/database-parser.yy"
                          {
      yylhs.value.text = yystack_[1].value.text;
      symbol_table.push_level();
    }
#line 1379 "../../mli-root/src/database-parser.cc"
    break;

  case 83: // proof_line: statement_label statement "by" find_statement "."
#line 1004 "../../mli-root/src/database-parser.yy"
                                                               {
      // Handles explicit find_statement substitutions A[x⤇e].
      proofline_database_context = false;

      theorem& t = ref_cast<theorem&>(statement_stack_.back());

      bool concluding = false;

      if (t.get_formula() == yystack_[3].value.object || head(t) == yystack_[3].value.object)
        concluding = true;

      if (!concluding && yystack_[4].value.text == "conclusion")
        throw syntax_error(yystack_[4].location, "Proof line name “conclusion” used when not the theorem conclusion.");

      if (!concluding && yystack_[4].value.text == "result")
        throw syntax_error(yystack_[4].location, "Proof line name “result” used when not the theorem result.");

      symbol_table_t::table& top = symbol_table.top();

      ref<statement> proof_line =
        t.push_back(
          yystack_[4].value.text, ref<formula>(yystack_[3].value.object), ref<database>(yystack_[1].value.object), concluding, proof_depth);

      symbol_table.pop_level();

      if (!proofline_stack_.insert(yystack_[4].value.text, proof_line)) {
        if (yystack_[4].value.text.empty())
          throw syntax_error(yystack_[4].location, "Proof line empty name “” used.");
        else
          throw syntax_error(yystack_[4].location, "Proof line name " + yystack_[4].value.text  + " already given to a proof line.");
      }
    }
#line 1416 "../../mli-root/src/database-parser.cc"
    break;

  case 84: // proof_line: subproof
#line 1036 "../../mli-root/src/database-parser.yy"
                {
      theorem& t = ref_cast<theorem&>(statement_stack_.back());
      ref<statement> proof_line = t.push_back(ref<statement>(yystack_[0].value.object));
      if (!proofline_stack_.insert(yystack_[0].value.text, proof_line)) {
        if (yystack_[0].value.text.empty())
          throw syntax_error(yystack_[0].location, "Proof line empty name “” used.");
        else
          throw syntax_error(yystack_[0].location, "Proof line name " + yystack_[0].value.text  + " already given to a proof line.");
      }
    }
#line 1431 "../../mli-root/src/database-parser.cc"
    break;

  case 85: // $@12: %empty
#line 1046 "../../mli-root/src/database-parser.yy"
    {}
#line 1437 "../../mli-root/src/database-parser.cc"
    break;

  case 86: // proof_line: $@12 identifier_declaration
#line 1046 "../../mli-root/src/database-parser.yy"
                              {}
#line 1443 "../../mli-root/src/database-parser.cc"
    break;

  case 87: // proof_line: definition_labelstatement
#line 1050 "../../mli-root/src/database-parser.yy"
                                 {
      theorem& t = ref_cast<theorem&>(statement_stack_.back());
      ref<statement> proof_line = t.push_back(ref<statement>(yystack_[0].value.object));

      if (!proofline_stack_.insert(yystack_[0].value.text, proof_line)) {
        if (yystack_[0].value.text.empty())
          throw syntax_error(yystack_[0].location, "Proof line name “” used.");
        else
          throw syntax_error(yystack_[0].location, "Proof line name " + yystack_[0].value.text  + " already given to a proof line.");
      }
    }
#line 1459 "../../mli-root/src/database-parser.cc"
    break;

  case 88: // proof_line: proof_of_conclusion
#line 1061 "../../mli-root/src/database-parser.yy"
                        {}
#line 1465 "../../mli-root/src/database-parser.cc"
    break;

  case 89: // subproof: subproof_statement compound-proof
#line 1066 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.text = yystack_[1].value.text;
      yylhs.value.object = statement_stack_.back();
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
#line 1476 "../../mli-root/src/database-parser.cc"
    break;

  case 90: // subproof_statement: statement_label statement
#line 1076 "../../mli-root/src/database-parser.yy"
                                    {
      yylhs.value.text = yystack_[1].value.text;
      symbol_table_t::table& top = symbol_table.top();
      ref<theorem> tp(make, theorem::claim_, yystack_[1].value.text, yystack_[0].value.object, theory_, proof_depth);
      statement_stack_.push_back(tp);
    }
#line 1487 "../../mli-root/src/database-parser.cc"
    break;

  case 91: // proof_of_conclusion: optional-result "by" find_statement "."
#line 1086 "../../mli-root/src/database-parser.yy"
                                                  {
      proofline_database_context = false;

      theorem& t = ref_cast<theorem&>(statement_stack_.back());
      ref<statement> proof_line =
        t.push_back(yystack_[3].value.text, t.get_formula(), ref<database>(yystack_[1].value.object), true, proof_depth);
    }
#line 1499 "../../mli-root/src/database-parser.cc"
    break;

  case 92: // optional-result: %empty
#line 1097 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.text = "result"; }
#line 1505 "../../mli-root/src/database-parser.cc"
    break;

  case 93: // optional-result: "result"
#line 1098 "../../mli-root/src/database-parser.yy"
                  { yylhs.value = yystack_[0].value; }
#line 1511 "../../mli-root/src/database-parser.cc"
    break;

  case 94: // find_statement: find_statement_list
#line 1103 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<level_database>(make, ref<database>(yystack_[0].value.object)); }
#line 1517 "../../mli-root/src/database-parser.cc"
    break;

  case 95: // find_statement: find_statement ":" find_statement_list
#line 1104 "../../mli-root/src/database-parser.yy"
                                                 {
      ref<level_database>(yystack_[2].value.object)->push_back(ref<database>(yystack_[0].value.object));
      yylhs.value.object = yystack_[2].value.object;
    }
#line 1526 "../../mli-root/src/database-parser.cc"
    break;

  case 96: // find_statement_list: find_statement_sequence
#line 1112 "../../mli-root/src/database-parser.yy"
                               {
      yylhs.value.object = ref<sublevel_database>(make, ref<sequence_database>(yystack_[0].value.object));
    }
#line 1534 "../../mli-root/src/database-parser.cc"
    break;

  case 97: // find_statement_list: find_statement_list ";" find_statement_sequence
#line 1115 "../../mli-root/src/database-parser.yy"
                                                          {
      ref<sublevel_database>(yystack_[2].value.object)->push_back(ref<database>(yystack_[0].value.object));
      yylhs.value.object = yystack_[2].value.object;
    }
#line 1543 "../../mli-root/src/database-parser.cc"
    break;

  case 98: // find_statement_sequence: %empty
#line 1123 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.object = ref<sequence_database>(make); }
#line 1549 "../../mli-root/src/database-parser.cc"
    break;

  case 99: // find_statement_sequence: find_statement_item
#line 1124 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<sequence_database>(make, ref<statement>(yystack_[0].value.object)); }
#line 1556 "../../mli-root/src/database-parser.cc"
    break;

  case 100: // find_statement_sequence: find_statement_item "₍" find_definition_sequence "₎"
#line 1126 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.object = ref<sequence_database>(make, ref<statement>(yystack_[3].value.object));
      ref<sequence_database>(yylhs.value.object)->insert(ref<sequence_database>(yystack_[1].value.object));
    }
#line 1565 "../../mli-root/src/database-parser.cc"
    break;

  case 101: // find_statement_sequence: find_statement_sequence "," find_statement_item
#line 1130 "../../mli-root/src/database-parser.yy"
                                                          {
      ref<sequence_database>(yystack_[2].value.object)->insert(ref<statement>(yystack_[0].value.object));
      yylhs.value.object = yystack_[2].value.object;
    }
#line 1574 "../../mli-root/src/database-parser.cc"
    break;

  case 102: // find_statement_sequence: find_statement_sequence "," find_statement_item "₍" find_definition_sequence "₎"
#line 1134 "../../mli-root/src/database-parser.yy"
                                                                                              {
      yylhs.value.object = yystack_[5].value.object;
      ref<sequence_database>(yylhs.value.object)->insert(ref<statement>(yystack_[3].value.object));
      ref<sequence_database>(yylhs.value.object)->insert(ref<sequence_database>(yystack_[1].value.object));
    }
#line 1584 "../../mli-root/src/database-parser.cc"
    break;

  case 103: // find_definition_sequence: find_statement_item
#line 1143 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<sequence_database>(make, ref<statement>(yystack_[0].value.object)); }
#line 1591 "../../mli-root/src/database-parser.cc"
    break;

  case 104: // find_definition_sequence: find_definition_sequence "," find_statement_item
#line 1145 "../../mli-root/src/database-parser.yy"
                                                           {
      ref<sequence_database>(yystack_[2].value.object)->insert(ref<statement>(yystack_[0].value.object));
      yylhs.value.object = yystack_[2].value.object;
    }
#line 1600 "../../mli-root/src/database-parser.cc"
    break;

  case 105: // find_statement_item: find_statement_name
#line 1153 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = yystack_[0].value.object;
    }
#line 1608 "../../mli-root/src/database-parser.cc"
    break;

  case 106: // find_statement_item: "premise"
#line 1156 "../../mli-root/src/database-parser.yy"
              {
      yylhs.value.object = ref<premise>(make, statement_stack_.back());
    }
#line 1616 "../../mli-root/src/database-parser.cc"
    break;

  case 107: // find_statement_item: "premise" statement_name
#line 1159 "../../mli-root/src/database-parser.yy"
                                {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == yystack_[0].value.text) {
          yylhs.value.object = ref<premise>(make, *i);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(yystack_[0].location, "Proof line premise " + yystack_[0].value.text  + " not found.");
    }
#line 1634 "../../mli-root/src/database-parser.cc"
    break;

  case 108: // find_statement_item: "premise" statement_name "subscript natural number value"
#line 1172 "../../mli-root/src/database-parser.yy"
                                                                  {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == yystack_[1].value.text) {
          size_type k = (size_type)ref_cast<integer&>(yystack_[0].value.object);
          yylhs.value.object = ref<premise>(make, *i, k);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(yystack_[1].location, "Proof line premise " + yystack_[1].value.text  + " not found.");
    }
#line 1653 "../../mli-root/src/database-parser.cc"
    break;

  case 109: // find_statement_item: "premise" "⊢"
#line 1186 "../../mli-root/src/database-parser.yy"
                  {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      yylhs.value.object = ref<premise>(make);
    }
#line 1663 "../../mli-root/src/database-parser.cc"
    break;

  case 110: // find_statement_item: "premise" "⊢" "subscript natural number value"
#line 1191 "../../mli-root/src/database-parser.yy"
                                                    {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      size_type k = (size_type)ref_cast<integer&>(yystack_[0].value.object);
      yylhs.value.object = ref<premise>(make, k);
    }
#line 1674 "../../mli-root/src/database-parser.cc"
    break;

  case 111: // find_statement_name: statement_name
#line 1201 "../../mli-root/src/database-parser.yy"
                      {
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref<statement>> st;
      st = proofline_stack_.find(yystack_[0].value.text);

      if (!st)
        st = theorem_theory_->find(yystack_[0].value.text, 0);

      if (!st)
        throw syntax_error(yystack_[0].location,
          "statement name " + yystack_[0].value.text + " not found earlier in proof, in premises or theory.");

      yylhs.value.object = *st;
    }
#line 1693 "../../mli-root/src/database-parser.cc"
    break;

  case 112: // @13: %empty
#line 1215 "../../mli-root/src/database-parser.yy"
                      {
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref<statement>> st;
      st = proofline_stack_.find(yystack_[0].value.text);
      if (!st)
        st = theorem_theory_->find(yystack_[0].value.text, 0);

      if (!st)
        throw syntax_error(yystack_[0].location,
          "statement name " + yystack_[0].value.text + " not found earlier in proof, in premises or theory.");

      yylhs.value.object = *st;
      // Find the variables of *st and record them for use in the substitution domain checks:
      ref<statement> pr = *st;
      statement_variables_.clear();
      pr->declared(statement_variables_);
      // Then push the declared *st variables & constants onto symbol_table
      // making them usable in substitution codomains:
      symbol_table.push_level();
      for (auto& i: statement_variables_)
        symbol_table.insert(i->name, {to_token(i->type_), i});
    }
#line 1720 "../../mli-root/src/database-parser.cc"
    break;

  case 113: // find_statement_name: statement_name @13 metaformula_substitution_sequence
#line 1238 "../../mli-root/src/database-parser.yy"
                                         {
      // The try-catch checks whether the statement-substitution is legal:
      ref<statement> p(yystack_[1].value.object);
      ref<substitution> s(yystack_[0].value.object);
      try {
        yylhs.value.object = ref<statement_substitution>(make, p, s);
      } catch (illegal_substitution&) {
        mli::database_parser::error(yystack_[0].location, "Proposition substitute error.");
        p->write(std::cerr,
          write_style(write_name | write_type | write_statement));
        std::cerr << "\n  " << s << std::endl;
        YYERROR;        
      }
      symbol_table.pop_level();
    }
#line 1740 "../../mli-root/src/database-parser.cc"
    break;

  case 114: // statement: metaformula
#line 1257 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.object = ref<formula>(yystack_[0].value.object)->set_bind(); }
#line 1746 "../../mli-root/src/database-parser.cc"
    break;

  case 115: // statement: identifier_declaration metaformula
#line 1258 "../../mli-root/src/database-parser.yy"
                                          {
      ref<formula> f(yystack_[0].value.object);
      yylhs.value.object = f->set_bind();

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
          mli::database_parser::error(yystack_[0].location, "warning: " + ds);
        else
          throw syntax_error(yystack_[0].location, ds);
        }
      }
    }
#line 1791 "../../mli-root/src/database-parser.cc"
    break;

  case 116: // definition_statement: definition
#line 1302 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.object = ref<formula>(yystack_[0].value.object)->set_bind(); }
#line 1797 "../../mli-root/src/database-parser.cc"
    break;

  case 117: // definition_statement: identifier_declaration definition
#line 1303 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.object = ref<formula>(yystack_[0].value.object)->set_bind();
    }
#line 1805 "../../mli-root/src/database-parser.cc"
    break;

  case 118: // identifier_declaration: declarator_list "."
#line 1310 "../../mli-root/src/database-parser.yy"
                        {}
#line 1811 "../../mli-root/src/database-parser.cc"
    break;

  case 119: // declarator_list: declarator_identifier_list
#line 1315 "../../mli-root/src/database-parser.yy"
                               {}
#line 1817 "../../mli-root/src/database-parser.cc"
    break;

  case 120: // declarator_list: declarator_list declarator_identifier_list
#line 1316 "../../mli-root/src/database-parser.yy"
                                               {}
#line 1823 "../../mli-root/src/database-parser.cc"
    break;

  case 121: // declarator_identifier_list: "identifier constant" identifier_constant_list
#line 1321 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 1829 "../../mli-root/src/database-parser.cc"
    break;

  case 122: // declarator_identifier_list: "identifier variable" identifier_variable_list
#line 1322 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 1835 "../../mli-root/src/database-parser.cc"
    break;

  case 123: // declarator_identifier_list: "identifier function" identifier_function_list
#line 1323 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 1841 "../../mli-root/src/database-parser.cc"
    break;

  case 124: // identifier_function_list: identifier_function_name
#line 1328 "../../mli-root/src/database-parser.yy"
                             {}
#line 1847 "../../mli-root/src/database-parser.cc"
    break;

  case 125: // identifier_function_list: identifier_function_list "," identifier_function_name
#line 1329 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 1853 "../../mli-root/src/database-parser.cc"
    break;

  case 126: // $@14: %empty
#line 1340 "../../mli-root/src/database-parser.yy"
              { current_declared_token = declared_token; }
#line 1859 "../../mli-root/src/database-parser.cc"
    break;

  case 127: // $@15: %empty
#line 1341 "../../mli-root/src/database-parser.yy"
        { bound_variable_type = database_parser::token::function_map_variable; }
#line 1865 "../../mli-root/src/database-parser.cc"
    break;

  case 128: // identifier_function_name: "name" $@14 ":" $@15 "function map variable" "↦" object_formula
#line 1342 "../../mli-root/src/database-parser.yy"
                                                   {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[6].value.text);
      if (x0) {
        throw syntax_error(yystack_[6].location, "Name " + yystack_[6].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[6].value.text, {current_declared_token,
        ref<function_map>(make, yystack_[2].value.object, yystack_[0].value.object)});
    }
#line 1881 "../../mli-root/src/database-parser.cc"
    break;

  case 129: // identifier_constant_list: identifier_constant_name
#line 1375 "../../mli-root/src/database-parser.yy"
                             {}
#line 1887 "../../mli-root/src/database-parser.cc"
    break;

  case 130: // identifier_constant_list: identifier_constant_list "," identifier_constant_name
#line 1376 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 1893 "../../mli-root/src/database-parser.cc"
    break;

  case 131: // identifier_constant_name: "name"
#line 1381 "../../mli-root/src/database-parser.yy"
              {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[0].value.text);
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.text, {declared_token,
        ref<constant>(make, yystack_[0].value.text, constant::type(declared_type))});
    }
#line 1909 "../../mli-root/src/database-parser.cc"
    break;

  case 132: // identifier_variable_list: identifier_variable_name
#line 1396 "../../mli-root/src/database-parser.yy"
                             {}
#line 1915 "../../mli-root/src/database-parser.cc"
    break;

  case 133: // identifier_variable_list: identifier_variable_list "," identifier_variable_name
#line 1397 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 1921 "../../mli-root/src/database-parser.cc"
    break;

  case 134: // identifier_variable_name: "name"
#line 1402 "../../mli-root/src/database-parser.yy"
              {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[0].value.text);
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.text, {declared_token,
       ref<variable>(make, yystack_[0].value.text, variable::ordinary_, variable::type(declared_type), -1)});
    }
#line 1937 "../../mli-root/src/database-parser.cc"
    break;

  case 135: // identifier_variable_name: "°" "name"
#line 1413 "../../mli-root/src/database-parser.yy"
                  {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[0].value.text);
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.text, {declared_token,
        ref<variable>(make, yystack_[0].value.text, variable::limited_, variable::type(declared_type), -1)});
    }
#line 1953 "../../mli-root/src/database-parser.cc"
    break;

  case 136: // identifier_variable_name: "•" "name"
#line 1424 "../../mli-root/src/database-parser.yy"
                  {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[0].value.text);
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.text, {declared_token,
        ref<variable>(make, yystack_[0].value.text, variable::term_, variable::type(declared_type), -1)});
    }
#line 1969 "../../mli-root/src/database-parser.cc"
    break;

  case 137: // definition: metaformula_definition
#line 1439 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[0].value.object; }
#line 1975 "../../mli-root/src/database-parser.cc"
    break;

  case 138: // definition: object_formula_definition
#line 1440 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.object = yystack_[0].value.object; }
#line 1981 "../../mli-root/src/database-parser.cc"
    break;

  case 139: // definition: term_definition
#line 1441 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 1987 "../../mli-root/src/database-parser.cc"
    break;

  case 140: // metaformula_definition: pure_metaformula "≔" pure_metaformula
#line 1446 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), ref<formula>(),
        formula::logic, formula_definition_oprec);
    }
#line 1996 "../../mli-root/src/database-parser.cc"
    break;

  case 141: // metaformula_definition: pure_metaformula "≕" pure_metaformula
#line 1450 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[2].value.object), ref<formula>(),
       formula::logic, formula_definition_oprec);
  }
#line 2005 "../../mli-root/src/database-parser.cc"
    break;

  case 142: // object_formula_definition: object_formula "≔" object_formula
#line 1463 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), ref<formula>(),
        formula::logic, formula_definition_oprec);
    }
#line 2014 "../../mli-root/src/database-parser.cc"
    break;

  case 143: // object_formula_definition: object_formula "≕" object_formula
#line 1467 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[2].value.object), ref<formula>(),
        formula::logic, formula_definition_oprec);
  }
#line 2023 "../../mli-root/src/database-parser.cc"
    break;

  case 144: // term_definition: term "≔" term
#line 1480 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), ref<formula>(),
        formula::object, term_definition_oprec);
    }
#line 2032 "../../mli-root/src/database-parser.cc"
    break;

  case 145: // term_definition: term "≕" term
#line 1490 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[2].value.object), ref<formula>(),
        formula::object, term_definition_oprec);
  }
#line 2041 "../../mli-root/src/database-parser.cc"
    break;

  case 146: // metaformula: pure_metaformula
#line 1498 "../../mli-root/src/database-parser.yy"
                        { yylhs.value.object = yystack_[0].value.object; }
#line 2047 "../../mli-root/src/database-parser.cc"
    break;

  case 147: // metaformula: object_formula
#line 1499 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.object = yystack_[0].value.object; }
#line 2053 "../../mli-root/src/database-parser.cc"
    break;

  case 148: // pure_metaformula: atomic_metaformula
#line 1504 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 2059 "../../mli-root/src/database-parser.cc"
    break;

  case 149: // pure_metaformula: special_metaformula
#line 1505 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = yystack_[0].value.object; }
#line 2065 "../../mli-root/src/database-parser.cc"
    break;

  case 150: // pure_metaformula: "~" metaformula
#line 1506 "../../mli-root/src/database-parser.yy"
                       {
      yylhs.value.object = ref<metanot>(make, ref<formula>(yystack_[0].value.object));
    }
#line 2073 "../../mli-root/src/database-parser.cc"
    break;

  case 151: // pure_metaformula: metaformula ";" metaformula
#line 1509 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.object = mli::concatenate(ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object));
    }
#line 2081 "../../mli-root/src/database-parser.cc"
    break;

  case 152: // pure_metaformula: metaformula "," metaformula
#line 1512 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.object = mli::concatenate(ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object));
    }
#line 2089 "../../mli-root/src/database-parser.cc"
    break;

  case 153: // pure_metaformula: metaformula "⊩" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_matrix metaformula
#line 1517 "../../mli-root/src/database-parser.yy"
                     {
      size_type k = (size_type)ref_cast<integer&>(yystack_[3].value.object);

      if (k < 1)
        k = 2;
      else
        k += 2;

      ref<inference> i(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[5].value.object), metalevel_t(k));

      inference* mp = ref_cast<inference*>(yystack_[2].value.object);
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = ref_cast<inference*>(yystack_[1].value.object);
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
          throw syntax_error(yystack_[2].location,
            "inference varied variable conclusion index " + std::to_string(vc_max)
            + " must be less than the number of conclusions " + std::to_string(n_head) + ".");

        if (vp_max >= n_body)
          throw syntax_error(yystack_[2].location,
            "inference varied variable premise index " + std::to_string(vp_max)
            + " must be less than the number of premises " + std::to_string(n_body) + ".");
      }

      yylhs.value.object = i;
    }
#line 2148 "../../mli-root/src/database-parser.cc"
    break;

  case 154: // pure_metaformula: metaformula "⊢" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_matrix metaformula
#line 1585 "../../mli-root/src/database-parser.yy"
                     {
      size_type k = (size_type)ref_cast<integer&>(yystack_[3].value.object);

      if (k < 1)
        k = 1;

      ref<inference> i(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[5].value.object), metalevel_t(k));

      inference* mp = ref_cast<inference*>(yystack_[2].value.object);
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = ref_cast<inference*>(yystack_[1].value.object);
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
          throw syntax_error(yystack_[2].location,
            "inference varied variable conclusion index " + std::to_string(vc_max)
            + " must be less than the number of conclusions " + std::to_string(n_head) + ".");

        if (vp_max >= n_body)
          throw syntax_error(yystack_[2].location,
            "inference varied variable premise index " + std::to_string(vp_max)
            + " must be less than the number of premises " + std::to_string(n_body) + ".");
      }

      yylhs.value.object = i;
    }
#line 2205 "../../mli-root/src/database-parser.cc"
    break;

  case 155: // pure_metaformula: "⊢" metaformula
#line 1644 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = ref<inference>(make, ref<formula>(yystack_[0].value.object)); }
#line 2211 "../../mli-root/src/database-parser.cc"
    break;

  case 156: // pure_metaformula: "(" pure_metaformula ")"
#line 1646 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.object = yystack_[1].value.object; }
#line 2217 "../../mli-root/src/database-parser.cc"
    break;

  case 157: // pure_metaformula: simple_metaformula metaformula_substitution_sequence
#line 1647 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.object = ref<substitution_formula>(make, ref<substitution>(yystack_[0].value.object), ref<formula>(yystack_[1].value.object)); }
#line 2224 "../../mli-root/src/database-parser.cc"
    break;

  case 159: // optional_varied_variable_matrix: "⁽" varied_variable_conclusions "⁾"
#line 1654 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.object = yystack_[1].value.object; }
#line 2230 "../../mli-root/src/database-parser.cc"
    break;

  case 160: // optional_varied_variable_matrix: "⁽" varied_variable_premises "⁾"
#line 1655 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.object = yystack_[1].value.object; }
#line 2236 "../../mli-root/src/database-parser.cc"
    break;

  case 161: // optional_varied_variable_matrix: "⁽" varied_variable_set "⁾"
#line 1656 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.object = yystack_[1].value.object; }
#line 2242 "../../mli-root/src/database-parser.cc"
    break;

  case 163: // varied_variable_conclusions: varied_variable_conclusions ";" varied_variable_conclusion
#line 1661 "../../mli-root/src/database-parser.yy"
                                                                      {
      inference& xs = ref_cast<inference&>(yystack_[2].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      for (auto& i: x.varied_)
        for (auto& j: i.second)
          xs.varied_[i.first][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.object = yystack_[2].value.object;
    }
#line 2257 "../../mli-root/src/database-parser.cc"
    break;

  case 164: // varied_variable_conclusion: "superscript natural number value" varied_variable_premises
#line 1674 "../../mli-root/src/database-parser.yy"
                                                                     {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>(yystack_[0].value.object);
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      i->varied_[k].insert(xs.varied_[0].begin(), xs.varied_[0].end());
      yylhs.value.object = i;

    }
#line 2271 "../../mli-root/src/database-parser.cc"
    break;

  case 166: // varied_variable_premises: varied_variable_premises "," varied_variable_premise
#line 1687 "../../mli-root/src/database-parser.yy"
                                                                {
      inference& xs = ref_cast<inference&>(yystack_[2].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      for (auto& j: x.varied_[0])
        xs.varied_[0][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.object = yystack_[2].value.object;
    }
#line 2285 "../../mli-root/src/database-parser.cc"
    break;

  case 167: // varied_variable_premise: "superscript natural number value" varied_variable_set
#line 1699 "../../mli-root/src/database-parser.yy"
                                                                {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>(yystack_[0].value.object);
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      i->varied_[0][k].insert(xs.varied_[0][0].begin(), xs.varied_[0][0].end());

      yylhs.value.object = i;
    }
#line 2299 "../../mli-root/src/database-parser.cc"
    break;

  case 169: // varied_variable_set: varied_variable_set varied_variable
#line 1712 "../../mli-root/src/database-parser.yy"
                                               {
      inference& xs = ref_cast<inference&>(yystack_[1].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      xs.varied_[0][0].insert(x.varied_[0][0].begin(), x.varied_[0][0].end());

      yylhs.value.object = yystack_[1].value.object;
    }
#line 2312 "../../mli-root/src/database-parser.cc"
    break;

  case 170: // varied_variable: "object variable"
#line 1723 "../../mli-root/src/database-parser.yy"
                       {
      ref<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.object);
      yylhs.value.object = i;
    }
#line 2322 "../../mli-root/src/database-parser.cc"
    break;

  case 171: // varied_variable: "metaformula variable"
#line 1728 "../../mli-root/src/database-parser.yy"
                            {
      ref<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.object);
      yylhs.value.object = i;
    }
#line 2332 "../../mli-root/src/database-parser.cc"
    break;

  case 173: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_conclusions "₎"
#line 1739 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.object = yystack_[1].value.object; }
#line 2338 "../../mli-root/src/database-parser.cc"
    break;

  case 174: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_premises "₎"
#line 1740 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.object = yystack_[1].value.object; }
#line 2344 "../../mli-root/src/database-parser.cc"
    break;

  case 175: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_set "₎"
#line 1741 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.object = yystack_[1].value.object; }
#line 2350 "../../mli-root/src/database-parser.cc"
    break;

  case 177: // varied_in_reduction_variable_conclusions: varied_in_reduction_variable_conclusions ";" varied_in_reduction_variable_conclusion
#line 1746 "../../mli-root/src/database-parser.yy"
                                                                                                {
      inference& xs = ref_cast<inference&>(yystack_[2].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      for (auto& i: x.varied_in_reduction_)
        for (auto& j: i.second)
          xs.varied_in_reduction_[i.first][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.object = yystack_[2].value.object;
    }
#line 2365 "../../mli-root/src/database-parser.cc"
    break;

  case 178: // varied_in_reduction_variable_conclusion: "subscript natural number value" varied_in_reduction_variable_premises
#line 1759 "../../mli-root/src/database-parser.yy"
                                                                                {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>(yystack_[0].value.object);
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      i->varied_in_reduction_[k].insert(xs.varied_in_reduction_[0].begin(), xs.varied_in_reduction_[0].end());
      yylhs.value.object = i;

    }
#line 2379 "../../mli-root/src/database-parser.cc"
    break;

  case 180: // varied_in_reduction_variable_premises: varied_in_reduction_variable_premises "," varied_in_reduction_variable_premise
#line 1772 "../../mli-root/src/database-parser.yy"
                                                                                          {
      inference& xs = ref_cast<inference&>(yystack_[2].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      for (auto& j: x.varied_in_reduction_[0])
        xs.varied_in_reduction_[0][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.object = yystack_[2].value.object;
    }
#line 2393 "../../mli-root/src/database-parser.cc"
    break;

  case 181: // varied_in_reduction_variable_premise: "subscript natural number value" varied_in_reduction_variable_set
#line 1784 "../../mli-root/src/database-parser.yy"
                                                                           {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>(yystack_[0].value.object);
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      i->varied_in_reduction_[0][k].insert(xs.varied_in_reduction_[0][0].begin(), xs.varied_in_reduction_[0][0].end());

      yylhs.value.object = i;
    }
#line 2407 "../../mli-root/src/database-parser.cc"
    break;

  case 183: // varied_in_reduction_variable_set: varied_in_reduction_variable_set varied_in_reduction_variable
#line 1797 "../../mli-root/src/database-parser.yy"
                                                                         {
      inference& xs = ref_cast<inference&>(yystack_[1].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      xs.varied_in_reduction_[0][0].insert(x.varied_in_reduction_[0][0].begin(), x.varied_in_reduction_[0][0].end());

      yylhs.value.object = yystack_[1].value.object;
    }
#line 2420 "../../mli-root/src/database-parser.cc"
    break;

  case 184: // varied_in_reduction_variable: "object variable"
#line 1808 "../../mli-root/src/database-parser.yy"
                       {
      ref<inference> i(make);
      i->varied_in_reduction_[0][0].insert(yystack_[0].value.object);
      yylhs.value.object = i;
    }
#line 2430 "../../mli-root/src/database-parser.cc"
    break;

  case 185: // varied_in_reduction_variable: "metaformula variable"
#line 1813 "../../mli-root/src/database-parser.yy"
                            {
      ref<inference> i(make);
      i->varied_in_reduction_[0][0].insert(yystack_[0].value.object);
      yylhs.value.object = i;
    }
#line 2440 "../../mli-root/src/database-parser.cc"
    break;

  case 186: // simple_metaformula: "metaformula variable"
#line 1881 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 2446 "../../mli-root/src/database-parser.cc"
    break;

  case 187: // simple_metaformula: "(" pure_metaformula ")"
#line 1882 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.object = yystack_[1].value.object; }
#line 2452 "../../mli-root/src/database-parser.cc"
    break;

  case 188: // atomic_metaformula: "metaformula variable"
#line 1887 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 2458 "../../mli-root/src/database-parser.cc"
    break;

  case 189: // atomic_metaformula: metapredicate
#line 1888 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2464 "../../mli-root/src/database-parser.cc"
    break;

  case 190: // special_metaformula: meta_object_free "≢" meta_object_free
#line 1900 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.object = ref<objectidentical>(make, ref<variable>(yystack_[2].value.object), ref<variable>(yystack_[0].value.object), false);
    }
#line 2472 "../../mli-root/src/database-parser.cc"
    break;

  case 191: // special_metaformula: meta_object_free "free in" object_formula
#line 1903 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.object = ref<free_in_object>(make, ref<variable>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2480 "../../mli-root/src/database-parser.cc"
    break;

  case 192: // special_metaformula: meta_object_free "free in" term
#line 1906 "../../mli-root/src/database-parser.yy"
                                          {
      yylhs.value.object = ref<free_in_object>(make, ref<variable>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2488 "../../mli-root/src/database-parser.cc"
    break;

  case 193: // special_metaformula: meta_object_free "not" "free in" object_formula
#line 1909 "../../mli-root/src/database-parser.yy"
                                                          {
      yylhs.value.object = ref<free_in_object>(make, ref<variable>(yystack_[3].value.object), ref<formula>(yystack_[0].value.object), false);
    }
#line 2496 "../../mli-root/src/database-parser.cc"
    break;

  case 194: // special_metaformula: meta_object_free "not" "free in" term
#line 1912 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.object = ref<free_in_object>(make, ref<variable>(yystack_[3].value.object), ref<formula>(yystack_[0].value.object), false);
    }
#line 2504 "../../mli-root/src/database-parser.cc"
    break;

  case 195: // special_metaformula: term "free for" meta_object_free "in" object_formula
#line 1915 "../../mli-root/src/database-parser.yy"
                                                                  {
      yylhs.value.object = ref<free_for_object>(make, 
        ref<formula>(yystack_[4].value.object), ref<variable>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2513 "../../mli-root/src/database-parser.cc"
    break;

  case 196: // special_metaformula: term "free for" meta_object_free "in" term
#line 1919 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.object = ref<free_for_object>(make, 
        ref<formula>(yystack_[4].value.object), ref<variable>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2522 "../../mli-root/src/database-parser.cc"
    break;

  case 197: // meta_object_free: "object variable"
#line 1927 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 2528 "../../mli-root/src/database-parser.cc"
    break;

  case 198: // metapredicate: metapredicate_function
#line 1932 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[0].value.object; }
#line 2534 "../../mli-root/src/database-parser.cc"
    break;

  case 199: // metapredicate: object_formula "≣" object_formula
#line 1933 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.object = ref<identical>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2542 "../../mli-root/src/database-parser.cc"
    break;

  case 200: // metapredicate: object_formula "≣̷" object_formula
#line 1936 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.object = ref<identical>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), false);
    }
#line 2550 "../../mli-root/src/database-parser.cc"
    break;

  case 201: // metapredicate: term "≣" term
#line 1939 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.object = ref<identical>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2558 "../../mli-root/src/database-parser.cc"
    break;

  case 202: // metapredicate: term "≣̷" term
#line 1942 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.object = ref<identical>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), false);
    }
#line 2566 "../../mli-root/src/database-parser.cc"
    break;

  case 203: // metapredicate_function: "metapredicate constant" metapredicate_argument
#line 1949 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.object = ref<structure>(make, ref<formula>(yystack_[1].value.object), ref<formula>(yystack_[0].value.object),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 2575 "../../mli-root/src/database-parser.cc"
    break;

  case 204: // metapredicate_function: "metaformula variable" metapredicate_argument
#line 1953 "../../mli-root/src/database-parser.yy"
                                                      {
      yylhs.value.object = ref<structure>(make, ref<formula>(yystack_[1].value.object), ref<formula>(yystack_[0].value.object),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 2584 "../../mli-root/src/database-parser.cc"
    break;

  case 205: // metapredicate_argument: "(" metapredicate_argument_body ")"
#line 1961 "../../mli-root/src/database-parser.yy"
                                           { yylhs.value.object = yystack_[1].value.object; }
#line 2590 "../../mli-root/src/database-parser.cc"
    break;

  case 206: // metapredicate_argument_body: object_formula
#line 1966 "../../mli-root/src/database-parser.yy"
                      {
      ref<sequence> vr(make, sequence::tuple);
      yylhs.value.object = vr;
      vr->push_back(ref<formula>(yystack_[0].value.object)); }
#line 2599 "../../mli-root/src/database-parser.cc"
    break;

  case 207: // metapredicate_argument_body: metapredicate_argument_body "," object_formula
#line 1970 "../../mli-root/src/database-parser.yy"
                                                         {
      yylhs.value.object = yystack_[2].value.object;
      sequence& vr = ref_cast<sequence&>(yylhs.value.object);
      vr.push_back(ref<formula>(yystack_[0].value.object)); }
#line 2608 "../../mli-root/src/database-parser.cc"
    break;

  case 208: // object_formula: atomic_formula
#line 1978 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.object = yystack_[0].value.object; }
#line 2614 "../../mli-root/src/database-parser.cc"
    break;

  case 209: // object_formula: very_simple_formula formula_substitution_sequence
#line 1979 "../../mli-root/src/database-parser.yy"
                                                            {
      yylhs.value.object = ref<substitution_formula>(make, ref<substitution>(yystack_[0].value.object), ref<formula>(yystack_[1].value.object));
    }
#line 2622 "../../mli-root/src/database-parser.cc"
    break;

  case 210: // object_formula: predicate_function_application
#line 1982 "../../mli-root/src/database-parser.yy"
                                      { yylhs.value.object = yystack_[0].value.object; }
#line 2628 "../../mli-root/src/database-parser.cc"
    break;

  case 211: // object_formula: logic_formula
#line 1983 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2634 "../../mli-root/src/database-parser.cc"
    break;

  case 212: // object_formula: "(" object_formula ")"
#line 1984 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[1].value.object; }
#line 2640 "../../mli-root/src/database-parser.cc"
    break;

  case 213: // object_formula: quantized_formula
#line 1985 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 2646 "../../mli-root/src/database-parser.cc"
    break;

  case 214: // object_formula: hoare_triple
#line 1986 "../../mli-root/src/database-parser.yy"
                 {}
#line 2652 "../../mli-root/src/database-parser.cc"
    break;

  case 215: // hoare_triple: "{" object_formula "}" code_sequence "{" object_formula "}"
#line 1991 "../../mli-root/src/database-parser.yy"
                                                              { yylhs.value.object = ref<formula>(); }
#line 2658 "../../mli-root/src/database-parser.cc"
    break;

  case 216: // code_statement: code_term
#line 2002 "../../mli-root/src/database-parser.yy"
              {}
#line 2664 "../../mli-root/src/database-parser.cc"
    break;

  case 218: // code_sequence: %empty
#line 2008 "../../mli-root/src/database-parser.yy"
           {}
#line 2670 "../../mli-root/src/database-parser.cc"
    break;

  case 219: // code_sequence: code_term
#line 2009 "../../mli-root/src/database-parser.yy"
              {}
#line 2676 "../../mli-root/src/database-parser.cc"
    break;

  case 220: // code_sequence: code_sequence ";" code_term
#line 2010 "../../mli-root/src/database-parser.yy"
                                {}
#line 2682 "../../mli-root/src/database-parser.cc"
    break;

  case 221: // code_term: "code variable"
#line 2015 "../../mli-root/src/database-parser.yy"
                 {}
#line 2688 "../../mli-root/src/database-parser.cc"
    break;

  case 222: // code_term: "∅"
#line 2016 "../../mli-root/src/database-parser.yy"
       {}
#line 2694 "../../mli-root/src/database-parser.cc"
    break;

  case 223: // code_term: "object variable" "≔" term
#line 2017 "../../mli-root/src/database-parser.yy"
                            {}
#line 2700 "../../mli-root/src/database-parser.cc"
    break;

  case 224: // code_term: "if" object_formula "then" code_statement "else" code_statement
#line 2018 "../../mli-root/src/database-parser.yy"
                                                                   {}
#line 2706 "../../mli-root/src/database-parser.cc"
    break;

  case 225: // code_term: "while" object_formula "do" code_statement
#line 2019 "../../mli-root/src/database-parser.yy"
                                              {}
#line 2712 "../../mli-root/src/database-parser.cc"
    break;

  case 226: // very_simple_formula: "object formula variable"
#line 2024 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 2718 "../../mli-root/src/database-parser.cc"
    break;

  case 227: // very_simple_formula: "atom variable"
#line 2025 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2724 "../../mli-root/src/database-parser.cc"
    break;

  case 228: // very_simple_formula: "(" object_formula ")"
#line 2026 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[1].value.object; }
#line 2730 "../../mli-root/src/database-parser.cc"
    break;

  case 229: // quantized_formula: quantizer_declaration quantized_body
#line 2031 "../../mli-root/src/database-parser.yy"
                                               {
      symbol_table.pop_level();
      variable_list& vsr = ref_cast<variable_list&>(yystack_[1].value.object);
      yylhs.value.object = ref<bound_formula>(make, vsr, ref<formula>(yystack_[0].value.object));
    }
#line 2740 "../../mli-root/src/database-parser.cc"
    break;

  case 230: // quantized_formula: quantizer_declaration optional_in_term ":" object_formula
#line 2036 "../../mli-root/src/database-parser.yy"
                                                                       {
      symbol_table.pop_level();
      variable_list& vsr = ref_cast<variable_list&>(yystack_[3].value.object);
      yylhs.value.object = ref<bound_formula>(make, vsr, yystack_[2].value.object, ref<formula>(yystack_[0].value.object));
    }
#line 2750 "../../mli-root/src/database-parser.cc"
    break;

  case 231: // quantized_formula: quantizer_declaration optional_in_term quantized_formula
#line 2041 "../../mli-root/src/database-parser.yy"
                                                                      {
      symbol_table.pop_level();
      variable_list& vsr = ref_cast<variable_list&>(yystack_[2].value.object);
      yylhs.value.object = ref<bound_formula>(make, vsr, yystack_[1].value.object, ref<formula>(yystack_[0].value.object));
    }
#line 2760 "../../mli-root/src/database-parser.cc"
    break;

  case 232: // simple_formula: "object formula variable"
#line 2050 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 2766 "../../mli-root/src/database-parser.cc"
    break;

  case 233: // simple_formula: "atom variable"
#line 2051 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2772 "../../mli-root/src/database-parser.cc"
    break;

  case 234: // simple_formula: predicate_expression
#line 2052 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 2778 "../../mli-root/src/database-parser.cc"
    break;

  case 235: // simple_formula: "(" object_formula ")"
#line 2053 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[1].value.object; }
#line 2784 "../../mli-root/src/database-parser.cc"
    break;

  case 236: // simple_formula: quantized_formula
#line 2054 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 2790 "../../mli-root/src/database-parser.cc"
    break;

  case 237: // quantized_body: atomic_formula
#line 2060 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.object = yystack_[0].value.object; }
#line 2796 "../../mli-root/src/database-parser.cc"
    break;

  case 238: // quantized_body: "(" object_formula ")"
#line 2061 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[1].value.object; }
#line 2802 "../../mli-root/src/database-parser.cc"
    break;

  case 239: // atomic_formula: "atom constant"
#line 2065 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2808 "../../mli-root/src/database-parser.cc"
    break;

  case 240: // atomic_formula: "object formula variable"
#line 2066 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 2814 "../../mli-root/src/database-parser.cc"
    break;

  case 241: // atomic_formula: "atom variable"
#line 2067 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2820 "../../mli-root/src/database-parser.cc"
    break;

  case 242: // atomic_formula: predicate
#line 2068 "../../mli-root/src/database-parser.yy"
                 { yylhs.value.object = yystack_[0].value.object; }
#line 2826 "../../mli-root/src/database-parser.cc"
    break;

  case 243: // predicate: predicate_expression
#line 2074 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 2832 "../../mli-root/src/database-parser.cc"
    break;

  case 244: // predicate: term "=" term
#line 2075 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2838 "../../mli-root/src/database-parser.cc"
    break;

  case 245: // predicate: term "≠" term
#line 2076 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2844 "../../mli-root/src/database-parser.cc"
    break;

  case 246: // predicate: term "∣" term
#line 2079 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2850 "../../mli-root/src/database-parser.cc"
    break;

  case 247: // predicate: term "∤" term
#line 2080 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2856 "../../mli-root/src/database-parser.cc"
    break;

  case 248: // predicate: term "<" term
#line 2083 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, less_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2862 "../../mli-root/src/database-parser.cc"
    break;

  case 249: // predicate: term ">" term
#line 2084 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, greater_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2868 "../../mli-root/src/database-parser.cc"
    break;

  case 250: // predicate: term "≤" term
#line 2085 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, less_or_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2874 "../../mli-root/src/database-parser.cc"
    break;

  case 251: // predicate: term "≥" term
#line 2086 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, greater_or_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2880 "../../mli-root/src/database-parser.cc"
    break;

  case 252: // predicate: term "≮" term
#line 2087 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_less_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2886 "../../mli-root/src/database-parser.cc"
    break;

  case 253: // predicate: term "≯" term
#line 2088 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_greater_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2892 "../../mli-root/src/database-parser.cc"
    break;

  case 254: // predicate: term "≰" term
#line 2089 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_less_or_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2898 "../../mli-root/src/database-parser.cc"
    break;

  case 255: // predicate: term "≱" term
#line 2090 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_greater_or_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2904 "../../mli-root/src/database-parser.cc"
    break;

  case 256: // predicate: term "∈" term
#line 2092 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, in_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2910 "../../mli-root/src/database-parser.cc"
    break;

  case 257: // predicate: term "∉" term
#line 2093 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_in_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2916 "../../mli-root/src/database-parser.cc"
    break;

  case 258: // predicate: term "⊆" term
#line 2094 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, subset_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2922 "../../mli-root/src/database-parser.cc"
    break;

  case 259: // predicate: term "⊊" term
#line 2095 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, proper_subset_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2928 "../../mli-root/src/database-parser.cc"
    break;

  case 260: // predicate: term "⊇" term
#line 2096 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, superset_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2934 "../../mli-root/src/database-parser.cc"
    break;

  case 261: // predicate: term "⊋" term
#line 2097 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, proper_superset_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2940 "../../mli-root/src/database-parser.cc"
    break;

  case 262: // $@16: %empty
#line 2098 "../../mli-root/src/database-parser.yy"
          { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 2946 "../../mli-root/src/database-parser.cc"
    break;

  case 263: // $@17: %empty
#line 2099 "../../mli-root/src/database-parser.yy"
                               { bound_variable_type = free_variable_context; }
#line 2952 "../../mli-root/src/database-parser.cc"
    break;

  case 264: // predicate: "Set" $@16 "₍" "Set variable" "₎" $@17 simple_formula
#line 2100 "../../mli-root/src/database-parser.yy"
                       {
      symbol_table.pop_level();
      yylhs.value.object = ref<bound_formula>(make,
        ref<variable>(yystack_[3].value.object), ref<formula>(yystack_[0].value.object), bound_formula::is_set_);
    }
#line 2962 "../../mli-root/src/database-parser.cc"
    break;

  case 265: // predicate_expression: predicate_identifier tuple
#line 2109 "../../mli-root/src/database-parser.yy"
                                     {
      yylhs.value.object = ref<structure>(make, ref<formula>(yystack_[1].value.object), ref<formula>(yystack_[0].value.object),
        structure::predicate, 0_ml, structure::postargument, precedence_t());
    }
#line 2971 "../../mli-root/src/database-parser.cc"
    break;

  case 266: // predicate_identifier: "predicate constant"
#line 2117 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object;  }
#line 2977 "../../mli-root/src/database-parser.cc"
    break;

  case 267: // predicate_identifier: "predicate variable"
#line 2118 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object;  }
#line 2983 "../../mli-root/src/database-parser.cc"
    break;

  case 268: // optional_superscript_natural_number_value: %empty
#line 2123 "../../mli-root/src/database-parser.yy"
           { yylhs.value.object = ref<mli::integer>(make); yylhs.value.text = ""; }
#line 2989 "../../mli-root/src/database-parser.cc"
    break;

  case 270: // logic_formula: "¬" optional_superscript_natural_number_value object_formula
#line 2136 "../../mli-root/src/database-parser.yy"
                                                                          {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::prefix, logical_not_oprec, yystack_[0].value.object);
    }
#line 3000 "../../mli-root/src/database-parser.cc"
    break;

  case 271: // logic_formula: object_formula "∨" optional_superscript_natural_number_value object_formula
#line 2142 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, logical_or_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 3011 "../../mli-root/src/database-parser.cc"
    break;

  case 272: // logic_formula: object_formula "∧" optional_superscript_natural_number_value object_formula
#line 2148 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, logical_and_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 3022 "../../mli-root/src/database-parser.cc"
    break;

  case 273: // logic_formula: object_formula "⇒" optional_superscript_natural_number_value object_formula
#line 2154 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, implies_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 3033 "../../mli-root/src/database-parser.cc"
    break;

  case 274: // logic_formula: object_formula "⇐" optional_superscript_natural_number_value object_formula
#line 2160 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, impliedby_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 3044 "../../mli-root/src/database-parser.cc"
    break;

  case 275: // logic_formula: object_formula "⇔" optional_superscript_natural_number_value object_formula
#line 2166 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, equivalent_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 3055 "../../mli-root/src/database-parser.cc"
    break;

  case 276: // logic_formula: prefix_logic_formula
#line 2172 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object;  }
#line 3061 "../../mli-root/src/database-parser.cc"
    break;

  case 277: // prefix_logic_formula: "prefix formula variable"
#line 2177 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 3067 "../../mli-root/src/database-parser.cc"
    break;

  case 278: // prefix_logic_formula: prefix_not_key prefix_logic_formula
#line 2178 "../../mli-root/src/database-parser.yy"
                                              {
      yylhs.value.object = ref<structure>(make, "¬", structure::logic, 0_ml,
        structure::prefix, logical_not_oprec, yystack_[0].value.object);
    }
#line 3076 "../../mli-root/src/database-parser.cc"
    break;

  case 279: // prefix_logic_formula: prefix_or_key prefix_logic_formula prefix_logic_formula
#line 2182 "../../mli-root/src/database-parser.yy"
                                                                     {
      yylhs.value.object = ref<structure>(make, "∨", structure::logic, 0_ml,
        structure::infix, logical_or_oprec, yystack_[1].value.object, yystack_[0].value.object);
    }
#line 3085 "../../mli-root/src/database-parser.cc"
    break;

  case 280: // prefix_logic_formula: prefix_and_key prefix_logic_formula prefix_logic_formula
#line 2186 "../../mli-root/src/database-parser.yy"
                                                                      {
      yylhs.value.object = ref<structure>(make, "∧", structure::logic, 0_ml,
        structure::infix, logical_and_oprec, yystack_[1].value.object, yystack_[0].value.object);
    }
#line 3094 "../../mli-root/src/database-parser.cc"
    break;

  case 281: // prefix_logic_formula: prefix_implies_key prefix_logic_formula prefix_logic_formula
#line 2190 "../../mli-root/src/database-parser.yy"
                                                                          {
      yylhs.value.object = ref<structure>(make, "⇒", structure::logic, 0_ml,
        structure::infix, implies_oprec, yystack_[1].value.object, yystack_[0].value.object);
    }
#line 3103 "../../mli-root/src/database-parser.cc"
    break;

  case 282: // prefix_logic_formula: prefix_equivalent_key prefix_logic_formula prefix_logic_formula
#line 2194 "../../mli-root/src/database-parser.yy"
                                                                             {
      yylhs.value.object = ref<structure>(make, "⇔", structure::logic, 0_ml,
        structure::infix, equivalent_oprec, yystack_[1].value.object, yystack_[0].value.object);
 }
#line 3112 "../../mli-root/src/database-parser.cc"
    break;

  case 283: // quantizer_declaration: quantized_variable_list
#line 2202 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 3118 "../../mli-root/src/database-parser.cc"
    break;

  case 284: // quantized_variable_list: all_variable_list
#line 2206 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 3124 "../../mli-root/src/database-parser.cc"
    break;

  case 285: // quantized_variable_list: exist_variable_list
#line 2207 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = yystack_[0].value.object; }
#line 3130 "../../mli-root/src/database-parser.cc"
    break;

  case 286: // all_variable_list: "∀" all_identifier_list
#line 2212 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 3136 "../../mli-root/src/database-parser.cc"
    break;

  case 287: // exist_variable_list: "∃" exist_identifier_list
#line 2217 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.object = yystack_[0].value.object; }
#line 3142 "../../mli-root/src/database-parser.cc"
    break;

  case 288: // all_identifier_list: "all variable"
#line 2222 "../../mli-root/src/database-parser.yy"
                    {
      bound_variable_type = free_variable_context;
      yylhs.value.object = ref<variable_list>(make, ref<variable>(yystack_[0].value.object), bound_formula::all_);
    }
#line 3151 "../../mli-root/src/database-parser.cc"
    break;

  case 289: // $@18: %empty
#line 2226 "../../mli-root/src/database-parser.yy"
                           { bound_variable_type = token::all_variable; }
#line 3157 "../../mli-root/src/database-parser.cc"
    break;

  case 290: // all_identifier_list: all_identifier_list $@18 "," "all variable"
#line 2227 "../../mli-root/src/database-parser.yy"
                          {
      bound_variable_type = free_variable_context;
      yylhs.value.object = yystack_[3].value.object;
      ref_cast<variable_list&>(yylhs.value.object).push_back(ref<variable>(yystack_[0].value.object), bound_formula::all_);
    }
#line 3167 "../../mli-root/src/database-parser.cc"
    break;

  case 291: // exist_identifier_list: "exist variable"
#line 2236 "../../mli-root/src/database-parser.yy"
                      {
      bound_variable_type = free_variable_context;
      yylhs.value.object = ref<variable_list>(make, ref<variable>(yystack_[0].value.object), bound_formula::exist_);
    }
#line 3176 "../../mli-root/src/database-parser.cc"
    break;

  case 292: // $@19: %empty
#line 2240 "../../mli-root/src/database-parser.yy"
                             { bound_variable_type = database_parser::token::exist_variable; }
#line 3182 "../../mli-root/src/database-parser.cc"
    break;

  case 293: // exist_identifier_list: exist_identifier_list $@19 "," "exist variable"
#line 2241 "../../mli-root/src/database-parser.yy"
                            {
      bound_variable_type = free_variable_context;
      yylhs.value.object = yystack_[3].value.object;
      ref_cast<variable_list&>(yylhs.value.object).push_back(ref<variable>(yystack_[0].value.object), bound_formula::exist_);
    }
#line 3192 "../../mli-root/src/database-parser.cc"
    break;

  case 294: // optional_in_term: %empty
#line 2251 "../../mli-root/src/database-parser.yy"
           { yylhs.value.object = ref<formula>(make); }
#line 3198 "../../mli-root/src/database-parser.cc"
    break;

  case 295: // optional_in_term: "∈" term
#line 2252 "../../mli-root/src/database-parser.yy"
                { yylhs.value.object = yystack_[0].value.object; }
#line 3204 "../../mli-root/src/database-parser.cc"
    break;

  case 296: // tuple: "(" tuple_body ")"
#line 2259 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[1].value.object; }
#line 3210 "../../mli-root/src/database-parser.cc"
    break;

  case 297: // tuple_body: term
#line 2264 "../../mli-root/src/database-parser.yy"
            {
      ref<sequence> vr(make, sequence::tuple);
      yylhs.value.object = vr;
      vr->push_back(ref<formula>(yystack_[0].value.object));
    }
#line 3220 "../../mli-root/src/database-parser.cc"
    break;

  case 298: // tuple_body: tuple_body "," term
#line 2269 "../../mli-root/src/database-parser.yy"
                              {
      yylhs.value.object = yystack_[2].value.object;
      sequence& vr = ref_cast<sequence&>(yylhs.value.object);
      vr.push_back(ref<formula>(yystack_[0].value.object));
    }
#line 3230 "../../mli-root/src/database-parser.cc"
    break;

  case 299: // term: simple_term
#line 2278 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.object = yystack_[0].value.object; }
#line 3236 "../../mli-root/src/database-parser.cc"
    break;

  case 300: // term: function_term
#line 2279 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 3242 "../../mli-root/src/database-parser.cc"
    break;

  case 301: // term: simple_term term_substitution_sequence
#line 2280 "../../mli-root/src/database-parser.yy"
                                                 {
      yylhs.value.object = ref<substitution_formula>(make, ref<substitution>(yystack_[0].value.object), ref<formula>(yystack_[1].value.object));
    }
#line 3250 "../../mli-root/src/database-parser.cc"
    break;

  case 302: // term: set_term
#line 2283 "../../mli-root/src/database-parser.yy"
                { yylhs.value.object = yystack_[0].value.object; }
#line 3256 "../../mli-root/src/database-parser.cc"
    break;

  case 303: // simple_term: "term constant"
#line 2288 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 3262 "../../mli-root/src/database-parser.cc"
    break;

  case 304: // simple_term: "natural number value"
#line 2289 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[0].value.object; }
#line 3268 "../../mli-root/src/database-parser.cc"
    break;

  case 305: // simple_term: "integer value"
#line 2290 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 3274 "../../mli-root/src/database-parser.cc"
    break;

  case 306: // simple_term: term_identifier
#line 2291 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 3280 "../../mli-root/src/database-parser.cc"
    break;

  case 307: // simple_term: "(" term ")"
#line 2292 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[1].value.object; }
#line 3286 "../../mli-root/src/database-parser.cc"
    break;

  case 308: // term_identifier: "object variable" variable_exclusion_set
#line 2297 "../../mli-root/src/database-parser.yy"
                                                    {
      ref<variable> xr = yystack_[1].value.object;
      ref<variable> vr = yystack_[0].value.object;
      xr->excluded_.insert(vr->excluded_.begin(), vr->excluded_.end());
      yylhs.value.object = yystack_[1].value.object;
    }
#line 3297 "../../mli-root/src/database-parser.cc"
    break;

  case 309: // term_identifier: "function variable"
#line 2303 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3303 "../../mli-root/src/database-parser.cc"
    break;

  case 310: // term_identifier: "function map variable"
#line 2304 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[0].value.object; }
#line 3309 "../../mli-root/src/database-parser.cc"
    break;

  case 311: // term_identifier: "all variable"
#line 2305 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3315 "../../mli-root/src/database-parser.cc"
    break;

  case 312: // term_identifier: "exist variable"
#line 2306 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3321 "../../mli-root/src/database-parser.cc"
    break;

  case 313: // term_identifier: "Set variable"
#line 2307 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3327 "../../mli-root/src/database-parser.cc"
    break;

  case 314: // term_identifier: "set variable"
#line 2308 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3333 "../../mli-root/src/database-parser.cc"
    break;

  case 315: // term_identifier: "implicit set variable"
#line 2309 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.object = yystack_[0].value.object; }
#line 3339 "../../mli-root/src/database-parser.cc"
    break;

  case 316: // variable_exclusion_set: %empty
#line 2314 "../../mli-root/src/database-parser.yy"
           { yylhs.value.object = ref<variable>(make);  }
#line 3345 "../../mli-root/src/database-parser.cc"
    break;

  case 317: // variable_exclusion_set: "ₓ" "₍" variable_exclusion_list "₎"
#line 2315 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.object = yystack_[1].value.object; }
#line 3351 "../../mli-root/src/database-parser.cc"
    break;

  case 318: // variable_exclusion_list: bound_variable
#line 2320 "../../mli-root/src/database-parser.yy"
                      { ref<variable> vr(make); vr->excluded_.insert(yystack_[0].value.object); yylhs.value.object = vr; }
#line 3357 "../../mli-root/src/database-parser.cc"
    break;

  case 319: // variable_exclusion_list: variable_exclusion_list bound_variable
#line 2321 "../../mli-root/src/database-parser.yy"
                                                   {
      ref<variable> vr = yystack_[1].value.object;
      vr->excluded_.insert(yystack_[0].value.object);
      yylhs.value.object = vr;
    }
#line 3367 "../../mli-root/src/database-parser.cc"
    break;

  case 320: // bound_variable: "all variable"
#line 2330 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3373 "../../mli-root/src/database-parser.cc"
    break;

  case 321: // bound_variable: "exist variable"
#line 2331 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3379 "../../mli-root/src/database-parser.cc"
    break;

  case 322: // bound_variable: "Set variable"
#line 2332 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3385 "../../mli-root/src/database-parser.cc"
    break;

  case 323: // bound_variable: "set variable"
#line 2333 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3391 "../../mli-root/src/database-parser.cc"
    break;

  case 324: // bound_variable: "implicit set variable"
#line 2334 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.object = yystack_[0].value.object; }
#line 3397 "../../mli-root/src/database-parser.cc"
    break;

  case 325: // function_term: function_term_identifier tuple
#line 2339 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.object = ref<structure>(make, ref<formula>(yystack_[1].value.object), ref<formula>(yystack_[0].value.object),
        structure::function, 0_ml, structure::postargument, precedence_t()); }
#line 3405 "../../mli-root/src/database-parser.cc"
    break;

  case 326: // function_term: term_function_application
#line 2342 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.object = yystack_[0].value.object; }
#line 3411 "../../mli-root/src/database-parser.cc"
    break;

  case 327: // function_term: term "!"
#line 2343 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.object = ref<structure>(make, yystack_[0].value.text, structure::function, 0_ml,
        structure::postfix, factorial_oprec, yystack_[1].value.object);
    }
#line 3420 "../../mli-root/src/database-parser.cc"
    break;

  case 328: // function_term: term "+" term
#line 2347 "../../mli-root/src/database-parser.yy"
                           { // $$.object = ref<integer_addition>(make, ref<formula>($x.object), ref<formula>($y.object));
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, plus_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3429 "../../mli-root/src/database-parser.cc"
    break;

  case 329: // function_term: term "-" term
#line 2351 "../../mli-root/src/database-parser.yy"
                           { // $$.object = ref<integer_addition>(make, ref<formula>($x.object), ref<integer_negative>(make, ref<formula>($y.object)));
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, minus_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3438 "../../mli-root/src/database-parser.cc"
    break;

  case 330: // function_term: "-" term
#line 2355 "../../mli-root/src/database-parser.yy"
                                      { // $$.object = ref<integer_negative>(make, ref<formula>($x.object)); }
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::prefix, unary_minus_oprec, yystack_[0].value.object);
    }
#line 3447 "../../mli-root/src/database-parser.cc"
    break;

  case 331: // function_term: term "⋅" term
#line 2359 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, mult_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3456 "../../mli-root/src/database-parser.cc"
    break;

  case 332: // function_term: term "/" term
#line 2363 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, divide_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3465 "../../mli-root/src/database-parser.cc"
    break;

  case 333: // set_term: "{" "}"
#line 2371 "../../mli-root/src/database-parser.yy"
            { yylhs.value.object = ref<sequence>(make, sequence::member_list_set); }
#line 3471 "../../mli-root/src/database-parser.cc"
    break;

  case 334: // set_term: "∅"
#line 2372 "../../mli-root/src/database-parser.yy"
        { yylhs.value.object = ref<constant>(make, "∅", constant::object); }
#line 3477 "../../mli-root/src/database-parser.cc"
    break;

  case 335: // set_term: "{" set_member_list "}"
#line 2373 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[1].value.object; }
#line 3483 "../../mli-root/src/database-parser.cc"
    break;

  case 336: // set_term: "{" "set variable definition" optional_in_term "|" object_formula "}"
#line 2374 "../../mli-root/src/database-parser.yy"
                                                                                 {
      symbol_table.pop_level();
      yylhs.value.object = ref<bound_formula>(make, yystack_[4].value.object, yystack_[3].value.object, yystack_[1].value.object, bound_formula::set_);
    }
#line 3492 "../../mli-root/src/database-parser.cc"
    break;

  case 337: // set_term: "{" "₍" implicit_set_identifier_list optional_in_term "₎" term "|" object_formula "}"
#line 2378 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      symbol_table.pop_level();
      variable_list& vs = ref_cast<variable_list&>(yystack_[6].value.object);
      ref<sequence> sp(make, ref<formula>(yystack_[3].value.object), sequence::implicit_set);
      sp->push_back(ref<formula>(yystack_[1].value.object));
      yylhs.value.object =
        ref<bound_formula>(make, vs, yystack_[5].value.object, ref<formula>(sp));
    }
#line 3505 "../../mli-root/src/database-parser.cc"
    break;

  case 338: // set_term: term "∪" term
#line 2386 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, set_union_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3514 "../../mli-root/src/database-parser.cc"
    break;

  case 339: // set_term: term "∩" term
#line 2390 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, set_intersection_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3523 "../../mli-root/src/database-parser.cc"
    break;

  case 340: // set_term: term "∖" term
#line 2394 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, set_difference_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3532 "../../mli-root/src/database-parser.cc"
    break;

  case 341: // set_term: "∁" term
#line 2398 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::prefix, set_complement_oprec, yystack_[0].value.object);
    }
#line 3541 "../../mli-root/src/database-parser.cc"
    break;

  case 342: // set_term: "⋃" term
#line 2402 "../../mli-root/src/database-parser.yy"
                   { /* prefix union operator  */
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::prefix, set_union_operator_oprec, yystack_[0].value.object);
    }
#line 3550 "../../mli-root/src/database-parser.cc"
    break;

  case 343: // set_term: "∩" term
#line 2406 "../../mli-root/src/database-parser.yy"
                   { /* prefix intersection operator  */
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::prefix, set_intersection_operator_oprec, yystack_[0].value.object);
    }
#line 3559 "../../mli-root/src/database-parser.cc"
    break;

  case 344: // $@20: %empty
#line 2414 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 3565 "../../mli-root/src/database-parser.cc"
    break;

  case 345: // implicit_set_identifier_list: $@20 "Set variable"
#line 2415 "../../mli-root/src/database-parser.yy"
                       {
      bound_variable_type = free_variable_context;
      yylhs.value.object = ref<variable_list>(make, ref<variable>(yystack_[0].value.object), bound_formula::implicit_set);
    }
#line 3574 "../../mli-root/src/database-parser.cc"
    break;

  case 346: // $@21: %empty
#line 2419 "../../mli-root/src/database-parser.yy"
                                    { bound_variable_type = database_parser::token::is_set_variable; }
#line 3580 "../../mli-root/src/database-parser.cc"
    break;

  case 347: // implicit_set_identifier_list: implicit_set_identifier_list $@21 "," "Set variable"
#line 2420 "../../mli-root/src/database-parser.yy"
                             {
      bound_variable_type = free_variable_context;
      yylhs.value.object = yystack_[3].value.object;
      ref_cast<variable_list&>(yylhs.value.object).push_back(ref<variable>(yystack_[0].value.object), bound_formula::implicit_set);
    }
#line 3590 "../../mli-root/src/database-parser.cc"
    break;

  case 348: // set_member_list: term
#line 2429 "../../mli-root/src/database-parser.yy"
            {
      ref<sequence> vr(make, sequence::member_list_set);
      yylhs.value.object = vr;
      vr->push_back(ref<formula>(yystack_[0].value.object)); }
#line 3599 "../../mli-root/src/database-parser.cc"
    break;

  case 349: // set_member_list: set_member_list "," term
#line 2433 "../../mli-root/src/database-parser.yy"
                                   {
      yylhs.value.object = yystack_[2].value.object;
      sequence& vr = ref_cast<sequence&>(yylhs.value.object);
      vr.push_back(ref<formula>(yystack_[0].value.object));
    }
#line 3609 "../../mli-root/src/database-parser.cc"
    break;

  case 350: // function_term_identifier: "function constant"
#line 2442 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 3615 "../../mli-root/src/database-parser.cc"
    break;

  case 351: // function_term_identifier: "function variable"
#line 2443 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 3621 "../../mli-root/src/database-parser.cc"
    break;


#line 3625 "../../mli-root/src/database-parser.cc"

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


  const short database_parser::yypact_ninf_ = -534;

  const short database_parser::yytable_ninf_ = -352;

  const short
  database_parser::yypact_[] =
  {
     321,  -534,    32,    70,  -534,    92,  -534,  -534,    25,  -534,
    -534,  -534,  -534,    -9,  -534,  -534,   301,   115,    42,  -534,
     168,  -534,   481,   188,  -534,   181,   481,    25,    25,    25,
     171,   -29,   217,  -534,  -534,  -534,  -534,   342,   507,  -534,
      31,  -534,  -534,  -534,   153,  -534,    25,   164,   180,   185,
    -534,   167,  -534,  -534,   294,   306,   244,  -534,  -534,   272,
    -534,  -534,  -534,  -534,   381,  -534,  -534,   793,   278,   280,
     280,  -534,  -534,  -534,  -534,   148,   284,  -534,   296,  -534,
     311,   192,  -534,  -534,  -534,  -534,  -534,  -534,   353,   387,
     343,   594,   594,   594,   594,   594,  -534,  -534,  1481,  -534,
    -534,  1481,  1481,  1481,   693,   947,   793,  -534,  -534,  -534,
     793,    -5,  -534,   319,  -534,  -534,   369,  -534,  -534,   579,
    -534,   332,  -534,  -534,  -534,  -534,   280,  -534,  -534,  1384,
    -534,  -534,  -534,   118,   346,  -534,  -534,  -534,   280,  -534,
    -534,  -534,   578,   371,  -534,  -534,  -534,  -534,   171,  -534,
    -534,   -29,   370,   217,  -534,  -534,   474,   152,   373,  1295,
    -534,  1481,  -534,  -534,  -534,   365,  -534,  -534,   376,  -534,
     385,  -534,  1295,  -534,   594,   594,   594,   594,   418,  1409,
    1019,  -534,   384,   257,   257,   257,   233,   453,    -5,   392,
      17,   854,   410,  1117,  -534,  -534,   232,  1637,   -64,  -534,
      -5,   343,   343,   793,   793,   724,   319,  -534,  -534,  -534,
    -534,   489,   473,  1295,  1295,  1295,   343,   343,   343,   343,
     343,   865,   332,  -534,  -534,  -534,  -534,  -534,  -534,  1481,
    1206,  -534,  -534,   -31,  1637,  1481,  1481,   473,  1481,  1481,
    1481,  1481,  1481,  1481,  1481,  1481,  1481,  1481,  1481,  1481,
    -534,  1481,  1481,  1481,  1481,  1481,  1481,  1481,  1481,  1481,
    1481,  1481,  1481,  1481,   769,   346,  -534,  -534,   519,    25,
      25,    25,  -534,  -534,  -534,  -534,  -534,  -534,   507,   507,
    -534,  -534,  -534,  -534,   202,  -534,  -534,   403,   507,  -534,
     367,  -534,   342,  -534,   216,   639,   274,   524,   644,   406,
     408,  -534,  -534,  -534,  -534,  -534,   166,   478,   398,   524,
     479,  1295,   445,   411,   412,  -534,   424,   196,   282,  1539,
     -56,   509,     8,  1481,  -534,   443,   443,    13,  -534,   484,
     487,   494,   510,  -534,   511,  -534,  1295,  -534,  -534,   639,
    1637,   639,   639,  1295,  1295,  1295,  1295,  1295,  -534,   524,
     314,  1295,  -534,   524,   524,   583,   524,   524,   524,   524,
     524,   524,   524,   524,   524,   524,   524,   524,  -534,   -87,
     -87,   524,   524,   580,   257,   257,   524,   524,   524,   524,
    -534,  -534,   486,   497,   528,   529,   530,   793,  -534,  -534,
    -534,  -534,   391,   590,    20,   532,   555,   154,   504,   285,
     521,   539,   500,  -534,  -534,   648,  -534,  -534,  1295,  -534,
    1481,  -534,  -534,  -534,  -534,  -534,  -534,   158,  -534,   617,
     619,  1481,   585,   552,   407,  1588,  1295,  1295,   553,   568,
    -534,   658,  -534,  -534,  1295,  1295,    34,  -534,   524,   129,
     562,   562,   793,  1295,  1091,   654,  1481,   639,  1637,  -534,
     633,   366,   366,   348,  -534,   639,  1295,  -534,  -534,  -534,
    -534,  -534,  -534,   793,   793,  1295,  1295,  1481,  1481,  -534,
     621,   615,   616,   319,   202,  -534,   202,   202,   202,   202,
     639,   524,  -534,  -534,  -534,  -534,   402,  1481,  -534,   280,
     280,   639,  1637,   267,  1481,   660,  1481,   226,   213,     8,
    1295,  -534,  -534,   133,   195,  -534,   137,  -534,   -22,  -534,
     220,   793,   793,    19,   309,   595,   596,   495,   639,  1637,
     507,   507,   507,   598,   601,   639,   639,   524,   524,  1295,
    -534,  -534,   319,   521,   539,   593,   -65,  -534,   300,   524,
     146,  -534,  -534,   592,   602,  -534,   576,  -534,   524,    43,
      43,  -534,   277,   340,   604,   340,   646,  -534,   652,  -534,
    -534,  -534,  -534,  -534,   222,    39,  -534,   136,  -534,   -15,
    -534,     4,   373,  -534,  -534,  -534,  -534,  -534,   630,   631,
     632,   639,   202,   202,  -534,  -534,  -534,  -534,  1295,  -534,
    -534,  -534,   280,   280,  1295,     8,   618,  -534,  -534,  -534,
     652,  -534,  -534,   341,   637,   341,   664,  -534,   665,  -534,
    -534,  -534,  -534,  -534,  -534,   206,  -534,   414,  -534,  -534,
     304,   -97,    43,   665,  -534,  -534,  -534,  -534,  -534,  -534,
    -534
  };

  const short
  database_parser::yydefact_[] =
  {
       0,     4,     0,     3,     6,     0,     1,     5,     0,     8,
      68,    69,    70,     0,    33,    37,    51,     0,     0,    38,
       0,    51,    42,     0,    44,     0,    43,     0,     0,     0,
       0,     0,     0,    52,    55,    56,    53,    75,     0,    54,
       0,   119,    40,    41,     0,    46,    35,     0,     0,     0,
     131,   121,   129,   134,     0,     0,   122,   132,   126,   123,
     124,    79,    78,    71,    92,    74,    80,     0,     0,     0,
       0,   266,   239,   350,   303,   188,   240,   267,   241,   277,
     309,   316,   311,   312,   310,   313,   314,   315,     0,     0,
     268,     0,     0,     0,     0,     0,   304,   305,     0,   262,
     334,     0,     0,     0,     0,     0,     0,   210,   326,    72,
       0,   114,   146,     0,   148,   149,     0,   189,   198,   147,
     214,     0,   213,   208,   242,   243,     0,   211,   276,   294,
     283,   284,   285,     0,   299,   306,   300,   302,     0,   118,
     120,    39,     0,     0,    36,    66,    64,    73,     0,   135,
     136,     0,     0,     0,    93,    76,     0,    85,   155,     0,
     203,     0,    32,    28,   204,     0,   308,   288,   286,   291,
     287,   269,     0,   278,     0,     0,     0,     0,   316,     0,
       0,   330,     0,   341,   343,   342,   316,     0,     0,   146,
     147,     0,   294,     0,   344,   333,     0,   348,     0,   150,
     115,   268,   268,     0,     0,     0,   157,     9,    11,    12,
      13,     0,     0,     0,     0,     0,   268,   268,   268,   268,
     268,     0,   209,    15,    17,    18,   265,   240,   241,     0,
       0,   229,   237,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     327,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   301,    22,   325,     0,     0,
       0,     0,    47,    49,    59,    50,    48,    34,     0,     0,
     130,   133,   127,   125,    98,    77,    87,     0,     0,    81,
       0,    84,     0,    88,     0,   206,     0,   297,     0,     0,
       0,   270,   280,   279,   281,   282,   316,     0,     0,   348,
       0,     0,     0,   156,   212,   307,     0,   316,     0,     0,
     294,     0,   218,     0,   335,   158,   158,   151,   152,     0,
       0,     0,     0,   309,     0,    10,     0,   197,   190,   191,
     192,   199,   200,     0,     0,     0,     0,     0,    16,   295,
       0,     0,   231,   201,   202,     0,   248,   249,   250,   251,
     252,   253,   254,   255,   244,   245,   246,   247,   331,   328,
     329,   256,   257,   338,   339,   340,   258,   259,   260,   261,
     332,    23,     0,     0,     0,     0,     0,     0,   116,   137,
     138,   139,   146,   147,     0,     0,     0,   106,   111,     0,
      94,    96,    99,   105,    82,    90,    86,    89,     0,   205,
       0,   296,   320,   321,   322,   323,   324,     0,   318,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     345,     0,   221,   222,     0,     0,     0,   219,   349,     0,
     172,   172,     0,     0,     0,     0,     0,   193,   194,   272,
     271,   273,   274,   275,   238,   230,     0,    45,    57,    60,
      62,    67,   117,     0,     0,     0,     0,     0,     0,    65,
       0,   109,   107,     0,    98,    91,    98,     0,     0,    98,
     207,   298,   317,   319,   290,   293,     0,     0,   263,     0,
       0,    26,    30,     0,     0,     0,     0,     0,     0,     0,
       0,   171,   170,     0,     0,   162,     0,   165,     0,   168,
       0,     0,     0,     0,     0,     0,     0,     0,   195,   196,
       0,     0,     0,   146,   146,   142,   143,   144,   145,     0,
     110,   108,   113,    95,    97,   101,     0,   103,     0,    30,
       0,    25,    29,     0,     0,   336,     0,   347,   223,     0,
       0,   220,     0,     0,   164,   167,     0,   159,     0,   160,
     161,   169,   185,   184,     0,     0,   176,     0,   179,     0,
     182,   153,   154,    14,    19,    20,    21,    24,     0,     0,
       0,   128,     0,     0,   100,    83,   232,   233,     0,   236,
     264,   234,     0,     0,     0,   218,     0,   216,   225,   215,
       0,   163,   166,     0,   178,   181,     0,   173,     0,   174,
     175,   183,    58,    61,    63,     0,   104,     0,    27,    31,
       0,     0,     0,     0,   177,   180,   102,   235,   337,   217,
     224
  };

  const short
  database_parser::yypgoto_[] =
  {
    -534,  -534,  -534,   761,  -534,   310,  -202,  -534,  -534,   564,
     -76,  -534,  -108,  -534,  -534,  -534,  -534,  -534,  -534,  -534,
    -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,   753,  -534,
    -534,  -534,  -534,  -534,   635,  -534,   -91,  -534,    -7,  -534,
    -534,  -534,  -534,  -534,   496,  -534,  -534,  -534,  -534,  -534,
    -534,  -534,   634,  -534,   308,   318,   317,   212,  -429,  -534,
    -534,  -269,  -534,   -11,  -534,   755,  -534,   643,  -534,  -534,
    -534,   649,  -534,   651,   413,  -534,  -534,  -534,   -32,   -98,
     477,  -534,   249,   368,   251,   372,  -479,   374,  -534,   204,
     302,   205,   307,  -528,  -534,  -534,  -534,   -54,  -534,  -534,
     739,  -534,  -102,  -534,  -533,   224,  -317,  -534,  -224,  -534,
    -534,   701,   378,  -534,  -534,   312,  -534,   375,  -534,   -12,
    -534,  -534,  -534,  -534,  -534,  -534,  -534,  -534,  -185,   -70,
    -534,   209,  -534,  -193,  -534,  -534,   429,  -534,  -534,  -534,
    -534,  -534,  -534,  -534
  };

  const short
  database_parser::yydefgoto_[] =
  {
       0,     2,     3,     4,     5,   206,   207,   208,   222,   223,
     209,   265,   210,   107,   543,   108,   544,     9,    15,   143,
      16,    19,    44,    20,    21,    45,   142,   272,    22,    33,
     273,   520,   521,   522,    34,   279,    35,   278,   398,    36,
      37,    38,    63,    64,    65,    66,   157,   288,   289,   290,
     291,   292,   155,   156,   399,   400,   401,   536,   402,   403,
     473,   109,   386,   110,    40,    41,    59,    60,   152,   396,
      51,    52,    56,    57,   388,   389,   390,   391,   111,   112,
     440,   504,   505,   554,   507,   555,   509,   511,   565,   566,
     604,   568,   605,   570,   113,   114,   115,   116,   117,   118,
     160,   294,   119,   120,   596,   436,   597,   121,   122,   590,
     231,   123,   124,   182,   540,   125,   126,   172,   127,   128,
     129,   130,   131,   132,   168,   299,   170,   300,   233,   162,
     296,   234,   134,   135,   166,   417,   418,   136,   137,   320,
     321,   429,   198,   138
  };

  const short
  database_parser::yytable_[] =
  {
     163,    13,   190,   196,   335,   437,   189,   316,    53,   352,
     395,    39,   334,   225,   201,    39,   251,   598,   202,   405,
      47,    48,    49,  -352,   501,   499,   266,   202,   334,   561,
     502,   562,     6,    88,    89,   158,   202,   563,   201,   144,
     629,   611,   202,   214,   215,   224,   235,   236,   535,   537,
     237,   275,   263,   229,   467,   468,   226,   295,   583,   323,
     431,   432,    10,    11,    54,    55,   286,  -346,   267,   584,
     301,   334,   188,   324,   199,    -7,   561,   611,   200,   173,
     174,   175,   176,   177,   216,   217,   218,   219,   220,   630,
     351,   318,    30,    31,    32,   431,   432,     8,   238,   239,
     240,   241,   242,   243,   244,   245,   246,   247,   248,   249,
     560,   339,   341,   342,   225,    14,   433,   203,   204,   610,
      23,    12,   250,   251,   252,   253,   203,   204,   350,   254,
     255,   276,   256,   257,   258,   428,   204,   259,   260,   261,
     262,   203,   204,   314,   235,   236,   224,   573,   237,   434,
     287,   433,   435,   537,   616,   139,   499,   381,   338,   263,
      27,   606,   302,   303,   304,   305,    24,   285,   -92,   500,
     154,   327,   328,   607,    25,   501,   393,   471,   595,   501,
     392,   502,   551,   355,   434,   502,    46,   435,    71,    10,
      11,    10,    11,   586,    77,   587,   238,   239,   240,   241,
     242,   243,   244,   245,   246,   247,   248,   249,    50,   424,
      88,    89,   412,   413,  -197,   414,   415,  -197,   416,   397,
     250,   251,   252,   253,  -197,    42,    43,   254,   255,   503,
     256,   257,   258,   553,   447,   259,   260,   261,   262,    10,
      11,   449,   450,   451,   452,   453,   188,   133,    12,   455,
      12,   578,   579,   580,    58,  -197,   421,   263,  -197,   608,
     558,   165,   383,   384,   385,  -197,   562,   387,   562,   559,
     609,   588,   563,   159,   563,  -186,   133,   141,   437,   406,
     216,   217,   218,   219,   220,   393,   311,   165,   145,   392,
     148,   165,   482,   216,   217,   218,   219,   220,    12,   216,
     217,   218,   219,   220,   146,    17,   480,   181,    18,   147,
     183,   184,   185,   191,   197,   133,   589,   556,   564,   133,
     603,    -2,     1,   311,   491,   493,    -7,   557,   165,   583,
     335,   149,   497,   498,   216,   217,   218,   219,   220,   408,
     626,   514,   409,   150,   216,   217,   218,   219,   220,   216,
     217,   218,   219,   220,   518,   188,    61,    62,   550,   250,
     251,   252,   253,   525,   526,   523,   524,   151,   549,   322,
     297,   216,   217,   218,   219,   220,   216,   217,   218,   219,
     220,   216,   217,   218,   219,   220,   501,   562,   308,   309,
     472,   211,   502,   563,   212,   153,   263,   410,   552,   154,
     411,   213,   319,   159,   545,   161,   474,   167,   314,   475,
     513,  -226,   133,   133,   599,   216,   217,   218,   219,   541,
     542,   474,   340,  -227,   585,   463,   464,   581,    30,    31,
      32,   188,   188,   216,   217,   218,  -351,   574,   349,   319,
     454,   628,   169,   171,   353,   354,   205,   356,   357,   358,
     359,   360,   361,   362,   363,   364,   365,   366,   367,   221,
     368,   369,   370,   371,   372,   373,   374,   375,   376,   377,
     378,   379,   380,   264,   216,   217,   218,   219,   220,   571,
     572,   216,   217,   218,   219,   220,   617,   394,   133,    27,
     284,   282,   620,    28,    29,   277,   204,   133,   298,  -289,
     250,   251,   252,   253,   250,   251,   252,   253,  -292,   312,
     256,   257,   258,   165,   256,   257,   258,   310,   313,   229,
     425,   336,   618,   619,   315,   337,   382,   404,   490,   419,
      67,   420,   438,   489,   422,   426,   423,   263,  -187,  -228,
     627,   263,    30,    31,    32,   448,    68,    69,    70,    71,
      72,    73,    74,    75,    76,    77,    78,    79,    80,    81,
     427,    82,    83,    84,    85,    86,   430,    87,    30,    31,
      32,    88,    89,    90,   439,   442,   325,   326,   443,    91,
      92,    93,    94,    95,   268,   444,    27,   269,   270,   271,
      28,   343,   344,   345,   346,   347,   394,   250,   251,   252,
     253,   445,   446,    96,    97,   214,   215,   256,   257,   258,
     457,   470,    98,    99,   456,   100,   214,   215,   101,   481,
     102,   458,   103,   577,   465,   466,   250,   251,   252,   253,
     486,  -112,   104,   478,   263,   492,   256,   257,   258,    30,
      31,    32,   105,   476,    79,   106,   216,   217,   218,   219,
     220,   133,   459,   460,   461,   517,   469,   216,   217,   218,
     219,   220,   477,   263,   479,   519,    91,    92,    93,    94,
      95,   484,   133,   133,   485,   487,   527,   528,   250,   251,
     252,   253,   250,   251,   252,   253,   488,   494,   256,   257,
     258,   495,   496,   257,   258,   510,   539,   516,   412,   413,
     216,   414,   415,   546,   416,   548,   216,   217,   218,   219,
     220,   529,   594,   530,   531,   263,    67,   547,   592,   263,
     133,   133,  -140,   575,   576,  -141,   582,   558,   593,   133,
     133,   133,    68,    69,    70,    71,    72,    73,    74,    75,
      76,    77,    78,    79,    80,   186,   600,    82,    83,    84,
      85,    86,   553,    87,   612,   613,   614,    88,    89,    90,
     608,   622,   623,   603,     7,    91,    92,    93,    94,    95,
     329,   330,   331,   332,    26,   333,   178,   274,    82,    83,
      84,    85,    86,   532,    87,   187,   348,   538,   407,    96,
      97,   293,   533,   534,   615,   140,   283,   280,    98,    99,
     462,   100,   281,   441,   101,   601,   102,   506,   103,   602,
     624,   508,   567,   625,   164,   512,    67,   569,   104,   621,
     333,   178,   515,    82,    83,    84,    85,    86,   105,    87,
     232,   106,    68,    69,    70,    71,    72,    73,    74,    75,
      76,    77,    78,    79,    80,    81,   483,    82,    83,    84,
      85,    86,   591,    87,     0,     0,     0,    88,    89,    90,
       0,     0,     0,     0,     0,    91,    92,    93,    94,    95,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     235,   236,     0,     0,   237,     0,     0,     0,     0,    96,
      97,     0,     0,     0,     0,     0,     0,     0,    98,    99,
       0,   100,     0,     0,   101,     0,   102,     0,   103,     0,
       0,     0,   330,   331,   332,     0,   333,   178,   104,    82,
      83,    84,    85,    86,     0,    87,     0,     0,   105,     0,
       0,   106,   238,   239,   240,   241,   242,   243,   244,   245,
     246,   247,   248,   249,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   250,   251,   252,   253,
       0,     0,     0,   254,   255,     0,   256,   257,   258,     0,
       0,   259,   260,   261,   262,     0,     0,     0,     0,     0,
     315,     0,     0,     0,     0,     0,     0,    69,    70,    71,
      72,    73,    74,   263,    76,    77,    78,    79,    80,   178,
       0,    82,    83,    84,    85,    86,   192,    87,     0,     0,
       0,    88,    89,    90,     0,     0,     0,     0,     0,    91,
      92,    93,    94,    95,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    96,    97,     0,     0,     0,     0,     0,
       0,     0,    98,    99,     0,   100,     0,     0,   101,    69,
     102,     0,   103,    73,    74,     0,     0,     0,     0,     0,
      80,   178,   193,    82,    83,    84,    85,    86,   192,    87,
     194,     0,   105,     0,   195,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    96,    97,     0,     0,     0,
       0,     0,     0,     0,    98,     0,     0,   100,     0,     0,
     101,    69,   102,    71,   103,    73,    74,     0,     0,    77,
       0,     0,    80,   178,   179,    82,    83,    84,    85,    86,
       0,    87,   194,     0,   180,     0,   195,    69,    70,    71,
      72,    73,    74,     0,    76,    77,    78,    79,    80,   317,
       0,    82,    83,    84,    85,    86,     0,    87,     0,     0,
       0,    88,    89,    90,     0,     0,     0,    96,    97,    91,
      92,    93,    94,    95,     0,     0,    98,    99,     0,   100,
       0,     0,   101,     0,   102,     0,   103,     0,     0,   187,
       0,     0,     0,    96,    97,     0,   179,     0,     0,     0,
       0,     0,    98,    99,     0,   100,   180,     0,   101,     0,
     102,     0,   103,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   193,     0,     0,     0,    69,    70,    71,    72,
      73,    74,   105,    76,    77,    78,    79,    80,   306,     0,
      82,    83,    84,    85,    86,     0,    87,     0,     0,     0,
      88,    89,    90,     0,     0,     0,     0,     0,    91,    92,
      93,    94,    95,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   307,     0,
       0,     0,    96,    97,     0,     0,     0,     0,     0,     0,
       0,    98,    99,     0,   100,     0,     0,   101,     0,   102,
       0,   103,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   193,     0,     0,     0,    69,    70,    71,    72,    73,
      74,   105,    76,    77,    78,    79,    80,   178,     0,    82,
      83,    84,    85,    86,     0,    87,     0,     0,     0,    88,
      89,    90,     0,     0,     0,     0,     0,    91,    92,    93,
      94,    95,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    96,    97,     0,     0,     0,     0,     0,     0,     0,
      98,    99,     0,   100,     0,     0,   101,     0,   102,     0,
     103,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     193,     0,     0,     0,    69,     0,    71,    72,    73,    74,
     105,   227,    77,   228,     0,    80,   178,     0,    82,    83,
      84,    85,    86,     0,    87,     0,     0,     0,     0,    69,
       0,     0,     0,    73,    74,     0,     0,     0,     0,     0,
      80,   306,     0,    82,    83,    84,    85,    86,     0,    87,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      96,    97,     0,     0,     0,     0,     0,     0,     0,    98,
      99,     0,   100,   229,     0,   101,     0,   102,     0,   103,
       0,   307,     0,     0,     0,    96,    97,     0,     0,   230,
       0,     0,     0,     0,    98,     0,     0,   100,     0,   180,
     101,    69,   102,     0,   103,    73,    74,     0,     0,     0,
       0,     0,    80,   178,   179,    82,    83,    84,    85,    86,
       0,    87,     0,     0,   180,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    96,    97,     0,
       0,     0,     0,     0,     0,     0,    98,     0,     0,   100,
       0,     0,   101,     0,   102,     0,   103,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   179,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   180,   238,   239,   240,
     241,   242,   243,   244,   245,   246,   247,   248,   249,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   250,   251,   252,   253,     0,     0,     0,   254,   255,
       0,   256,   257,   258,     0,     0,   259,   260,   261,   262,
       0,     0,     0,     0,     0,   315,   238,   239,   240,   241,
     242,   243,   244,   245,   246,   247,   248,   249,   263,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     250,   251,   252,   253,     0,     0,     0,   254,   255,     0,
     256,   257,   258,     0,     0,   259,   260,   261,   262,     0,
       0,     0,     0,     0,   490,   238,   239,   240,   241,   242,
     243,   244,   245,   246,   247,   248,   249,   263,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   250,
     251,   252,   253,     0,     0,     0,   254,   255,     0,   256,
     257,   258,     0,     0,   259,   260,   261,   262,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   263
  };

  const short
  database_parser::yycheck_[] =
  {
      70,     8,   104,   105,   206,   322,   104,   192,    37,   233,
     279,    22,   205,   121,    19,    26,   103,   550,    23,   288,
      27,    28,    29,    19,    46,   122,   134,    23,   221,   508,
      52,    46,     0,    64,    65,    67,    23,    52,    19,    46,
     137,   569,    23,    26,    27,   121,    26,    27,   477,   478,
      30,   142,   139,   109,    34,    35,   126,   159,   123,   123,
      52,    53,    37,    38,    93,    94,   157,   123,   138,   134,
     172,   264,   104,   137,   106,     5,   555,   605,   110,    91,
      92,    93,    94,    95,    67,    68,    69,    70,    71,   622,
     121,   193,    61,    62,    63,    52,    53,     5,    78,    79,
      80,    81,    82,    83,    84,    85,    86,    87,    88,    89,
     132,   213,   214,   215,   222,   124,   108,   122,   123,   134,
       5,    96,   102,   103,   104,   105,   122,   123,   230,   109,
     110,   142,   112,   113,   114,   320,   123,   117,   118,   119,
     120,   122,   123,   126,    26,    27,   222,   128,    30,   141,
     157,   108,   144,   582,   583,   124,   122,   265,   212,   139,
       8,   122,   174,   175,   176,   177,   124,    15,    16,   135,
      18,   203,   204,   134,     6,    46,   278,    23,   135,    46,
     278,    52,   499,   237,   141,    52,     5,   144,    42,    37,
      38,    37,    38,    47,    48,    49,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    87,    88,    89,    37,   311,
      64,    65,    54,    55,    22,    57,    58,    25,    60,    17,
     102,   103,   104,   105,    32,    37,    38,   109,   110,   100,
     112,   113,   114,   100,   336,   117,   118,   119,   120,    37,
      38,   343,   344,   345,   346,   347,   278,    38,    96,   351,
      96,   520,   521,   522,    37,    22,    90,   139,    25,   123,
     123,    95,   269,   270,   271,    32,    46,   278,    46,   132,
     134,   125,    52,   125,    52,   127,    67,   124,   595,   290,
      67,    68,    69,    70,    71,   387,    90,    95,   124,   387,
     123,    95,   134,    67,    68,    69,    70,    71,    96,    67,
      68,    69,    70,    71,   124,     4,   408,    98,     7,   124,
     101,   102,   103,   104,   105,   106,   540,   122,    98,   110,
      98,     0,     1,    90,   426,   427,     5,   132,    95,   123,
     532,    37,   434,   435,    67,    68,    69,    70,    71,   123,
     134,   443,   126,    37,    67,    68,    69,    70,    71,    67,
      68,    69,    70,    71,   456,   387,    14,    15,   145,   102,
     103,   104,   105,   465,   466,   463,   464,   123,   142,   137,
     161,    67,    68,    69,    70,    71,    67,    68,    69,    70,
      71,    67,    68,    69,    70,    71,    46,    46,   179,   180,
     397,    22,    52,    52,    25,   123,   139,   123,   500,    18,
     126,    32,   193,   125,   137,   125,   121,    54,   126,   124,
     442,   127,   203,   204,   137,    67,    68,    69,    70,   489,
     490,   121,   213,   127,   124,    34,    35,   529,    61,    62,
      63,   463,   464,    67,    68,    69,   125,   128,   229,   230,
     126,   137,    55,   100,   235,   236,   127,   238,   239,   240,
     241,   242,   243,   244,   245,   246,   247,   248,   249,   127,
     251,   252,   253,   254,   255,   256,   257,   258,   259,   260,
     261,   262,   263,   127,    67,    68,    69,    70,    71,   511,
     512,    67,    68,    69,    70,    71,   588,   278,   279,     8,
      16,   121,   594,    12,    13,   124,   123,   288,   133,   123,
     102,   103,   104,   105,   102,   103,   104,   105,   123,    56,
     112,   113,   114,    95,   112,   113,   114,   133,   126,   109,
     311,    32,   592,   593,   126,    52,     7,   124,   126,   123,
      23,   123,   323,   126,    56,    90,    57,   139,   127,   127,
     126,   139,    61,    62,    63,   336,    39,    40,    41,    42,
      43,    44,    45,    46,    47,    48,    49,    50,    51,    52,
     136,    54,    55,    56,    57,    58,    57,    60,    61,    62,
      63,    64,    65,    66,   131,    91,   201,   202,    91,    72,
      73,    74,    75,    76,     6,    91,     8,     9,    10,    11,
      12,   216,   217,   218,   219,   220,   387,   102,   103,   104,
     105,    91,    91,    96,    97,    26,    27,   112,   113,   114,
     124,    56,   105,   106,    31,   108,    26,    27,   111,   410,
     113,   124,   115,   128,    34,    35,   102,   103,   104,   105,
     421,   127,   125,   133,   139,   426,   112,   113,   114,    61,
      62,    63,   135,   122,    50,   138,    67,    68,    69,    70,
      71,   442,   124,   124,   124,   446,   124,    67,    68,    69,
      70,    71,   123,   139,    16,   456,    72,    73,    74,    75,
      76,    54,   463,   464,    55,    90,   467,   468,   102,   103,
     104,   105,   102,   103,   104,   105,   134,   134,   112,   113,
     114,   123,    34,   113,   114,   133,   487,    43,    54,    55,
      67,    57,    58,   494,    60,   496,    67,    68,    69,    70,
      71,    90,   136,    98,    98,   139,    23,    57,   126,   139,
     511,   512,   124,   128,   128,   124,   133,   123,   126,   520,
     521,   522,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,   100,    54,    55,    56,
      57,    58,   100,    60,   124,   124,   124,    64,    65,    66,
     123,   143,    98,    98,     3,    72,    73,    74,    75,    76,
      46,    47,    48,    49,    21,    51,    52,   142,    54,    55,
      56,    57,    58,   473,    60,    92,   222,   479,   292,    96,
      97,   157,   474,   476,   582,    40,   153,   148,   105,   106,
     387,   108,   151,   326,   111,   556,   113,   439,   115,   558,
     606,   439,   510,   608,    75,   441,    23,   510,   125,   595,
      51,    52,   444,    54,    55,    56,    57,    58,   135,    60,
     129,   138,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,   417,    54,    55,    56,
      57,    58,   540,    60,    -1,    -1,    -1,    64,    65,    66,
      -1,    -1,    -1,    -1,    -1,    72,    73,    74,    75,    76,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      26,    27,    -1,    -1,    30,    -1,    -1,    -1,    -1,    96,
      97,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,   106,
      -1,   108,    -1,    -1,   111,    -1,   113,    -1,   115,    -1,
      -1,    -1,    47,    48,    49,    -1,    51,    52,   125,    54,
      55,    56,    57,    58,    -1,    60,    -1,    -1,   135,    -1,
      -1,   138,    78,    79,    80,    81,    82,    83,    84,    85,
      86,    87,    88,    89,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   102,   103,   104,   105,
      -1,    -1,    -1,   109,   110,    -1,   112,   113,   114,    -1,
      -1,   117,   118,   119,   120,    -1,    -1,    -1,    -1,    -1,
     126,    -1,    -1,    -1,    -1,    -1,    -1,    40,    41,    42,
      43,    44,    45,   139,    47,    48,    49,    50,    51,    52,
      -1,    54,    55,    56,    57,    58,    59,    60,    -1,    -1,
      -1,    64,    65,    66,    -1,    -1,    -1,    -1,    -1,    72,
      73,    74,    75,    76,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    96,    97,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   105,   106,    -1,   108,    -1,    -1,   111,    40,
     113,    -1,   115,    44,    45,    -1,    -1,    -1,    -1,    -1,
      51,    52,   125,    54,    55,    56,    57,    58,    59,    60,
     133,    -1,   135,    -1,   137,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    96,    97,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   105,    -1,    -1,   108,    -1,    -1,
     111,    40,   113,    42,   115,    44,    45,    -1,    -1,    48,
      -1,    -1,    51,    52,   125,    54,    55,    56,    57,    58,
      -1,    60,   133,    -1,   135,    -1,   137,    40,    41,    42,
      43,    44,    45,    -1,    47,    48,    49,    50,    51,    52,
      -1,    54,    55,    56,    57,    58,    -1,    60,    -1,    -1,
      -1,    64,    65,    66,    -1,    -1,    -1,    96,    97,    72,
      73,    74,    75,    76,    -1,    -1,   105,   106,    -1,   108,
      -1,    -1,   111,    -1,   113,    -1,   115,    -1,    -1,    92,
      -1,    -1,    -1,    96,    97,    -1,   125,    -1,    -1,    -1,
      -1,    -1,   105,   106,    -1,   108,   135,    -1,   111,    -1,
     113,    -1,   115,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   125,    -1,    -1,    -1,    40,    41,    42,    43,
      44,    45,   135,    47,    48,    49,    50,    51,    52,    -1,
      54,    55,    56,    57,    58,    -1,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    -1,    -1,    72,    73,
      74,    75,    76,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    92,    -1,
      -1,    -1,    96,    97,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   105,   106,    -1,   108,    -1,    -1,   111,    -1,   113,
      -1,   115,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   125,    -1,    -1,    -1,    40,    41,    42,    43,    44,
      45,   135,    47,    48,    49,    50,    51,    52,    -1,    54,
      55,    56,    57,    58,    -1,    60,    -1,    -1,    -1,    64,
      65,    66,    -1,    -1,    -1,    -1,    -1,    72,    73,    74,
      75,    76,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    96,    97,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     105,   106,    -1,   108,    -1,    -1,   111,    -1,   113,    -1,
     115,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     125,    -1,    -1,    -1,    40,    -1,    42,    43,    44,    45,
     135,    47,    48,    49,    -1,    51,    52,    -1,    54,    55,
      56,    57,    58,    -1,    60,    -1,    -1,    -1,    -1,    40,
      -1,    -1,    -1,    44,    45,    -1,    -1,    -1,    -1,    -1,
      51,    52,    -1,    54,    55,    56,    57,    58,    -1,    60,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      96,    97,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   105,
     106,    -1,   108,   109,    -1,   111,    -1,   113,    -1,   115,
      -1,    92,    -1,    -1,    -1,    96,    97,    -1,    -1,   125,
      -1,    -1,    -1,    -1,   105,    -1,    -1,   108,    -1,   135,
     111,    40,   113,    -1,   115,    44,    45,    -1,    -1,    -1,
      -1,    -1,    51,    52,   125,    54,    55,    56,    57,    58,
      -1,    60,    -1,    -1,   135,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    96,    97,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   105,    -1,    -1,   108,
      -1,    -1,   111,    -1,   113,    -1,   115,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   125,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   135,    78,    79,    80,
      81,    82,    83,    84,    85,    86,    87,    88,    89,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   102,   103,   104,   105,    -1,    -1,    -1,   109,   110,
      -1,   112,   113,   114,    -1,    -1,   117,   118,   119,   120,
      -1,    -1,    -1,    -1,    -1,   126,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    87,    88,    89,   139,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     102,   103,   104,   105,    -1,    -1,    -1,   109,   110,    -1,
     112,   113,   114,    -1,    -1,   117,   118,   119,   120,    -1,
      -1,    -1,    -1,    -1,   126,    78,    79,    80,    81,    82,
      83,    84,    85,    86,    87,    88,    89,   139,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   102,
     103,   104,   105,    -1,    -1,    -1,   109,   110,    -1,   112,
     113,   114,    -1,    -1,   117,   118,   119,   120,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   139
  };

  const short
  database_parser::yystos_[] =
  {
       0,     1,   156,   157,   158,   159,     0,   158,     5,   172,
      37,    38,    96,   193,   124,   173,   175,     4,     7,   176,
     178,   179,   183,     5,   124,     6,   183,     8,    12,    13,
      61,    62,    63,   184,   189,   191,   194,   195,   196,   218,
     219,   220,    37,    38,   177,   180,     5,   193,   193,   193,
      37,   225,   226,    37,    93,    94,   227,   228,    37,   221,
     222,    14,    15,   197,   198,   199,   200,    23,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    54,    55,    56,    57,    58,    60,    64,    65,
      66,    72,    73,    74,    75,    76,    96,    97,   105,   106,
     108,   111,   113,   115,   125,   135,   138,   168,   170,   216,
     218,   233,   234,   249,   250,   251,   252,   253,   254,   257,
     258,   262,   263,   266,   267,   270,   271,   273,   274,   275,
     276,   277,   278,   286,   287,   288,   292,   293,   298,   124,
     220,   124,   181,   174,   193,   124,   124,   124,   123,    37,
      37,   123,   223,   123,    18,   207,   208,   201,   233,   125,
     255,   125,   284,   284,   255,    95,   289,    54,   279,    55,
     281,   100,   272,   274,   274,   274,   274,   274,    52,   125,
     135,   286,   268,   286,   286,   286,    52,    92,   233,   234,
     257,   286,    59,   125,   133,   137,   257,   286,   297,   233,
     233,    19,    23,   122,   123,   127,   160,   161,   162,   165,
     167,    22,    25,    32,    26,    27,    67,    68,    69,    70,
      71,   127,   163,   164,   165,   167,   284,    47,    49,   109,
     125,   265,   266,   283,   286,    26,    27,    30,    78,    79,
      80,    81,    82,    83,    84,    85,    86,    87,    88,    89,
     102,   103,   104,   105,   109,   110,   112,   113,   114,   117,
     118,   119,   120,   139,   127,   166,   167,   284,     6,     9,
      10,    11,   182,   185,   189,   191,   218,   124,   192,   190,
     226,   228,   121,   222,    16,    15,   191,   193,   202,   203,
     204,   205,   206,   207,   256,   257,   285,   286,   133,   280,
     282,   257,   274,   274,   274,   274,    52,    92,   286,   286,
     133,    90,    56,   126,   126,   126,   283,    52,   257,   286,
     294,   295,   137,   123,   137,   272,   272,   233,   233,    46,
      47,    48,    49,    51,   288,   161,    32,    52,   252,   257,
     286,   257,   257,   272,   272,   272,   272,   272,   164,   286,
     257,   121,   263,   286,   286,   252,   286,   286,   286,   286,
     286,   286,   286,   286,   286,   286,   286,   286,   286,   286,
     286,   286,   286,   286,   286,   286,   286,   286,   286,   286,
     286,   167,     7,   193,   193,   193,   217,   218,   229,   230,
     231,   232,   234,   257,   286,   216,   224,    17,   193,   209,
     210,   211,   213,   214,   124,   216,   218,   199,   123,   126,
     123,   126,    54,    55,    57,    58,    60,   290,   291,   123,
     123,    90,    56,    57,   257,   286,    90,   136,   283,   296,
      57,    52,    53,   108,   141,   144,   260,   261,   286,   131,
     235,   235,    91,    91,    91,    91,    91,   257,   286,   257,
     257,   257,   257,   257,   126,   257,    31,   124,   124,   124,
     124,   124,   229,    34,    35,    34,    35,    34,    35,   124,
      56,    23,   193,   215,   121,   124,   122,   123,   133,    16,
     257,   286,   134,   291,    54,    55,   286,    90,   134,   126,
     126,   257,   286,   257,   134,   123,    34,   257,   257,   122,
     135,    46,    52,   100,   236,   237,   238,   239,   240,   241,
     133,   242,   242,   233,   257,   267,    43,   286,   257,   286,
     186,   187,   188,   234,   234,   257,   257,   286,   286,    90,
      98,    98,   160,   210,   211,   213,   212,   213,   209,   286,
     269,   284,   284,   169,   171,   137,   286,    57,   286,   142,
     145,   261,   257,   100,   238,   240,   122,   132,   123,   132,
     132,   241,    46,    52,    98,   243,   244,   245,   246,   247,
     248,   233,   233,   128,   128,   128,   128,   128,   216,   216,
     216,   257,   133,   123,   134,   124,    47,    49,   125,   263,
     264,   270,   126,   126,   136,   135,   259,   261,   259,   137,
     100,   237,   239,    98,   245,   247,   122,   134,   123,   134,
     134,   248,   124,   124,   124,   212,   213,   257,   284,   284,
     257,   260,   143,    98,   244,   246,   134,   126,   137,   137,
     259
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
     206,   207,   208,   208,   209,   209,   210,   210,   211,   211,
     211,   211,   211,   212,   212,   213,   213,   213,   213,   213,
     213,   214,   215,   214,   216,   216,   217,   217,   218,   219,
     219,   220,   220,   220,   221,   221,   223,   224,   222,   225,
     225,   226,   227,   227,   228,   228,   228,   229,   229,   229,
     230,   230,   231,   231,   232,   232,   233,   233,   234,   234,
     234,   234,   234,   234,   234,   234,   234,   234,   235,   235,
     235,   235,   236,   236,   237,   238,   238,   239,   240,   240,
     241,   241,   242,   242,   242,   242,   243,   243,   244,   245,
     245,   246,   247,   247,   248,   248,   249,   249,   250,   250,
     251,   251,   251,   251,   251,   251,   251,   252,   253,   253,
     253,   253,   253,   254,   254,   255,   256,   256,   257,   257,
     257,   257,   257,   257,   257,   258,   259,   259,   260,   260,
     260,   261,   261,   261,   261,   261,   262,   262,   262,   263,
     263,   263,   264,   264,   264,   264,   264,   265,   265,   266,
     266,   266,   266,   267,   267,   267,   267,   267,   267,   267,
     267,   267,   267,   267,   267,   267,   267,   267,   267,   267,
     267,   267,   268,   269,   267,   270,   271,   271,   272,   272,
     273,   273,   273,   273,   273,   273,   273,   274,   274,   274,
     274,   274,   274,   275,   276,   276,   277,   278,   279,   280,
     279,   281,   282,   281,   283,   283,   284,   285,   285,   286,
     286,   286,   286,   287,   287,   287,   287,   287,   288,   288,
     288,   288,   288,   288,   288,   288,   289,   289,   290,   290,
     291,   291,   291,   291,   291,   292,   292,   292,   292,   292,
     292,   292,   292,   293,   293,   293,   293,   293,   293,   293,
     293,   293,   293,   293,   295,   294,   296,   294,   297,   297,
     298,   298
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
       0,     2,     2,     5,     1,     0,     2,     1,     1,     2,
       2,     4,     0,     1,     1,     3,     1,     3,     0,     1,
       4,     3,     6,     1,     3,     1,     1,     2,     3,     2,
       3,     1,     0,     3,     1,     2,     1,     2,     2,     1,
       2,     2,     2,     2,     1,     3,     0,     0,     7,     1,
       3,     1,     1,     3,     1,     2,     2,     1,     1,     1,
       3,     3,     3,     3,     3,     3,     1,     1,     1,     1,
       2,     3,     3,     6,     6,     2,     3,     2,     0,     3,
       3,     3,     1,     3,     2,     1,     3,     2,     1,     2,
       1,     1,     0,     3,     3,     3,     1,     3,     2,     1,
       3,     2,     1,     2,     1,     1,     1,     3,     1,     1,
       3,     3,     3,     4,     4,     5,     5,     1,     1,     3,
       3,     3,     3,     2,     2,     3,     1,     3,     1,     2,
       1,     1,     3,     1,     1,     7,     1,     3,     0,     1,
       3,     1,     1,     3,     6,     4,     1,     1,     3,     2,
       4,     3,     1,     1,     1,     3,     1,     1,     3,     1,
       1,     1,     1,     1,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     0,     0,     7,     2,     1,     1,     0,     1,
       3,     4,     4,     4,     4,     4,     1,     1,     2,     3,
       3,     3,     3,     1,     1,     1,     2,     2,     1,     0,
       4,     1,     0,     4,     0,     2,     3,     1,     3,     1,
       1,     2,     1,     1,     1,     1,     1,     3,     2,     1,
       1,     1,     1,     1,     1,     1,     0,     4,     1,     2,
       1,     1,     1,     1,     1,     2,     1,     2,     3,     3,
       2,     3,     3,     2,     1,     3,     6,     9,     3,     3,
       3,     2,     2,     2,     0,     2,     0,     4,     1,     3,
       1,     1
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
  "statement_label", "proof_line", "$@12", "subproof",
  "subproof_statement", "proof_of_conclusion", "optional-result",
  "find_statement", "find_statement_list", "find_statement_sequence",
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
  "all_identifier_list", "$@18", "exist_identifier_list", "$@19",
  "optional_in_term", "tuple", "tuple_body", "term", "simple_term",
  "term_identifier", "variable_exclusion_set", "variable_exclusion_list",
  "bound_variable", "function_term", "set_term",
  "implicit_set_identifier_list", "$@20", "$@21", "set_member_list",
  "function_term_identifier", YY_NULLPTR
  };
#endif


#if MLIDEBUG
  const short
  database_parser::yyrline_[] =
  {
       0,   649,   649,   650,   651,   660,   661,   666,   666,   671,
     672,   679,   680,   681,   686,   695,   696,   703,   704,   709,
     714,   719,   728,   729,   736,   745,   748,   748,   751,   756,
     759,   759,   762,   768,   767,   786,   787,   792,   793,   797,
     809,   810,   815,   816,   822,   821,   829,   830,   835,   836,
     837,   842,   843,   853,   854,   855,   857,   863,   862,   868,
     870,   869,   882,   881,   898,   897,   907,   906,   917,   918,
     919,   924,   935,   946,   956,   957,   957,   971,   976,   981,
     990,   991,   996,  1004,  1036,  1046,  1046,  1050,  1061,  1066,
    1076,  1086,  1097,  1098,  1103,  1104,  1112,  1115,  1123,  1124,
    1126,  1130,  1134,  1143,  1145,  1153,  1156,  1159,  1172,  1186,
    1191,  1201,  1215,  1215,  1257,  1258,  1302,  1303,  1310,  1315,
    1316,  1321,  1322,  1323,  1328,  1329,  1340,  1341,  1340,  1375,
    1376,  1381,  1396,  1397,  1402,  1413,  1424,  1439,  1440,  1441,
    1446,  1450,  1463,  1467,  1480,  1490,  1498,  1499,  1504,  1505,
    1506,  1509,  1512,  1515,  1583,  1644,  1646,  1647,  1653,  1654,
    1655,  1656,  1660,  1661,  1674,  1686,  1687,  1699,  1711,  1712,
    1723,  1728,  1738,  1739,  1740,  1741,  1745,  1746,  1759,  1771,
    1772,  1784,  1796,  1797,  1808,  1813,  1881,  1882,  1887,  1888,
    1900,  1903,  1906,  1909,  1912,  1915,  1919,  1927,  1932,  1933,
    1936,  1939,  1942,  1949,  1953,  1961,  1966,  1970,  1978,  1979,
    1982,  1983,  1984,  1985,  1986,  1991,  2002,  2003,  2008,  2009,
    2010,  2015,  2016,  2017,  2018,  2019,  2024,  2025,  2026,  2031,
    2036,  2041,  2050,  2051,  2052,  2053,  2054,  2060,  2061,  2065,
    2066,  2067,  2068,  2074,  2075,  2076,  2079,  2080,  2083,  2084,
    2085,  2086,  2087,  2088,  2089,  2090,  2092,  2093,  2094,  2095,
    2096,  2097,  2098,  2099,  2098,  2109,  2117,  2118,  2123,  2124,
    2136,  2142,  2148,  2154,  2160,  2166,  2172,  2177,  2178,  2182,
    2186,  2190,  2194,  2202,  2206,  2207,  2212,  2217,  2222,  2226,
    2226,  2236,  2240,  2240,  2251,  2252,  2259,  2264,  2269,  2278,
    2279,  2280,  2283,  2288,  2289,  2290,  2291,  2292,  2297,  2303,
    2304,  2305,  2306,  2307,  2308,  2309,  2314,  2315,  2320,  2321,
    2330,  2331,  2332,  2333,  2334,  2339,  2342,  2343,  2347,  2351,
    2355,  2359,  2363,  2371,  2372,  2373,  2374,  2378,  2386,  2390,
    2394,  2398,  2402,  2406,  2414,  2414,  2419,  2419,  2429,  2433,
    2442,  2443
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
#line 5039 "../../mli-root/src/database-parser.cc"

#line 2447 "../../mli-root/src/database-parser.yy"


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

