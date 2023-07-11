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

%{

#include "directive-parser.hh"

#include <iostream>
#include <fstream>
#include <locale>
#include <set>
#include <stack>
#include <string>
#include <sstream>
#include <vector>

#include "proposition.hh"
#include "basictype.hh"


#define YYERRCODE	256

#define the_text std::string(yytext, yyleng)
#define get_text yylval.text = std::string(yytext, yyleng)

int directive_comment_level = 0;
bool directive_declaration_context = false;
mli::directive_parser::token_type directive_declared_token = mli::free_variable_context;
int directive_declared_type = 0;

int directive_current_token = 0;

extern std::istream::pos_type current_position, line_position;

std::vector<std::string> directive_strs;
mli::kleenean directive_directive_type = false;

%}

%option noyywrap
%option c++
%option yyclass="mli::directive_lexer"

%x comment
%x line_comment
%x block_comment
%x directive

%x any_identifier
%x C_string
%x find_set_variable
%x find_vertical_line
%x include_file
%x logic_prefix


bold-upper  "𝐀"|"𝐁"|"𝐂"|"𝐃"|"𝐄"|"𝐅"|"𝐆"|"𝐇"|"𝐈"|"𝐉"|"𝐊"|"𝐋"|"𝐌"|"𝐍"|"𝐎"|"𝐏"|"𝐐"|"𝐑"|"𝐒"|"𝐓"|"𝐔"|"𝐕"|"𝐖"|"𝐗"|"𝐘"|"𝐙"
bold-lower  "𝐚"|"𝐛"|"𝐜"|"𝐝"|"𝐞"|"𝐟"|"𝐠"|"𝐡"|"𝐢"|"𝐣"|"𝐤"|"𝐥"|"𝐦"|"𝐧"|"𝐨"|"𝐩"|"𝐪"|"𝐫"|"𝐬"|"𝐭"|"𝐮"|"𝐯"|"𝐰"|"𝐱"|"𝐲"|"𝐳"
bold-digit  "𝟎"|"𝟏"|"𝟐"|"𝟑"|"𝟒"|"𝟓"|"𝟔"|"𝟕"|"𝟖"|"𝟗"

bold    {bold-upper}|{bold-lower}


italic-upper  "𝐴"|"𝐵"|"𝐶"|"𝐷"|"𝐸"|"𝐹"|"𝐺"|"𝐻"|"𝐼"|"𝐽"|"𝐾"|"𝐿"|"𝑀"|"𝑁"|"𝑂"|"𝑃"|"𝑄"|"𝑅"|"𝑆"|"𝑇"|"𝑈"|"𝑉"|"𝑊"|"𝑋"|"𝑌"|"𝑍"
italic-lower  "𝑎"|"𝑏"|"𝑐"|"𝑑"|"𝑒"|"𝑓"|"𝑔"|"ℎ"|"𝑖"|"𝑗"|"𝑘"|"𝑙"|"𝑚"|"𝑛"|"𝑜"|"𝑝"|"𝑞"|"𝑟"|"𝑠"|"𝑡"|"𝑢"|"𝑣"|"𝑤"|"𝑥"|"𝑦"|"𝑧"

italic    {italic-upper}|{italic-lower}


bold-italic-upper   "𝑨"|"𝑩"|"𝑪"|"𝑫"|"𝑬"|"𝑭"|"𝑮"|"𝑯"|"𝑰"|"𝑱"|"𝑲"|"𝑳"|"𝑴"|"𝑵"|"𝑶"|"𝑷"|"𝑸"|"𝑹"|"𝑺"|"𝑻"|"𝑼"|"𝑽"|"𝑾"|"𝑿"|"𝒀"|"𝒁"
bold-italic-lower   "𝒂"|"𝒃"|"𝒄"|"𝒅"|"𝒆"|"𝒇"|"𝒈"|"𝒉"|"𝒊"|"𝒋"|"𝒌"|"𝒍"|"𝒎"|"𝒏"|"𝒐"|"𝒑"|"𝒒"|"𝒓"|"𝒔"|"𝒕"|"𝒖"|"𝒗"|"𝒘"|"𝒙"|"𝒚"|"𝒛"

bold-italic  {bold-italic-upper}|{bold-italic-lower}


script-upper   "𝒜"|"ℬ"|"𝒞"|"𝓓"|"ℰ"|"ℱ"|"𝒢"|"ℋ"|"ℐ"|"𝒥"|"𝒦"|"ℒ"|"ℳ"|"𝒩"|"𝒪"|"𝒫"|"𝒬"|"ℛ"|"𝒮"|"𝒯"|"𝒰"|"𝒱"|"𝒲"|"𝒳"|"𝒴"|"𝒵"
script-lower   "𝒶"|"𝒷"|"𝒸"|"𝒹"|"ℯ"|"𝒻"|"ℊ"|"𝒽"|"𝒾"|"𝒿"|"𝓀"|"𝓁"|"𝓂"|"𝓃"|"ℴ"|"𝓅"|"𝓆"|"𝓇"|"𝓈"|"𝓊"|"𝓋"|"𝓌"|"𝓍"|"𝓎"|"𝓏"

script  {script-upper}|{script-lower}


script-bold-upper   "𝓐"|"𝓑"|"𝓒"|"𝓓"|"𝓔"|"𝓕"|"𝓖"|"𝓗"|"𝓘"|"𝓙"|"𝓚"|"𝓛"|"𝓜"|"𝓝"|"𝓞"|"𝓟"|"𝓠"|"𝓡"|"𝓢"|"𝓣"|"𝓤"|"𝓥"|"𝓦"|"𝓧"|"𝓨"|"𝓩"
script-bold-lower   "𝓪"|"𝓫"|"𝓬"|"𝓭"|"𝓮"|"𝓯"|"𝓰"|"𝓱"|"𝓲"|"𝓳"|"𝓴"|"𝓵"|"𝓶"|"𝓷"|"𝓸"|"𝓹"|"𝓺"|"𝓻"|"𝓼"|"𝓽"|"𝓾"|"𝓿"|"𝔀"|"𝔁"|"𝔂"|"𝔃"

script-bold  {script-bold-upper}|{script-bold-lower}


fraktur-upper   "𝔄"|"𝔅"|"ℭ"|"𝔇"|"𝔈"|"𝔉"|"𝔊"|"ℌ"|"ℑ"|"𝔍"|"𝔎"|"𝔏"|"𝔐"|"𝔑"|"𝔒"|"𝔓"|"𝔔"|"ℜ"|"𝔖"|"𝔗"|"𝔘"|"𝔙"|"𝔚"|"𝔛"|"𝔜"|"ℨ"
fraktur-lower   "𝔞"|"𝔟"|"𝔠"|"𝔡"|"𝔢"|"𝔣"|"𝔤"|"𝔥"|"𝔦"|"𝔧"|"𝔨"|"𝔩"|"𝔪"|"𝔫"|"𝔬"|"𝔭"|"𝔮"|"𝔯"|"𝔰"|"𝔱"|"𝔲"|"𝔳"|"𝔴"|"𝔵"|"𝔶"|"𝔷"

fraktur  {fraktur-upper}|{fraktur-lower}


fraktur-bold-upper  "𝕬"|"𝕭"|"𝕮"|"𝕯"|"𝕰"|"𝕱"|"𝕲"|"𝕳"|"𝕴"|"𝕵"|"𝕶"|"𝕷"|"𝕸"|"𝕹"|"𝕺"|"𝕻"|"𝕼"|"𝕽"|"𝕾"|"𝕿"|"𝖀"|"𝖁"|"𝖂"|"𝖃"|"𝖄"|"𝖅"
fraktur-bold-lower  "𝖆"|"𝖇"|"𝖈"|"𝖉"|"𝖊"|"𝖋"|"𝖌"|"𝖍"|"𝖎"|"𝖏"|"𝖐"|"𝖑"|"𝖒"|"𝖓"|"𝖔"|"𝖕"|"𝖖"|"𝖗"|"𝖘"|"𝖙"|"𝖚"|"𝖛"|"𝖜"|"𝖝"|"𝖞"|"𝖟"

fraktur-bold  {fraktur-bold-upper}|{fraktur-bold-lower}


double-struck-upper   "𝔸"|"𝔹"|"ℂ"|"𝔻"|"𝔼"|"𝔽"|"𝔾"|"ℍ"|"𝕀"|"𝕁"|"𝕂"|"𝕃"|"𝕄"|"ℕ"|"𝕆"|"ℙ"|"ℚ"|"ℝ"|"𝕊"|"𝕋"|"𝕌"|"𝕍"|"𝕎"|"𝕏"|"𝕐"|"ℤ"
double-struck-lower   "𝕒"|"𝕓"|"𝕔"|"𝕕"|"𝕖"|"𝕗"|"𝕘"|"𝕙"|"𝕚"|"𝕛"|"𝕜"|"𝕝"|"𝕞"|"𝕟"|"𝕠"|"𝕡"|"𝕢"|"𝕣"|"𝕤"|"𝕥"|"𝕦"|"𝕧"|"𝕨"|"𝕩"|"𝕪"|"𝕫"
double-struck-digit   "𝟘"|"𝟙"|"𝟚"|"𝟛"|"𝟜"|"𝟝"|"𝟞"|"𝟟"|"𝟠"|"𝟡"

double-struck   {double-struck-upper}|{double-struck-lower}


greek-upper  "Α"|"Β"|"Γ"|"Δ"|"Ε"|"Ζ"|"Η"|"Θ"|"Ι"|"Κ"|"Λ"|"Μ"|"Ν"|"Ξ"|"Ο"|"Π"|"Ρ"|"ϴ"|"Σ"|"Τ"|"Υ"|"Φ"|"Χ"|"Ψ"|"Ω"
greek-lower  "α"|"β"|"γ"|"δ"|"ε"|"ζ"|"η"|"θ"|"ι"|"κ"|"λ"|"μ"|"ν"|"ξ"|"ο"|"π"|"ρ"|"ς"|"σ"|"τ"|"υ"|"φ"|"χ"|"ψ"|"ω"|"ϵ"|"ϑ"|"ϰ"|"ϕ"|"ϱ"|"ϖ"

greek  {greek-upper}|{greek-lower}


greek-bold-upper    "𝚨"|"𝚩"|"𝚪"|"𝚫"|"𝚬"|"𝚭"|"𝚮"|"𝚯"|"𝚰"|"𝚱"|"𝚲"|"𝚳"|"𝚴"|"𝚵"|"𝚶"|"𝚷"|"𝚸"|"𝚹"|"𝚺"|"𝚻"|"𝚼"|"𝚽"|"𝚾"|"𝚿"|"𝛀"
greek-bold-lower    "𝛂"|"𝛃"|"𝛄"|"𝛅"|"𝛆"|"𝛇"|"𝛈"|"𝛉"|"𝛊"|"𝛋"|"𝛌"|"𝛍"|"𝛎"|"𝛏"|"𝛐"|"𝛑"|"𝛒"|"𝛓"|"𝛔"|"𝛕"|"𝛖"|"𝛗"|"𝛘"|"𝛙"|"𝛚"|"𝛜"|"𝛝"|"𝛞"|"𝛟"|"𝛠"|"𝛡"

greek-bold  {greek-bold-upper}|{greek-bold-lower}


greek-italic-upper  "𝛢"|"𝛣"|"𝛤"|"𝛥"|"𝛦"|"𝛧"|"𝛨"|"𝛩"|"𝛪"|"𝛫"|"𝛬"|"𝛭"|"𝛮"|"𝛯"|"𝛰"|"𝛱"|"𝛲"|"𝛳"|"𝛴"|"𝛵"|"𝛶"|"𝛷"|"𝛸"|"𝛹"|"𝛺"
greek-italic-lower  "𝛼"|"𝛽"|"𝛾"|"𝛿"|"𝜀"|"𝜁"|"𝜂"|"𝜃"|"𝜄"|"𝜅"|"𝜆"|"𝜇"|"𝜈"|"𝜉"|"𝜊"|"𝜋"|"𝜌"|"𝜍"|"𝜎"|"𝜏"|"𝜐"|"𝜑"|"𝜒"|"𝜓"|"𝜔"|"𝜖"|"𝜗"|"𝜘"|"𝜙"|"𝜚"|"𝜛"

greek-italic  {greek-italic-upper}|{greek-italic-lower}


greek-bold-italic-upper   "𝜜"|"𝜝"|"𝜞"|"𝜟"|"𝜠"|"𝜡"|"𝜢"|"𝜣"|"𝜤"|"𝜥"|"𝜦"|"𝜧"|"𝜨"|"𝜩"|"𝜪"|"𝜫"|"𝜬"|"𝜭"|"𝜮"|"𝜯"|"𝜰"|"𝜱"|"𝜲"|"𝜳"|"𝜴"
greek-bold-italic-lower   "𝜶"|"𝜷"|"𝜸"|"𝜹"|"𝜺"|"𝜻"|"𝜼"|"𝜽"|"𝜾"|"𝜿"|"𝝀"|"𝝁"|"𝝂"|"𝝃"|"𝝄"|"𝝅"|"𝝆"|"𝝇"|"𝝈"|"𝝉"|"𝝊"|"𝝋"|"𝝌"|"𝝍"|"𝝎"|"𝝐"|"𝝑"|"𝝒"|"𝝓"|"𝝔"|"𝝕"

greek-bold-italic  {greek-bold-italic-upper}|{greek-bold-italic-lower}


identifier  ([[:alpha:]]+|{bold}+|{italic}+|{bold-italic}+|{script}+|{script-bold}+|{fraktur}+|{fraktur-bold}+|{double-struck}+|{greek}+|{greek-bold}+|{greek-italic}+|{greek-bold-italic}+)

logic_prefix_identifier  ([[:alpha:]]|{bold}|{italic}|{bold-italic}|{script}|{script-bold}|{fraktur}|{fraktur-bold}|{double-struck}|{greek}|{greek-bold}|{greek-italic}|{greek-bold-italic})

label       [[:alnum:]]+

/*
whitespace
" " U+2002 en space
" " U+2003 em space
" " U+2004 three-per-em space
" " U+2005 four-per-em space
" " U+2006 six-per-em space
" " U+2007 figure space
" " U+2008 punctuation space
" " U+2009 thin space
" " U+200A hair space
" " U+205F medium mathematical space
*/
whitespace  [ \f\r\t\v]|" "|" "|" "|" "|" "|" "|" "|" "|" "|" "

comment_begin "[*"
comment_end   "*]"

subscript_digit     "₀"|"₁"|"₂"|"₃"|"₄"|"₅"|"₆"|"₇"|"₈"|"₉"
superscript_digit   "⁰"|"¹"|"²"|"³"|"⁴"|"⁵"|"⁶"|"⁷"|"⁸"|"⁹"

subscript_sign   "₊"|"₋"
superscript_sign "⁺"|"⁻"

/* UTF-8 character with valid Unicode code point. */
utf8char    [\x09\x0A\x0D\x20-\x7E]|[\xC2-\xDF][\x80-\xBF]|\xE0[\xA0-\xBF][\x80-\xBF]|[\xE1-\xEC\xEE\xEF]([\x80-\xBF]{2})|\xED[\x80-\x9F][\x80-\xBF]|\xF0[\x\90-\xBF]([\x80-\xBF]{2})|[\xF1-\xF3]([\x80-\xBF]{3})|\xF4[\x80-\x8F]([\x80-\xBF]{2})

%{
#define YY_USER_ACTION  yylloc.columns(yyleng); current_position += yyleng;
%}


%%
%{
  mli::semantic_type& yylval = *yylvalp;
  mli::location_type& yylloc = *yyllocp;

  if (directive_current_token != 0) { int tok = directive_current_token; directive_current_token = 0; return tok; }

  yylloc.step();
%}

{whitespace}+ { yylloc.step(); }
\n+           { yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }


"expand_implicit_premise" { expand_implicit_premise = true; }
"unexpand_implicit_premise" { expand_implicit_premise = false; }


"count" { return mli::directive_parser::token::count_key; }
"max" { return mli::directive_parser::token::max_key; }
"level" { return mli::directive_parser::token::level_key; }
"sublevel" { return mli::directive_parser::token::sublevel_key; }


"diagnostic" { return mli::directive_parser::token::diagnostic_key; }
"ignored" { return mli::directive_parser::token::ignored_key; }
"warning" { return mli::directive_parser::token::warning_key; }
"error"   { return mli::directive_parser::token::error_key; }

"unused" { return mli::directive_parser::token::unused_key; }
"variable" { return mli::directive_parser::token::variable_key; }
"type" { return mli::directive_parser::token::type_key; }
"label" { return mli::directive_parser::token::label_key; }


"trace" { return mli::directive_parser::token::trace_key; }
"untrace" { return mli::directive_parser::token::untrace_key; }


"conditional" { return mli::directive_parser::token::conditional_key; }
"strict"      { return mli::directive_parser::token::strict_key; }


"all" { return mli::directive_parser::token::all_key; }
"none" { return mli::directive_parser::token::none_key; }
"no" { return mli::directive_parser::token::no_key; }
"use" { return mli::directive_parser::token::use_key; }


"null" { return mli::directive_parser::token::null_key; }
"empty" { return mli::directive_parser::token::empty_key; }
"result" { return mli::directive_parser::token::result_key; }
"proof" { return mli::directive_parser::token::proof_key; }
"solve" { return mli::directive_parser::token::solve_key; }
"prooftree" { return mli::directive_parser::token::prooftree_key; }
"unify" { return mli::directive_parser::token::unify_key; }
"split" { return mli::directive_parser::token::split_key; }
"substitute" { return mli::directive_parser::token::substitute_key; }
"statement" { return mli::directive_parser::token::statement_key; }
"database" { return mli::directive_parser::token::database_key; }
"formula" { return mli::directive_parser::token::formula_key; }
"unspecializable" { return mli::directive_parser::token::unspecializable_key; }
"structure" { return mli::directive_parser::token::structure_key; }
"thread" { return mli::directive_parser::token::thread_key; }

"logic" { return mli::directive_parser::token::logic_key; }

"-𝕗" { return mli::directive_parser::token::false_elimination_key; }
"+𝕗" { return mli::directive_parser::token::false_introduction_key; }

"-¬" { return mli::directive_parser::token::negation_elimination_key; }
"-¬⊢" { return mli::directive_parser::token::negation_elimination_in_premise_key; }

"-¬¬" { return mli::directive_parser::token::double_negation_elimination_key; }
"-¬¬⊢" { return mli::directive_parser::token::double_negation_elimination_in_premise_key; }
"+¬¬" { return mli::directive_parser::token::double_negation_introduction_key; }
"+¬¬⊢" { return mli::directive_parser::token::double_negation_introduction_in_premise_key; }

"-⇒" { return mli::directive_parser::token::implication_elimination_key; }
"-⇒⊢" { return mli::directive_parser::token::implication_elimination_in_premise_key; }

"-∧" { return mli::directive_parser::token::conjunction_elimination_key; }
"-∧⊢" { return mli::directive_parser::token::conjunction_elimination_in_premise_key; }
"-∨" { return mli::directive_parser::token::disjunction_elimination_key; }
"-∨⊢" { return mli::directive_parser::token::disjunction_elimination_in_premise_key; }


"include"    { get_text; return mli::directive_parser::token::include_key; }
"end"        { get_text; return mli::directive_parser::token::end_key; }


"⇒"   { get_text; return mli::directive_parser::token::implies_key; }
"⇐"   { get_text; return mli::directive_parser::token::impliedby_key; }
"⇔"  { get_text; return mli::directive_parser::token::equivalent_key; }

"∧"  { get_text; return mli::directive_parser::token::logical_and_key; }
"∨"   { get_text; return mli::directive_parser::token::logical_or_key; }
"¬"   { get_text; return mli::directive_parser::token::logical_not_key; }

":"  { directive_declaration_context = false;
       directive_bound_variable_type = free_variable_context;
       return mli::directive_parser::token::colon_key; }
","  { return mli::directive_parser::token::comma_key; }
"."  { directive_declaration_context = false;
       directive_bound_variable_type = free_variable_context;
       return mli::directive_parser::token::period_key; }

";"  { return mli::directive_parser::token::semicolon_key; }


"<"  { get_text; return mli::directive_parser::token::less_key; }
">"  { get_text; return mli::directive_parser::token::greater_key; }
"≤"  { get_text; return mli::directive_parser::token::less_or_equal_key; }
"≥"  { get_text; return mli::directive_parser::token::greater_or_equal_key; }

"≮"  { get_text; return mli::directive_parser::token::not_less_key; }
"≯"  { get_text; return mli::directive_parser::token::not_greater_key; }
"≰"  { get_text; return mli::directive_parser::token::not_less_or_equal_key; }
"≱"  { get_text; return mli::directive_parser::token::not_greater_or_equal_key; }

"="  { get_text; return mli::directive_parser::token::equal_key; }
"≠"  { get_text; return mli::directive_parser::token::not_equal_key; }


"↦" { get_text; return mli::directive_parser::token::mapsto_key; }

"°"  { get_text; return mli::directive_parser::token::degree_key; }


"("  { return mli::directive_parser::token::left_parenthesis_key; }
")"  { return mli::directive_parser::token::right_parenthesis_key; }

"⁽"  { return mli::directive_parser::token::superscript_left_parenthesis_key; }
"⁾"  { return mli::directive_parser::token::superscript_right_parenthesis_key; }

"₍"  { return mli::directive_parser::token::subscript_left_parenthesis_key; }
"₎"  { return mli::directive_parser::token::subscript_right_parenthesis_key; }


"["  { return mli::directive_parser::token::left_bracket_key; }
"]"  { return mli::directive_parser::token::right_bracket_key; }

"⟨"  { return mli::directive_parser::token::left_angle_bracket_key; }
"⟩"  { return mli::directive_parser::token::right_angle_bracket_key; }

"{"  { return mli::directive_parser::token::left_brace_key; }
"|"  { return mli::directive_parser::token::vertical_line_key; }
"}"  { return mli::directive_parser::token::right_brace_key; }

"~"  { return mli::directive_parser::token::tilde_key; }

"⋅"   { get_text; return mli::directive_parser::token::mult_key; }
"+"   { get_text; return mli::directive_parser::token::plus_key; }
"-"   { get_text; return mli::directive_parser::token::minus_key; }

"if"    { return mli::directive_parser::token::if_key; }
"then"  { return mli::directive_parser::token::then_key; }
"else"  { return mli::directive_parser::token::else_key; }

"while" { return mli::directive_parser::token::while_key; }
"do"    { return mli::directive_parser::token::do_key; }
"loop"  { return mli::directive_parser::token::loop_key; }
"for"   { return mli::directive_parser::token::for_key; }

"break"     { return mli::directive_parser::token::break_key; }
"continue"  { return mli::directive_parser::token::continue_key; }

"throw"  { return mli::directive_parser::token::throw_key; }
"try"    { return mli::directive_parser::token::try_key; }
"catch"  { return mli::directive_parser::token::catch_key; }


[[:digit:]]+ {
  get_text;
  yylval.object = ref<integer>(mli::make, yytext);
  return mli::directive_parser::token::natural_number_value;
}

[+-][[:digit:]]+ {
  get_text;
  yylval.object = ref<integer>(make, yytext);
  return mli::directive_parser::token::integer_value;
}




{identifier} {
  get_text;

  directive_parser::token_type ret = directive_define_variable(yylval);

  return ret;
}


{label} { get_text; return mli::directive_parser::token::label_key; }


"“" { yylval.text.clear(); BEGIN(any_identifier); }

<any_identifier>{
  "”" { /* Closing quote - all done. Text now in yylval.text. */
    BEGIN(INITIAL);

    directive_parser::token_type ret = directive_define_variable(yylval);


    return ret;
  }

  "“"    {
    BEGIN(INITIAL);
    throw mli::directive_parser::syntax_error(yylloc,
     "String with “; an earlier string might be unterminated.");
  }
  "\\“"  { yylval.text += "“"; }
  "\\”"  { yylval.text += "”"; }

	\\[0-7]{1,3} { /* Octal escape sequence. */
	  int result;
	  std::sscanf(yytext + 1, "%o", &result);
	  if (result > 0xff) {
      BEGIN(INITIAL);
      throw mli::directive_parser::syntax_error(yylloc,
        "String octal escape " + the_text + " is out-of-bounds, must be ≤ \\ 377.");
    }
	  yylval.text += (char)result;
	}

	\\x[[:xdigit:]]{1,2} { /* Hexadecimal escape sequence. */
	  int result;
	  std::sscanf(yytext + 2, "%x", &result);
	  if (result > 0xff) {
      // Can actually not get here, as scanning for max 2 hex digits!
      BEGIN(INITIAL);
      throw mli::directive_parser::syntax_error(yylloc,
        "String hexadecimal escape " + the_text + " is out-of-bounds, must be ≤ \\xff.");
    }
	  yylval.text += (char)result;
	}

	\\[uU][[:xdigit:]]{1,8} { /* Hexadecimal escape sequence to give UTF-8 characters. */
    yylval.text += to_utf8(std::stoul(yytext + 2, nullptr, 16));
	}

  \\[0-9]+   {
    BEGIN(INITIAL);
    throw mli::directive_parser::syntax_error(yylloc,
      "Bad string escape sequence " + the_text);
  }

  \\{2}   { yylval.text += '\\'; }
  \\&     { ; /* Non-character, used to delimit numeric escapes */ }

  \\a     { yylval.text += '\a'; }
  \\b     { yylval.text += '\b'; }
  \\f     { yylval.text += '\f'; }
  \\n     { yylval.text += '\n'; }
  \\r     { yylval.text += '\r'; }
  \\t     { yylval.text += '\t'; }
  \\v     { yylval.text += '\v'; }

  .     { yylval.text += the_text; }
  \n    {
    BEGIN(INITIAL); yylloc.lines(yyleng); yylloc.step(); line_position = current_position;
    throw mli::directive_parser::syntax_error(yylloc, "Newline in string.");
  }
}



"—"   { BEGIN(line_comment); }

<line_comment>.*\n { BEGIN(INITIAL); yylloc.lines(1); yylloc.step(); line_position = current_position; }


"[—"  { BEGIN(block_comment); directive_comment_level = 1; }

<block_comment>{ /* Block comments. */
  "—]" { /* End of the comment. */
    if (--directive_comment_level == 0) {
      BEGIN INITIAL;
    }
  }

  "[—"        { directive_comment_level++; }
  [^\xe2[\n]+ {}
  \n+         { yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }
  .           { /* Stray characters ignored, including — and [. */ }

  <<EOF>> {
    BEGIN(INITIAL);
    throw mli::directive_parser::syntax_error(yylloc,
      "Nested comments not properly closed at end of directive.");
  }
}

"—]"  {
  std::cout << "Dash" << std::endl;
  BEGIN(INITIAL);
  throw mli::directive_parser::syntax_error(yylloc, "No block comment open [— to match the close —].");
}


"\""      { yylval.text.clear(); BEGIN(C_string); }


<C_string>{
  "\""   { /* Closing quote - all done. */ BEGIN(INITIAL); return mli::directive_parser::token::plain_name; }
  \n     {
    BEGIN(INITIAL); yylloc.lines(yyleng); yylloc.step(); line_position = current_position;
    throw mli::directive_parser::syntax_error(yylloc, "Unterminated C-string.");
  }

	\\[0-7]{1,3} { /* Octal escape sequence. */
	  int result;
	  std::sscanf(yytext + 1, "%o", &result);
	  if (result > 0xff) {
      BEGIN(INITIAL);
      throw mli::directive_parser::syntax_error(yylloc,
        "String octal escape " + the_text + " is out-of-bounds, must be ≤ \\377.");
    }
	  yylval.text += (char)result;
	}

	\\x[[:xdigit:]]{1,2} { /* Hexadecimal escape sequence. */
	  int result;
	  std::sscanf(yytext + 2, "%x", &result);
	  if (result > 0xff) {
      BEGIN(INITIAL);
      throw mli::directive_parser::syntax_error(yylloc,
        "String hexadecimal escape " + the_text + " is out-of-bounds, must be ≤ \\xff.");
    }
	  yylval.text += (char)result;
	}

  \\[0-9]+    {
    BEGIN(INITIAL);
    throw mli::directive_parser::syntax_error(yylloc,
      "Bad string escape sequence " + the_text);
  }

  \\{2}   { yylval.text += '\\'; }
  \\&     { ; /* Non-character, used to delimit numeric escapes */ }

  \\a     { yylval.text += '\a'; }
  \\b     { yylval.text += '\b'; }
  \\f     { yylval.text += '\f'; }
  \\n     { yylval.text += '\n'; }
  \\r     { yylval.text += '\r'; }
  \\t     { yylval.text += '\t'; }
  \\v     { yylval.text += '\v'; }

  \\.     { yylval.text += yytext[1]; }
  \\(\n)  { yylval.text += yytext[1]; yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }
  [^\\\n\"]+  { /* " */ yylval.text += the_text; }
}


{utf8char}   { get_text;
  throw mli::directive_parser::syntax_error(yylloc, "invalid character \"" + yylval.text + "\""); }

.     { std::stringstream ss;
        ss << std::hex << std::uppercase << (unsigned)(unsigned char)yytext[0] << "ₓ";
        throw mli::directive_parser::syntax_error(yylloc, "invalid byte " + ss.str()); }

"—}"  { return EOF; }

<<EOF>> { return EOF; }

%%

