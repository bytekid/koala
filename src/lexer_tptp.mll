{open Lib
 open Parser_tptp
 let increment_lnumber_pos position =  
   {Lexing.pos_fname = position.Lexing.pos_fname;
    Lexing.pos_lnum  = position.Lexing.pos_lnum+1;
    Lexing.pos_bol   = position.Lexing.pos_bol;
    Lexing.pos_cnum  = position.Lexing.pos_cnum;}
let increment_lnumber_lexbuf lexbuf = 
  lexbuf.Lexing.lex_curr_p <- (increment_lnumber_pos lexbuf.Lexing.lex_curr_p)

}

  
let percentage_sign ='%'
let double_quote    ='\"'
let single_quote    = '\''

(* "Space and visible characters upto ~, except " and *)
(*  i.e. everything inside double quotes *)
let do_char         = ([^ '\"']|"\\\"" | '\\')


(*%---Space and visible characters upto ~, except ' and \ *)
(* i.e. evrything inside double quotes  *)
(*<sq_char>            ::: ([\40-\46\50-\133\135-\176]|[\\]['\\])*)
let sq_char           = ([^ '\'']| "\\\'" | '\\')

let sign              = ['+''-']
let dot               = '.'
(* let exponent          = "Ee" *)

let exponent          = ['E''e'] 
let slash             = '/'
let zero_numeric      = '0'
let non_zero_numeric  = ['1'-'9']
let numeric           = ['0'-'9']
let positive_decimal  = (non_zero_numeric)(numeric)*
(* decimal: 0 or non_zero* *)
let decimal           = (zero_numeric|positive_decimal)
let dot_decimal       = (dot)(numeric)(numeric)*
let decimal_fraction  = (decimal)(dot_decimal)
let decimal_exponent = (decimal | decimal_fraction) (exponent) (sign)? (numeric)(numeric)* 
let lower_alpha       = ['a'-'z']
let upper_alpha       = ['A'-'Z']
let alpha_numeric     = (lower_alpha|upper_alpha|numeric|'_')
let dollar            = '$'
let upper_word        = (upper_alpha)(alpha_numeric)*
let lower_word        = (lower_alpha)(alpha_numeric)*
let dollar_word        = (dollar)lower_word

(* Vampire's answer predicates use quotes *)
let dollar_dollar_word = (((dollar)(dollar)lower_word) | single_quote((dollar)(dollar)lower_word)  single_quote)

(*%----<printable_char> is any printable ASCII character, codes 32 (space) to 126*)
(*%----(tilde). printable_char> does not include tabs, newlines, bells, etc. The*)
(*%----use of . does not not exclude tab, so this is a bit loose.*)
let printable_char    = [' '-'~']
let viewable_char     = (printable_char | '\n')

(*
let word_char          = ['A'-'Z'] | ['a'-'z'] | ['0'-'9'] | ['_']
let upper_word         = ['A'-'Z']word_char*
let lower_word         = ['a'-'z']word_char*

*)

(*%----Numbers. Signs are made part of the same token here.*)

(*
<real>               ::- (<signed_real>|<unsigned_real>)
<signed_real>        ::- <sign><unsigned_real>
<unsigned_real>      ::- (<decimal_fraction>|<decimal_exponent>)
<rational>           ::- (<signed_rational>|<unsigned_rational>)
<signed_rational>    ::- <sign><unsigned_rational>
<unsigned_rational>  ::- <decimal><slash><positive_decimal>
<integer>            ::- (<signed_integer>|<unsigned_integer>)
<signed_integer>     ::- <sign><unsigned_integer>
<unsigned_integer>   ::- <decimal>
<decimal>            ::- (<zero_numeric>|<positive_decimal>)
<positive_decimal>   ::- <non_zero_numeric><numeric>*
<decimal_exponent>   ::- (<decimal>|<decimal_fraction>)<exponent><decimal>
<decimal_fraction>   ::- <decimal><dot_decimal>
<dot_decimal>        ::- <dot><numeric><numeric>*
*)

rule token = parse
  [' ' '\t'] {token lexbuf} 
  | "\r\n" {(increment_lnumber_lexbuf lexbuf); (token lexbuf)} 
  | '\n' {(increment_lnumber_lexbuf lexbuf); (token lexbuf)} 
  | ','  {Comma}
  | '.'  {Dot}
  | ':'  {Column}
  | '('  {LeftParen} 
  | ')'  {RightParen}
  | '['  {LBrace}
  | ']'  {RBrace}

(* logic *)
  | '!'   {ForAll}
  | '?'   {Exists}
  | '&'   {And}
  | "~&"  {NegAnd}
  | '|'   {Or}
  | "~|"  {NegOr}
  | '='   {Equality}
  | "!="  {NegEquality}
  | '~'   {Negation}
  | "=>"  {ImplicationLR}
  | "<="  {ImplicationRL}
  | "<=>" {Equivalence}
  | "<~>" {NegEquivalence}
(*  | "$true" {True}
  | "$false" {False}
*)

(* nubers *)
(*  | zero_numeric     {Zero_numeric (Lexing.lexeme lexbuf)}
  | non_zero_numeric {Non_zero_numeric (Lexing.lexeme lexbuf)}
  | positive_decimal {Positive_Decimal (Lexing.lexeme lexbuf)}*)

  | decimal          {Decimal (Lexing.lexeme lexbuf)}
  | decimal_fraction {Decimal_fraction (Lexing.lexeme lexbuf)}
  | decimal_exponent {Decimal_exponent (Lexing.lexeme lexbuf)}
  | '+'        {Plus}
  | '-'        {Minus}
  | '*'        {Star}
  | '>'        {Arrow}
  | '<'        {Less_Sign}
  | slash      {Slash}
(*  | exponent   {Exponent} *)


(*keywords*)

  |"cnf"                   {CNF_T (Lexing.lexeme lexbuf)}
  |"fof"                   {FOF_T (Lexing.lexeme lexbuf)}
  |"tff"                   {TFF_T (Lexing.lexeme lexbuf)}
  |"tcf"                   {TCF_T (Lexing.lexeme lexbuf)}
  |"thf"                   {THF_T (Lexing.lexeme lexbuf)}
  |"include"               {Include (Lexing.lexeme lexbuf)}
  |"type"                  {Type (Lexing.lexeme lexbuf)}

(* words *)
  |upper_word            {UpperWord(Lexing.lexeme lexbuf)}
  |lower_word            {LowerWord(Lexing.lexeme lexbuf)}
  |dollar_word           {DollarWord(Lexing.lexeme lexbuf)}
  |dollar_dollar_word    {DollarDollarWord(Lexing.lexeme lexbuf)}

(*  |'\"' [^ '\"']*'\"'     {String(Lexing.lexeme lexbuf)}*)
  |'\"' ([^ '\"']|"\\\"" | '\\')*'\"'     
{out_str "\n\n \n !Warning Distinct objects are not supported! \n\n"; String(Lexing.lexeme lexbuf)}
(*  |'\''[^ '\'']*'\''      {QuotedStr(Lexing.lexeme lexbuf)}*)

  |'\''([^ '\'']| "\\\'" | '\\')*'\''      {QuotedStr(Lexing.lexeme lexbuf)}
  

(*comments annotations*)
  | "%$"[^ '\n']*      {AnnotationPercent (Lexing.lexeme lexbuf)}
  | "/*$"([^ '*'] | "\\*")*"*/"  {AnnotationStar (Lexing.lexeme lexbuf)}
  | '%'[^ '\n']*      {CommentPercent (Lexing.lexeme lexbuf)}
  | '#'[^ '\n']*      {CommentEprover (Lexing.lexeme lexbuf)}
  | "/*"([^ '*'] | "\\*")*"*/"  {CommentStar (Lexing.lexeme lexbuf)}   

 |_ as c                          
    {        
    errors c lexbuf
    }
(* eof*)
  | eof {EOF}
 and
   (* rule errors error_first_char = parse*)
    errors c = parse
   |[^ '\n']*  as error_rest_line 
    {
    let fail_str = 
    "Lexing failed at line number: "
    ^(string_of_int lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum)^"\n"^ 
    "Unrecognized token starting with: \'"^(string_of_char c)^error_rest_line^"\'\n"
    in
    failwith fail_str
    }
