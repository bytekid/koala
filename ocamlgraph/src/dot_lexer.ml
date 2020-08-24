# 20 "src/dot_lexer.mll"
 
  open Dot_ast
  open Dot_parser

  let string_buf = Buffer.create 1024

  let keyword =
    let h = Hashtbl.create 17 in
    List.iter 
      (fun (s,k) -> Hashtbl.add h s k)
      [
	"strict", STRICT;
	"graph", GRAPH;
	"digraph", DIGRAPH;
	"subgraph", SUBGRAPH;
	"node", NODE;
	"edge", EDGE;
      ];
    fun s -> let s = String.lowercase s in Hashtbl.find h s


# 24 "src/dot_lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\238\255\239\255\240\255\241\255\078\000\088\000\098\000\
    \176\000\245\255\246\255\247\255\248\255\249\255\250\255\251\255\
    \252\255\114\000\001\000\005\000\254\255\002\000\253\255\191\000\
    \244\255\211\000\221\000\157\000\252\255\253\255\002\000\255\255\
    \254\255\032\000\252\255\253\255\254\255\255\255\054\000\253\255\
    \254\255\015\000\255\255";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\255\255\255\255\013\000\017\000\012\000\
    \017\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\017\000\017\000\000\000\255\255\255\255\255\255\255\255\
    \255\255\013\000\013\000\255\255\255\255\255\255\002\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\001\000\255\255";
  Lexing.lex_default =
   "\001\000\000\000\000\000\000\000\000\000\255\255\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\021\000\255\255\000\000\021\000\000\000\255\255\
    \000\000\255\255\255\255\029\000\000\000\000\000\255\255\000\000\
    \000\000\035\000\000\000\000\000\000\000\000\000\040\000\000\000\
    \000\000\255\255\000\000";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\019\000\019\000\020\000\020\000\019\000\019\000\019\000\
    \000\000\000\000\019\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \019\000\000\000\004\000\018\000\032\000\019\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\015\000\008\000\006\000\017\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\016\000\014\000\003\000\013\000\042\000\000\000\
    \000\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\010\000\036\000\009\000\037\000\007\000\
    \041\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\012\000\026\000\011\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\022\000\000\000\000\000\000\000\
    \000\000\021\000\000\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\000\000\000\000\031\000\
    \000\000\007\000\000\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\024\000\023\000\000\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\000\000\000\000\000\000\000\000\024\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\030\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \002\000\255\255\255\255\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \034\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\039\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\028\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\018\000\021\000\000\000\019\000\019\000\
    \255\255\255\255\019\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\000\000\000\000\030\000\019\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\041\000\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\033\000\000\000\033\000\000\000\
    \038\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\005\000\000\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\017\000\255\255\255\255\255\255\
    \255\255\017\000\255\255\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\255\255\255\255\027\000\
    \255\255\007\000\255\255\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\008\000\008\000\255\255\
    \008\000\008\000\008\000\008\000\008\000\008\000\008\000\008\000\
    \008\000\008\000\255\255\255\255\255\255\255\255\008\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\027\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\018\000\021\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \033\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\038\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\027\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec token lexbuf =
   __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 51 "src/dot_lexer.mll"
      ( token lexbuf )
# 190 "src/dot_lexer.ml"

  | 1 ->
# 53 "src/dot_lexer.mll"
      ( token lexbuf )
# 195 "src/dot_lexer.ml"

  | 2 ->
# 55 "src/dot_lexer.mll"
      ( comment lexbuf; token lexbuf )
# 200 "src/dot_lexer.ml"

  | 3 ->
# 57 "src/dot_lexer.mll"
      ( COLON )
# 205 "src/dot_lexer.ml"

  | 4 ->
# 59 "src/dot_lexer.mll"
      ( COMMA )
# 210 "src/dot_lexer.ml"

  | 5 ->
# 61 "src/dot_lexer.mll"
      ( SEMICOLON )
# 215 "src/dot_lexer.ml"

  | 6 ->
# 63 "src/dot_lexer.mll"
      ( EQUAL )
# 220 "src/dot_lexer.ml"

  | 7 ->
# 65 "src/dot_lexer.mll"
      ( LBRA )
# 225 "src/dot_lexer.ml"

  | 8 ->
# 67 "src/dot_lexer.mll"
      ( RBRA )
# 230 "src/dot_lexer.ml"

  | 9 ->
# 69 "src/dot_lexer.mll"
      ( LSQ )
# 235 "src/dot_lexer.ml"

  | 10 ->
# 71 "src/dot_lexer.mll"
      ( RSQ )
# 240 "src/dot_lexer.ml"

  | 11 ->
# 73 "src/dot_lexer.mll"
      ( EDGEOP )
# 245 "src/dot_lexer.ml"

  | 12 ->
let
# 74 "src/dot_lexer.mll"
             s
# 251 "src/dot_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 75 "src/dot_lexer.mll"
      ( try keyword s with Not_found -> ID (Ident s) )
# 255 "src/dot_lexer.ml"

  | 13 ->
let
# 76 "src/dot_lexer.mll"
              s
# 261 "src/dot_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 77 "src/dot_lexer.mll"
      ( ID (Number s) )
# 265 "src/dot_lexer.ml"

  | 14 ->
# 79 "src/dot_lexer.mll"
      ( Buffer.clear string_buf; 
	let s = string lexbuf in
	ID (String s) )
# 272 "src/dot_lexer.ml"

  | 15 ->
# 83 "src/dot_lexer.mll"
      ( Buffer.clear string_buf; 
	html lexbuf; 
	ID (Html (Buffer.contents string_buf)) )
# 279 "src/dot_lexer.ml"

  | 16 ->
# 87 "src/dot_lexer.mll"
      ( EOF )
# 284 "src/dot_lexer.ml"

  | 17 ->
let
# 88 "src/dot_lexer.mll"
         c
# 290 "src/dot_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 89 "src/dot_lexer.mll"
      ( failwith ("Dot_lexer: invalid character " ^ String.make 1 c) )
# 294 "src/dot_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and string lexbuf =
   __ocaml_lex_string_rec lexbuf 27
and __ocaml_lex_string_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 93 "src/dot_lexer.mll"
      ( Buffer.contents string_buf )
# 306 "src/dot_lexer.ml"

  | 1 ->
# 95 "src/dot_lexer.mll"
      ( Buffer.add_char string_buf '"';
	string lexbuf )
# 312 "src/dot_lexer.ml"

  | 2 ->
let
# 97 "src/dot_lexer.mll"
         c
# 318 "src/dot_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 98 "src/dot_lexer.mll"
      ( Buffer.add_char string_buf c;
	string lexbuf )
# 323 "src/dot_lexer.ml"

  | 3 ->
# 101 "src/dot_lexer.mll"
      ( failwith ("Dot_lexer: unterminated string literal") )
# 328 "src/dot_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_string_rec lexbuf __ocaml_lex_state

and html lexbuf =
   __ocaml_lex_html_rec lexbuf 33
and __ocaml_lex_html_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 105 "src/dot_lexer.mll"
      ( () )
# 340 "src/dot_lexer.ml"

  | 1 ->
# 107 "src/dot_lexer.mll"
      ( Buffer.add_char string_buf '<'; html lexbuf;
	Buffer.add_char string_buf '>'; html lexbuf )
# 346 "src/dot_lexer.ml"

  | 2 ->
let
# 109 "src/dot_lexer.mll"
         c
# 352 "src/dot_lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 110 "src/dot_lexer.mll"
      ( Buffer.add_char string_buf c;
	html lexbuf )
# 357 "src/dot_lexer.ml"

  | 3 ->
# 113 "src/dot_lexer.mll"
      ( failwith ("Dot_lexer: unterminated html literal") )
# 362 "src/dot_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_html_rec lexbuf __ocaml_lex_state

and comment lexbuf =
   __ocaml_lex_comment_rec lexbuf 38
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 117 "src/dot_lexer.mll"
      ( () )
# 374 "src/dot_lexer.ml"

  | 1 ->
# 119 "src/dot_lexer.mll"
      ( comment lexbuf )
# 379 "src/dot_lexer.ml"

  | 2 ->
# 121 "src/dot_lexer.mll"
      ( failwith "Dot_lexer: unterminated comment" )
# 384 "src/dot_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;

