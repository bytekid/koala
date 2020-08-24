{open Parser_dimacs}

rule token = parse
  [' ' '\t' '\n'] {token lexbuf}

  | '-'['1'-'9']* {NegInt(Lexing.lexeme lexbuf)}
  | ['1'-'9']* {PosInt(Lexing.lexeme lexbuf)}
  |'0' {Zero}
(*comments *)
  | 'c' [^ '\n']* {token lexbuf}
  | 'p' [^ '\n']* {token lexbuf}
  | eof {EOF}
