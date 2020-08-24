%{ 
 type var = int 
 type lit = Pos(var) | Neg(var)
 type cluase = lit list
%}

%token Zero
%token <string> NegInt PosInt
%token  EOF
%start main
%type <clause list> main
%%

