%token Equality 
%token NegEquality Comma LeftParen RightParen Dot
%token <string> DollarWord UpperWord LowerWord
%nonassoc Equality

%start main
%type <unit> main
%%


main : atomic_formula {}
| main Comma atomic_formula {}


atomic_formula :
  name  {}  /* constant pred */    
| name LeftParen arguments RightParen  {}
| term Equality term {}

term :
 name {}  /* constant */      
| name LeftParen arguments RightParen {}  


name : LowerWord{}
 
arguments :  
     term {}
 |arguments Comma term {}

