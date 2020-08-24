type token =
  | Equality
  | NegEquality
  | Comma
  | Dot
  | Column
  | LeftParen
  | RightParen
  | LBrace
  | RBrace
  | True
  | False
  | ForAll
  | Exists
  | And
  | NegAnd
  | Or
  | NegOr
  | Negation
  | ImplicationLR
  | ImplicationRL
  | Equivalence
  | NegEquivalence
  | Positive_Decimal of (string)
  | Decimal of (string)
  | Decimal_fraction of (string)
  | Decimal_exponent of (string)
  | Plus
  | Minus
  | Slash
  | Exponent
  | Star
  | Arrow
  | Less_Sign
  | CNF_T of (string)
  | FOF_T of (string)
  | TFF_T of (string)
  | TCF_T of (string)
  | THF_T of (string)
  | Include of (string)
  | Type of (string)
  | STATE_SEP
  | UpperWord of (string)
  | LowerWord of (string)
  | DollarWord of (string)
  | DollarDollarWord of (string)
  | String of (string)
  | QuotedStr of (string)
  | CommentPercent of (string)
  | CommentEprover of (string)
  | CommentStar of (string)
  | AnnotationPercent of (string)
  | AnnotationStar of (string)
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> unit
