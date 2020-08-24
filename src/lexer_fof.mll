(* Lexer for output of clausification from Vampire 

   Very simple: a line beginning with fof(f<n> is concatenated with
   the following lines until there is either
   inference(.*,[],[f<m>]). or file(.,.) at the end of a line.

   The whole line is paired with <m> and stored as the value for key
   <n> in a hash table.
   
*)

{

open Lib

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace

let dbg_gr_to_str = function 
  | D_trace -> "trace"
	
let dbg_groups =
  [
   D_trace; 
 ]
    
let module_name = "lexer_fof"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)



exception Lexing_error
  
(* Update position in lexing buffer *)
let incr_linenum lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- 
      { pos with
	 Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
	 Lexing.pos_bol = pos.Lexing.pos_cnum;
      }

}


(* Definitions of POSIX character classes from Mikmatch *)

let digit = ['0'-'9']

let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = lower | upper
let digit = ['0'-'9']
let alnum = alpha | digit
(*KK uncomment punct !*)


let punct = 
  ['!' '\\' '\"' '#' '$' '%' '&' '\'' '(' ')' '*' '+' ',' '-' '.' '/' ':' ';' 
     '<' '=' '>' '?' '@' '[' ']' '^' '_' '`' '{' '|' '}' '~']


let graph = alnum | punct
let blank = ' ' | '\t'


(* Entry point for lexer *)
rule line proof = parse

  (* Every line must start with fof( *)
  
 (* vcalusify_rel starts with fof(f%d  *)
  | ("fof(f" | "tff(f" | "tcf(f") (digit+ as fof_id) as fof_head  
   { 	

      dbg_env D_trace (fun () -> Format.eprintf "Parsed '%s' with id %s@." fof_head fof_id);

	(* Continue with rest of line *)
	cont_vamp fof_head fof_id proof lexbuf

      } 

(* eprover starts with fof(c_0_%d *)
(*  | "fof(c_0_" (digit+ as fof_id) as fof_head  
  | "cnf(c_0_" (digit+ as fof_id) as fof_head  
*)
  | ("cnf(c_0_"|"fof(c_0_"| "tcf(c_0_" | "tff(c_0_")  (digit+ as fof_id) as fof_head  
      { 	
	dbg_env D_trace (fun () -> Format.eprintf "Parsed '%s' with id %s@." fof_head fof_id );

	(* Continue with rest of line *)
     cont_e fof_head fof_id proof lexbuf

   } 
   

  | "cnf(u"[^ '\n']*'\n'[^ '\n']* (* has one new line before the body of the clause *)
      {
     dbg_env D_trace (fun () -> Format.eprintf "Skipping Vampire clause");
       incr_linenum lexbuf;
       line proof lexbuf} (* Vampire's cnf*)

  |'#'[^ '\n']* {
    dbg_env D_trace (fun () -> Format.eprintf "E prover comments"); 
    line proof lexbuf}

  |blank+ {line proof lexbuf}

  |'\n' 
      {
       dbg_env D_trace (fun () -> Format.eprintf "New line") ; 
       incr_linenum lexbuf;
       line proof lexbuf
     }
	

  (* End of file reached *)
  | eof 
      {  dbg_env D_trace (fun () -> Format.eprintf "End of file"); 
	raise End_of_file }

  (* Nothing else allowed *)
  | _

      { dbg_env D_trace (fun () -> (Format.eprintf "Non-parsable at line")); 
	raise Lexing_error }

and cont_e fof_head fof_id proof = shortest
  |  (graph|blank)* "c_0_"(digit+ as parent_id) blank* ("," |"]") as fof_cont       
      { 

	dbg_env D_trace (fun () -> (Format.eprintf "Recognised '%s'  as continued line@." fof_cont));  
	dbg_env D_trace (fun () -> (Format.eprintf "Recognised parent id '%s'  as continued line@." parent_id));  
	(* Recurse to get possibly multiple parents *)
	parents_e
	  (fof_head ^ fof_cont) 
	  fof_id 
	  proof 
	  [(int_of_string parent_id)] 
	  lexbuf 
      }
        
     
    
  | (graph|blank)* ("file"|"introduced") (graph|blank)*  "))." blank* "\n"  as fof_cont 
      {
       dbg_env D_trace (fun () -> Format.eprintf "Parsed '%s' as file source @." fof_cont); 
	    
	    (* Increment line number *)
       incr_linenum lexbuf;

	    (* Add line and no parent to hash table *)
       Hashtbl.add 
	 proof 
	 (int_of_string fof_id) 
	 ((fof_head ^ fof_cont), []);

       (* Continue with remaining lines *)
       line proof lexbuf 	  
     }

and parents_e fof_head fof_id proof fof_parents = parse
  | (graph|blank)* "c_0_"(digit+ as parent_id) blank* ("," |"]") as fof_cont
      {
       dbg_env D_trace (fun () ->
	 (
	  Format.eprintf "Recognised '%s'  as continued line@." fof_cont;  
	  Format.eprintf "Recognised parent_id '%s'  as continued line@." parent_id;
	 ));
	(* Recurse to get possibly multiple parents *)
	parents_e
	  (fof_head ^ fof_cont) 
	  fof_id 
	  proof 
	 ((int_of_string parent_id)::fof_parents)
	 lexbuf
       
     }

  | (graph| blank)* ")." blank* "\n" as fof_cont
      {
	incr_linenum lexbuf;

       dbg_env D_trace (fun () -> Format.eprintf "Adding fof_id: %s parents: [%s] " fof_id (list_to_string string_of_int fof_parents ","));  

	(* Add line and parent to hash table *)
       Hashtbl.add 
	  proof 
	 (int_of_string fof_id) 
	 ((fof_head ^ fof_cont), fof_parents);
	
	(* Continue with remaining lines *)
	line proof lexbuf       
     }
  | _ as c
      {
       dbg_env D_trace (fun () -> Format.eprintf "\n\n Lexing error: clean the table \n\n %c " c);  
       raise Lexing_error	  
     }

(* Match continued lines, must use shortest instead of parse *)
and cont_vamp fof_head fof_id proof = shortest

  (* Keyword inference found *)
(*  | blank+ (alpha+ as inference) "(" graph+ ",[],[" as fof_cont  *)
  | blank+ (alpha+ as inference) "(" graph+ "],[" as fof_cont   (* KK fix 2018*)

      { 

	(* Inference rule found? *)
	if inference = "inference" then

	  (

	     dbg_env D_trace (fun () -> Format.eprintf "Parsed '%s' @." fof_cont); 
	  
	    (* Parse lists of parent formulae *)
	    parents (fof_head ^ fof_cont) fof_id proof [] lexbuf

	  )

	else

	  (
	   
	     dbg_env D_trace (fun () -> Format.eprintf "Not recognised '%s' as inference keyword@\nParsing '%s' as continued line@." inference fof_cont); 
	    
	    (* Treat as continued line *)
	    cont_vamp (fof_head ^ fof_cont) fof_id proof lexbuf 

	  )
      }

  (* Keyword file found at the end of the line *)
(*  | blank+ (alpha+ as introduced) "(" graph+ ",[])).\n" as fof_cont *)
  | blank+ (alpha+ as introduced) "(" graph+ "])).\n" as fof_cont  (* KK fix 2018*)

      { 
	
	(* Introduced formula found? *)
	if introduced = "introduced" then
	  
	  (
	    
	     dbg_env D_trace (fun () -> Format.eprintf "Parsed '%s' as introduced formula @." fof_cont); 
	    
	    (* Increment line number *)
	    incr_linenum lexbuf;
	    
	    (* Add line and no parent to hash table *)
	    Hashtbl.add 
	      proof 
	      (int_of_string fof_id) 
	      ((fof_head ^ fof_cont), []);
	    
	    (* Continue with remaining lines *)
	    line proof lexbuf 
	  
	  )
	    
	else

	  (

	     dbg_env D_trace (fun () -> Format.eprintf "Not recognised '%s' as introduced keyword@\nParsing '%s' as continued line@." introduced fof_cont); 


	    (* Treat as continued line *)
	    cont_vamp (fof_head ^ fof_cont) fof_id proof lexbuf 
	    
	  )

      }
      
  (* Keyword file found at the end of the line *)
  | blank+ (alpha+ as file) "(" graph+ "," graph+ ")).\n" as fof_cont

      { 
	
	(* File source found? *)
	if file = "file" then
	  
	  (
	    
	     dbg_env D_trace (fun () -> Format.eprintf "Parsed '%s' as file source @." fof_cont); 
	    
	    (* Increment line number *)
	    incr_linenum lexbuf;

	    (* Add line and no parent to hash table *)
	    Hashtbl.add 
	      proof 
	      (int_of_string fof_id) 
	      ((fof_head ^ fof_cont), []);
	    
	    (* Continue with remaining lines *)
	    line proof lexbuf 
	      
	  )

	else
	  
	  (

	    dbg_env D_trace (fun () -> Format.eprintf "Not recognised '%s' as file keyword@\nParsing '%s' as continued line@." file fof_cont); 

	    (* Treat as continued line *)
	    cont_vamp (fof_head ^ fof_cont) fof_id proof lexbuf 
	    
	  )

      }

  (* No keywords found until the end of the line *)
  | [^ '\n']* "\n" as fof_cont
      
      { 
	
	 dbg_env D_trace (fun () -> Format.eprintf "Parsed '%s' as continued line@." fof_cont); 
	
	(* Increment line number *)
	incr_linenum lexbuf;
	
	(* Append line and continue *)
	cont_vamp (fof_head ^ fof_cont) fof_id proof lexbuf 

      }

  (* End of file reached *)
  | eof 
      { raise End_of_file }


and parents fof_head fof_id proof fof_parents = parse

  (* Formula source *)
  | "f" (digit+ as parent_id) as fof_cont 

      {
       dbg_env D_trace (fun () -> Format.eprintf "Recognised '%s'  as continued line@." fof_cont);  
	(* Recurse to get possibly multiple parents *)
	parents 
	  (fof_head ^  fof_cont) 
	  fof_id 
	  proof 
	  ((int_of_string parent_id) :: fof_parents) 
	  lexbuf 

      }

  (* Another formula source *)
  | ",f" (digit+ as parent_id) as fof_cont 
 
      { 
	
	(* Recurse to get possibly multiple parents *)
	parents 
	  (fof_head ^  fof_cont) 
	  fof_id 
	  proof 
	  ((int_of_string parent_id) :: fof_parents) 
	  lexbuf 

      }

  (* End of line *)
  | "])).\n" as fof_cont 

      { 

	(* Increment line number *)
	incr_linenum lexbuf;

        dbg_env D_trace (fun () -> Format.eprintf "Add  Hashtbl: fof_id %s @." fof_id);   
	(* Add line and parent to hash table *)
	Hashtbl.add 
	  proof 
	  (int_of_string fof_id) 
	  ((fof_head ^ fof_cont), fof_parents);
	
	(* Continue with remaining lines *)
	line proof lexbuf 

      }

  | blank 
      {parents fof_head fof_id proof fof_parents lexbuf}

  (* Treat line as continuation *)
  | '\n' as c
      
      {
	
	(* Increment line number *)
	incr_linenum lexbuf;

	(* Continue *)
	cont_vamp (fof_head ^ (String.make 1 c)) fof_id proof lexbuf

      }

  (* Treat line as continuation *)
  | _ as c
      
      {
	
	(* Continue *)
	cont_vamp (fof_head ^ (String.make 1 c)) fof_id proof lexbuf

      }

{      
	    
  let rec pp_proof_parents ppf = function 
    | [] -> ()
    | [p] -> Format.fprintf ppf "%d" p
    | p :: tl -> 
      pp_proof_parents ppf [p]; 
      Format.fprintf ppf ","; 
      pp_proof_parents ppf tl

  let pp_proof_line ppf f = function
    | s, p->
	Format.fprintf ppf "%d: %a@\n%s@." f pp_proof_parents p s
	  
  let pp_proof ppf p =
    Hashtbl.iter (pp_proof_line ppf) p 

  (* Parse output from channel *)
  let parse proof ch_in =

    (* Lexbuf from input channel *)
    let lexbuf = Lexing.from_channel ch_in in
      
      try 
	
	(* Parse output *)
	line proof lexbuf
	  
      with 

	| End_of_file -> 

	    (* All formulae are in hash table *)
	    (	  dbg_env D_trace (fun () ->  Format.eprintf "\n\n Finished parsing \n\n");  )

	| Lexing_error ->
	    dbg_env D_trace (fun () -> Format.eprintf "\n\n Lexing error; clean the table \n\n");  
	    (* Clear hash table *)
	    Hashtbl.clear proof

(*
(* Test function *)
let main () =
  
  (* Open channel to stdin or file if given *)
  let ch_in =
    if Array.length Sys.argv > 1
    then open_in Sys.argv.(1)
    else stdin
  in
    
  (* Pass empty result *)
  let proof = Hashtbl.create 100 in
    
    (* Parse output *)
    parse proof ch_in;
    
    (* Output result *)
    Format.printf "%a" pp_proof proof;
    
;;

  main ()
;;

*)
	  
}
