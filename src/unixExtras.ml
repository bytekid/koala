(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2016 Konstantin Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 2 of the License, or 
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         *)
(*----------------------------------------------------------------------[C]-*)




(* Unix extension routines for ocaml
   Copyright (C) 2002 Shawn Wagner <raevnos@pennmush.org>

   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.
	 
   This library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.
	 
   You should have received a copy of the GNU Lesser General Public
   License along with this library; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*)

open Unix

(*

let make_daemon f do_exit =
  if fork () <> 0 then begin
    if do_exit then
      exit 0
    else
      ()
  end else begin
    ignore (setsid ());
    ignore (Sys.chdir "/");
    ignore (umask 0);
    (* Really should close all open files here... *)
    f ()
  end


external send_file: src:Unix.file_descr -> dest:Unix.file_descr -> start:int -> len:int -> int = "stew_sendfile"

external unsafe_pread: Unix.file_descr -> string -> int -> int -> int = "stew_pread"
external unsafe_pwrite: Unix.file_descr -> string -> int -> int -> int = "stew_pwrite"

let pread fd buf ofs len =
  if ofs < 0 || len < 0 || ofs > String.length buf - len then
    invalid_arg "UnixExtras.pread"
  else
    unsafe_pread fd buf ofs len

let pwrite fd buf ofs len =
  if ofs < 0 || len < 0 || ofs > String.length buf - len then
    invalid_arg "UnixExtras.pwrite"
  else
    unsafe_pwrite fd buf ofs len
      
external getservent: unit -> service_entry = "stew_getservent"
external setservent: bool -> unit = "stew_setservent"
external endservent: unit -> unit = "stew_endservent" 

let listdir dir =
  let files = ref [] in
    try
      while true do
	files := readdir dir :: !files
      done; !files
    with End_of_file -> !files
	
let do_expand user path =
  let pwent = getpwnam user in
    Filename.concat pwent.pw_dir path

let tilde_expand path =
  let pathlen = String.length path in
  if pathlen = 0 or path.[0] <> '~' then
    path
  else if pathlen = 1 then
    do_expand (getlogin ()) ""
  else if pathlen >= 2 && path.[1] = '/' then
    do_expand (getlogin ()) (StrExtras.cut_first_n path 2)
  else try
    let slash = String.index path '/' in
      do_expand (String.sub path 1 (slash - 1)) (StrExtras.cut_first_n path (slash+1))
  with Not_found -> do_expand (StrExtras.cut_first_char path) ""


type rusage_who = RUSAGE_SELF | RUSAGE_CHILDREN

type rusage = { 
  ru_utime: Time.timeval;
  ru_stime: Time.timeval;
  ru_maxrss: int;
  ru_ixrss: int;
  ru_idrss: int;
  ru_isrss: int;
  ru_minflt: int;
  ru_majflt: int;
  ru_nswap: int;
  ru_inblock: int;
  ru_oublock: int;
  ru_msgsnd: int;
  ru_msgrcv: int;
  ru_nsignals: int;
  ru_nvcsw: int;
  ru_nivcsw: int
}

external getrusage: rusage_who -> rusage = "stew_getrusage"

*)

(** The resource type to query or set with [getrlimit] or [setrlimit] *)
type rlimit_resource = RLIMIT_CPU (** CPU time in seconds *)
		       | RLIMIT_FSIZE (** Maximum file size *)
		       | RLIMIT_DATA (** Max data size *)
		       | RLIMIT_STACK (** Max stack size *)
		       | RLIMIT_CORE (** Max core file size *)
		       | RLIMIT_RSS (** Max resident set size *)
		       | RLIMIT_NPROF (** Max number of processes *)
		       | RLIMIT_NOFILE (** Max number of open files *)
		       | RLIMIT_MEMLOCK (** Max locked-in-memory address space *)
		       | RLIMIT_AS (** Address space limit *)

type rlimit = {
  rlim_cur: int;
  rlim_max: int
}

external getrlimit: rlimit_resource -> rlimit = "stew_getrlimit"
external setrlimit: rlimit_resource -> rlimit -> unit = "stew_setrlimit"

external getpgid: int -> int = "stew_getpgid"
external setpgid: int -> int -> unit = "stew_setpgid"
external getpgrp: unit -> int = "stew_getpgrp"
external setpgrp: unit -> unit = "stew_setpgrp"
