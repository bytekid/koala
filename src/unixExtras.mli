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

(*
(** Supplements to the Unix module *)

(** {1 Daemon-related functions} *)

(** Runs f in a new daemon process. The calling process will exit
  if the second argument is true.
 
  For example:
  [let _ = UnixExtras.make_daemon server_func true]
  will start a new process and run [server_func] in it, while the original
  process will exit. See Stevens, Advanced Programming in the Unix Environment
  for details.
 *)
val make_daemon: (unit -> unit) -> bool -> unit

(** {1 I/O Functions} *)

(** Reads [len] bytes from the [src] descr with offset [start] and
copies them to the [dest] descr. Currently implemented only for Linux
and FreeBSD. The FreeBSD sendfile() system call requires that [dest] be
a socket.

@raise Unix_error on failure.
 *)
val send_file: src:Unix.file_descr -> dest:Unix.file_descr -> start:int -> len:int -> int

(** [pread fd buff ofs len] is just like [Unix.read] except it doesn't update the file descriptor's offset. The file must be capable of seeking. *)
val pread: Unix.file_descr -> string -> int -> int -> int

(** [pwrite fd buff ofs len] is just like [Unix.write] except it doesn't update the file descriptor's offset. The file must be capable of seeking. *)
val pwrite: Unix.file_descr -> string -> int -> int -> int

(** {1 Servent functions} *)

(** Same as the Unix getservent(3) *)
val getservent: unit -> Unix.service_entry

(** Same as the Unix setservent(3) *)
val setservent: bool -> unit

(** Same as the Unix endservent(3) *)
val endservent: unit -> unit

(** {1 Filesytem functions} *)

(** Returns a list of all filenames that can be read from a dirhandle *)
val listdir: Unix.dir_handle -> string list

(** Does shell-like tilde expansion of a file path. [tilde_expand
"~/foo"] returns the home directory of the current user (Via
[Unix.getlogin]) with /foo appended to it. "~foo/bar" does the same
for the user foo. Anything else is returned unaltered.

@raise Not_found if the user doesn't exist. *)
val tilde_expand: string -> string

(** {1 Process information functions} *)

(** Do we get rusage information about the calling process or its child processes? *)
type rusage_who = RUSAGE_SELF | RUSAGE_CHILDREN

(** The structure retured by [getrusage]. Not all OSes track all
fields. Notably, Linux only uses ru_rutime, ru_stime, ru_minflt,
ru_majflt and ru_nswap. *)
type rusage = { 
  ru_utime: Time.timeval; (** User time used *)
  ru_stime: Time.timeval; (** System time used *)
  ru_maxrss: int; (** Maximum resident set size *)
  ru_ixrss: int; (** Integral shared memory size *)
  ru_idrss: int; (** Integral unshared data size *)
  ru_isrss: int; (** Integral unshared stack size *)
  ru_minflt: int; (** Page reclaims *)
  ru_majflt: int; (** Page faults *)
  ru_nswap: int; (** Swaps *)
  ru_inblock: int; (** Block input operations *)
  ru_oublock: int; (** Block output operations *)
  ru_msgsnd: int; (** Messages sent *)
  ru_msgrcv: int; (** Messages received *)
  ru_nsignals: int; (** Signals received *)
  ru_nvcsw: int; (** Voluntary context switches *)
  ru_nivcsw: int (** Involuntary context switches *)
}

(** Same as the Unix getrusage(2) *) 
val getrusage: rusage_who -> rusage

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

(** The type for querying resource limits. *)
type rlimit = {
  rlim_cur: int (** The current limit *);
  rlim_max: int (** The maximum limit *)
}

(** Same as the Unix getrlimit(2) *)
val getrlimit: rlimit_resource -> rlimit

(** Same as the Unix setrlimit(2) *)
val setrlimit: rlimit_resource -> rlimit -> unit

(*

(** Same as the Unix getpgid(2) *)
val getpgid: int -> int

(** Same as the Unix setpgid(2) *)
val setpgid: int -> int -> unit

(** Same as the Unix getpgrp(2) *)
val getpgrp: unit -> int

(** Same as the Unix setpgrp(2) *)
val setpgrp: unit -> unit

*)
