
(** Lazy List
@author Christian Sternagel
@since  Mon May 11 13:38:15 CEST 2009
*)

(** This is an implementation of lazy lists. *)
  (*** TYPES *******************************************************************)
  type 'a t = 'a cell Lazy.t
  and 'a cell = Nil | Cons of ('a * 'a t)
 
  exception Is_empty
  (*** VALUES ******************************************************************)
  (** {3 Constructors and Destructors} *)
 
  val cons : 'a -> 'a t -> 'a t
  val append : 'a t -> 'a t -> 'a t
  (** [append xs ys] concatenates the two lazy lists [xs] and [ys]. *)
  val combinations : int -> 'a t ->'a t t
  (** [combinations n xs] constructs all possible combinations of [n]
  elements from [xs]. *)
  val concat : 'a t t -> 'a t
  (** [concat ls] is equivalent to [!val: Util.LazyList.flatten]. *)
  val empty : 'a t
  (** The empty lazy list. *)
  val flatten : 'a t t -> 'a t
  (** [flatten ls] transforms a lazy list of lazy lists into
  a lazy list by concatenating all elements of [ls]. *)
  val filter : ('a -> bool) -> 'a t -> 'a t
  (** [filter f ls] removes all elements from [ls] that do not
  satisfy the predicate [f]. *)
  val hd : 'a t -> 'a
  (** Extracts the first element of the given lazy list.
  @raise Failure "empty" if the lazy list was empty. *)
  val init : int -> (int -> 'a) -> 'a t
  (** [init i f] Initializes a lazy list with [i] elements generated
  by the function [f]. *)
  val iterate : ('a -> 'a) -> 'a -> 'a t
  (** [iterate f x] returns the infinite list [\[x;f x;f(f x); ...\]]. *)
  val map : ('a -> 'b) -> 'a t -> 'b t
  (** [map f ls] maps the lazy list [\[e1; e2; ...\]] to
  the lazy list [\[f e1; f e2; ...\]]. *)
  val make : 'a -> ('a -> 'a) -> 'a t
  (** [make i n] creates an infinite list with first element
  [i] and all following elements obtained by applying [f] to
  their immediate predecessor i.e. [\[i; f i; f (f i); ...\]]. *)
  val nth : int -> 'a t -> 'a
  (** [nth i xs] extracts the [i]-th element of [xs].
  @raise Failure "out of bounds" if the list does not contain index [i]. *)
  val of_channel : in_channel -> char t
  (** [of_channel c] returns the content of channel [c] as a lazy list
  of characters. *)
  val of_file : string -> char t
  (** [of_file f] returns the content of file [f] as a lazy list
  of characters. *)
  val of_function : (int -> 'a option) -> 'a t
  (** [of_function f] applies the function [f] in turn to the values
  [0], [1], [2], ... As long as [f i] generates [Some x], [x] is
  used as [i]th element of the resulting lazy list. The list ends
  as soon as [None] is returned. *)
  val of_list : 'a list -> 'a t
  (** [of_list xs] transforms the given list [xs] into a lazy list. *)
  val of_string : string -> char t
  (** [of_string s] is a lazy list containing the characters of
  string [s]. *)
  val tl : 'a t -> 'a t
  (** Extracts all but the first element of the given lazy list.
  @raise Failure "empty" if the lazy list was empty. *)
  val to_list : ?n:int -> 'a t -> 'a list
  (** Transforms a lazy list into a list. This function does not
  terminate if the given lazy list was infinite. If [n] is specified,
  at most [n] elements are taken from the lazy list. *)
  val permutations : 'a t -> 'a t t
  (** [permutations ls]. *)
  val singleton : 'a -> 'a t
  (** The singleton lazy list. *)
  val take : int -> 'a t -> 'a t
  (** [take n xs] returns the prefix of [xs] with length [n], or
  [xs] itself if it has less elements than [n]. *)
  val take_while : ('a -> bool) -> 'a t -> 'a t
  (** [take_while p xs] returns the longest prefix of [xs] such that all
  its elements satisfy predicate [p]. *)
  val zip : 'a t -> 'b t -> ('a * 'b)t
  (** Similar to the list function. *)