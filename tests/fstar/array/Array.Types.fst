(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [array]: type definitions *)
module Array.Types
open Primitives

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [array::AB]
    Source: 'src/array.rs', lines 3:0-3:11 *)
type aB_t = | AB_A : aB_t | AB_B : aB_t

