(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap_main]: type definitions *)
module HashmapMain.Types
open Primitives
include HashmapMain.TypesExternal

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [hashmap_main::hashmap::List]
    Source: 'src/hashmap.rs', lines 19:0-19:16 *)
type hashmap_List_t (t : Type0) =
| Hashmap_List_Cons : usize -> t -> hashmap_List_t t -> hashmap_List_t t
| Hashmap_List_Nil : hashmap_List_t t

(** [hashmap_main::hashmap::HashMap]
    Source: 'src/hashmap.rs', lines 35:0-35:21 *)
type hashmap_HashMap_t (t : Type0) =
{
  num_entries : usize;
  max_load_factor : (usize & usize);
  max_load : usize;
  slots : alloc_vec_Vec (hashmap_List_t t);
}

