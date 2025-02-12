(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap_main]: opaque function definitions *)
module HashmapMain.Opaque
open Primitives
include HashmapMain.Types

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [hashmap_main::hashmap_utils::deserialize] *)
val hashmap_utils_deserialize_fwd
  : state -> result (state & (hashmap_hash_map_t u64))

(** [hashmap_main::hashmap_utils::serialize] *)
val hashmap_utils_serialize_fwd
  : hashmap_hash_map_t u64 -> state -> result (state & unit)

