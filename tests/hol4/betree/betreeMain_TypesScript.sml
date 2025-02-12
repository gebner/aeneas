(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [betree_main]: type definitions *)
open primitivesLib divDefLib

val _ = new_theory "betreeMain_Types"


Datatype:
  (** [betree_main::betree::List] *)
  betree_list_t = | BetreeListCons 't betree_list_t | BetreeListNil
End

Datatype:
  (** [betree_main::betree::UpsertFunState] *)
  betree_upsert_fun_state_t =
  | BetreeUpsertFunStateAdd u64
  | BetreeUpsertFunStateSub u64
End

Datatype:
  (** [betree_main::betree::Message] *)
  betree_message_t =
  | BetreeMessageInsert u64
  | BetreeMessageDelete
  | BetreeMessageUpsert betree_upsert_fun_state_t
End

Datatype:
  (** [betree_main::betree::Leaf] *)
  betree_leaf_t = <| betree_leaf_id : u64; betree_leaf_size : u64; |>
End

Datatype:
  (** [betree_main::betree::Node] *)
  betree_node_t =
  | BetreeNodeInternal betree_internal_t
  | BetreeNodeLeaf betree_leaf_t
  ;
  
  (** [betree_main::betree::Internal] *)
  betree_internal_t =
  <|
    betree_internal_id : u64;
    betree_internal_pivot : u64;
    betree_internal_left : betree_node_t;
    betree_internal_right : betree_node_t;
  |>
End

Datatype:
  (** [betree_main::betree::Params] *)
  betree_params_t =
  <|
    betree_params_min_flush_size : u64; betree_params_split_size : u64;
  |>
End

Datatype:
  (** [betree_main::betree::NodeIdCounter] *)
  betree_node_id_counter_t = <| betree_node_id_counter_next_node_id : u64; |>
End

Datatype:
  (** [betree_main::betree::BeTree] *)
  betree_be_tree_t =
  <|
    betree_be_tree_params : betree_params_t;
    betree_be_tree_node_id_cnt : betree_node_id_counter_t;
    betree_be_tree_root : betree_node_t;
  |>
End

(** The state type used in the state-error monad *)
val _ = new_type ("state", 0)

val _ = export_theory ()
