(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [betree_main]: type definitions *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import BetreeMain_TypesExternal.
Include BetreeMain_TypesExternal.
Module BetreeMain_Types.

(** [betree_main::betree::List]
    Source: 'src/betree.rs', lines 17:0-17:23 *)
Inductive betree_List_t (T : Type) :=
| Betree_List_Cons : T -> betree_List_t T -> betree_List_t T
| Betree_List_Nil : betree_List_t T
.

Arguments Betree_List_Cons { _ }.
Arguments Betree_List_Nil { _ }.

(** [betree_main::betree::UpsertFunState]
    Source: 'src/betree.rs', lines 63:0-63:23 *)
Inductive betree_UpsertFunState_t :=
| Betree_UpsertFunState_Add : u64 -> betree_UpsertFunState_t
| Betree_UpsertFunState_Sub : u64 -> betree_UpsertFunState_t
.

(** [betree_main::betree::Message]
    Source: 'src/betree.rs', lines 69:0-69:23 *)
Inductive betree_Message_t :=
| Betree_Message_Insert : u64 -> betree_Message_t
| Betree_Message_Delete : betree_Message_t
| Betree_Message_Upsert : betree_UpsertFunState_t -> betree_Message_t
.

(** [betree_main::betree::Leaf]
    Source: 'src/betree.rs', lines 167:0-167:11 *)
Record betree_Leaf_t :=
mkbetree_Leaf_t {
  betree_Leaf_id : u64; betree_Leaf_size : u64;
}
.

(** [betree_main::betree::Internal]
    Source: 'src/betree.rs', lines 156:0-156:15 *)
Inductive betree_Internal_t :=
| mkbetree_Internal_t :
  u64 ->
  u64 ->
  betree_Node_t ->
  betree_Node_t ->
  betree_Internal_t

(** [betree_main::betree::Node]
    Source: 'src/betree.rs', lines 179:0-179:9 *)
with betree_Node_t :=
| Betree_Node_Internal : betree_Internal_t -> betree_Node_t
| Betree_Node_Leaf : betree_Leaf_t -> betree_Node_t
.

Definition betree_Internal_id (x : betree_Internal_t) :=
  match x with | mkbetree_Internal_t x0 _ _ _ => x0 end
.

Notation "x1 .(betree_Internal_id)" := (betree_Internal_id x1) (at level 9).

Definition betree_Internal_pivot (x : betree_Internal_t) :=
  match x with | mkbetree_Internal_t _ x0 _ _ => x0 end
.

Notation "x1 .(betree_Internal_pivot)" := (betree_Internal_pivot x1)
  (at level 9)
.

Definition betree_Internal_left (x : betree_Internal_t) :=
  match x with | mkbetree_Internal_t _ _ x0 _ => x0 end
.

Notation "x1 .(betree_Internal_left)" := (betree_Internal_left x1) (at level 9)
.

Definition betree_Internal_right (x : betree_Internal_t) :=
  match x with | mkbetree_Internal_t _ _ _ x0 => x0 end
.

Notation "x1 .(betree_Internal_right)" := (betree_Internal_right x1)
  (at level 9)
.

(** [betree_main::betree::Params]
    Source: 'src/betree.rs', lines 187:0-187:13 *)
Record betree_Params_t :=
mkbetree_Params_t {
  betree_Params_min_flush_size : u64; betree_Params_split_size : u64;
}
.

(** [betree_main::betree::NodeIdCounter]
    Source: 'src/betree.rs', lines 201:0-201:20 *)
Record betree_NodeIdCounter_t :=
mkbetree_NodeIdCounter_t {
  betree_NodeIdCounter_next_node_id : u64;
}
.

(** [betree_main::betree::BeTree]
    Source: 'src/betree.rs', lines 218:0-218:17 *)
Record betree_BeTree_t :=
mkbetree_BeTree_t {
  betree_BeTree_params : betree_Params_t;
  betree_BeTree_node_id_cnt : betree_NodeIdCounter_t;
  betree_BeTree_root : betree_Node_t;
}
.

End BetreeMain_Types.
