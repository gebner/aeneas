(** The "symbolic" AST is the AST directly generated by the symbolic execution.
    It is very rough and meant to be extremely straightforward to build during
    the symbolic execution: we later apply transformations to generate the
    pure AST that we export. *)

open Types
open Expressions
open Values
open LlbcAst

(** "Meta"-place: a place stored as meta-data.

    Whenever we need to introduce new symbolic variables, for instance because
    of symbolic expansions, we try to store a "place", which gives information
    about the origin of the values (this place information comes from assignment
    information, etc.).
    We later use this place information to generate meaningful name, to prettify
    the generated code.
 *)
type mplace = {
  bv : Contexts.var_binder;
      (** It is important that we store the binder, and not just the variable id,
          because the most important information in a place is the name of the
          variable!
       *)
  projection : projection;
      (** We store the projection because we can, but it is actually not that useful *)
}
[@@deriving show]

type call_id =
  | Fun of fun_id_or_trait_method_ref * FunCallId.id
      (** A "regular" function (i.e., a function which is not a primitive operation) *)
  | Unop of unop
  | Binop of binop
[@@deriving show, ord]

type call = {
  call_id : call_id;
  ctx : Contexts.eval_ctx;
      (** The context upon calling the function (after the operands have been
          evaluated). We need it to compute the translated values for shared
          borrows (we need to perform lookups).
       *)
  abstractions : AbstractionId.id list;
  generics : generic_args;
  args : typed_value list;
  args_places : mplace option list;  (** Meta information *)
  dest : symbolic_value;
  dest_place : mplace option;  (** Meta information *)
}
[@@deriving show]

(** Meta information for expressions, not necessary for synthesis but useful to
    guide it to generate a pretty output.
 *)
type emeta =
  | Assignment of Contexts.eval_ctx * mplace * typed_value * mplace option
      (** We generated an assignment (destination, assigned value, src) *)
[@@deriving show]

type variant_id = VariantId.id [@@deriving show]
type global_decl_id = GlobalDeclId.id [@@deriving show]
type 'a symbolic_value_id_map = 'a SymbolicValueId.Map.t [@@deriving show]
type 'a region_group_id_map = 'a RegionGroupId.Map.t [@@deriving show]

(** Ancestor for {!expression} iter visitor.

    We could make it inherit the visitor for {!eval_ctx}, but in all the uses
    of this visitor we don't need to explore {!eval_ctx}, so we make it inherit
    the abstraction visitors instead.
 *)
class ['self] iter_expression_base =
  object (self : 'self)
    inherit [_] iter_abs
    method visit_eval_ctx : 'env -> Contexts.eval_ctx -> unit = fun _ _ -> ()
    method visit_call : 'env -> call -> unit = fun _ _ -> ()
    method visit_loop_id : 'env -> loop_id -> unit = fun _ _ -> ()

    method visit_region_group_id : 'env -> RegionGroupId.id -> unit =
      fun _ _ -> ()

    method visit_mplace : 'env -> mplace -> unit = fun _ _ -> ()
    method visit_emeta : 'env -> emeta -> unit = fun _ _ -> ()
    method visit_meta : 'env -> Meta.meta -> unit = fun _ _ -> ()

    method visit_region_group_id_map
        : 'a. ('env -> 'a -> unit) -> 'env -> 'a region_group_id_map -> unit =
      fun f env m ->
        RegionGroupId.Map.iter
          (fun id x ->
            self#visit_region_group_id env id;
            f env x)
          m

    method visit_symbolic_value_id_map
        : 'a. ('env -> 'a -> unit) -> 'env -> 'a symbolic_value_id_map -> unit =
      fun f env m ->
        SymbolicValueId.Map.iter
          (fun id x ->
            self#visit_symbolic_value_id env id;
            f env x)
          m

    method visit_symbolic_value_id_set : 'env -> symbolic_value_id_set -> unit =
      fun env s -> SymbolicValueId.Set.iter (self#visit_symbolic_value_id env) s

    method visit_symbolic_expansion : 'env -> symbolic_expansion -> unit =
      fun _ _ -> ()
  end

(** **Rem.:** here, {!expression} is not at all equivalent to the expressions
    used in LLBC or in lambda-calculus: they are simply a first step towards
    lambda-calculus expressions.
 *)
type expression =
  | Return of Contexts.eval_ctx * typed_value option
      (** There are two cases:
          - the AST is for a forward function: the typed value should contain
            the value which was in the return variable
          - the AST is for a backward function: the typed value should be [None]

          The context is the evaluation context upon reaching the return, We
          need it to translate shared borrows to pure values (we need to be able
          to look up the shared values in the context).
       *)
  | Panic
  | FunCall of call * expression
  | EndAbstraction of Contexts.eval_ctx * abs * expression
      (** The context is the evaluation context upon ending the abstraction,
          just after we removed the abstraction from the context.

          The context is the evaluation context from after evaluating the asserted
          value. It has the same purpose as for the {!Return} case.
       *)
  | EvalGlobal of global_decl_id * symbolic_value * expression
      (** Evaluate a global to a fresh symbolic value *)
  | Assertion of Contexts.eval_ctx * typed_value * expression
      (** An assertion.

          The context is the evaluation context from after evaluating the asserted
          value. It has the same purpose as for the {!Return} case.
       *)
  | Expansion of mplace option * symbolic_value * expansion
      (** Expansion of a symbolic value.
    
          The place is "meta": it gives the path to the symbolic value (if available)
          which got expanded (this path is available when the symbolic expansion
          comes from a path evaluation, during an assignment for instance).
          We use it to compute meaningful names for the variables we introduce,
          to prettify the generated code.
       *)
  | IntroSymbolic of
      Contexts.eval_ctx
      * mplace option
      * symbolic_value
      * value_aggregate
      * expression
      (** We introduce a new symbolic value, equal to some other value.

          This is used for instance when reorganizing the environment to compute
          fixed points: we duplicate some shared symbolic values to destructure
          the shared values, in order to make the environment a bit more general
          (while losing precision of course). We also use it to introduce symbolic
          values when evaluating constant generics, or trait constants.

          The context is the evaluation context from before introducing the new
          value. It has the same purpose as for the {!Return} case.
       *)
  | ForwardEnd of
      Contexts.eval_ctx
      * typed_value symbolic_value_id_map option
      * expression
      * expression region_group_id_map
      (** We use this delimiter to indicate at which point we switch to the
          generation of code specific to the backward function(s). This allows
          us in particular to factor the work out: we don't need to replay the
          symbolic execution up to this point, and can reuse it for the forward
          function and all the backward functions.

          The first expression gives the end of the translation for the forward
          function, the map from region group ids to expressions gives the end
          of the translation for the backward functions.

          The optional map from symbolic values to input values are input values
          for loops: upon entering a loop, in the translation we call the loop
          translation function, which takes care of the end of the execution.

          The evaluation context is the context at the moment we introduce the
          [ForwardEnd], and is used to translate the input values (see the
          comments for the {!Return} variant).
       *)
  | Loop of loop  (** Loop *)
  | ReturnWithLoop of loop_id * bool
      (** End the function with a call to a loop function.

          This encompasses the cases when we synthesize a function body
          and enter a loop for the first time, or when we synthesize a
          loop body and reach a [Continue].

          The boolean is [is_continue].
       *)
  | Meta of emeta * expression  (** Meta information *)

and loop = {
  loop_id : loop_id;
  input_svalues : symbolic_value list;  (** The input symbolic values *)
  fresh_svalues : symbolic_value_id_set;
      (** The symbolic values introduced by the loop fixed-point *)
  rg_to_given_back_tys :
    ((RegionId.Set.t * ty list) RegionGroupId.Map.t[@opaque]);
      (** The map from region group ids to the types of the values given back
          by the corresponding loop abstractions.
       *)
  end_expr : expression;
      (** The end of the function (upon the moment it enters the loop) *)
  loop_expr : expression;  (** The symbolically executed loop body *)
  meta : Meta.meta;  (** Information about where the origin of the loop body *)
}

and expansion =
  | ExpandNoBranch of symbolic_expansion * expression
      (** A symbolic expansion which doesn't generate a branching.
          Includes:
          - concrete expansion
          - borrow expansion
          *Doesn't* include:
          - expansion of ADTs with one variant
       *)
  | ExpandAdt of (variant_id option * symbolic_value list * expression) list
      (** ADT expansion *)
  | ExpandBool of expression * expression
      (** A boolean expansion (i.e, an [if ... then ... else ...]) *)
  | ExpandInt of integer_type * (scalar_value * expression) list * expression
      (** An integer expansion (i.e, a switch over an integer). The last
          expression is for the "otherwise" branch. *)

(* Remark: this type doesn't have to be mutually recursive with the other
   types, but it makes it easy to generate the visitors *)
and value_aggregate =
  | VaSingleValue of typed_value  (** Regular case *)
  | VaArray of typed_value list
      (** This is used when introducing array aggregates *)
  | VaCgValue of const_generic_var_id
      (** This is used when evaluating a const generic value: in the interpreter,
          we introduce a fresh symbolic value. *)
  | VaTraitConstValue of trait_ref * generic_args * string
      (** A trait constant value *)
[@@deriving
  show,
    visitors
      {
        name = "iter_expression";
        variety = "iter";
        ancestors = [ "iter_expression_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      }]
