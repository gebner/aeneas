open Pure

type regular_fun_id = A.fun_id * T.RegionGroupId.id option
[@@deriving show, ord]
(** We use this type as a key for lookups *)

module RegularFunIdOrderedType = struct
  type t = regular_fun_id

  let compare = compare_regular_fun_id

  let to_string = show_regular_fun_id

  let pp_t = pp_regular_fun_id

  let show_t = show_regular_fun_id
end

module RegularFunIdMap = Collections.MakeMap (RegularFunIdOrderedType)

module FunIdOrderedType = struct
  type t = fun_id

  let compare = compare_fun_id

  let to_string = show_fun_id

  let pp_t = pp_fun_id

  let show_t = show_fun_id
end

module FunIdMap = Collections.MakeMap (FunIdOrderedType)
module FunIdSet = Collections.MakeSet (FunIdOrderedType)

(* TODO : move *)
let binop_can_fail (binop : E.binop) : bool =
  match binop with
  | BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt -> false
  | Div | Rem | Add | Sub | Mul -> true
  | Shl | Shr -> raise Errors.Unimplemented

let mk_place_from_var (v : var) : place = { var = v.id; projection = [] }

let mk_tuple_ty (tys : ty list) : ty = Adt (Tuple, tys)

let unit_ty : ty = Adt (Tuple, [])

let unit_rvalue : typed_rvalue =
  let value = RvAdt { variant_id = None; field_values = [] } in
  let ty = unit_ty in
  { value; ty }

let mk_typed_rvalue_from_var (v : var) : typed_rvalue =
  let value = RvPlace (mk_place_from_var v) in
  let ty = v.ty in
  { value; ty }

let mk_typed_lvalue_from_var (v : var) (mp : mplace option) : typed_lvalue =
  let value = LvVar (Var (v, mp)) in
  let ty = v.ty in
  { value; ty }

let mk_tuple_lvalue (vl : typed_lvalue list) : typed_lvalue =
  let tys = List.map (fun (v : typed_lvalue) -> v.ty) vl in
  let ty = Adt (Tuple, tys) in
  let value = LvAdt { variant_id = None; field_values = vl } in
  { value; ty }

let mk_adt_lvalue (adt_ty : ty) (variant_id : VariantId.id)
    (vl : typed_lvalue list) : typed_lvalue =
  let value = LvAdt { variant_id = Some variant_id; field_values = vl } in
  { value; ty = adt_ty }

let ty_as_integer (t : ty) : T.integer_type =
  match t with Integer int_ty -> int_ty | _ -> failwith "Unreachable"

(* TODO: move *)
let type_def_is_enum (def : T.type_def) : bool =
  match def.kind with T.Struct _ -> false | Enum _ -> true

let mk_result_fail_rvalue (ty : ty) : typed_rvalue =
  let ty = Adt (Assumed Result, [ ty ]) in
  let value = RvAdt { variant_id = Some result_fail_id; field_values = [] } in
  { value; ty }

let mk_result_return_rvalue (v : typed_rvalue) : typed_rvalue =
  let ty = Adt (Assumed Result, [ v.ty ]) in
  let value =
    RvAdt { variant_id = Some result_return_id; field_values = [ v ] }
  in
  { value; ty }

let mk_result_fail_lvalue (ty : ty) : typed_lvalue =
  let ty = Adt (Assumed Result, [ ty ]) in
  let value = LvAdt { variant_id = Some result_fail_id; field_values = [] } in
  { value; ty }

let mk_result_return_lvalue (v : typed_lvalue) : typed_lvalue =
  let ty = Adt (Assumed Result, [ v.ty ]) in
  let value =
    LvAdt { variant_id = Some result_return_id; field_values = [ v ] }
  in
  { value; ty }

let mk_result_ty (ty : ty) : ty = Adt (Assumed Result, [ ty ])

let mk_value_expression (v : typed_rvalue) (mp : mplace option) : texpression =
  let e = Value (v, mp) in
  let ty = v.ty in
  { e; ty }

let mk_let (monadic : bool) (lv : typed_lvalue) (re : texpression)
    (next_e : texpression) : texpression =
  let e = Let (monadic, lv, re, next_e) in
  let ty = next_e.ty in
  { e; ty }

(** Type substitution *)
let ty_substitute (tsubst : TypeVarId.id -> ty) (ty : ty) : ty =
  let obj =
    object
      inherit [_] map_ty

      method! visit_TypeVar _ var_id = tsubst var_id
    end
  in
  obj#visit_ty () ty

let make_type_subst (vars : type_var list) (tys : ty list) : TypeVarId.id -> ty
    =
  let ls = List.combine vars tys in
  let mp =
    List.fold_left
      (fun mp (k, v) -> TypeVarId.Map.add (k : type_var).index v mp)
      TypeVarId.Map.empty ls
  in
  fun id -> TypeVarId.Map.find id mp

let fun_sig_substitute (tsubst : TypeVarId.id -> ty) (sg : fun_sig) :
    inst_fun_sig =
  let subst = ty_substitute tsubst in
  let inputs = List.map subst sg.inputs in
  let outputs = List.map subst sg.outputs in
  { inputs; outputs }

(** Return true if a list of functions are *not* mutually recursive, false otherwise.
    This function is meant to be applied on a set of (forward, backwards) functions
    generated for one recursive function.
    The way we do the test is very simple:
    - we explore the functions one by one, in the order
    - if all functions only call functions we already explored, they are not
      mutually recursive
 *)
let functions_not_mutually_recursive (funs : fun_def list) : bool =
  (* Compute the set of function identifiers in the group *)
  let ids =
    FunIdSet.of_list
      (List.map
         (fun (f : fun_def) -> Regular (A.Local f.def_id, f.back_id))
         funs)
  in
  let ids = ref ids in
  (* Explore every body *)
  let body_only_calls_itself (fdef : fun_def) : bool =
    (* Remove the current id from the id set *)
    ids := FunIdSet.remove (Regular (A.Local fdef.def_id, fdef.back_id)) !ids;

    (* Check if we call functions from the updated id set *)
    let obj =
      object
        inherit [_] iter_expression as super

        method! visit_call env call =
          if FunIdSet.mem call.func !ids then raise Utils.Found
          else super#visit_call env call
      end
    in

    try
      obj#visit_texpression () fdef.body;
      true
    with Utils.Found -> false
  in
  List.for_all body_only_calls_itself funs
