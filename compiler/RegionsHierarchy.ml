(** This module analyzes function signatures to compute the
    hierarchy between regions.

    Note that we don't need to analyze the types: when there is a non-trivial
    relation between lifetimes in a type definition, the Rust compiler will
    automatically introduce the relevant where clauses. For instance, in the
    definition below:

    {[
      struct Wrapper<'a, 'b, T> {
        x : &'a mut &'b mut T,
      }
    ]}
    
    the Rust compiler will introduce the where clauses:
    {[
      'b : 'a
      T : 'b
    ]}

    However, it doesn't do so for the function signatures, which means we have
    to compute the constraints between the lifetimes ourselves, then that we
    have to compute the SCCs of the lifetimes (two lifetimes 'a and 'b may
    satisfy 'a : 'b and 'b : 'a, meaning they are actually equal and should
    be grouped together).
 *)

open Types
open TypesUtils
open Expressions
open LlbcAst
open LlbcAstUtils
open Assumed
open SCC
module Subst = Substitute

let compute_regions_hierarchy_for_sig (type_decls : type_decl TypeDeclId.Map.t)
    (sg : fun_sig) : region_groups =
  (* Create the dependency graph.

     An edge from 'short to 'long means that 'long outlives 'short (that is
     we have 'long : 'short,  using Rust notations).
  *)
  (* First initialize the regions map.

     We add:
     - the region variables
     - the static region
     - edges from the region variables to the static region
  *)
  let g : RegionSet.t RegionMap.t ref =
    let s_set = RegionSet.singleton RStatic in
    let m =
      List.map
        (fun (r : region_var) -> (RVar r.index, s_set))
        sg.generics.regions
    in
    let s = (RStatic, RegionSet.empty) in
    ref (RegionMap.of_list (s :: m))
  in

  let add_edge ~(short : region) ~(long : region) =
    let m = !g in
    let s = RegionMap.find short !g in
    let s = RegionSet.add long s in
    g := RegionMap.add short s m
  in

  let add_edge_from_region_constraint ((long, short) : region_outlives) =
    add_edge ~short ~long
  in

  let add_edges ~(long : region) ~(shorts : region list) =
    List.iter (fun short -> add_edge ~short ~long) shorts
  in

  (* Explore the clauses - we only explore the "region outlives" clause,
     not the "type outlives" clauses *)
  List.iter add_edge_from_region_constraint sg.preds.regions_outlive;

  (* Explore the types in the signature to add the edges *)
  let rec explore_ty (outer : region list) (ty : ty) =
    match ty with
    | TAdt (id, generics) ->
        (* Add constraints coming from the type clauses *)
        (match id with
        | TAdtId id ->
            (* Lookup the type declaration *)
            let decl = TypeDeclId.Map.find id type_decls in
            (* Instantiate the predicates *)
            let tr_self =
              UnknownTrait ("Unexpected, introduced by " ^ __FUNCTION__)
            in
            let subst =
              Subst.make_subst_from_generics decl.generics generics tr_self
            in
            let predicates = Subst.predicates_substitute subst decl.preds in
            (* Note that because we also explore the generics below, we may
               explore several times the same type - this is ok *)
            List.iter
              (fun (long, short) -> add_edges ~long ~shorts:(short :: outer))
              predicates.regions_outlive;
            List.iter
              (fun (ty, short) -> explore_ty (short :: outer) ty)
              predicates.types_outlive
        | TTuple -> (* No clauses for tuples *) ()
        | TAssumed aid -> (
            match aid with
            | TBox | TArray | TSlice | TStr -> (* No clauses for those *) ()));
        (* Explore the generics *)
        explore_generics outer generics
    | TVar _ | TLiteral _ | TNever -> ()
    | TRef (r, ty, _) ->
        (* Add the constraints for r *)
        add_edges ~long:r ~shorts:outer;
        (* Add r to the outer regions *)
        let outer = r :: outer in
        (* Continue *)
        explore_ty outer ty
    | TRawPtr (ty, _) -> explore_ty outer ty
    | TTraitType (trait_ref, _generic_args, _) ->
        (* The trait should reference a clause, and not an implementation
           (otherwise it should have been normalized) *)
        assert (
          AssociatedTypes.trait_instance_id_is_local_clause trait_ref.trait_id);
        (* We have nothing to do *)
        ()
    | TArrow (inputs, output) ->
        (* TODO: this may be too constraining *)
        List.iter (explore_ty outer) (output :: inputs)
  and explore_generics (outer : region list) (generics : generic_args) =
    let { regions; types; const_generics = _; trait_refs = _ } = generics in
    List.iter (fun long -> add_edges ~long ~shorts:outer) regions;
    List.iter (explore_ty outer) types
  in

  List.iter (explore_ty []) (sg.output :: sg.inputs);

  (* Compute the ordered SCCs *)
  let module Scc = SCC.Make (RegionOrderedType) in
  let sccs = Scc.compute (RegionMap.bindings !g) in

  (* Remove the SCC containing the static region.

     For now, we don't handle cases where regions different from 'static
     can live as long as 'static, so we check that if the group contains
     'static then it is the only region it contains, and then we filter
     the group.
     TODO: general support for 'static
  *)
  let sccs =
    (* Find the SCC which contains the static region *)
    let static_gr_id, static_scc =
      List.find
        (fun (_, scc) -> List.mem RStatic scc)
        (SccId.Map.bindings sccs.sccs)
    in
    (* The SCC should only contain the 'static *)
    assert (static_scc = [ RStatic ]);
    (* Remove the group as well as references to this group from the
       other SCCs *)
    let { sccs; scc_deps } = sccs in
    (* We have to change the indexing:
       - if id < static_gr_id: we leave the id as it is
       - if id = static_gr_id: we remove id
       - if id > static_gr_id: we decrement it by one
    *)
    let static_i = SccId.to_int static_gr_id in
    let convert_id (id : SccId.id) : SccId.id option =
      let i = SccId.to_int id in
      if i < static_i then Some id
      else if i = static_i then None
      else Some (SccId.of_int (i - 1))
    in
    let sccs =
      SccId.Map.of_list
        (List.filter_map
           (fun (id, rg_ids) ->
             match convert_id id with
             | None -> None
             | Some id -> Some (id, rg_ids))
           (SccId.Map.bindings sccs))
    in

    let scc_deps =
      List.filter_map
        (fun (id, deps) ->
          match convert_id id with
          | None -> None
          | Some id ->
              let deps = List.filter_map convert_id (SccId.Set.elements deps) in
              Some (id, SccId.Set.of_list deps))
        (SccId.Map.bindings scc_deps)
    in
    let scc_deps = SccId.Map.of_list scc_deps in

    { sccs; scc_deps }
  in

  (*
   * Compute the regions hierarchy
   *)
  List.filter_map
    (fun (scc_id, scc) ->
      (* The region id *)
      let i = SccId.to_int scc_id in
      let id = RegionGroupId.of_int i in

      (* Retrieve the set of regions in the group *)
      let regions =
        List.map
          (fun r ->
            match r with RVar r -> r | _ -> raise (Failure "Unreachable"))
          scc
      in

      (* Compute the set of parent region groups *)
      let parents =
        List.map
          (fun id -> RegionGroupId.of_int (SccId.to_int id))
          (SccId.Set.elements (SccId.Map.find scc_id sccs.scc_deps))
      in

      (* Put together *)
      Some { id; regions; parents })
    (SccId.Map.bindings sccs.sccs)

let compute_regions_hierarchies (type_decls : type_decl TypeDeclId.Map.t)
    (fun_decls : fun_decl FunDeclId.Map.t) : region_groups FunIdMap.t =
  let regular =
    List.map
      (fun (fid, d) -> (FRegular fid, d.signature))
      (FunDeclId.Map.bindings fun_decls)
  in
  let assumed =
    List.map
      (fun (info : assumed_fun_info) -> (FAssumed info.fun_id, info.fun_sig))
      assumed_fun_infos
  in
  FunIdMap.of_list
    (List.map
       (fun (fid, sg) -> (fid, compute_regions_hierarchy_for_sig type_decls sg))
       (regular @ assumed))
