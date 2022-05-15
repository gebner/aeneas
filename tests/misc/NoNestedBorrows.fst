(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [no_nested_borrows] *)
module NoNestedBorrows
open Primitives

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [no_nested_borrows::Pair] *)
type pair_t (t1 t2 : Type0) = { pair_x : t1; pair_y : t2; }

(** [no_nested_borrows::List] *)
type list_t (t : Type0) =
| ListCons : t -> list_t t -> list_t t
| ListNil : list_t t

(** [no_nested_borrows::One] *)
type one_t (t1 : Type0) = | OneOne : t1 -> one_t t1

(** [no_nested_borrows::EmptyEnum] *)
type empty_enum_t = | EmptyEnumEmpty : empty_enum_t

(** [no_nested_borrows::Enum] *)
type enum_t = | EnumVariant1 : enum_t | EnumVariant2 : enum_t

(** [no_nested_borrows::EmptyStruct] *)
type empty_struct_t = unit

(** [no_nested_borrows::Sum] *)
type sum_t (t1 t2 : Type0) =
| SumLeft : t1 -> sum_t t1 t2
| SumRight : t2 -> sum_t t1 t2

(** [no_nested_borrows::neg_test] *)
let neg_test_fwd (x : i32) : result i32 =
  begin match i32_neg x with | Fail -> Fail | Return i -> Return i end

(** [no_nested_borrows::add_test] *)
let add_test_fwd (x : u32) (y : u32) : result u32 =
  begin match u32_add x y with | Fail -> Fail | Return i -> Return i end

(** [no_nested_borrows::subs_test] *)
let subs_test_fwd (x : u32) (y : u32) : result u32 =
  begin match u32_sub x y with | Fail -> Fail | Return i -> Return i end

(** [no_nested_borrows::div_test] *)
let div_test_fwd (x : u32) (y : u32) : result u32 =
  begin match u32_div x y with | Fail -> Fail | Return i -> Return i end

(** [no_nested_borrows::div_test1] *)
let div_test1_fwd (x : u32) : result u32 =
  begin match u32_div x 2 with | Fail -> Fail | Return i -> Return i end

(** [no_nested_borrows::rem_test] *)
let rem_test_fwd (x : u32) (y : u32) : result u32 =
  begin match u32_rem x y with | Fail -> Fail | Return i -> Return i end

(** [no_nested_borrows::test2] *)
let test2_fwd : result unit = Return ()

(** Unit test for [no_nested_borrows::test2] *)
let _ = assert_norm (test2_fwd = Return ())

(** [no_nested_borrows::get_max] *)
let get_max_fwd (x : u32) (y : u32) : result u32 =
  if x >= y then Return x else Return y

(** [no_nested_borrows::test3] *)
let test3_fwd : result unit =
  begin match get_max_fwd 4 3 with
  | Fail -> Fail
  | Return x ->
    begin match get_max_fwd 10 11 with
    | Fail -> Fail
    | Return y ->
      begin match u32_add x y with
      | Fail -> Fail
      | Return z -> if not (z = 15) then Fail else Return ()
      end
    end
  end

(** Unit test for [no_nested_borrows::test3] *)
let _ = assert_norm (test3_fwd = Return ())

(** [no_nested_borrows::test_neg1] *)
let test_neg1_fwd : result unit = Return ()

(** Unit test for [no_nested_borrows::test_neg1] *)
let _ = assert_norm (test_neg1_fwd = Return ())

(** [no_nested_borrows::refs_test1] *)
let refs_test1_fwd : result unit = if not (1 = 1) then Fail else Return ()

(** Unit test for [no_nested_borrows::refs_test1] *)
let _ = assert_norm (refs_test1_fwd = Return ())

(** [no_nested_borrows::refs_test2] *)
let refs_test2_fwd : result unit =
  if not (2 = 2)
  then Fail
  else
    if not (0 = 0)
    then Fail
    else if not (2 = 2) then Fail else if not (2 = 2) then Fail else Return ()

(** Unit test for [no_nested_borrows::refs_test2] *)
let _ = assert_norm (refs_test2_fwd = Return ())

(** [no_nested_borrows::test_list1] *)
let test_list1_fwd : result unit = Return ()

(** Unit test for [no_nested_borrows::test_list1] *)
let _ = assert_norm (test_list1_fwd = Return ())

(** [no_nested_borrows::test_box1] *)
let test_box1_fwd : result unit =
  let b = 1 in let x = b in if not (x = 1) then Fail else Return ()

(** Unit test for [no_nested_borrows::test_box1] *)
let _ = assert_norm (test_box1_fwd = Return ())

(** [no_nested_borrows::copy_int] *)
let copy_int_fwd (x : i32) : result i32 = Return x

(** [no_nested_borrows::test_unreachable] *)
let test_unreachable_fwd (b : bool) : result unit =
  if b then Fail else Return ()

(** [no_nested_borrows::test_panic] *)
let test_panic_fwd (b : bool) : result unit = if b then Fail else Return ()

(** [no_nested_borrows::test_copy_int] *)
let test_copy_int_fwd : result unit =
  begin match copy_int_fwd 0 with
  | Fail -> Fail
  | Return y -> if not (0 = y) then Fail else Return ()
  end

(** Unit test for [no_nested_borrows::test_copy_int] *)
let _ = assert_norm (test_copy_int_fwd = Return ())

(** [no_nested_borrows::is_cons] *)
let is_cons_fwd (t : Type0) (l : list_t t) : result bool =
  begin match l with
  | ListCons x l0 -> Return true
  | ListNil -> Return false
  end

(** [no_nested_borrows::test_is_cons] *)
let test_is_cons_fwd : result unit =
  let l = ListNil in
  begin match is_cons_fwd i32 (ListCons 0 l) with
  | Fail -> Fail
  | Return b -> if not b then Fail else Return ()
  end

(** Unit test for [no_nested_borrows::test_is_cons] *)
let _ = assert_norm (test_is_cons_fwd = Return ())

(** [no_nested_borrows::split_list] *)
let split_list_fwd (t : Type0) (l : list_t t) : result (t & (list_t t)) =
  begin match l with | ListCons hd tl -> Return (hd, tl) | ListNil -> Fail end

(** [no_nested_borrows::test_split_list] *)
let test_split_list_fwd : result unit =
  let l = ListNil in
  begin match split_list_fwd i32 (ListCons 0 l) with
  | Fail -> Fail
  | Return p -> let (hd, _) = p in if not (hd = 0) then Fail else Return ()
  end

(** Unit test for [no_nested_borrows::test_split_list] *)
let _ = assert_norm (test_split_list_fwd = Return ())

(** [no_nested_borrows::get_elem] *)
let get_elem_fwd (t : Type0) (b : bool) (x : t) (y : t) : result t =
  if b then Return x else Return y

(** [no_nested_borrows::get_elem] *)
let get_elem_back
  (t : Type0) (b : bool) (x : t) (y : t) (ret : t) : result (t & t) =
  if b then Return (ret, y) else Return (x, ret)

(** [no_nested_borrows::get_elem_test] *)
let get_elem_test_fwd : result unit =
  begin match get_elem_fwd i32 true 0 0 with
  | Fail -> Fail
  | Return z ->
    begin match i32_add z 1 with
    | Fail -> Fail
    | Return z0 ->
      if not (z0 = 1)
      then Fail
      else
        begin match get_elem_back i32 true 0 0 z0 with
        | Fail -> Fail
        | Return (x, y) ->
          if not (x = 1) then Fail else if not (y = 0) then Fail else Return ()
        end
    end
  end

(** Unit test for [no_nested_borrows::get_elem_test] *)
let _ = assert_norm (get_elem_test_fwd = Return ())

(** [no_nested_borrows::test_char] *)
let test_char_fwd : result char = Return 'a'

(** [no_nested_borrows::Tree] *)
type tree_t (t : Type0) =
| TreeLeaf : t -> tree_t t
| TreeNode : t -> node_elem_t t -> tree_t t -> tree_t t

(** [no_nested_borrows::NodeElem] *)
and node_elem_t (t : Type0) =
| NodeElemCons : tree_t t -> node_elem_t t -> node_elem_t t
| NodeElemNil : node_elem_t t

(** [no_nested_borrows::even] *)
let rec even_fwd (x : u32) : result bool =
  begin match x with
  | 0 -> Return true
  | _ ->
    begin match u32_sub x 1 with
    | Fail -> Fail
    | Return i ->
      begin match odd_fwd i with | Fail -> Fail | Return b -> Return b end
    end
  end

(** [no_nested_borrows::odd] *)
and odd_fwd (x : u32) : result bool =
  begin match x with
  | 0 -> Return false
  | _ ->
    begin match u32_sub x 1 with
    | Fail -> Fail
    | Return i ->
      begin match even_fwd i with | Fail -> Fail | Return b -> Return b end
    end
  end

(** [no_nested_borrows::test_even_odd] *)
let test_even_odd_fwd : result unit =
  begin match even_fwd 0 with
  | Fail -> Fail
  | Return b ->
    if not b
    then Fail
    else
      begin match even_fwd 4 with
      | Fail -> Fail
      | Return b0 ->
        if not b0
        then Fail
        else
          begin match odd_fwd 1 with
          | Fail -> Fail
          | Return b1 ->
            if not b1
            then Fail
            else
              begin match odd_fwd 5 with
              | Fail -> Fail
              | Return b2 -> if not b2 then Fail else Return ()
              end
          end
      end
  end

(** Unit test for [no_nested_borrows::test_even_odd] *)
let _ = assert_norm (test_even_odd_fwd = Return ())

(** [no_nested_borrows::list_length] *)
let rec list_length_fwd (t : Type0) (l : list_t t) : result u32 =
  begin match l with
  | ListCons x l1 ->
    begin match list_length_fwd t l1 with
    | Fail -> Fail
    | Return i ->
      begin match u32_add 1 i with | Fail -> Fail | Return i0 -> Return i0 end
    end
  | ListNil -> Return 0
  end

(** [no_nested_borrows::list_nth_shared] *)
let rec list_nth_shared_fwd (t : Type0) (l : list_t t) (i : u32) : result t =
  begin match l with
  | ListCons x tl ->
    begin match i with
    | 0 -> Return x
    | _ ->
      begin match u32_sub i 1 with
      | Fail -> Fail
      | Return i0 ->
        begin match list_nth_shared_fwd t tl i0 with
        | Fail -> Fail
        | Return x0 -> Return x0
        end
      end
    end
  | ListNil -> Fail
  end

(** [no_nested_borrows::list_nth_mut] *)
let rec list_nth_mut_fwd (t : Type0) (l : list_t t) (i : u32) : result t =
  begin match l with
  | ListCons x tl ->
    begin match i with
    | 0 -> Return x
    | _ ->
      begin match u32_sub i 1 with
      | Fail -> Fail
      | Return i0 ->
        begin match list_nth_mut_fwd t tl i0 with
        | Fail -> Fail
        | Return x0 -> Return x0
        end
      end
    end
  | ListNil -> Fail
  end

(** [no_nested_borrows::list_nth_mut] *)
let rec list_nth_mut_back
  (t : Type0) (l : list_t t) (i : u32) (ret : t) : result (list_t t) =
  begin match l with
  | ListCons x tl ->
    begin match i with
    | 0 -> Return (ListCons ret tl)
    | _ ->
      begin match u32_sub i 1 with
      | Fail -> Fail
      | Return i0 ->
        begin match list_nth_mut_back t tl i0 ret with
        | Fail -> Fail
        | Return tl0 -> Return (ListCons x tl0)
        end
      end
    end
  | ListNil -> Fail
  end

(** [no_nested_borrows::list_rev_aux] *)
let rec list_rev_aux_fwd
  (t : Type0) (li : list_t t) (lo : list_t t) : result (list_t t) =
  begin match li with
  | ListCons hd tl ->
    begin match list_rev_aux_fwd t tl (ListCons hd lo) with
    | Fail -> Fail
    | Return l -> Return l
    end
  | ListNil -> Return lo
  end

(** [no_nested_borrows::list_rev] *)
let list_rev_fwd_back (t : Type0) (l : list_t t) : result (list_t t) =
  let li = mem_replace_fwd (list_t t) l ListNil in
  begin match list_rev_aux_fwd t li ListNil with
  | Fail -> Fail
  | Return l0 -> Return l0
  end

(** [no_nested_borrows::test_list_functions] *)
let test_list_functions_fwd : result unit =
  let l = ListNil in
  let l0 = ListCons 2 l in
  let l1 = ListCons 1 l0 in
  begin match list_length_fwd i32 (ListCons 0 l1) with
  | Fail -> Fail
  | Return i ->
    if not (i = 3)
    then Fail
    else
      begin match list_nth_shared_fwd i32 (ListCons 0 l1) 0 with
      | Fail -> Fail
      | Return i0 ->
        if not (i0 = 0)
        then Fail
        else
          begin match list_nth_shared_fwd i32 (ListCons 0 l1) 1 with
          | Fail -> Fail
          | Return i1 ->
            if not (i1 = 1)
            then Fail
            else
              begin match list_nth_shared_fwd i32 (ListCons 0 l1) 2 with
              | Fail -> Fail
              | Return i2 ->
                if not (i2 = 2)
                then Fail
                else
                  begin match list_nth_mut_back i32 (ListCons 0 l1) 1 3 with
                  | Fail -> Fail
                  | Return ls ->
                    begin match list_nth_shared_fwd i32 ls 0 with
                    | Fail -> Fail
                    | Return i3 ->
                      if not (i3 = 0)
                      then Fail
                      else
                        begin match list_nth_shared_fwd i32 ls 1 with
                        | Fail -> Fail
                        | Return i4 ->
                          if not (i4 = 3)
                          then Fail
                          else
                            begin match list_nth_shared_fwd i32 ls 2 with
                            | Fail -> Fail
                            | Return i5 ->
                              if not (i5 = 2) then Fail else Return ()
                            end
                        end
                    end
                  end
              end
          end
      end
  end

(** Unit test for [no_nested_borrows::test_list_functions] *)
let _ = assert_norm (test_list_functions_fwd = Return ())

(** [no_nested_borrows::id_mut_pair1] *)
let id_mut_pair1_fwd (t1 t2 : Type0) (x : t1) (y : t2) : result (t1 & t2) =
  Return (x, y)

(** [no_nested_borrows::id_mut_pair1] *)
let id_mut_pair1_back
  (t1 t2 : Type0) (x : t1) (y : t2) (ret : (t1 & t2)) : result (t1 & t2) =
  let (x0, x1) = ret in Return (x0, x1)

(** [no_nested_borrows::id_mut_pair2] *)
let id_mut_pair2_fwd (t1 t2 : Type0) (p : (t1 & t2)) : result (t1 & t2) =
  let (x, x0) = p in Return (x, x0)

(** [no_nested_borrows::id_mut_pair2] *)
let id_mut_pair2_back
  (t1 t2 : Type0) (p : (t1 & t2)) (ret : (t1 & t2)) : result (t1 & t2) =
  let (x, x0) = ret in Return (x, x0)

(** [no_nested_borrows::id_mut_pair3] *)
let id_mut_pair3_fwd (t1 t2 : Type0) (x : t1) (y : t2) : result (t1 & t2) =
  Return (x, y)

(** [no_nested_borrows::id_mut_pair3] *)
let id_mut_pair3_back'a
  (t1 t2 : Type0) (x : t1) (y : t2) (ret : t1) : result t1 =
  Return ret

(** [no_nested_borrows::id_mut_pair3] *)
let id_mut_pair3_back'b
  (t1 t2 : Type0) (x : t1) (y : t2) (ret : t2) : result t2 =
  Return ret

(** [no_nested_borrows::id_mut_pair4] *)
let id_mut_pair4_fwd (t1 t2 : Type0) (p : (t1 & t2)) : result (t1 & t2) =
  let (x, x0) = p in Return (x, x0)

(** [no_nested_borrows::id_mut_pair4] *)
let id_mut_pair4_back'a
  (t1 t2 : Type0) (p : (t1 & t2)) (ret : t1) : result t1 =
  Return ret

(** [no_nested_borrows::id_mut_pair4] *)
let id_mut_pair4_back'b
  (t1 t2 : Type0) (p : (t1 & t2)) (ret : t2) : result t2 =
  Return ret

(** [no_nested_borrows::StructWithTuple] *)
type struct_with_tuple_t (t1 t2 : Type0) = { struct_with_tuple_p : (t1 & t2); }

(** [no_nested_borrows::new_tuple1] *)
let new_tuple1_fwd : result (struct_with_tuple_t u32 u32) =
  Return (Mkstruct_with_tuple_t (1, 2))

(** [no_nested_borrows::new_tuple2] *)
let new_tuple2_fwd : result (struct_with_tuple_t i16 i16) =
  Return (Mkstruct_with_tuple_t (1, 2))

(** [no_nested_borrows::new_tuple3] *)
let new_tuple3_fwd : result (struct_with_tuple_t u64 i64) =
  Return (Mkstruct_with_tuple_t (1, 2))

(** [no_nested_borrows::StructWithPair] *)
type struct_with_pair_t (t1 t2 : Type0) =
{
  struct_with_pair_p : pair_t t1 t2;
}

(** [no_nested_borrows::new_pair1] *)
let new_pair1_fwd : result (struct_with_pair_t u32 u32) =
  Return (Mkstruct_with_pair_t (Mkpair_t 1 2))

(** [no_nested_borrows::test_constants] *)
let test_constants_fwd : result unit =
  begin match new_tuple1_fwd with
  | Fail -> Fail
  | Return swt ->
    let (i, _) = swt.struct_with_tuple_p in
    if not (i = 1)
    then Fail
    else
      begin match new_tuple2_fwd with
      | Fail -> Fail
      | Return swt0 ->
        let (i0, _) = swt0.struct_with_tuple_p in
        if not (i0 = 1)
        then Fail
        else
          begin match new_tuple3_fwd with
          | Fail -> Fail
          | Return swt1 ->
            let (i1, _) = swt1.struct_with_tuple_p in
            if not (i1 = 1)
            then Fail
            else
              begin match new_pair1_fwd with
              | Fail -> Fail
              | Return swp ->
                if not (swp.struct_with_pair_p.pair_x = 1)
                then Fail
                else Return ()
              end
          end
      end
  end

(** Unit test for [no_nested_borrows::test_constants] *)
let _ = assert_norm (test_constants_fwd = Return ())

(** [no_nested_borrows::test_weird_borrows1] *)
let test_weird_borrows1_fwd : result unit = Return ()

(** Unit test for [no_nested_borrows::test_weird_borrows1] *)
let _ = assert_norm (test_weird_borrows1_fwd = Return ())

(** [no_nested_borrows::test_mem_replace] *)
let test_mem_replace_fwd_back (px : u32) : result u32 =
  let y = mem_replace_fwd u32 px 1 in if not (y = 0) then Fail else Return 2

(** [no_nested_borrows::test_shared_borrow_bool1] *)
let test_shared_borrow_bool1_fwd (b : bool) : result u32 =
  if b then Return 0 else Return 1

(** [no_nested_borrows::test_shared_borrow_bool2] *)
let test_shared_borrow_bool2_fwd : result u32 = Return 0

(** [no_nested_borrows::test_shared_borrow_enum1] *)
let test_shared_borrow_enum1_fwd (l : list_t u32) : result u32 =
  begin match l with | ListCons i l0 -> Return 1 | ListNil -> Return 0 end

(** [no_nested_borrows::test_shared_borrow_enum2] *)
let test_shared_borrow_enum2_fwd : result u32 = Return 0

