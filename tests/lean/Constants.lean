-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [constants]
import Base
open Primitives

namespace Constants

/- [constants::X0] -/
def x0_body : Result U32 := Result.ret (U32.ofInt 0 (by intlit))
def x0_c : U32 := eval_global x0_body (by simp)

/- [core::num::u32::{9}::MAX] -/
def core_num_u32_max_body : Result U32 :=
  Result.ret (U32.ofInt 4294967295 (by intlit))
def core_num_u32_max_c : U32 := eval_global core_num_u32_max_body (by simp)

/- [constants::X1] -/
def x1_body : Result U32 := Result.ret core_num_u32_max_c
def x1_c : U32 := eval_global x1_body (by simp)

/- [constants::X2] -/
def x2_body : Result U32 := Result.ret (U32.ofInt 3 (by intlit))
def x2_c : U32 := eval_global x2_body (by simp)

/- [constants::incr] -/
def incr_fwd (n : U32) : Result U32 :=
  n + (U32.ofInt 1 (by intlit))

/- [constants::X3] -/
def x3_body : Result U32 := incr_fwd (U32.ofInt 32 (by intlit))
def x3_c : U32 := eval_global x3_body (by simp)

/- [constants::mk_pair0] -/
def mk_pair0_fwd (x : U32) (y : U32) : Result (U32 × U32) :=
  Result.ret (x, y)

/- [constants::Pair] -/
structure pair_t (T1 T2 : Type) where
  pair_x : T1
  pair_y : T2

/- [constants::mk_pair1] -/
def mk_pair1_fwd (x : U32) (y : U32) : Result (pair_t U32 U32) :=
  Result.ret { pair_x := x, pair_y := y }

/- [constants::P0] -/
def p0_body : Result (U32 × U32) :=
  mk_pair0_fwd (U32.ofInt 0 (by intlit)) (U32.ofInt 1 (by intlit))
def p0_c : (U32 × U32) := eval_global p0_body (by simp)

/- [constants::P1] -/
def p1_body : Result (pair_t U32 U32) :=
  mk_pair1_fwd (U32.ofInt 0 (by intlit)) (U32.ofInt 1 (by intlit))
def p1_c : pair_t U32 U32 := eval_global p1_body (by simp)

/- [constants::P2] -/
def p2_body : Result (U32 × U32) :=
  Result.ret ((U32.ofInt 0 (by intlit)), (U32.ofInt 1 (by intlit)))
def p2_c : (U32 × U32) := eval_global p2_body (by simp)

/- [constants::P3] -/
def p3_body : Result (pair_t U32 U32) :=
  Result.ret
  { pair_x := (U32.ofInt 0 (by intlit)), pair_y := (U32.ofInt 1 (by intlit)) }
def p3_c : pair_t U32 U32 := eval_global p3_body (by simp)

/- [constants::Wrap] -/
structure wrap_t (T : Type) where
  wrap_val : T

/- [constants::Wrap::{0}::new] -/
def wrap_new_fwd (T : Type) (val : T) : Result (wrap_t T) :=
  Result.ret { wrap_val := val }

/- [constants::Y] -/
def y_body : Result (wrap_t I32) := wrap_new_fwd I32 (I32.ofInt 2 (by intlit))
def y_c : wrap_t I32 := eval_global y_body (by simp)

/- [constants::unwrap_y] -/
def unwrap_y_fwd : Result I32 :=
  Result.ret y_c.wrap_val

/- [constants::YVAL] -/
def yval_body : Result I32 := unwrap_y_fwd
def yval_c : I32 := eval_global yval_body (by simp)

/- [constants::get_z1::Z1] -/
def get_z1_z1_body : Result I32 := Result.ret (I32.ofInt 3 (by intlit))
def get_z1_z1_c : I32 := eval_global get_z1_z1_body (by simp)

/- [constants::get_z1] -/
def get_z1_fwd : Result I32 :=
  Result.ret get_z1_z1_c

/- [constants::add] -/
def add_fwd (a : I32) (b : I32) : Result I32 :=
  a + b

/- [constants::Q1] -/
def q1_body : Result I32 := Result.ret (I32.ofInt 5 (by intlit))
def q1_c : I32 := eval_global q1_body (by simp)

/- [constants::Q2] -/
def q2_body : Result I32 := Result.ret q1_c
def q2_c : I32 := eval_global q2_body (by simp)

/- [constants::Q3] -/
def q3_body : Result I32 := add_fwd q2_c (I32.ofInt 3 (by intlit))
def q3_c : I32 := eval_global q3_body (by simp)

/- [constants::get_z2] -/
def get_z2_fwd : Result I32 :=
  do
    let i ← get_z1_fwd
    let i0 ← add_fwd i q3_c
    add_fwd q1_c i0

/- [constants::S1] -/
def s1_body : Result U32 := Result.ret (U32.ofInt 6 (by intlit))
def s1_c : U32 := eval_global s1_body (by simp)

/- [constants::S2] -/
def s2_body : Result U32 := incr_fwd s1_c
def s2_c : U32 := eval_global s2_body (by simp)

/- [constants::S3] -/
def s3_body : Result (pair_t U32 U32) := Result.ret p3_c
def s3_c : pair_t U32 U32 := eval_global s3_body (by simp)

/- [constants::S4] -/
def s4_body : Result (pair_t U32 U32) :=
  mk_pair1_fwd (U32.ofInt 7 (by intlit)) (U32.ofInt 8 (by intlit))
def s4_c : pair_t U32 U32 := eval_global s4_body (by simp)

end Constants
