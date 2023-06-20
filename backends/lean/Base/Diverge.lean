import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Linarith
import Mathlib.Order.FixedPoints

/-
TODO:
- we want an easier to use cases:
  - keeps in the goal an equation of the shape: `t = case`
  - if called on Prop terms, uses Classical.em
  Actually, the cases from mathlib seems already quite powerful
  (https://leanprover-community.github.io/mathlib_docs/tactics.html#cases)
  For instance: cases h : e
  Also: cases_matching
- better split tactic
- we need conversions to operate on the head of applications.
  Actually, something like this works:
  ```
  conv at Hl =>
    apply congr_fun
    simp [fix_fuel_P]
  ```
  Maybe we need a rpt ... ; focus?
- simplifier/rewriter have a strange behavior sometimes
-/

namespace Diverge

namespace Primitives
/-! # Copy-pasting from Primitives to make the file self-contained -/

inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
deriving Repr, BEq

open Error

inductive Result (α : Type u) where
  | ret (v: α): Result α
  | fail (e: Error): Result α
  | div
  | undef
deriving Repr, BEq

-- TODO: generalize (we should parameterize the definition by a relation over `a`)
instance : LE (Result α) where
  le a b := a = .div ∨ a = b ∨ b = .undef

@[simp] theorem Result.le_undef {a : Result α} : a ≤ .undef := .inr (.inr rfl)
@[simp] theorem Result.div_le {a : Result α} : .div ≤ a := .inl rfl

instance : PartialOrder (Result α) where
  le_refl a := .inr (.inl rfl)
  le_trans a b c hab hbc :=
    show a = .div ∨ a = c ∨ c = .undef from by
      rcases hab with rfl|rfl|rfl <;> rcases hbc with ⟨⟩|rfl|rfl <;> simp_all
  le_antisymm a b hab hba := by
      rcases hab with rfl|rfl|rfl <;> rcases hba with h|h|h <;> simp_all

noncomputable instance : InfSet (Result α) where
  sInf s := open Classical in
    if s = ∅ then .undef else if h : ∃ a, s = {a} ∨ s = {.undef, a} then Classical.choose h else .div

noncomputable instance : CompleteLattice (Result α) :=
  completeLatticeOfInf _ fun s => by
    classical
    show IsGLB s (dite _ _ _)
    by_cases h : s = ∅ <;> simp only [if_pos, if_neg, h]
    case pos => simp [h, IsTop]
    by_cases h' : ∃ a, s = {a} ∨ s = {.undef, a} <;> simp only [dif_pos, dif_neg, h']
    case pos =>
      rcases Classical.choose_spec h' with h' | h' <;> conv => arg 1; rw [h']
      case inl => apply isGLB_singleton
      case inr => refine ⟨by rintro a (rfl|rfl) <;> simp, fun a ha => by simpa using ha⟩
    case neg =>
      have ⟨a, ha, hau⟩ : ∃ a ∈ s, a ≠ .undef := by
        contrapose! h'
        have ⟨a, ha⟩ := s.eq_empty_or_nonempty.resolve_left h
        refine ⟨a, .inl (Set.eq_singleton_iff_unique_mem.2 ⟨ha, fun b hb => h' a ha ▸ h' b hb ▸ rfl⟩)⟩
      have ⟨b, hb, hab, hbu⟩ : ∃ b ∈ s, a ≠ b ∧ b ≠ .undef := by
        have : ¬ s = {a} := fun h => h' ⟨a, .inl h⟩
        contrapose! h'; simp only [not_exists, not_and, ne_eq, not_not] at h'
        rw [Set.eq_singleton_iff_unique_mem] at this; push_neg at this
        have ⟨b, hb, hba⟩ := this ha
        obtain rfl := h' b hb (Ne.symm hba)
        refine ⟨a, .inr (le_antisymm (fun c hc => ?_) (by simp [Set.insert_subset, ha, hb]))⟩
        have t := h' c hc; contrapose! t; simpa [not_or, and_comm, eq_comm] using t
      refine ⟨by simp [lowerBounds], fun c hc => ?_⟩
      replace ha := hc ha
      replace hb := hc hb
      rcases ha with rfl|rfl|rfl <;> simp at hau ⊢
      rcases hb with rfl|rfl|rfl <;> simp at hbu ⊢
      contradiction

theorem Result.top_eq_undef : (⊤ : Result α) = .undef := by
  rw [← sInf_empty]; refine if_pos rfl

theorem Result.bot_eq_div : (⊥ : Result α) = .div := by
  rw [← sInf_univ]
  refine (if_neg (by simp)).trans (dif_neg ?_)
  rintro ⟨a, h | h⟩ <;> simp [Set.ext_iff] at h <;>
    have := h div <;> have := h undef <;> have := h (fail .panic) <;>
    rcases a <;> simp at *

open Result

def bind (x: Result α) (f: α -> Result β) : Result β :=
  match x with
  | ret v  => f v 
  | fail v => fail v
  | div => div
  | undef => undef

@[simp] theorem bind_ret (x : α) (f : α → Result β) : bind (.ret x) f = f x := by simp [bind]
@[simp] theorem bind_fail (x : Error) (f : α → Result β) : bind (.fail x) f = .fail x := by simp [bind]
@[simp] theorem bind_div (f : α → Result β) : bind .div f = .div := by simp [bind]
@[simp] theorem bind_undef (f : α → Result β) : bind .undef f = .undef := by simp [bind]

theorem bind_mono {x y : Result α} {f g : α → Result β} (hx : x ≤ y) (hf : f ≤ g) :
    bind x f ≤ bind y g := by
  rcases hx with rfl|rfl|rfl <;> simp
  rcases x <;> simp
  apply hf

-- Allows using Result in do-blocks
instance : Bind Result where
  bind := bind

-- Allows using return x in do-blocks
instance : Pure Result where
  pure := fun x => ret x

@[simp] theorem bind_tc_ret (x : α) (f : α → Result β) :
  (do let y ← .ret x; f y) = f x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_fail (x : Error) (f : α → Result β) :
  (do let y ← fail x; f y) = fail x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_div (f : α → Result β) :
  (do let y ← div; f y) = div := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_undef (f : α → Result β) :
  (do let y ← undef; f y) = undef := by simp [Bind.bind, bind]

def div? {α: Type} (r: Result α): Bool :=
  r matches div

end Primitives

namespace Fix

  open Primitives
  open Result

  variable {a b c d : Type _}

  /-! # The least fixed point definition and its properties -/

  partial def fixImpl (f : (a → Result b) → a → Result b) (x : a) : Result b :=
    f (fixImpl f) x

  open Classical in
  @[implemented_by fixImpl] -- FIXME: this implementation is only correct if f is monotone.
  def fix (f : (a → Result b) → a → Result b) (x : a) : Result b :=
    if monotone' : Monotone f then
      OrderHom.lfp { toFun := f, monotone' } x
    else
      .div

  /-! # The validity property -/

  theorem fix_fixed_eq_forall {f : (a → Result b) → a → Result b} (Hmono : Monotone f) :
    ∀ x, fix f x = f (fix f) x := by
    intro x; 
    simp_rw [fix, dif_pos (show Monotone f from Hmono)]
    conv => lhs; rw [← OrderHom.map_lfp]

  -- The final fixed point equation
  theorem fix_fixed_eq {f : (a → Result b) → a → Result b} (Hmono : Monotone f) :
      fix f = f (fix f) :=
    funext (fix_fixed_eq_forall Hmono)

  /-! # Making the proofs of validity manageable (and automatable) -/

  attribute [simp] monotone_const

  theorem Monotone_same [CompleteLattice α] (x : Result c) :
      Monotone (λ _ : α => x) := by
    simp

  @[simp] theorem Monotone_rec (x : α) : Monotone (λ f : α → Result β => f x) := by
    simp_all [Monotone, Pi.le_def]

  -- The important lemma about `Monotone`
  -- Lean is good at unification: we can write a very general version
  -- (in particular, it will manage to figure out `g` and `h` when we
  -- apply the lemma)
  theorem Monotone_bind [CompleteLattice α]
    (g : α → Result c)
    (h : c → α → Result d) :
    Monotone g →
    (∀ y, Monotone (h y)) →
    Monotone (λ k => do let y ← g k; h y k) := by
    intro hg hh fg fh Hrgh
    refine bind_mono (hg Hrgh) fun y => hh _ Hrgh

  theorem Monotone_imp_is_valid [CompleteLattice α] {{e : α → a → Result b}}
      (Hvalid : ∀ x, Monotone (λ k => e k x)) :
    Monotone e := by
    intro f h Hr x
    apply Hvalid; assumption

  theorem Monotone_fix_fixed_eq {{e : (a → Result b) → a → Result b}}
    (Hvalid : ∀ x, Monotone (λ k => e k x)) :
    fix e = e (fix e) := by
    exact fix_fixed_eq (Monotone_imp_is_valid Hvalid)

end Fix

namespace Ex1
  /- An example of use of the fixed-point -/
  open Primitives Fix

  variable {a : Type} (k : (List a × Int) → Result a)

  def list_nth_body (x : (List a × Int)) : Result a :=
    let (ls, i) := x
    match ls with
    | [] => .fail .panic
    | hd :: tl =>
      if i = 0 then .ret hd
      else k (tl, i - 1)

  theorem list_nth_body_is_valid: ∀ x, Monotone (λ k => @list_nth_body a k x) := by
    intro k x
    simp [list_nth_body]
    split <;> simp
    split <;> simp
    intro b hb; apply hb

  def list_nth (ls : List a) (i : Int) : Result a := fix list_nth_body (ls, i)

  -- The unfolding equation - diverges if `i < 0`
  theorem list_nth_eq (ls : List a) (i : Int) :
    list_nth ls i =
      match ls with
      | [] => .fail .panic
      | hd :: tl =>
        if i = 0 then .ret hd
        else list_nth tl (i - 1)
    := by
    have Heq := Monotone_fix_fixed_eq (@list_nth_body_is_valid a)
    simp [list_nth]
    conv => lhs; rw [Heq]

end Ex1

namespace Ex2
  /- Same as Ex1, but we make the body of nth non tail-rec (this is mostly
     to see what happens when there are let-bindings) -/
  open Primitives Fix

  variable {a : Type} (k : (List a × Int) → Result a)

  def list_nth_body (x : (List a × Int)) : Result a :=
    let (ls, i) := x
    match ls with
    | [] => .fail .panic
    | hd :: tl =>
      if i = 0 then .ret hd
      else
        do
          let y ← k (tl, i - 1)
          .ret y

  theorem list_nth_body_is_valid: ∀ x, Monotone (λ k => @list_nth_body a k x) := by
    intro x
    simp [list_nth_body]
    split <;> simp
    split <;> simp
    apply Monotone_bind <;> intros <;> simp_all

  def list_nth (ls : List a) (i : Int) : Result a := fix list_nth_body (ls, i)

  -- The unfolding equation - diverges if `i < 0`
  theorem list_nth_eq (ls : List a) (i : Int) :
    (list_nth ls i =
       match ls with
       | [] => .fail .panic
       | hd :: tl =>
         if i = 0 then .ret hd
         else
           do
             let y ← list_nth tl (i - 1)
             .ret y)
    := by
    have Heq := Monotone_fix_fixed_eq (@list_nth_body_is_valid a)
    simp [list_nth]
    conv => lhs; rw [Heq]

end Ex2

namespace Ex3
  /- Mutually recursive functions -/
  open Primitives Fix

  /- Because we have mutually recursive functions, we use a sum for the inputs
     and the output types:
     - inputs: the sum allows to select the function to call in the recursive
       calls (and the functions may not have the same input types)
     - outputs: this case is degenerate because `even` and `odd` have the same
       return type `Bool`, but generally speaking we need a sum type because
       the functions in the mutually recursive group may have different
       return types.
   -/
  variable (k : (Int ⊕ Int) → Result (Bool ⊕ Bool))

  def is_even_is_odd_body (x : (Int ⊕ Int)) : Result (Bool ⊕ Bool) :=
    match x with
    | .inl i =>
      -- Body of `is_even`
      if i = 0
      then .ret (.inl true) -- We use .inl because this is `is_even`
      else
        do
          let b ←
            do
              -- Call `odd`: we need to wrap the input value in `.inr`, then
              -- extract the output value
              let r ← k (.inr (i- 1))
              match r with
              | .inl _ => .fail .panic -- Invalid output
              | .inr b => .ret b
          -- Wrap the return value
          .ret (.inl b)
    | .inr i =>
      -- Body of `is_odd`
      if i = 0
      then .ret (.inr false) -- We use .inr because this is `is_odd`
      else
        do
          let b ←
            do
              -- Call `is_even`: we need to wrap the input value in .inr, then
              -- extract the output value
              let r ← k (.inl (i- 1))
              match r with
              | .inl b => .ret b
              | .inr _ => .fail .panic -- Invalid output
          -- Wrap the return value
          .ret (.inr b)

  theorem is_even_is_odd_body_is_valid:
    ∀ x, Monotone (λ k => is_even_is_odd_body k x) := by
    intro k x
    simp [is_even_is_odd_body]
    split <;> simp <;> split <;> simp
    apply Monotone_bind; simp
    intros; split <;> simp
    apply Monotone_bind; simp
    intros; split <;> simp

  def is_even (i : Int): Result Bool :=
    do
      let r ← fix is_even_is_odd_body (.inl i)
      match r with
      | .inl b => .ret b
      | .inr _ => .fail .panic

  def is_odd (i : Int): Result Bool :=
    do
      let r ← fix is_even_is_odd_body (.inr i)
      match r with
      | .inl _ => .fail .panic
      | .inr b => .ret b

  -- TODO: move
  -- TODO: this is not enough
  theorem swap_if_bind {a b : Type} (e : Prop) [Decidable e]
    (x y : Result a) (f : a → Result b) :
    (do
      let z ← (if e then x else y)
      f z)
     =
    (if e then do let z ← x; f z
     else do let z ← y; f z) := by
    split <;> simp

  -- The unfolding equation for `is_even` - diverges if `i < 0`
  theorem is_even_eq (i : Int) :
    is_even i = (if i = 0 then .ret true else is_odd (i - 1))
    := by
    have Heq := Monotone_fix_fixed_eq is_even_is_odd_body_is_valid
    simp [is_even, is_odd]
    conv => lhs; rw [Heq]; simp; rw [is_even_is_odd_body]; simp
    simp
    -- Very annoying: we need to swap the matches
    -- Doing this with rewriting lemmas is hard generally speaking
    -- (especially as we may have to generate lemmas for user-defined
    -- inductives on the fly).
    -- The simplest is to repeatedly split then simplify (we identify
    -- the outer match or monadic let-binding, and split on its scrutinee)
    split <;> simp
    cases H0 : fix is_even_is_odd_body (Sum.inr (i - 1)) <;> simp
    rename_i v
    split <;> simp

  -- The unfolding equation for `is_odd` - diverges if `i < 0`
  theorem is_odd_eq (i : Int) :
    is_odd i = (if i = 0 then .ret false else is_even (i - 1))
    := by
    have Heq := Monotone_fix_fixed_eq is_even_is_odd_body_is_valid
    simp [is_even, is_odd]
    conv => lhs; rw [Heq]; simp; rw [is_even_is_odd_body]; simp
    -- Same remark as for `even`
    split <;> simp
    cases H0 : fix is_even_is_odd_body (Sum.inl (i - 1)) <;> simp
    rename_i v
    split <;> simp

end Ex3

namespace Ex4
  /- Higher-order example -/
  open Primitives Fix

  variable {a b : Type}

  /- An auxiliary function, which doesn't require the fixed-point -/
  def map (f : a → Result b) (ls : List a) : Result (List b) :=
    match ls with
    | [] => .ret []
    | hd :: tl =>
      do
        let hd ← f hd
        let tl ← map f tl
        .ret (hd :: tl)

  /- The validity theorem for `map`, generic in `f` -/
  theorem map_is_valid
    {{f : (a → Result b) → a → Result c}}
    (Hfvalid : ∀ x, Monotone (λ k => f k x))
    (ls : List a) :
    Monotone (λ k => map (f k) ls) := by
    induction ls <;> simp [map]
    apply Monotone_bind <;> simp_all
    intros
    apply Monotone_bind <;> simp_all

  /- An example which uses map -/
  inductive Tree (a : Type) :=
  | leaf (x : a)
  | node (tl : List (Tree a))

  def id_body (f : Tree a → Result (Tree a)) (t : Tree a) : Result (Tree a) :=
    match t with
    | .leaf x => .ret (.leaf x)
    | .node tl =>
      do
        let tl ← map f tl
        .ret (.node tl)

  theorem id_body_is_valid : ∀ x, Monotone (λ k => @id_body a k x) := by
    intro k x
    simp [id_body]
    split <;> simp
    apply Monotone_bind <;> simp_all
    -- We have to show that `map k tl` is valid
    apply map_is_valid; simp

  def id (t : Tree a) := fix id_body t

  -- The unfolding equation
  theorem id_eq (t : Tree a) :
    (id t =
       match t with
       | .leaf x => .ret (.leaf x)
       | .node tl =>
       do
         let tl ← map id tl
         .ret (.node tl))
    := by
    have Heq := Monotone_fix_fixed_eq (@id_body_is_valid a)
    simp [id]
    conv => lhs; rw [Heq]; simp; rw [id_body]

end Ex4

end Diverge
