import Mathlib.Data.ZMod.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1000000

/-!
# Normal Word Collection Algorithm for Polycyclic U₆ ⊂ G₂(2)

Formalizes the normal word collection algorithm transforming any uncollected word
`w : List (Fin 6)` over unipotent generators `e₀, ..., e₅` into canonical,
strictly sorted polycyclic (PC) normal form `e₀^v₀ e₁^v₁ ... e₅^v₅` with `v ∈ 𝔽₂⁶`.

Transition table (CAS-certified against the concrete 8×8 Zorn carrier,
see `scratch/verify_pc_commutator_table.py` and `scratch/true_mulgen_table.json`;
orders of the generators are `(2, 4, 4, 2, 2, 2)` with `e₁² = e₂² = e₅`):

Proves:
  1. Base insertion: `mulGen g zeroExp = basisExp g`, and the order-4 law
     `mulGen g^[4] v = v` for `g ∈ {1, 2}` with the central square correction.
  2. Normal form idempotence: `collectWord (toNormalWord v) = v`.
  3. Canonical sortedness: `IsSortedPC (toNormalWord v)`.
  4. Normalization idempotence: `normalizeWord (normalizeWord w) = normalizeWord w`.
  5. Derived commutator preservation in `[U, U] = span(e₂, e₃, e₄, e₅)`.
-/

namespace InfoGeometry.Algebra.Zorn.G2PCCollection

/-! =========================================================================
    1. PC Coordinate Space, Generators, and Word Datatypes
    ========================================================================= -/

/-- Unipotent generator index `0 ≤ i ≤ 5` corresponding to `e₀, ..., e₅`. -/
abbrev Gen := Fin 6

/-- Arbitrary uncollected word over the unipotent generators. -/
abbrev Word := List Gen

/-- Polycyclic exponent vector `v ∈ 𝔽₂⁶` representing `e₀^v₀ e₁^v₁ ... e₅^v₅`. -/
abbrev PCExp := Fin 6 → ZMod 2

/-- Zero exponent vector representing the group identity `1 ∈ U₆`. -/
def zeroExp : PCExp := fun _ => 0

/-- Standard basis exponent vector for generator `eₖ`. -/
def basisExp (k : Gen) : PCExp :=
  fun i => if i = k then 1 else 0

/-! =========================================================================
    2. Canonical Normal Word Embedding and Sortedness Predicate
    ========================================================================= -/

/--
Transforms an exponent vector `v ∈ 𝔽₂⁶` into its canonical, strictly ascending
word `e₀^{v₀} e₁^{v₁} ... e₅^{v₅}`.
-/
def toNormalWord (v : PCExp) : Word :=
  (if v 0 = 1 then [0] else []) ++
  (if v 1 = 1 then [1] else []) ++
  (if v 2 = 1 then [2] else []) ++
  (if v 3 = 1 then [3] else []) ++
  (if v 4 = 1 then [4] else []) ++
  (if v 5 = 1 then [5] else [])

/--
Strictly sorted predicate: A word is in PC normal form if generator indices
are strictly increasing with no repetitions (as `eᵢ² = 1`).
-/
def IsSortedPC : Word → Prop
  | [] => True
  | [_] => True
  | g₁ :: g₂ :: rest => g₁ < g₂ ∧ IsSortedPC (g₂ :: rest)

instance (w : Word) : Decidable (IsSortedPC w) := by
  induction w with
  | nil => exact isTrue trivial
  | cons g₁ rest =>
    cases rest with
    | nil => exact isTrue trivial
    | cons g₂ tail =>
      dsimp [IsSortedPC]
      infer_instance

/-! =========================================================================
    3. The Left-Multiplication Collection Step (mulGen)
    ========================================================================= -/

/--
Left-multiplication action `mulGen(g, v) = e_g * (e₀^{v₀} ... e₅^{v₅})`
derived by commuting `e_g` through lower generators via the CAS-certified
G₂(2) PC relations (see `scratch/verify_pc_commutator_table.py`):
  - `[e₀, e₁] = e₂ e₃ e₅`
  - `[e₀, e₂] = e₅`
  - `[e₀, e₄] = e₃`
  - `[e₁, e₃] = e₅`
  - `[e₁, e₄] = e₅`
  - `[e₂, e₄] = e₅`
-/
def mulGen (g : Gen) (v : PCExp) : PCExp :=
  match g with
  | 0 => fun k => match k with
    | 0 => v 0 + 1
    | _ => v k
  | 1 => fun k => match k with
    | 0 => v 0
    | 1 => v 1 + 1
    | 2 => v 0 + v 2
    | 3 => v 0 + v 3
    | 4 => v 4
    | 5 => v 1 + v 5 + v 0 * v 1 + v 0 * v 2
  | 2 => fun k => match k with
    | 0 => v 0
    | 1 => v 1
    | 2 => v 2 + 1
    | _ => if k = 5 then v 0 + v 2 + v 5 else v k
  | 3 => fun k => match k with
    | 0 => v 0
    | 1 => v 1
    | 2 => v 2
    | 3 => v 3 + 1
    | _ => if k = 5 then v 1 + v 5 else v k
  | 4 => fun k => match k with
    | 0 => v 0
    | 1 => v 1
    | 2 => v 2
    | 3 => v 0 + v 3
    | 4 => v 4 + 1
    | 5 => v 1 + v 2 + v 5 + v 0 * v 1
  | 5 => fun k => match k with
    | 5 => v 5 + 1
    | _ => v k

/-- In `ZMod 2`, every element is its own additive inverse. -/
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

/-- Insertion at the identity: left-multiplying by `e_g` on the identity
produces exactly the standard basis exponent vector. -/
theorem mulGen_zero_left (g : Gen) :
    mulGen g zeroExp = basisExp g := by
  funext k
  fin_cases g <;> fin_cases k <;> rfl

/-- The generator `e₁` has order 4: four-fold left multiplication is the
identity transformation on every coordinate. -/
theorem mulGen_1_iterate_four (v : PCExp) :
    mulGen 1 (mulGen 1 (mulGen 1 (mulGen 1 v))) = v := by
  funext k
  have hval : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hval (v 0) with h0 | h0 <;> rcases hval (v 1) with h1 | h1 <;>
    rcases hval (v 2) with h2 | h2 <;> rcases hval (v 3) with h3 | h3 <;>
    rcases hval (v 4) with h4 | h4 <;> rcases hval (v 5) with h5 | h5 <;>
    fin_cases k <;>
      simp [mulGen, h0, h1, h2, h3, h4, h5, zmod2_add_self]

/-- The generator `e₂` has order 4: four-fold left multiplication is the
identity transformation on every coordinate. -/
theorem mulGen_2_iterate_four (v : PCExp) :
    mulGen 2 (mulGen 2 (mulGen 2 (mulGen 2 v))) = v := by
  funext k
  have hval : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hval (v 0) with h0 | h0 <;> rcases hval (v 1) with h1 | h1 <;>
    rcases hval (v 2) with h2 | h2 <;> rcases hval (v 3) with h3 | h3 <;>
    rcases hval (v 4) with h4 | h4 <;> rcases hval (v 5) with h5 | h5 <;>
    fin_cases k <;>
      simp [mulGen, h0, h1, h2, h3, h4, h5, zmod2_add_self]

set_option maxHeartbeats 1000000 in
/-- The central square law for `e₁`: squaring through `e₁` flips the maximal
root generator `e₅` and fixes all other coordinates. -/
theorem mulGen_1_square_center (v : PCExp) :
    ∀ k, mulGen 1 (mulGen 1 v) k = if k = 5 then v 5 + 1 else v k := by
  intro k
  have hval : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hval (v 0) with h0 | h0 <;> rcases hval (v 1) with h1 | h1 <;>
    rcases hval (v 2) with h2 | h2 <;> rcases hval (v 3) with h3 | h3 <;>
    rcases hval (v 4) with h4 | h4 <;> rcases hval (v 5) with h5 | h5 <;>
    fin_cases k <;> simp [mulGen, h0, h1, h2, h3, h4, h5] <;> rfl

/-! =========================================================================
    4. Normal Word Collection Algorithm
    ========================================================================= -/

/--
The complete Polycyclic Collection Algorithm:
Folds left-multiplication `mulGen` from the right across any arbitrary word `w`.
-/
def collectWord (w : Word) : PCExp :=
  w.foldr mulGen zeroExp

/--
Full Normalization Pipeline:
Transforms an arbitrary uncollected word `w` into its canonical normal word.
-/
def normalizeWord (w : Word) : Word :=
  toNormalWord (collectWord w)

/-! =========================================================================
    5. Correctness, Idempotence, and Structural Theorems
    ========================================================================= -/

/-- Empty word evaluates to the identity exponent vector `zeroExp`. -/
theorem collectWord_nil : collectWord [] = zeroExp := rfl

/-- Word concatenation is a homomorphism of the collection action. -/
theorem collectWord_append (w₁ w₂ : Word) :
    collectWord (w₁ ++ w₂) = w₁.foldr mulGen (collectWord w₂) := by
  dsimp [collectWord]
  rw [List.foldr_append]

/--
THEOREM (Single Generator Word Collection):
Collecting a single letter `[g]` yields the standard basis vector `basisExp g`.
-/
theorem collectWord_singleton (g : Gen) :
    collectWord [g] = basisExp g := by
  funext k
  fin_cases g <;> fin_cases k <;> rfl

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

/--
MAIN THEOREM (Normal Form Idempotence):
Collecting an already normalized word `toNormalWord v` reproduces the exact
exponent vector `v`.
-/
theorem collectWord_toNormalWord (v : PCExp) :
    collectWord (toNormalWord v) = v := by
  have hv_eval (i : Fin 6) : v i = match i with
    | 0 => v 0 | 1 => v 1 | 2 => v 2 | 3 => v 3 | 4 => v 4 | 5 => v 5 := by
    fin_cases i <;> rfl
  rcases zmod2_cases (v 0) with r0 | r0 <;>
  rcases zmod2_cases (v 1) with r1 | r1 <;>
  rcases zmod2_cases (v 2) with r2 | r2 <;>
  rcases zmod2_cases (v 3) with r3 | r3 <;>
  rcases zmod2_cases (v 4) with r4 | r4 <;>
  rcases zmod2_cases (v 5) with r5 | r5 <;> {
    funext k
    dsimp [toNormalWord]
    rw [r0, r1, r2, r3, r4, r5]
    dsimp [collectWord, mulGen, zeroExp]
    rw [hv_eval k]
    rw [r0, r1, r2, r3, r4, r5]
    revert k
    decide
  }

/--
MAIN THEOREM (Sortedness of Normal Words):
Every canonical word produced by `toNormalWord v` is strictly sorted.
-/
theorem isSorted_toNormalWord (v : PCExp) :
    IsSortedPC (toNormalWord v) := by
  rcases zmod2_cases (v 0) with r0 | r0 <;>
  rcases zmod2_cases (v 1) with r1 | r1 <;>
  rcases zmod2_cases (v 2) with r2 | r2 <;>
  rcases zmod2_cases (v 3) with r3 | r3 <;>
  rcases zmod2_cases (v 4) with r4 | r4 <;>
  rcases zmod2_cases (v 5) with r5 | r5 <;> {
    dsimp [toNormalWord]
    rw [r0, r1, r2, r3, r4, r5]
    decide
  }

/--
COROLLARY (Full Normalization Idempotence):
  `normalizeWord (normalizeWord w) = normalizeWord w`
-/
theorem normalizeWord_idempotent (w : Word) :
    normalizeWord (normalizeWord w) = normalizeWord w := by
  dsimp [normalizeWord]
  rw [collectWord_toNormalWord]

/--
THEOREM (Derived Commutator Subgroup Preservation):
Collecting any commutator word `[eᵢ, eⱼ, eᵢ, eⱼ]` vanishes on simple root
components `v₀` and `v₁`, remaining strictly within `[U, U] ⊆ span(e₂, e₃, e₄, e₅)`.
-/
theorem collectWord_commutator_derived (i j : Gen) :
    (collectWord [i, j, i, j]) 0 = 0 ∧ (collectWord [i, j, i, j]) 1 = 0 := by
  fin_cases i <;> fin_cases j <;> decide

end InfoGeometry.Algebra.Zorn.G2PCCollection
