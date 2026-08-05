import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Canonical.CantorCuntzCliffordBridge

/-!
# Cantor Boundary Cuntz Shifts

This module implements the algebraic/cylindrical boundary layer for Cuntz
shifts on the Cantor boundary.

The proof boundary is intentionally narrow:

* the symbolic Cantor carrier is `ℕ → Bool`;
* global left/right Cuntz boundary maps are front-prefix maps;
* finite UHF cylinder compatibility uses the stage-local operation that appends
  the newly created bit at depth `n`, matching `diagEmbedSucc`;
* Cuntz-to-CAR facts are re-exported from the existing abstract `CuntzO2Carrier`
  owner.

No topology, C*-completion, KMS state, phase transition, or zeta-zero theorem is
claimed here.

#### BUCKET 1: CLOSED FINITE THEOREMS
Symbolic branch readbacks for `prefixBit`/`leftShift`/`rightShift`, finite
prefix compatibility, stage-local UHF successor-cylinder compatibility,
boundary/Cuntz branch packet readbacks, CAR consequences inherited from the
existing `CuntzO2Carrier`, and binary orbit recursion readouts.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`BoundaryCuntzShiftPacket` theorem readouts depend only on the explicit packet
fields and the existing `CuntzO2Carrier` premises.

#### BUCKET 3: OPEN CLOSURE DEBT
Full topological Cantor space, C*-completion, Cuntz representation on a Hilbert
space, KMS dynamics, BEC/Hagedorn interpretation, and zeta/RH consequences.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryCuntzShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorCuntzBasis
open InfoGeometry.Topology

/-! ## Symbolic boundary shifts -/

/-- Add a bit to the front of an infinite binary Cantor stream. -/
def prefixBit (b : Bool) (x : CantorBoundary) : CantorBoundary :=
  fun
    | 0 => b
    | n + 1 => x n

/-- The left Cuntz symbolic branch prefixes `false`. -/
def leftShift (x : CantorBoundary) : CantorBoundary :=
  prefixBit false x

/-- The right Cuntz symbolic branch prefixes `true`. -/
def rightShift (x : CantorBoundary) : CantorBoundary :=
  prefixBit true x

@[simp] theorem prefixBit_zero (b : Bool) (x : CantorBoundary) :
    prefixBit b x 0 = b := by
  rfl

@[simp] theorem prefixBit_succ (b : Bool) (x : CantorBoundary) (n : ℕ) :
    prefixBit b x (n + 1) = x n := by
  rfl

@[simp] theorem leftShift_zero (x : CantorBoundary) :
    leftShift x 0 = false := by
  rfl

@[simp] theorem rightShift_zero (x : CantorBoundary) :
    rightShift x 0 = true := by
  rfl

@[simp] theorem leftShift_succ (x : CantorBoundary) (n : ℕ) :
    leftShift x (n + 1) = x n := by
  rfl

@[simp] theorem rightShift_succ (x : CantorBoundary) (n : ℕ) :
    rightShift x (n + 1) = x n := by
  rfl

theorem prefixBit_injective (b : Bool) :
    Function.Injective (prefixBit b) := by
  intro x y hxy
  funext n
  have h := congrFun hxy (n + 1)
  simpa [prefixBit] using h

theorem leftShift_injective :
    Function.Injective leftShift := by
  simpa [leftShift] using prefixBit_injective false

theorem rightShift_injective :
    Function.Injective rightShift := by
  simpa [rightShift] using prefixBit_injective true

theorem leftShift_range_disjoint (x y : CantorBoundary) :
    leftShift x ≠ rightShift y := by
  intro hxy
  have h := congrFun hxy 0
  simpa [leftShift, rightShift, prefixBit] using h

theorem prefixBit_head_tail (x : CantorBoundary) :
    prefixBit (x 0) (fun n => x (n + 1)) = x := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem prefixBit_range_cover (x : CantorBoundary) :
    (∃ y, prefixBit false y = x) ∨
      ∃ y, prefixBit true y = x := by
  cases h : x 0 with
  | false =>
      left
      exact ⟨fun n => x (n + 1), by
        simpa [h] using prefixBit_head_tail x⟩
  | true =>
      right
      exact ⟨fun n => x (n + 1), by
        simpa [h] using prefixBit_head_tail x⟩

theorem prefixBit_nested_succ_succ
    (a b : Bool) (x : CantorBoundary) (n : ℕ) :
    prefixBit a (prefixBit b x) (n + 2) = x n := by
  rfl

theorem prefixBit_nested_prefix
    (a b : Bool) (x : CantorBoundary) :
    prefixBit a (prefixBit b x) 0 = a ∧
      prefixBit a (prefixBit b x) 1 = b := by
  exact ⟨rfl, rfl⟩

/-- Prefixing fixes the first finite prefix bit. -/
theorem boundaryPrefix_prefixBit_zero (n : ℕ) (b : Bool) (x : CantorBoundary) :
    boundaryPrefix (n + 1) (prefixBit b x) ⟨0, Nat.succ_pos n⟩ = b := by
  rfl

/-- The tail of the finite prefix after front-prefixing is the old prefix. -/
theorem boundaryPrefix_prefixBit_succ
    {n : ℕ} (b : Bool) (x : CantorBoundary) (i : Fin n) :
    boundaryPrefix (n + 1) (prefixBit b x) ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ =
      boundaryPrefix n x i := by
  rfl

/-! ## Stage-local branch extension compatible with UHF cylinders -/

/--
Insert the next finite-stage branch bit at depth `n`.

This is not the same as front-prefixing.  It is the operation compatible with
the existing UHF owner, where `diagEmbedSucc` duplicates a stage-`n` observable
over the newly added last bit.
-/
def appendBitAtDepth (n : ℕ) (b : Bool) (x : CantorBoundary) : CantorBoundary :=
  fun k => if k < n then x k else if k = n then b else x k

def appendLeftAtDepth (n : ℕ) (x : CantorBoundary) : CantorBoundary :=
  appendBitAtDepth n false x

def appendRightAtDepth (n : ℕ) (x : CantorBoundary) : CantorBoundary :=
  appendBitAtDepth n true x

@[simp] theorem appendBitAtDepth_of_lt
    {n k : ℕ} (hk : k < n) (b : Bool) (x : CantorBoundary) :
    appendBitAtDepth n b x k = x k := by
  simp [appendBitAtDepth, hk]

@[simp] theorem appendBitAtDepth_self (n : ℕ) (b : Bool) (x : CantorBoundary) :
    appendBitAtDepth n b x n = b := by
  simp [appendBitAtDepth]

@[simp] theorem appendBitAtDepth_of_gt
    {n k : ℕ} (hk : n < k) (b : Bool) (x : CantorBoundary) :
    appendBitAtDepth n b x k = x k := by
  simp [appendBitAtDepth, Nat.not_lt_of_ge (Nat.le_of_lt hk), Nat.ne_of_gt hk]

/--
The first `n+1` bits of the stage-local branch are exactly the finite word
obtained by extending the first `n` bits with the new branch bit.
-/
theorem boundaryPrefix_appendBitAtDepth_succ
    (n : ℕ) (b : Bool) (x : CantorBoundary) :
    boundaryPrefix (n + 1) (appendBitAtDepth n b x) =
      extendSucc n (boundaryPrefix n x) b := by
  ext i
  unfold boundaryPrefix appendBitAtDepth extendSucc
  by_cases hi : i.1 < n
  · simp [hi]
  · have hin : i.1 = n := by omega
    simp [hin]

/--
Stage-local left/right branches are compatible with the diagonal UHF successor
embedding.
-/
theorem cylinder_diagEmbedSucc_appendBitAtDepth
    (n : ℕ) (b : Bool) (f : DiagAlg n) (x : CantorBoundary) :
    cylinder (n + 1) (diagEmbedSucc n f) (appendBitAtDepth n b x) =
      cylinder n f x := by
  unfold cylinder
  rw [boundaryPrefix_appendBitAtDepth_succ, diagEmbedSucc_apply,
    prefixSucc_extendSucc]

theorem cylinder_diagEmbedSucc_appendLeftAtDepth
    (n : ℕ) (f : DiagAlg n) (x : CantorBoundary) :
    cylinder (n + 1) (diagEmbedSucc n f) (appendLeftAtDepth n x) =
      cylinder n f x := by
  exact cylinder_diagEmbedSucc_appendBitAtDepth n false f x

theorem cylinder_diagEmbedSucc_appendRightAtDepth
    (n : ℕ) (f : DiagAlg n) (x : CantorBoundary) :
    cylinder (n + 1) (diagEmbedSucc n f) (appendRightAtDepth n x) =
      cylinder n f x := by
  exact cylinder_diagEmbedSucc_appendBitAtDepth n true f x

/-! ## Boundary maps attached to abstract Cuntz branches -/

namespace BoundaryCuntzShiftPacket

variable {Op : Type*} [Ring Op] [StarRing Op]

variable (P : CuntzO2Carrier Op)

/-- The symbolic boundary maps are definitions, not independent packet data. -/
abbrev leftBoundary : CantorBoundary → CantorBoundary := leftShift

abbrev rightBoundary : CantorBoundary → CantorBoundary := rightShift

/-- The left algebraic Cuntz branch operator. -/
def leftOperator : Op :=
  CuntzO2Carrier.S_left P

/-- The right algebraic Cuntz branch operator. -/
def rightOperator : Op :=
  CuntzO2Carrier.S_right P

theorem leftBoundary_apply (x : CantorBoundary) :
    leftBoundary x = leftShift x := by
  rfl

theorem rightBoundary_apply (x : CantorBoundary) :
    rightBoundary x = rightShift x := by
  rfl

theorem leftOperator_eq_cuntz :
    leftOperator P = CuntzO2Carrier.S_left P := by
  rfl

theorem rightOperator_eq_cuntz :
    rightOperator P = CuntzO2Carrier.S_right P := by
  rfl

/-- The Cuntz-derived CAR generator is nilpotent. -/
theorem car_sq_zero :
    carFromCuntz P * carFromCuntz P = 0 :=
  carFromCuntz_sq_eq_zero P

/-- The Cuntz-derived CAR generator satisfies `{a,a*}=1`. -/
theorem car_anticommutator_star_eq_one :
    cantorAnticommutator (carFromCuntz P) (star (carFromCuntz P)) = 1 :=
  carFromCuntz_anticommutator_star_eq_one P

theorem left_operator_isometry :
    star (CuntzO2Carrier.S_left P) * CuntzO2Carrier.S_left P = 1 :=
  CuntzO2Carrier.left_isometry P

theorem right_operator_isometry :
    star (CuntzO2Carrier.S_right P) * CuntzO2Carrier.S_right P = 1 :=
  CuntzO2Carrier.right_isometry P

theorem left_right_ranges_orthogonal :
    star (CuntzO2Carrier.S_left P) * CuntzO2Carrier.S_right P = 0 :=
  (CuntzO2Carrier.orthogonal_ranges P).1

theorem right_left_ranges_orthogonal :
    star (CuntzO2Carrier.S_right P) * CuntzO2Carrier.S_left P = 0 :=
  (CuntzO2Carrier.orthogonal_ranges P).2

theorem range_projections_sum :
    CuntzO2Carrier.S_left P * star (CuntzO2Carrier.S_left P) +
        CuntzO2Carrier.S_right P * star (CuntzO2Carrier.S_right P) = 1 :=
  CuntzO2Carrier.range_sum P

end BoundaryCuntzShiftPacket

/-! ## Existing Cantor/Cuntz orbit recursion, re-exported in shift language -/

variable {Op : Type*} [Ring Op] [StarRing Op]

theorem orbit_left_branch
    (C : CuntzO2Carrier Op) (seed : Op)
    (w : CantorCuntzBasis.BinaryWord) :
    CantorCuntzBasis.orbit C seed (false :: w) =
      CuntzO2Carrier.S_left C * CantorCuntzBasis.orbit C seed w :=
  CantorCuntzBasis.orbit_cons_false_action C seed w

theorem orbit_right_branch
    (C : CuntzO2Carrier Op) (seed : Op)
    (w : CantorCuntzBasis.BinaryWord) :
    CantorCuntzBasis.orbit C seed (true :: w) =
      CuntzO2Carrier.S_right C * CantorCuntzBasis.orbit C seed w :=
  CantorCuntzBasis.orbit_cons_true_action C seed w

theorem orbit_branch_recursion_readout
    (C : CuntzO2Carrier Op) (seed : Op)
    (b : Bool) (w : CantorCuntzBasis.BinaryWord) :
    CantorCuntzBasis.orbit C seed (b :: w) =
      (if b then CuntzO2Carrier.S_right C else CuntzO2Carrier.S_left C) *
        CantorCuntzBasis.orbit C seed w :=
  CantorCuntzBasis.orbit_branch_recursion C seed b w

end InfoGeometry.Canonical.CantorBoundaryCuntzShift

end noncomputable section
