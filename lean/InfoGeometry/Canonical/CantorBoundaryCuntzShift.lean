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

/--
Proof-carrying boundary/Cuntz branch packet.

The symbolic branch maps are front-prefix maps.  The algebraic branch operators
are the existing abstract Cuntz `O₂` operators.
-/
abbrev BoundaryCuntzShiftPacket
    (Op : Type*) [Ring Op] [StarRing Op] := CuntzO2Carrier Op

namespace BoundaryCuntzShiftPacket

variable {Op : Type*} [Ring Op] [StarRing Op]

abbrev cuntz (P : BoundaryCuntzShiftPacket Op) : CuntzO2Carrier Op := P

variable (P : BoundaryCuntzShiftPacket Op)

/-- The symbolic boundary maps are definitions, not independent packet data. -/
def leftBoundary : CantorBoundary → CantorBoundary := leftShift

def rightBoundary : CantorBoundary → CantorBoundary := rightShift

/-- The left algebraic Cuntz branch operator. -/
def leftOperator : Op :=
  P.cuntz.S_left

/-- The right algebraic Cuntz branch operator. -/
def rightOperator : Op :=
  P.cuntz.S_right

theorem leftBoundary_apply (x : CantorBoundary) :
    leftBoundary x = leftShift x := by
  rfl

theorem rightBoundary_apply (x : CantorBoundary) :
    rightBoundary x = rightShift x := by
  rfl

theorem leftOperator_eq_cuntz :
    P.leftOperator = P.cuntz.S_left := by
  rfl

theorem rightOperator_eq_cuntz :
    P.rightOperator = P.cuntz.S_right := by
  rfl

/-- The Cuntz-derived CAR generator is nilpotent. -/
theorem car_sq_zero :
    carFromCuntz P.cuntz * carFromCuntz P.cuntz = 0 :=
  carFromCuntz_sq_eq_zero P.cuntz

/-- The Cuntz-derived CAR generator satisfies `{a,a*}=1`. -/
theorem car_anticommutator_star_eq_one :
    cantorAnticommutator (carFromCuntz P.cuntz) (star (carFromCuntz P.cuntz)) = 1 :=
  carFromCuntz_anticommutator_star_eq_one P.cuntz

end BoundaryCuntzShiftPacket

/-! ## Existing Cantor/Cuntz orbit recursion, re-exported in shift language -/

variable {Op : Type*} [Ring Op] [StarRing Op]

theorem orbit_left_branch
    (B : CantorCuntzBasis.CantorCuntzBasisPacket Op)
    (w : CantorCuntzBasis.BinaryWord) :
    CantorCuntzBasis.CantorCuntzBasisPacket.orbit B (false :: w) =
      B.cuntz.S_left * CantorCuntzBasis.CantorCuntzBasisPacket.orbit B w :=
  CantorCuntzBasis.CantorCuntzBasisPacket.orbit_cons_false_action B w

theorem orbit_right_branch
    (B : CantorCuntzBasis.CantorCuntzBasisPacket Op)
    (w : CantorCuntzBasis.BinaryWord) :
    CantorCuntzBasis.CantorCuntzBasisPacket.orbit B (true :: w) =
      B.cuntz.S_right * CantorCuntzBasis.CantorCuntzBasisPacket.orbit B w :=
  CantorCuntzBasis.CantorCuntzBasisPacket.orbit_cons_true_action B w

theorem orbit_branch_recursion_readout
    (B : CantorCuntzBasis.CantorCuntzBasisPacket Op)
    (b : Bool) (w : CantorCuntzBasis.BinaryWord) :
    CantorCuntzBasis.CantorCuntzBasisPacket.orbit B (b :: w) =
      (if b then B.cuntz.S_right else B.cuntz.S_left) *
        CantorCuntzBasis.CantorCuntzBasisPacket.orbit B w :=
  CantorCuntzBasis.CantorCuntzBasisPacket.orbit_branch_recursion B b w

end InfoGeometry.Canonical.CantorBoundaryCuntzShift

end noncomputable section
