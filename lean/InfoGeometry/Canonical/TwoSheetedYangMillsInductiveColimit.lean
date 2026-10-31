/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

open InfoGeometry.OperatorAlgebra.PeirceSpine

set_option maxHeartbeats 5000000

/-!
# Algebraic transport of two-sheet Peirce identities along star-preserving
# ring homomorphisms. These are operator identities; this file proves no physical
# mass gap or reflection-positivity theorem.
#
# The ring identities are non-commutative. The Peirce identities assume only
# P² = P; the star-specialized transport theorem additionally assumes star P = P.
-/

namespace CanonicalTwoSheetedInductiveColimit

variable {B : Type*} [Ring B] [StarRing B]

/-! ## 1. Two-Sheet Peirce Operator Names -/
/-! Forward nilpotent horizon wave `N₊ = P * A * (1 - P)`. -/
def opZig (P A : B) : B := conePlus P A

/-! Backward nilpotent horizon wave `N₋ = (1 - P) * C * P`. -/
def opZag (P C : B) : B := coneMinus P C

/-! The self-adjoint grading expression, without a self-adjointness claim. -/
def opBitGrading (P : B) : B := invS P

/-! Coupled Dirac matter state `E = N₊ + N₋`. -/
def opElectron (P A C : B) : B := genPhi P A C

/-! Axial chiral gauge current `J₅ = N₊ - N₋`. -/
def opAxial (P A C : B) : B := genJ P A C

/-! Quadratic Peirce coupling `V = {N₊, N₋}`. -/
def opQuadraticCoupling (P A C : B) : B := genV P A C

/-! Restored Spin-Dipole Operator `Σ_spin = [N₊, N₋]`. -/
def opSpinDipole (P A C : B) : B := genSig P A C

/-! Grading-star sandwich `X ↦ S_P * star X * S_P`. -/
def opGradingStarSandwich (P X : B) : B :=
  opBitGrading P * star X * opBitGrading P

/-! Negative adjoint-square operator `X ↦ -[E, [E, X]]`. -/
abbrev opNegativeAdjointSquare (P A C X : B) : B :=
  derivSqPhi P A C X

/-! Confluent right-associative idempotent normalizer in any ring `B`. -/
lemma op_P_mul_P_assoc {P : B} (hP : P * P = P) (X : B) :
    P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

section IdempotentIdentities

variable {P : B} (hP : P * P = P)
include hP

/-- The directed Peirce components are square-zero. The multiplication table
itself is owned by `Tetraktys`. -/
theorem directed_components_square_zero (A C : B) :
    opZig P A * opZig P A = 0 ∧ opZag P C * opZag P C = 0 := by
  exact ⟨(archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).1,
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.1⟩

/-- The two-sheet symmetric and signed operators obey their defining square
and ordered-product identities. -/
theorem two_sheet_tetraktys (A C : B) :
    opElectron P A C * opElectron P A C = opQuadraticCoupling P A C ∧
    opAxial P A C * opAxial P A C = -opQuadraticCoupling P A C ∧
    opAxial P A C * opElectron P A C = opSpinDipole P A C := by
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table hP A C with
    ⟨_, _, hPhi, hJ, _, hJPhi, _, _, _, _, _, _, _, _, _⟩
  exact ⟨hPhi, hJ, hJPhi⟩

/-- The grading involution negates the odd components and fixes the quadratic
Peirce coupling. -/
theorem grading_action (A C : B) :
    opBitGrading P * opBitGrading P = 1 ∧
    opBitGrading P * opZig P A * opBitGrading P = -opZig P A ∧
    opBitGrading P * opZag P C * opBitGrading P = -opZag P C ∧
    opBitGrading P * opQuadraticCoupling P A C * opBitGrading P =
      opQuadraticCoupling P A C := by
  rcases archetype_A2_peirce_cartan_grading_and_tangent_closure hP A C with
    ⟨hS, _, _, _, _, _, _⟩
  refine ⟨hS, ?_, ?_, ?_⟩
  · simpa [opBitGrading, opZig] using
      (show invS P * conePlus P A * invS P = -conePlus P A by peirce_nf hP)
  · simpa [opBitGrading, opZag] using
      (show invS P * coneMinus P C * invS P = -coneMinus P C by peirce_nf hP)
  · simpa [opBitGrading, opQuadraticCoupling] using
      (show invS P * genV P A C * invS P = genV P A C by peirce_nf hP)

end IdempotentIdentities

/-! ## 2. Functoriality under Star-Preserving Ring Homomorphisms -/

/-! **Lemma (Functoriality of the Two-Sheet Operators):**
Every unital ring homomorphism `φ` that preserves star commutes strictly
with `opBitGrading`, `opZig`, `opZag`, `opElectron`, `opAxial`, `opQuadraticCoupling`,
`opSpinDipole`, `opGradingStarSandwich`, and `opNegativeAdjointSquare`. -/
theorem starRingHom_intertwines_two_sheeted_tower
    {B₁ B₂ : Type*} [Ring B₁] [StarRing B₁] [Ring B₂] [StarRing B₂]
    (φ : B₁ →+* B₂) (hφStar : ∀ x : B₁, φ (star x) = star (φ x)) (P A C X : B₁) :
    φ (opBitGrading P) = opBitGrading (φ P) ∧
    φ (opZig P A) = opZig (φ P) (φ A) ∧
    φ (opZag P C) = opZag (φ P) (φ C) ∧
    φ (opElectron P A C) = opElectron (φ P) (φ A) (φ C) ∧
    φ (opAxial P A C) = opAxial (φ P) (φ A) (φ C) ∧
    φ (opQuadraticCoupling P A C) = opQuadraticCoupling (φ P) (φ A) (φ C) ∧
    φ (opSpinDipole P A C) = opSpinDipole (φ P) (φ A) (φ C) ∧
    φ (opGradingStarSandwich P X) = opGradingStarSandwich (φ P) (φ X) ∧
    φ (opNegativeAdjointSquare P A C X) = opNegativeAdjointSquare (φ P) (φ A) (φ C) (φ X) := by
  have hBit : φ (opBitGrading P) = opBitGrading (φ P) := by
    unfold opBitGrading invS
    rw [map_sub, map_sub, map_one]
  have hZig : φ (opZig P A) = opZig (φ P) (φ A) := by
    simp [opZig, conePlus, map_mul, map_sub, map_one]
  have hZag : φ (opZag P C) = opZag (φ P) (φ C) := by
    simp [opZag, coneMinus, map_mul, map_sub, map_one]
  have hElec : φ (opElectron P A C) = opElectron (φ P) (φ A) (φ C) := by
    simp [opElectron, opZig, opZag, genPhi, conePlus, coneMinus,
      map_add, map_mul, map_sub, map_one]
  have hAx : φ (opAxial P A C) = opAxial (φ P) (φ A) (φ C) := by
    simp [opAxial, opZig, opZag, genJ, conePlus, coneMinus,
      map_sub, map_mul, map_one]
  have hMass : φ (opQuadraticCoupling P A C) = opQuadraticCoupling (φ P) (φ A) (φ C) := by
    simp [opQuadraticCoupling, genV, anticomm, opZig, opZag, conePlus, coneMinus,
      map_add, map_mul, map_sub, map_one]
  have hSpin : φ (opSpinDipole P A C) = opSpinDipole (φ P) (φ A) (φ C) := by
    simp [opSpinDipole, genSig, InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      opZig, opZag, conePlus, coneMinus, map_sub, map_mul, map_one]
  have hOS : φ (opGradingStarSandwich P X) = opGradingStarSandwich (φ P) (φ X) := by
    unfold opGradingStarSandwich
    rw [map_mul, map_mul, hBit, hφStar]
  have hDiss : φ (opNegativeAdjointSquare P A C X) = opNegativeAdjointSquare (φ P) (φ A) (φ C) (φ X) := by
    have hElec' : φ (genPhi P A C) = genPhi (φ P) (φ A) (φ C) := hElec
    change φ (-comm (genPhi P A C) (comm (genPhi P A C) X)) =
      -comm (genPhi (φ P) (φ A) (φ C)) (comm (genPhi (φ P) (φ A) (φ C)) (φ X))
    simp only [map_neg, InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      map_sub, map_mul, hElec']
  exact ⟨hBit, hZig, hZag, hElec, hAx, hMass, hSpin, hOS, hDiss⟩

/-- Compatibility theorem for the original transport interface. It records the
seven two-sheet formulas and the star-transport law for the base operator. -/
theorem starRingHom_intertwines_two_sheeted_operators
    {B₁ B₂ : Type*} [Ring B₁] [StarRing B₁] [Ring B₂] [StarRing B₂]
    (f : B₁ →+* B₂) (hstar : ∀ x : B₁, f (star x) = star (f x))
    (P A C : B₁) :
    f (opBitGrading P) = opBitGrading (f P) ∧
    f (opZig P A) = opZig (f P) (f A) ∧
    f (opZag P C) = opZag (f P) (f C) ∧
    f (opElectron P A C) = opElectron (f P) (f A) (f C) ∧
    f (opAxial P A C) = opAxial (f P) (f A) (f C) ∧
    f (opQuadraticCoupling P A C) = opQuadraticCoupling (f P) (f A) (f C) ∧
    f (opSpinDipole P A C) = opSpinDipole (f P) (f A) (f C) ∧
    f (star P) = star (f P) := by
  rcases starRingHom_intertwines_two_sheeted_tower f hstar P A C P with
    ⟨hBit, hZig, hZag, hElec, hAx, hMass, hSpin, _, _⟩
  exact ⟨hBit, hZig, hZag, hElec, hAx, hMass, hSpin, hstar P⟩

/-! **Theorem (Transport of two-sheet Peirce identities):**
Let `φ : B₁ →+* B₂` preserve the star operation, and let `P_k : B₁` be a
self-adjoint binary idempotent (`P_k * P_k = P_k`, `star P_k = P_k`) and
`A_k : B₁` be any operator. Let `P_inf = φ P_k` and `A_inf_op = φ A_k`.
Then the stated algebraic identities hold for their images in `B₂`. No
spectral-gap, positivity, or dynamics conclusion is asserted.

1. **Lifted Null Horizon Cones (`∂² = 0`):**
   `opZig P_∞ A_∞ * opZig P_∞ A_∞ = 0` and `opZag P_∞ C_∞ * opZag P_∞ C_∞ = 0`.

2. **Lifted Spontaneous Chiral Symmetry Breaking (Linear Order):**
   `opBitGrading P_∞ * opElectron P_∞ A_∞ C_∞ * opBitGrading P_∞ =
   -opElectron P_∞ A_∞ C_∞` and similarly for `opAxial`.

3. **Lifted Chiral Symmetry Restoration & Spin–Mass Locking (Quadratic Order):**
   `opBitGrading P_∞ * opQuadraticCoupling P_∞ A_∞ C_∞ * opBitGrading P_∞ =
   opQuadraticCoupling P_∞ A_∞ C_∞` and
   `opSpinDipole P_∞ A_∞ C_∞ = opBitGrading P_∞ * opQuadraticCoupling P_∞ A_∞ C_∞`.

4. **Lifted star-duality of the two Peirce cones:**
   `star (opZig P_∞ A_∞) = opZag P_∞ (star A_∞)`.

5. **Lifted adjoint-square eigen-operator identities:**
   `opNegativeAdjointSquare P_∞ A_∞ C_∞ (opQuadraticCoupling P_∞ A_∞ C_∞) = 0`,
   `opNegativeAdjointSquare P_∞ A_∞ C_∞ (opElectron P_∞ A_∞ C_∞) = 0`,
   `opNegativeAdjointSquare P_∞ A_∞ C_∞ (opAxial P_∞ A_∞ C_∞) =
   -((4 : ℤ) • (opQuadraticCoupling P_∞ A_∞ C_∞ * opAxial P_∞ A_∞ C_∞))`,
   `opNegativeAdjointSquare P_∞ A_∞ C_∞ (opSpinDipole P_∞ A_∞ C_∞) =
   -((4 : ℤ) • (opQuadraticCoupling P_∞ A_∞ C_∞ * opSpinDipole P_∞ A_∞ C_∞))`. -/
theorem star_hom_two_sheeted_operator_identities
    {B₁ B₂ : Type*} [Ring B₁] [StarRing B₁] [Ring B₂] [StarRing B₂]
    (φ : B₁ →+* B₂) (hφStar : ∀ x : B₁, φ (star x) = star (φ x))
    (P_k A_k : B₁)
    (hP_k : P_k * P_k = P_k) (hPsym_k : star P_k = P_k) :
    let P_inf := φ P_k
    let A_inf_op := φ A_k
    let C_inf_op := star A_inf_op
    opZig P_inf A_inf_op * opZig P_inf A_inf_op = 0 ∧
    opZag P_inf C_inf_op * opZag P_inf C_inf_op = 0 ∧
    opBitGrading P_inf * opElectron P_inf A_inf_op C_inf_op * opBitGrading P_inf =
      -opElectron P_inf A_inf_op C_inf_op ∧
    opBitGrading P_inf * opAxial P_inf A_inf_op C_inf_op * opBitGrading P_inf =
      -opAxial P_inf A_inf_op C_inf_op ∧
    opBitGrading P_inf * opQuadraticCoupling P_inf A_inf_op C_inf_op * opBitGrading P_inf =
      opQuadraticCoupling P_inf A_inf_op C_inf_op ∧
    opSpinDipole P_inf A_inf_op C_inf_op =
      opBitGrading P_inf * opQuadraticCoupling P_inf A_inf_op C_inf_op ∧
    star (opZig P_inf A_inf_op) = opZag P_inf (star A_inf_op) ∧
    opNegativeAdjointSquare P_inf A_inf_op C_inf_op (opQuadraticCoupling P_inf A_inf_op C_inf_op) = 0 ∧
    opNegativeAdjointSquare P_inf A_inf_op C_inf_op (opElectron P_inf A_inf_op C_inf_op) = 0 ∧
    opNegativeAdjointSquare P_inf A_inf_op C_inf_op (opAxial P_inf A_inf_op C_inf_op) =
      -((4 : ℤ) • (opQuadraticCoupling P_inf A_inf_op C_inf_op * opAxial P_inf A_inf_op C_inf_op)) ∧
    opNegativeAdjointSquare P_inf A_inf_op C_inf_op (opSpinDipole P_inf A_inf_op C_inf_op) =
      -((4 : ℤ) • (opQuadraticCoupling P_inf A_inf_op C_inf_op * opSpinDipole P_inf A_inf_op C_inf_op)) := by
  intro P_inf A_inf_op C_inf_op
  have hP : P_inf * P_inf = P_inf := by
    calc
      P_inf * P_inf = φ P_k * φ P_k := by rfl
      _ = φ (P_k * P_k) := by rw [map_mul]
      _ = φ P_k := by rw [hP_k]
      _ = P_inf := by rfl
  have hPsym : star P_inf = P_inf := by
    calc
      star P_inf = star (φ P_k) := by rfl
      _ = φ (star P_k) := by rw [hφStar P_k]
      _ = φ P_k := by rw [hPsym_k]
      _ = P_inf := by rfl
  have hSpectral := archetype_A5_klein_hadamard_spectra_and_partition
    hP A_inf_op C_inf_op (0 : B₂)
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hP A_inf_op C_inf_op
  rcases hA3 with ⟨hNplus, hNminus, hPhiSq, hJSq, _, hJPhi, _, _, hSpin, _, _, _, _, _, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Null cone N₊² = 0
    exact hNplus
  · -- Null cone N₋² = 0
    exact hNminus
  · -- Chiral breaking S E S = -E
    change invS P_inf * genPhi P_inf A_inf_op C_inf_op * invS P_inf =
      -genPhi P_inf A_inf_op C_inf_op
    peirce_nf hP <;> abel
  · -- Chiral breaking S J₅ S = -J₅
    change invS P_inf * genJ P_inf A_inf_op C_inf_op * invS P_inf =
      -genJ P_inf A_inf_op C_inf_op
    peirce_nf hP <;> abel
  · -- Chiral restoration S M² S = +M²
    change invS P_inf * genV P_inf A_inf_op C_inf_op * invS P_inf =
      genV P_inf A_inf_op C_inf_op
    peirce_nf hP <;> abel
  · -- Spin-mass locking Σ = S M²
    simpa [opSpinDipole, opBitGrading, opQuadraticCoupling] using hSpin
  · -- Star-duality of the two directed cones
    have hZigStar : star (opZig P_inf A_inf_op) = opZag P_inf C_inf_op := by
      simpa [opZig, opZag, C_inf_op] using star_conePlus hPsym A_inf_op
    exact hZigStar
  · -- D_Dirac(M²) = 0
    change derivSqPhi P_inf A_inf_op C_inf_op (genV P_inf A_inf_op C_inf_op) = 0
    exact hSpectral.2.2.1
  · -- D_Dirac(E) = 0
    change derivSqPhi P_inf A_inf_op C_inf_op (genPhi P_inf A_inf_op C_inf_op) = 0
    exact hSpectral.2.1
  · -- D_Dirac(J₅) = -4 M² J₅
    change derivSqPhi P_inf A_inf_op C_inf_op (genJ P_inf A_inf_op C_inf_op) = _
    exact hSpectral.2.2.2.1
  · -- D_Dirac(Σ) = -4 M² Σ
    change derivSqPhi P_inf A_inf_op C_inf_op (genSig P_inf A_inf_op C_inf_op) = _
    exact hSpectral.2.2.2.2.1

end CanonicalTwoSheetedInductiveColimit
