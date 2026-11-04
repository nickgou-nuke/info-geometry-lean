/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Pi
import Mathlib.Algebra.Star.Prod
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

/-- An injective star-preserving ring map cannot collapse a nonzero two-sheet
quadratic coupling. This is the algebraic nonvanishing statement needed when
transporting a nonzero finite-stage support to a later injective stage; it
does not assert a uniform numerical spectral lower bound. -/
theorem starRingHom_preserves_nonzero_two_sheet_coupling
    {B₁ B₂ : Type*} [Ring B₁] [StarRing B₁] [Ring B₂] [StarRing B₂]
    (φ : B₁ →+* B₂) (hφ_inj : Function.Injective φ)
    (hφStar : ∀ x : B₁, φ (star x) = star (φ x)) (P A C : B₁)
    (hMass : opQuadraticCoupling P A C ≠ 0) :
    opQuadraticCoupling (φ P) (φ A) (φ C) ≠ 0 := by
  intro hImage
  rcases starRingHom_intertwines_two_sheeted_tower φ hφStar P A C A with
    ⟨_, _, _, _, _, hTransport, _, _, _⟩
  apply hMass
  apply hφ_inj
  calc
    φ (opQuadraticCoupling P A C) =
        opQuadraticCoupling (φ P) (φ A) (φ C) := hTransport
    _ = 0 := hImage
    _ = φ 0 := by rw [map_zero]

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

/-! ## 3. Directed Inductive System of Star-Rings & Multi-Channel Orthogonality (`LIII → LIV`) -/

/-- Right-associative zero-product normalizer for confluent monomial elimination. -/
lemma zero_mul_assoc {X Y : B} (h : X * Y = 0) (Z : B) :
    X * (Y * Z) = 0 := by
  rw [← mul_assoc, h, zero_mul]

/-- Any two forward Peirce corners over the same idempotent `P` mutually annihilate. -/
lemma opZig_mul_opZig {P : B} (hP : P * P = P) (A₁ A₂ : B) :
    opZig P A₁ * opZig P A₂ = 0 :=
  conePlus_mul_conePlus hP A₁ A₂

/-- Right-associated mutual annihilation of any two forward Peirce corners over `P`. -/
lemma opZig_mul_opZig_assoc {P : B} (hP : P * P = P) (A₁ A₂ X : B) :
    opZig P A₁ * (opZig P A₂ * X) = 0 :=
  zero_mul_assoc (opZig_mul_opZig hP A₁ A₂) X

/-- Any two backward Peirce corners over the same idempotent `P` mutually annihilate. -/
lemma opZag_mul_opZag {P : B} (hP : P * P = P) (C₁ C₂ : B) :
    opZag P C₁ * opZag P C₂ = 0 :=
  coneMinus_mul_coneMinus hP C₁ C₂

/-- Right-associated mutual annihilation of any two backward Peirce corners over `P`. -/
lemma opZag_mul_opZag_assoc {P : B} (hP : P * P = P) (C₁ C₂ X : B) :
    opZag P C₁ * (opZag P C₂ * X) = 0 :=
  zero_mul_assoc (opZag_mul_opZag hP C₁ C₂) X

/-- A unital star-ring homomorphism `φ : B₁ →⋆+* B₂` between non-commutative operator rings. -/
structure StarRingHom (B₁ B₂ : Type*) [Ring B₁] [StarRing B₁] [Ring B₂] [StarRing B₂]
    extends B₁ →+* B₂ where
  map_star' : ∀ x : B₁, toRingHom (star x) = star (toRingHom x)

/-- Identity `StarRingHom` on any star-ring `B₁`. -/
def StarRingHom.id (B₁ : Type*) [Ring B₁] [StarRing B₁] : StarRingHom B₁ B₁ where
  toRingHom := RingHom.id B₁
  map_star' _ := rfl

/-- Composition of two `StarRingHom` morphisms. -/
def StarRingHom.comp {B₁ B₂ B₃ : Type*}
    [Ring B₁] [StarRing B₁] [Ring B₂] [StarRing B₂] [Ring B₃] [StarRing B₃]
    (ψ : StarRingHom B₂ B₃) (φ : StarRingHom B₁ B₂) : StarRingHom B₁ B₃ where
  toRingHom := ψ.toRingHom.comp φ.toRingHom
  map_star' x := by
    change ψ.toRingHom (φ.toRingHom (star x)) = star (ψ.toRingHom (φ.toRingHom x))
    rw [φ.map_star', ψ.map_star']

/-- An inductive directed tower of star-rings `A : ℕ → Type*` equipped with a colimit
cone into a target operator star-ring `A_inf`. -/
structure InductiveStarColimitCone (A : ℕ → Type*) [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    (A_inf : Type*) [Ring A_inf] [StarRing A_inf] where
  stepHom : ∀ k, StarRingHom (A k) (A (k + 1))
  toColimit : ∀ k, StarRingHom (A k) A_inf
  compat : ∀ k (x : A k),
    (toColimit (k + 1)).toRingHom ((stepHom k).toRingHom x) = (toColimit k).toRingHom x

/-- Multi-step transition homomorphism `A k →⋆+* A (k + m)` across `m` steps of the directed tower. -/
def stepHomIter {A : ℕ → Type*} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf) (k : ℕ) :
    ∀ m : ℕ, StarRingHom (A k) (A (k + m))
  | 0 => StarRingHom.id (A k)
  | m + 1 => (Cone.stepHom (k + m)).comp (stepHomIter Cone k m)

/-- A composite transition in an injective tower is injective. The abstract
cone itself does not assume injectivity, so it is supplied as a hypothesis. -/
theorem stepHomIter_injective
    {A : ℕ → Type*} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (hstep : ∀ j, Function.Injective (Cone.stepHom j).toRingHom)
    (k m : ℕ) :
    Function.Injective (stepHomIter Cone k m).toRingHom := by
  induction m with
  | zero =>
      intro x y h
      exact h
  | succ m ih =>
      change Function.Injective
        ((Cone.stepHom (k + m)).toRingHom.comp (stepHomIter Cone k m).toRingHom)
      exact (hstep (k + m)).comp ih

/-- Injective star-preserving transitions preserve nonvanishing of the
two-sheet quadratic coupling at every finite later stage. This is an
algebraic nonzero statement, not a uniform numerical gap estimate. -/
theorem stepHomIter_preserves_nonzero_two_sheet_coupling
    {A : ℕ → Type*} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (hstep : ∀ j, Function.Injective (Cone.stepHom j).toRingHom)
    (k m : ℕ) (P Aop C : A k)
    (hMass : opQuadraticCoupling P Aop C ≠ 0) :
    opQuadraticCoupling
      ((stepHomIter Cone k m).toRingHom P)
      ((stepHomIter Cone k m).toRingHom Aop)
      ((stepHomIter Cone k m).toRingHom C) ≠ 0 := by
  exact starRingHom_preserves_nonzero_two_sheet_coupling
    (stepHomIter Cone k m).toRingHom
    (stepHomIter_injective Cone hstep k m)
    (stepHomIter Cone k m).map_star' P Aop C hMass

/-- **Theorem `LIII.1` (`colimit_renormalization_scale_invariance`):**
Multi-step colimit cocycle invariance (`k → k + m → ∞`) of `opQuadraticCoupling`, `opSpinDipole`,
`opGradingStarSandwich`, and `opNegativeAdjointSquare`. -/
theorem colimit_renormalization_scale_invariance
    {A : ℕ → Type*} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf) (k m : ℕ) (P_k A_k C_k X_k : A k) :
    let ψ_m := (stepHomIter Cone k m).toRingHom
    let ι_km := (Cone.toColimit (k + m)).toRingHom
    let ι_k := (Cone.toColimit k).toRingHom
    (∀ x : A k, ι_km (ψ_m x) = ι_k x) ∧
    ι_km (opQuadraticCoupling (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) =
      opQuadraticCoupling (ι_k P_k) (ι_k A_k) (ι_k C_k) ∧
    ι_km (opSpinDipole (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) =
      opSpinDipole (ι_k P_k) (ι_k A_k) (ι_k C_k) ∧
    ι_km (opGradingStarSandwich (ψ_m P_k) (ψ_m X_k)) =
      opGradingStarSandwich (ι_k P_k) (ι_k X_k) ∧
    ι_km (opNegativeAdjointSquare (ψ_m P_k) (ψ_m A_k) (ψ_m C_k) (ψ_m X_k)) =
      opNegativeAdjointSquare (ι_k P_k) (ι_k A_k) (ι_k C_k) (ι_k X_k) := by
  intro ψ_m ι_km ι_k
  have hCocycle : ∀ m' : ℕ, ∀ x : A k,
      (Cone.toColimit (k + m')).toRingHom ((stepHomIter Cone k m').toRingHom x) =
      (Cone.toColimit k).toRingHom x := by
    intro m'
    induction m' with
    | zero => intro x; rfl
    | succ m' ih =>
      intro x
      change (Cone.toColimit (k + m' + 1)).toRingHom
        ((Cone.stepHom (k + m')).toRingHom ((stepHomIter Cone k m').toRingHom x)) =
        (Cone.toColimit k).toRingHom x
      rw [Cone.compat (k + m') ((stepHomIter Cone k m').toRingHom x)]
      exact ih x
  rcases starRingHom_intertwines_two_sheeted_tower
      (stepHomIter Cone k m).toRingHom (stepHomIter Cone k m).map_star' P_k A_k C_k X_k with
    ⟨_, _, _, _, _, hMass_m, hSpin_m, hOS_m, hDiss_m⟩
  rcases starRingHom_intertwines_two_sheeted_tower
      (Cone.toColimit k).toRingHom (Cone.toColimit k).map_star' P_k A_k C_k X_k with
    ⟨_, _, _, _, _, hMass_k, hSpin_k, hOS_k, hDiss_k⟩
  refine ⟨hCocycle m, ?_, ?_, ?_, ?_⟩
  · calc ι_km (opQuadraticCoupling (ψ_m P_k) (ψ_m A_k) (ψ_m C_k))
      _ = ι_km (ψ_m (opQuadraticCoupling P_k A_k C_k)) := congr_arg ι_km hMass_m.symm
      _ = ι_k (opQuadraticCoupling P_k A_k C_k) := hCocycle m _
      _ = opQuadraticCoupling (ι_k P_k) (ι_k A_k) (ι_k C_k) := hMass_k
  · calc ι_km (opSpinDipole (ψ_m P_k) (ψ_m A_k) (ψ_m C_k))
      _ = ι_km (ψ_m (opSpinDipole P_k A_k C_k)) := congr_arg ι_km hSpin_m.symm
      _ = ι_k (opSpinDipole P_k A_k C_k) := hCocycle m _
      _ = opSpinDipole (ι_k P_k) (ι_k A_k) (ι_k C_k) := hSpin_k
  · calc ι_km (opGradingStarSandwich (ψ_m P_k) (ψ_m X_k))
      _ = ι_km (ψ_m (opGradingStarSandwich P_k X_k)) := congr_arg ι_km hOS_m.symm
      _ = ι_k (opGradingStarSandwich P_k X_k) := hCocycle m _
      _ = opGradingStarSandwich (ι_k P_k) (ι_k X_k) := hOS_k
  · calc ι_km (opNegativeAdjointSquare (ψ_m P_k) (ψ_m A_k) (ψ_m C_k) (ψ_m X_k))
      _ = ι_km (ψ_m (opNegativeAdjointSquare P_k A_k C_k X_k)) := congr_arg ι_km hDiss_m.symm
      _ = ι_k (opNegativeAdjointSquare P_k A_k C_k X_k) := hCocycle m _
      _ = opNegativeAdjointSquare (ι_k P_k) (ι_k A_k) (ι_k C_k) (ι_k X_k) := hDiss_k

/-- **Theorem `LIII.2` (`multi_channel_orthogonal_mass_gap_additivity`):**
Multi-channel orthogonal additivity of `opElectron`, `opAxial`, `opQuadraticCoupling`, and `opSpinDipole`. -/
theorem multi_channel_orthogonal_mass_gap_additivity
    (P A₁ C₁ A₂ C₂ : B)
    (h12 : opZig P A₁ * opZag P C₂ = 0)
    (h21 : opZig P A₂ * opZag P C₁ = 0)
    (h12' : opZag P C₁ * opZig P A₂ = 0)
    (h21' : opZag P C₂ * opZig P A₁ = 0) :
    opElectron P (A₁ + A₂) (C₁ + C₂) = opElectron P A₁ C₁ + opElectron P A₂ C₂ ∧
    opAxial P (A₁ + A₂) (C₁ + C₂) = opAxial P A₁ C₁ + opAxial P A₂ C₂ ∧
    opQuadraticCoupling P (A₁ + A₂) (C₁ + C₂) =
      opQuadraticCoupling P A₁ C₁ + opQuadraticCoupling P A₂ C₂ ∧
    opSpinDipole P (A₁ + A₂) (C₁ + C₂) = opSpinDipole P A₁ C₁ + opSpinDipole P A₂ C₂ := by
  have hZigAdd : opZig P (A₁ + A₂) = opZig P A₁ + opZig P A₂ := by
    unfold opZig conePlus; simp only [mul_add, add_mul]
  have hZagAdd : opZag P (C₁ + C₂) = opZag P C₁ + opZag P C₂ := by
    unfold opZag coneMinus; simp only [mul_add, add_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change opZig P (A₁ + A₂) + opZag P (C₁ + C₂) =
      (opZig P A₁ + opZag P C₁) + (opZig P A₂ + opZag P C₂)
    rw [hZigAdd, hZagAdd]; abel
  · change opZig P (A₁ + A₂) - opZag P (C₁ + C₂) =
      (opZig P A₁ - opZag P C₁) + (opZig P A₂ - opZag P C₂)
    rw [hZigAdd, hZagAdd]; abel
  · change anticomm (opZig P (A₁ + A₂)) (opZag P (C₁ + C₂)) =
      anticomm (opZig P A₁) (opZag P C₁) + anticomm (opZig P A₂) (opZag P C₂)
    unfold anticomm; rw [hZigAdd, hZagAdd]
    simp only [add_mul, mul_add, h12, h21, h12', h21']; abel
  · change comm (opZig P (A₁ + A₂)) (opZag P (C₁ + C₂)) =
      comm (opZig P A₁) (opZag P C₁) + comm (opZig P A₂) (opZag P C₂)
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm; rw [hZigAdd, hZagAdd]
    simp only [add_mul, mul_add, h12, h21, h12', h21']; abel

/-- **Theorem `LIV.1` (`multi_channel_orthogonal_dissipator_and_spectral_gap_decoupling`):**
Multi-channel orthogonal annihilation and double-commutator decoupling across channels. -/
theorem multi_channel_orthogonal_dissipator_and_spectral_gap_decoupling
    {P : B} (hP : P * P = P) (A₁ C₁ A₂ C₂ : B)
    (h12 : opZig P A₁ * opZag P C₂ = 0)
    (h21 : opZig P A₂ * opZag P C₁ = 0)
    (h12' : opZag P C₁ * opZig P A₂ = 0)
    (h21' : opZag P C₂ * opZig P A₁ = 0) :
    opQuadraticCoupling P A₁ C₁ * opQuadraticCoupling P A₂ C₂ = 0 ∧
    opQuadraticCoupling P A₂ C₂ * opQuadraticCoupling P A₁ C₁ = 0 ∧
    opSpinDipole P A₁ C₁ * opSpinDipole P A₂ C₂ = 0 ∧
    opSpinDipole P A₂ C₂ * opSpinDipole P A₁ C₁ = 0 ∧
    opNegativeAdjointSquare P (A₁ + A₂) (C₁ + C₂) (opAxial P (A₁ + A₂) (C₁ + C₂)) =
      opNegativeAdjointSquare P A₁ C₁ (opAxial P A₁ C₁) +
      opNegativeAdjointSquare P A₂ C₂ (opAxial P A₂ C₂) ∧
    opNegativeAdjointSquare P (A₁ + A₂) (C₁ + C₂) (opSpinDipole P (A₁ + A₂) (C₁ + C₂)) =
      opNegativeAdjointSquare P A₁ C₁ (opSpinDipole P A₁ C₁) +
      opNegativeAdjointSquare P A₂ C₂ (opSpinDipole P A₂ C₂) := by
  have hZigAdd : opZig P (A₁ + A₂) = opZig P A₁ + opZig P A₂ := by
    unfold opZig conePlus; simp only [mul_add, add_mul]
  have hZagAdd : opZag P (C₁ + C₂) = opZag P C₁ + opZag P C₂ := by
    unfold opZag coneMinus; simp only [mul_add, add_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (opZig P A₁ * opZag P C₁ + opZag P C₁ * opZig P A₁) *
      (opZig P A₂ * opZag P C₂ + opZag P C₂ * opZig P A₂) = 0
    simp only [add_mul, mul_add, mul_assoc, opZig_mul_opZig_assoc hP,
               opZag_mul_opZag_assoc hP, h12, h21, h12', h21',
               zero_mul_assoc h12, zero_mul_assoc h21, zero_mul_assoc h12', zero_mul_assoc h21',
               mul_zero, zero_mul]; abel
  · change (opZig P A₂ * opZag P C₂ + opZag P C₂ * opZig P A₂) *
      (opZig P A₁ * opZag P C₁ + opZag P C₁ * opZig P A₁) = 0
    simp only [add_mul, mul_add, mul_assoc, opZig_mul_opZig_assoc hP,
               opZag_mul_opZag_assoc hP, h12, h21, h12', h21',
               zero_mul_assoc h12, zero_mul_assoc h21, zero_mul_assoc h12', zero_mul_assoc h21',
               mul_zero, zero_mul]; abel
  · change (opZig P A₁ * opZag P C₁ - opZag P C₁ * opZig P A₁) *
      (opZig P A₂ * opZag P C₂ - opZag P C₂ * opZig P A₂) = 0
    simp only [sub_mul, mul_sub, mul_assoc, opZig_mul_opZig_assoc hP,
               opZag_mul_opZag_assoc hP, h12, h21, h12', h21',
               zero_mul_assoc h12, zero_mul_assoc h21, zero_mul_assoc h12', zero_mul_assoc h21',
               mul_zero, zero_mul]; abel
  · change (opZig P A₂ * opZag P C₂ - opZag P C₂ * opZig P A₂) *
      (opZig P A₁ * opZag P C₁ - opZag P C₁ * opZig P A₁) = 0
    simp only [sub_mul, mul_sub, mul_assoc, opZig_mul_opZig_assoc hP,
               opZag_mul_opZag_assoc hP, h12, h21, h12', h21',
               zero_mul_assoc h12, zero_mul_assoc h21, zero_mul_assoc h12', zero_mul_assoc h21',
               mul_zero, zero_mul]; abel
  · change -comm (opZig P (A₁ + A₂) + opZag P (C₁ + C₂))
        (comm (opZig P (A₁ + A₂) + opZag P (C₁ + C₂)) (opZig P (A₁ + A₂) - opZag P (C₁ + C₂))) =
      -comm (opZig P A₁ + opZag P C₁) (comm (opZig P A₁ + opZag P C₁) (opZig P A₁ - opZag P C₁)) +
      -comm (opZig P A₂ + opZag P C₂) (comm (opZig P A₂ + opZag P C₂) (opZig P A₂ - opZag P C₂))
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm; rw [hZigAdd, hZagAdd]
    simp only [sub_mul, mul_sub, add_mul, mul_add, mul_assoc,
               opZig_mul_opZig hP, opZig_mul_opZig_assoc hP,
               opZag_mul_opZag hP, opZag_mul_opZag_assoc hP, h12, h21, h12', h21',
               zero_mul_assoc h12, zero_mul_assoc h21, zero_mul_assoc h12', zero_mul_assoc h21',
               mul_zero, zero_mul]; abel
  · change -comm (opZig P (A₁ + A₂) + opZag P (C₁ + C₂))
        (comm (opZig P (A₁ + A₂) + opZag P (C₁ + C₂))
          (opZig P (A₁ + A₂) * opZag P (C₁ + C₂) - opZag P (C₁ + C₂) * opZig P (A₁ + A₂))) =
      -comm (opZig P A₁ + opZag P C₁)
        (comm (opZig P A₁ + opZag P C₁) (opZig P A₁ * opZag P C₁ - opZag P C₁ * opZig P A₁)) +
      -comm (opZig P A₂ + opZag P C₂)
        (comm (opZig P A₂ + opZag P C₂) (opZig P A₂ * opZag P C₂ - opZag P C₂ * opZig P A₂))
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm; rw [hZigAdd, hZagAdd]
    simp only [sub_mul, mul_sub, add_mul, mul_add, mul_assoc,
               opZig_mul_opZig hP, opZig_mul_opZig_assoc hP,
               opZag_mul_opZag hP, opZag_mul_opZag_assoc hP, h12, h21, h12', h21',
               zero_mul_assoc h12, zero_mul_assoc h21, zero_mul_assoc h12', zero_mul_assoc h21',
               mul_zero, zero_mul]; abel

/-! ## 4. Concrete Tail-Stabilized Infinite Channel Tower (`TowerColimit R`, `LV → LIX`) -/

variable {R : Type*} [Ring R] [StarRing R]

/-- Finite-scale operator star-ring at renormalization step `k`. -/
abbrev TowerLevel (R : Type*) (k : ℕ) := (Fin k → R) × R

/-- Infinite-channel colimit operator star-ring `A_∞ = ℕ → R`. -/
abbrev TowerColimit (R : Type*) := ℕ → R

/-- Step transition map `A_k → A_{k+1}`. -/
def towerStepFn (k : ℕ) (x : TowerLevel R k) : TowerLevel R (k + 1) :=
  (fun i => if h : i.val < k then x.1 ⟨i.val, h⟩ else x.2, x.2)

/-- Unital star-ring homomorphism `A_k →⋆+* A_{k+1}`. -/
def towerStepHom (k : ℕ) : StarRingHom (TowerLevel R k) (TowerLevel R (k + 1)) where
  toFun := towerStepFn k
  map_one' := by
    refine Prod.ext (funext fun i => ?_) rfl; by_cases h : i.val < k <;> simp [towerStepFn, h]
  map_mul' x y := by
    refine Prod.ext (funext fun i => ?_) rfl; by_cases h : i.val < k <;> simp [towerStepFn, h]
  map_zero' := by
    refine Prod.ext (funext fun i => ?_) rfl; by_cases h : i.val < k <;> simp [towerStepFn, h]
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) rfl; by_cases h : i.val < k <;> simp [towerStepFn, h]
  map_star' x := by
    refine Prod.ext (funext fun i => ?_) rfl; by_cases h : i.val < k <;> simp [towerStepFn, h]

/-- Every concrete tail-replication transition is injective: the old finite
coordinates remain in the first block and the tail coordinate is retained. -/
theorem towerStepHom_injective (k : ℕ) :
    Function.Injective (towerStepHom (R := R) k).toRingHom := by
  intro x y h
  change towerStepFn k x = towerStepFn k y at h
  apply Prod.ext
  · funext i
    have hi := congrFun (congrArg Prod.fst h) i.castSucc
    simpa [towerStepFn] using hi
  · simpa [towerStepFn] using congrArg Prod.snd h

/-- Colimit evaluation map `A_k → A_∞`. -/
def towerColimitFn (k : ℕ) (x : TowerLevel R k) (n : ℕ) : R :=
  if h : n < k then x.1 ⟨n, h⟩ else x.2

/-- Unital star-ring homomorphism `A_k →⋆+* A_∞`. -/
def towerToColimit (k : ℕ) : StarRingHom (TowerLevel R k) (TowerColimit R) where
  toFun := towerColimitFn k
  map_one' := by funext n; by_cases h : n < k <;> simp [towerColimitFn, h]
  map_mul' x y := by funext n; by_cases h : n < k <;> simp [towerColimitFn, h]
  map_zero' := by funext n; by_cases h : n < k <;> simp [towerColimitFn, h]
  map_add' x y := by funext n; by_cases h : n < k <;> simp [towerColimitFn, h]
  map_star' x := by funext n; by_cases h : n < k <;> simp [towerColimitFn, h]

/-- The canonical map from a finite tail-stabilized stage into the sequence
colimit is injective: the first `k` coordinates recover the finite block and
coordinate `k` recovers the stable tail. -/
theorem towerToColimit_injective (k : ℕ) :
    Function.Injective (towerToColimit (R := R) k).toRingHom := by
  intro x y h
  change towerColimitFn k x = towerColimitFn k y at h
  apply Prod.ext
  · funext i
    have hi := congrFun h i.val
    simpa [towerColimitFn, i.isLt] using hi
  · have hk := congrFun h k
    simpa [towerColimitFn] using hk

/-- A nonzero finite-stage two-sheet coupling remains nonzero in the concrete
tail-stabilized sequence colimit. This is algebraic injective transport only. -/
theorem towerToColimit_preserves_nonzero_two_sheet_coupling
    (k : ℕ) (P Aop C : TowerLevel R k)
    (hMass : opQuadraticCoupling P Aop C ≠ 0) :
    opQuadraticCoupling
      ((towerToColimit (R := R) k).toRingHom P)
      ((towerToColimit (R := R) k).toRingHom Aop)
      ((towerToColimit (R := R) k).toRingHom C) ≠ 0 := by
  exact starRingHom_preserves_nonzero_two_sheet_coupling
    (towerToColimit (R := R) k).toRingHom
    (towerToColimit_injective (R := R) k)
    (towerToColimit (R := R) k).map_star' P Aop C hMass

/-- Concrete instance of `InductiveStarColimitCone` over `R`. -/
def tailTowerCone (R : Type*) [Ring R] [StarRing R] :
    InductiveStarColimitCone (TowerLevel R) (TowerColimit R) where
  stepHom := towerStepHom
  toColimit := towerToColimit
  compat k x := by
    funext n
    dsimp [towerToColimit, towerStepHom, towerColimitFn, towerStepFn]
    by_cases h2 : n < k + 1
    · exact dif_pos h2
    · have h1 : ¬ (n < k) := fun h => h2 (Nat.lt_succ_of_lt h)
      rw [dif_neg h2, dif_neg h1]

instance instInhabitedInductiveStarColimitCone {R : Type*} [Ring R] [StarRing R] :
    Inhabited (InductiveStarColimitCone (TowerLevel R) (TowerColimit R)) :=
  ⟨tailTowerCone R⟩

/-- Concrete ground-ring model witness of `InductiveStarColimitCone` over `ℤ`. -/
def intTailTowerCone : InductiveStarColimitCone (TowerLevel ℤ) (TowerColimit ℤ) :=
  tailTowerCone ℤ

/-- Single-channel operator in the colimit `A_∞ = ℕ → R` supported solely at channel `k`. -/
def colimitChannel (k : ℕ) (r : R) : TowerColimit R :=
  fun n => if n = k then r else 0

/-- Uniform idempotent in the colimit `A_∞ = ℕ → R` generated by a base idempotent `p : R`. -/
def colimitVacuum (p : R) : TowerColimit R :=
  fun _ => p

omit [StarRing R] in
lemma colimitVacuum_idempotent {p : R} (hp : p * p = p) :
    colimitVacuum p * colimitVacuum p = colimitVacuum p := by
  funext _; exact hp

lemma colimitChannel_mul_of_ne {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) (u v : R) :
    colimitChannel k₁ u * colimitChannel k₂ v = 0 := by
  funext n
  change (if n = k₁ then u else 0) * (if n = k₂ then v else 0) = 0
  by_cases h1 : n = k₁
  · have h2 : n ≠ k₂ := fun h => hne (h1.symm.trans h)
    rw [if_pos h1, if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

lemma opZig_colimitChannel (p : R) (k : ℕ) (a : R) :
    opZig (colimitVacuum p) (colimitChannel k a) = colimitChannel k (opZig p a) := by
  funext n
  change p * (if n = k then a else 0) * (1 - p) = if n = k then p * a * (1 - p) else 0
  by_cases h : n = k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero, zero_mul]

lemma opZag_colimitChannel (p : R) (k : ℕ) (c : R) :
    opZag (colimitVacuum p) (colimitChannel k c) = colimitChannel k (opZag p c) := by
  funext n
  change (1 - p) * (if n = k then c else 0) * p = if n = k then (1 - p) * c * p else 0
  by_cases h : n = k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero, zero_mul]

lemma colimitChannel_horizon_orthogonal (p : R) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂)
    (a₁ c₁ a₂ c₂ : R) :
    let P_inf := colimitVacuum p
    let A₁ := colimitChannel k₁ a₁
    let C₁ := colimitChannel k₁ c₁
    let A₂ := colimitChannel k₂ a₂
    let C₂ := colimitChannel k₂ c₂
    opZig P_inf A₁ * opZag P_inf C₂ = 0 ∧
    opZig P_inf A₂ * opZag P_inf C₁ = 0 ∧
    opZag P_inf C₁ * opZig P_inf A₂ = 0 ∧
    opZag P_inf C₂ * opZig P_inf A₁ = 0 := by
  intro P_inf A₁ C₁ A₂ C₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · change opZig (colimitVacuum p) (colimitChannel k₁ a₁) *
      opZag (colimitVacuum p) (colimitChannel k₂ c₂) = 0
    rw [opZig_colimitChannel, opZag_colimitChannel]; exact colimitChannel_mul_of_ne hne _ _
  · change opZig (colimitVacuum p) (colimitChannel k₂ a₂) *
      opZag (colimitVacuum p) (colimitChannel k₁ c₁) = 0
    rw [opZig_colimitChannel, opZag_colimitChannel]; exact colimitChannel_mul_of_ne hne.symm _ _
  · change opZag (colimitVacuum p) (colimitChannel k₁ c₁) *
      opZig (colimitVacuum p) (colimitChannel k₂ a₂) = 0
    rw [opZag_colimitChannel, opZig_colimitChannel]; exact colimitChannel_mul_of_ne hne _ _
  · change opZag (colimitVacuum p) (colimitChannel k₂ c₂) *
      opZig (colimitVacuum p) (colimitChannel k₁ a₁) = 0
    rw [opZag_colimitChannel, opZig_colimitChannel]; exact colimitChannel_mul_of_ne hne.symm _ _

/-! ## 5. Archetypes `LX → LXIII`: Two-Sheet Odd/Even Coupling & Colimit Scaling -/

/-- Two-sheet odd coupling operator `Φ = opElectron P A C = N₊ + N₋`. -/
def opHiggsField (P A C : B) : B := opElectron P A C

/-- Two-sheet even quadratic operator `V = Φ² = {N₊, N₋}`. -/
def opHiggsVEVSq (P A C : B) : B := opQuadraticCoupling P A C

/-- Double-commutator adjoint-square operator `M(X) = -[Φ, [Φ, X]]`. -/
def opHiggsMassOperator (P A C X : B) : B := opNegativeAdjointSquare P A C X

/-- **Theorem `LX.1` (`connes_higgs_yukawa_mass_mechanism`):**
Universal double-commutator eigenvalue law for `opHiggsMassOperator`:
1. `opHiggsField P A C * opHiggsField P A C = opHiggsVEVSq P A C`,
2. `comm (opHiggsField P A C) X = 0 → opHiggsMassOperator P A C X = 0`,
3. `anticomm (opHiggsField P A C) X = 0 → comm (opHiggsVEVSq P A C) X = 0 → opHiggsMassOperator P A C X = -((4 : ℤ) • (opHiggsVEVSq P A C * X))`. -/
theorem connes_higgs_yukawa_mass_mechanism
    {P : B} (hP : P * P = P) (A C X : B) :
    opHiggsField P A C * opHiggsField P A C = opHiggsVEVSq P A C ∧
    (comm (opHiggsField P A C) X = 0 → opHiggsMassOperator P A C X = 0) ∧
    (anticomm (opHiggsField P A C) X = 0 →
     comm (opHiggsVEVSq P A C) X = 0 →
      opHiggsMassOperator P A C X = -((4 : ℤ) • (opHiggsVEVSq P A C * X))) := by
  have hPhiSq : opHiggsField P A C * opHiggsField P A C = opHiggsVEVSq P A C :=
    (two_sheet_tetraktys hP A C).1
  refine ⟨hPhiSq, ?_, ?_⟩
  · intro hComm0
    change -comm (opHiggsField P A C) (comm (opHiggsField P A C) X) = 0
    rw [hComm0]
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [mul_zero, zero_mul, sub_self, neg_zero]
  · intro hAnti0 hVEVComm0
    have hPhiX : X * opHiggsField P A C = -(opHiggsField P A C * X) :=
      eq_neg_of_add_eq_zero_right hAnti0
    have hXV : X * opHiggsVEVSq P A C = opHiggsVEVSq P A C * X :=
      (sub_eq_zero.mp hVEVComm0).symm
    have hSandwich :
        opHiggsField P A C * X * opHiggsField P A C = -(opHiggsVEVSq P A C * X) := by
      calc opHiggsField P A C * X * opHiggsField P A C
        _ = opHiggsField P A C * (X * opHiggsField P A C) := by rw [mul_assoc]
        _ = opHiggsField P A C * -(opHiggsField P A C * X) := by rw [hPhiX]
        _ = -((opHiggsField P A C * opHiggsField P A C) * X) := by simp only [mul_neg, mul_assoc]
        _ = -(opHiggsVEVSq P A C * X) := by rw [hPhiSq]
    change -(opHiggsField P A C * (opHiggsField P A C * X - X * opHiggsField P A C) -
             (opHiggsField P A C * X - X * opHiggsField P A C) * opHiggsField P A C) = _
    calc -(opHiggsField P A C * (opHiggsField P A C * X - X * opHiggsField P A C) -
           (opHiggsField P A C * X - X * opHiggsField P A C) * opHiggsField P A C)
      _ = -((opHiggsField P A C * opHiggsField P A C) * X -
            opHiggsField P A C * X * opHiggsField P A C -
            opHiggsField P A C * X * opHiggsField P A C +
            X * (opHiggsField P A C * opHiggsField P A C)) := by
          simp only [mul_sub, sub_mul, mul_assoc]; abel
      _ = -(opHiggsVEVSq P A C * X - -(opHiggsVEVSq P A C * X) -
            -(opHiggsVEVSq P A C * X) + opHiggsVEVSq P A C * X) := by
          rw [hPhiSq, hSandwich, hXV]
      _ = -((4 : ℤ) • (opHiggsVEVSq P A C * X)) := by abel

/-- **Theorem `LX.2` (`higgs_mexican_hat_and_goldstone_eating`):**
Repaired with explicit reflexive cross-sheet hypotheses `hReflZig` and `hReflZag`: proves the
tripotent/idempotent closure `Φ * (Φ * Φ) = Φ` and `(Φ * Φ)² = Φ * Φ`, together with the
unit-normalized eigenvalues `opHiggsMassOperator P A C (opAxial P A C) = -(4 : ℤ) • opAxial P A C`
and `opHiggsMassOperator P A C (opSpinDipole P A C) = -(4 : ℤ) • opSpinDipole P A C`. -/
theorem higgs_mexican_hat_and_goldstone_eating
    {P : B} (hP : P * P = P) (A C : B)
    (hReflZig : opZig P A * opZag P C * opZig P A = opZig P A)
    (hReflZag : opZag P C * opZig P A * opZag P C = opZag P C) :
    opHiggsField P A C * opHiggsField P A C - opHiggsVEVSq P A C = 0 ∧
    (opHiggsField P A C * opHiggsField P A C - opHiggsVEVSq P A C) *
      (opHiggsField P A C * opHiggsField P A C - opHiggsVEVSq P A C) = 0 ∧
    opHiggsField P A C * (opHiggsField P A C * opHiggsField P A C) = opHiggsField P A C ∧
    (opHiggsField P A C * opHiggsField P A C) * (opHiggsField P A C * opHiggsField P A C) =
      opHiggsField P A C * opHiggsField P A C ∧
    opHiggsMassOperator P A C (opHiggsField P A C) = 0 ∧
    opHiggsMassOperator P A C (opAxial P A C) = -((4 : ℤ) • opAxial P A C) ∧
    opHiggsMassOperator P A C (opSpinDipole P A C) = -((4 : ℤ) • opSpinDipole P A C) := by
  have hPhiSq := (connes_higgs_yukawa_mass_mechanism hP A C 0).1
  have hSubSq : opHiggsField P A C * opHiggsField P A C - opHiggsVEVSq P A C = 0 :=
    sub_eq_zero.mpr hPhiSq
  have hPhiTrip :
      opHiggsField P A C * (opHiggsField P A C * opHiggsField P A C) = opHiggsField P A C := by
    rw [hPhiSq]
    change (opZig P A + opZag P C) * (opZig P A * opZag P C + opZag P C * opZig P A) =
      opZig P A + opZag P C
    calc (opZig P A + opZag P C) * (opZig P A * opZag P C + opZag P C * opZig P A)
      _ = opZig P A * opZag P C * opZig P A +
          (opZig P A * opZig P A) * opZag P C +
          (opZag P C * opZag P C) * opZig P A +
          opZag P C * opZig P A * opZag P C := by
          simp only [add_mul, mul_add, mul_assoc]; abel
      _ = opZig P A + opZag P C := by
          rw [opZig_mul_opZig hP, opZag_mul_opZag hP, zero_mul, zero_mul,
              add_zero, add_zero, hReflZig, hReflZag]
  have hVEV_J : opHiggsVEVSq P A C * opAxial P A C = opAxial P A C := by
    change (opZig P A * opZag P C + opZag P C * opZig P A) * (opZig P A - opZag P C) =
      opZig P A - opZag P C
    calc (opZig P A * opZag P C + opZag P C * opZig P A) * (opZig P A - opZag P C)
      _ = opZig P A * opZag P C * opZig P A -
          opZig P A * (opZag P C * opZag P C) +
          opZag P C * (opZig P A * opZig P A) -
          opZag P C * opZig P A * opZag P C := by
          simp only [add_mul, mul_sub, mul_assoc]; abel
      _ = opZig P A - opZag P C := by
          rw [opZig_mul_opZig hP, opZag_mul_opZag hP, mul_zero, mul_zero,
              sub_zero, add_zero, hReflZig, hReflZag]
  have hVEV_Spin : opHiggsVEVSq P A C * opSpinDipole P A C = opSpinDipole P A C := by
    change (opZig P A * opZag P C + opZag P C * opZig P A) *
      (opZig P A * opZag P C - opZag P C * opZig P A) =
      opZig P A * opZag P C - opZag P C * opZig P A
    calc (opZig P A * opZag P C + opZag P C * opZig P A) *
         (opZig P A * opZag P C - opZag P C * opZig P A)
      _ = (opZig P A * opZag P C * opZig P A) * opZag P C -
          opZig P A * ((opZag P C * opZag P C) * opZig P A) +
          opZag P C * ((opZig P A * opZig P A) * opZag P C) -
          (opZag P C * opZig P A * opZag P C) * opZig P A := by
          simp only [add_mul, mul_sub, mul_assoc]; abel
      _ = opZig P A * opZag P C - opZag P C * opZig P A := by
          rw [opZig_mul_opZig hP, opZag_mul_opZag hP, zero_mul, zero_mul,
              mul_zero, mul_zero, sub_zero, add_zero, hReflZig, hReflZag]
  have hSpectral := archetype_A5_klein_hadamard_spectra_and_partition hP A C (0 : B)
  refine ⟨hSubSq, by rw [hSubSq, mul_zero], hPhiTrip, ?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, hPhiTrip]
  · exact hSpectral.2.1
  · change derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • opAxial P A C)
    rw [hSpectral.2.2.2.1]
    change -((4 : ℤ) • (opHiggsVEVSq P A C * opAxial P A C)) = _
    rw [hVEV_J]
  · change derivSqPhi P A C (genSig P A C) = -((4 : ℤ) • opSpinDipole P A C)
    rw [hSpectral.2.2.2.2.1]
    change -((4 : ℤ) • (opHiggsVEVSq P A C * opSpinDipole P A C)) = _
    rw [hVEV_Spin]

/-- **Theorem `LXI.1` (`universal_higgs_goldstone_spin_triad`):**
Universal algebraic relations of `(Φ, J₅, V, Σ)` under `opHiggsMassOperator`. -/
theorem universal_higgs_goldstone_spin_triad
    {P : B} (hP : P * P = P) (A C : B) :
    let Φ := opHiggsField P A C
    let J₅ := opAxial P A C
    let V := opHiggsVEVSq P A C
    let Sig := opSpinDipole P A C
    J₅ * J₅ = -V ∧
    Φ * Φ + J₅ * J₅ = 0 ∧
    Φ * J₅ = -Sig ∧
    J₅ * Φ = Sig ∧
    comm Φ V = 0 ∧
    anticomm Φ J₅ = 0 ∧
    anticomm Φ Sig = 0 ∧
    comm V J₅ = 0 ∧
    comm V Sig = 0 ∧
    opHiggsMassOperator P A C Φ = 0 ∧
    opHiggsMassOperator P A C V = 0 ∧
    opHiggsMassOperator P A C J₅ = -((4 : ℤ) • (V * J₅)) ∧
    opHiggsMassOperator P A C Sig = -((4 : ℤ) • (V * Sig)) := by
  intro Φ J₅ V Sig
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hP A C
  have hSpectral := archetype_A5_klein_hadamard_spectra_and_partition hP A C (0 : B)
  refine ⟨hA3.2.2.2.1, ?_, ?_, hA3.2.2.2.2.2.1,
          ?_, ?_, ?_, ?_, ?_,
          hSpectral.2.1, hSpectral.2.2.1, hSpectral.2.2.2.1, hSpectral.2.2.2.2.1⟩
  · change genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0; peirce_nf hP
  · change genPhi P A C * genJ P A C = -genSig P A C; peirce_nf hP
  · change comm (genPhi P A C) (genV P A C) = 0; peirce_nf hP
  · change anticomm (genPhi P A C) (genJ P A C) = 0; peirce_nf hP
  · change anticomm (genPhi P A C) (genSig P A C) = 0; peirce_nf hP
  · change comm (genV P A C) (genJ P A C) = 0; peirce_nf hP
  · change comm (genV P A C) (genSig P A C) = 0; peirce_nf hP

/-- `ℤ`-linearity of `opHiggsMassOperator P A C`. -/
lemma opHiggsMassOperator_zsmul_add (P A C X Y : B) (α β : ℤ) :
    opHiggsMassOperator P A C (α • X + β • Y) =
      α • opHiggsMassOperator P A C X + β • opHiggsMassOperator P A C Y := by
  change -comm (genPhi P A C) (comm (genPhi P A C) (α • X + β • Y)) =
    α • (-comm (genPhi P A C) (comm (genPhi P A C) X)) +
    β • (-comm (genPhi P A C) (comm (genPhi P A C) Y))
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
             smul_sub, smul_add, smul_neg, neg_sub]
  abel

/-- **Theorem `LXI.2` (`erlangen_unitary_gauge_higgs_projection`):**
Projection of `α • opHiggsField P A C + β • opAxial P A C` under `opHiggsMassOperator P A C`. -/
theorem erlangen_unitary_gauge_higgs_projection
    {P : B} (hP : P * P = P) (A C : B) (α β : ℤ) :
    opHiggsMassOperator P A C (α • opHiggsField P A C + β • opAxial P A C) =
      β • (-((4 : ℤ) • (opHiggsVEVSq P A C * opAxial P A C))) := by
  rcases universal_higgs_goldstone_spin_triad hP A C with
    ⟨_, _, _, _, _, _, _, _, _, hMPhi, _, hMJ, _⟩
  rw [opHiggsMassOperator_zsmul_add, hMPhi, hMJ, smul_zero, zero_add]

/-- **Theorem `LXII.1` (`colimit_connes_higgs_triad_lift`):**
Inductive colimit lift of the `(Φ, J₅, V, Σ)` triad and multi-step scale invariance in `A_inf`. -/
theorem colimit_connes_higgs_triad_lift
    {A : ℕ → Type*} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (k m : ℕ) (P_k A_k C_k X_k : A k) (hP_k : P_k * P_k = P_k) (α β : ℤ) :
    let ψ_m := (stepHomIter Cone k m).toRingHom
    let ι_km := (Cone.toColimit (k + m)).toRingHom
    let ι_k := (Cone.toColimit k).toRingHom
    let P_inf := ι_k P_k
    let A_inf := ι_k A_k
    let C_inf := ι_k C_k
    let Φ_inf := opHiggsField P_inf A_inf C_inf
    let J₅_inf := opAxial P_inf A_inf C_inf
    let V_inf := opHiggsVEVSq P_inf A_inf C_inf
    let Sig_inf := opSpinDipole P_inf A_inf C_inf
    ι_km (opHiggsField (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) = Φ_inf ∧
    ι_km (opHiggsVEVSq (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) = V_inf ∧
    ι_km (opHiggsMassOperator (ψ_m P_k) (ψ_m A_k) (ψ_m C_k) (ψ_m X_k)) =
      opHiggsMassOperator P_inf A_inf C_inf (ι_k X_k) ∧
    Φ_inf * Φ_inf = V_inf ∧
    J₅_inf * J₅_inf = -V_inf ∧
    Φ_inf * Φ_inf + J₅_inf * J₅_inf = 0 ∧
    Φ_inf * J₅_inf = -Sig_inf ∧
    J₅_inf * Φ_inf = Sig_inf ∧
    opHiggsMassOperator P_inf A_inf C_inf Φ_inf = 0 ∧
    opHiggsMassOperator P_inf A_inf C_inf V_inf = 0 ∧
    opHiggsMassOperator P_inf A_inf C_inf J₅_inf = -((4 : ℤ) • (V_inf * J₅_inf)) ∧
    opHiggsMassOperator P_inf A_inf C_inf Sig_inf = -((4 : ℤ) • (V_inf * Sig_inf)) ∧
    opHiggsMassOperator P_inf A_inf C_inf (α • Φ_inf + β • J₅_inf) =
      β • (-((4 : ℤ) • (V_inf * J₅_inf))) := by
  intro ψ_m ι_km ι_k P_inf A_inf C_inf Φ_inf J₅_inf V_inf Sig_inf
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf, ι_k]; rw [← map_mul, hP_k]
  have hRG := colimit_renormalization_scale_invariance Cone k m P_k A_k C_k X_k
  rcases hRG with ⟨hCocycle, hRG_Mass, _, _, hRG_Diss⟩
  rcases starRingHom_intertwines_two_sheeted_tower
      (stepHomIter Cone k m).toRingHom (stepHomIter Cone k m).map_star' P_k A_k C_k X_k with
    ⟨_, _, _, hElec_m, _, _, _, _, _⟩
  rcases starRingHom_intertwines_two_sheeted_tower
      (Cone.toColimit k).toRingHom (Cone.toColimit k).map_star' P_k A_k C_k X_k with
    ⟨_, _, _, hElec_k, _, _, _, _, _⟩
  have hRG_Phi : ι_km (opHiggsField (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) = Φ_inf := by
    change ι_km (opElectron (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) = opElectron P_inf A_inf C_inf
    calc ι_km (opElectron (ψ_m P_k) (ψ_m A_k) (ψ_m C_k))
      _ = ι_km (ψ_m (opElectron P_k A_k C_k)) := congr_arg ι_km hElec_m.symm
      _ = ι_k (opElectron P_k A_k C_k) := hCocycle _
      _ = opElectron P_inf A_inf C_inf := hElec_k
  have hPhiSq := (connes_higgs_yukawa_mass_mechanism hP_inf A_inf C_inf 0).1
  rcases universal_higgs_goldstone_spin_triad hP_inf A_inf C_inf with
    ⟨hJSq, hNorm0, hPhiJ, hJPhi, _, _, _, _, _, hMPhi, hMV, hMJ, hMSpin⟩
  have hErl := erlangen_unitary_gauge_higgs_projection hP_inf A_inf C_inf α β
  exact ⟨hRG_Phi, hRG_Mass, hRG_Diss, hPhiSq, hJSq, hNorm0, hPhiJ, hJPhi,
         hMPhi, hMV, hMJ, hMSpin, hErl⟩

/-- **Theorem `LXII.2` (`colimit_higgs_mexican_hat_and_goldstone_lift`):**
Inductive colimit lift of the reflexive cross-sheet tripotent/idempotent identities into `A_inf`. -/
theorem colimit_higgs_mexican_hat_and_goldstone_lift
    {A : ℕ → Type*} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (k : ℕ) (P_k A_k C_k : A k) (hP_k : P_k * P_k = P_k)
    (hReflZig_k : opZig P_k A_k * opZag P_k C_k * opZig P_k A_k = opZig P_k A_k)
    (hReflZag_k : opZag P_k C_k * opZig P_k A_k * opZag P_k C_k = opZag P_k C_k) :
    let ι_k := (Cone.toColimit k).toRingHom
    let P_inf := ι_k P_k
    let A_inf := ι_k A_k
    let C_inf := ι_k C_k
    let Φ_inf := opHiggsField P_inf A_inf C_inf
    let V_inf := opHiggsVEVSq P_inf A_inf C_inf
    let J₅_inf := opAxial P_inf A_inf C_inf
    let Sig_inf := opSpinDipole P_inf A_inf C_inf
    Φ_inf * Φ_inf - V_inf = 0 ∧
    (Φ_inf * Φ_inf - V_inf) * (Φ_inf * Φ_inf - V_inf) = 0 ∧
    Φ_inf * (Φ_inf * Φ_inf) = Φ_inf ∧
    (Φ_inf * Φ_inf) * (Φ_inf * Φ_inf) = Φ_inf * Φ_inf ∧
    opHiggsMassOperator P_inf A_inf C_inf Φ_inf = 0 ∧
    opHiggsMassOperator P_inf A_inf C_inf J₅_inf = -((4 : ℤ) • J₅_inf) ∧
    opHiggsMassOperator P_inf A_inf C_inf Sig_inf = -((4 : ℤ) • Sig_inf) := by
  intro ι_k P_inf A_inf C_inf Φ_inf V_inf J₅_inf Sig_inf
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf, ι_k]; rw [← map_mul, hP_k]
  rcases starRingHom_intertwines_two_sheeted_tower
      (Cone.toColimit k).toRingHom (Cone.toColimit k).map_star' P_k A_k C_k 0 with
    ⟨_, hZig, hZag, _, _, _, _, _, _⟩
  have hReflZig_inf :
      opZig P_inf A_inf * opZag P_inf C_inf * opZig P_inf A_inf = opZig P_inf A_inf := by
    dsimp [P_inf, A_inf, C_inf, ι_k]
    rw [← hZig, ← hZag, ← map_mul, ← map_mul, hReflZig_k]
  have hReflZag_inf :
      opZag P_inf C_inf * opZig P_inf A_inf * opZag P_inf C_inf = opZag P_inf C_inf := by
    dsimp [P_inf, A_inf, C_inf, ι_k]
    rw [← hZig, ← hZag, ← map_mul, ← map_mul, hReflZag_k]
  exact higgs_mexican_hat_and_goldstone_eating hP_inf A_inf C_inf hReflZig_inf hReflZag_inf

/-- Bilinear `ℤ`-scalar multiplication identity `(N • X) * (N • Y) = (N * N) • (X * Y)`. -/
lemma zsmul_mul_zsmul (N : ℤ) (X Y : B) :
    (N • X) * (N • Y) = (N * N) • (X * Y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

lemma opZig_zsmul (P A : B) (N : ℤ) :
    opZig P (N • A) = N • opZig P A := by
  unfold opZig conePlus; rw [mul_smul_comm, smul_mul_assoc]

lemma opZag_zsmul (P C : B) (N : ℤ) :
    opZag P (N • C) = N • opZag P C := by
  unfold opZag coneMinus; rw [mul_smul_comm, smul_mul_assoc]

lemma opHiggsField_zsmul (P A C : B) (N : ℤ) :
    opHiggsField P (N • A) (N • C) = N • opHiggsField P A C := by
  change opZig P (N • A) + opZag P (N • C) = N • (opZig P A + opZag P C)
  rw [opZig_zsmul, opZag_zsmul, ← smul_add]

lemma opAxial_zsmul (P A C : B) (N : ℤ) :
    opAxial P (N • A) (N • C) = N • opAxial P A C := by
  change opZig P (N • A) - opZag P (N • C) = N • (opZig P A - opZag P C)
  rw [opZig_zsmul, opZag_zsmul, ← smul_sub]

lemma opHiggsVEVSq_zsmul (P A C : B) (N : ℤ) :
    opHiggsVEVSq P (N • A) (N • C) = (N * N) • opHiggsVEVSq P A C := by
  change opZig P (N • A) * opZag P (N • C) + opZag P (N • C) * opZig P (N • A) =
    (N * N) • (opZig P A * opZag P C + opZag P C * opZig P A)
  rw [opZig_zsmul, opZag_zsmul, zsmul_mul_zsmul, zsmul_mul_zsmul, ← smul_add]

lemma opSpinDipole_zsmul (P A C : B) (N : ℤ) :
    opSpinDipole P (N • A) (N • C) = (N * N) • opSpinDipole P A C := by
  change opZig P (N • A) * opZag P (N • C) - opZag P (N • C) * opZig P (N • A) =
    (N * N) • (opZig P A * opZag P C - opZag P C * opZig P A)
  rw [opZig_zsmul, opZag_zsmul, zsmul_mul_zsmul, zsmul_mul_zsmul, ← smul_sub]

lemma comm_zsmul_left (U V : B) (N : ℤ) :
    comm (N • U) V = N • comm U V := by
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]

lemma comm_zsmul_right (U V : B) (N : ℤ) :
    comm U (N • V) = N • comm U V := by
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]

lemma opHiggsMassOperator_zsmul_mode (P A C X : B) (N : ℤ) :
    opHiggsMassOperator P (N • A) (N • C) X =
      (N * N) • opHiggsMassOperator P A C X := by
  change -comm (opHiggsField P (N • A) (N • C))
      (comm (opHiggsField P (N • A) (N • C)) X) =
    (N * N) • (-comm (opHiggsField P A C) (comm (opHiggsField P A C) X))
  rw [opHiggsField_zsmul, comm_zsmul_left, comm_zsmul_left,
      comm_zsmul_right, smul_smul, smul_neg]

/-- **Theorem `LXIII.1` (`colimit_coherent_bec_higgs_vev_scaling`):**
Quadratic `N * N` scaling of `opHiggsVEVSq`, `opSpinDipole`, and `opHiggsMassOperator` under `N`-fold
coherent mode scaling `(N • A_inf, N • C_inf)` in `A_inf`. -/
theorem colimit_coherent_bec_higgs_vev_scaling
    {A : ℕ → Type*} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (k : ℕ) (P_k A_k C_k : A k) (hP_k : P_k * P_k = P_k) (N : ℤ) (X : A_inf) :
    let ι_k := (Cone.toColimit k).toRingHom
    let P_inf := ι_k P_k
    let A_inf := ι_k A_k
    let C_inf := ι_k C_k
    let Φ_inf := opHiggsField P_inf A_inf C_inf
    let J₅_inf := opAxial P_inf A_inf C_inf
    let V_inf := opHiggsVEVSq P_inf A_inf C_inf
    let Sig_inf := opSpinDipole P_inf A_inf C_inf
    let Φ_BEC := opHiggsField P_inf (N • A_inf) (N • C_inf)
    let J₅_BEC := opAxial P_inf (N • A_inf) (N • C_inf)
    let V_BEC := opHiggsVEVSq P_inf (N • A_inf) (N • C_inf)
    let Sig_BEC := opSpinDipole P_inf (N • A_inf) (N • C_inf)
    Φ_BEC = N • Φ_inf ∧
    J₅_BEC = N • J₅_inf ∧
    V_BEC = (N * N) • V_inf ∧
    Sig_BEC = (N * N) • Sig_inf ∧
    opHiggsMassOperator P_inf (N • A_inf) (N • C_inf) X =
      (N * N) • opHiggsMassOperator P_inf A_inf C_inf X ∧
    opHiggsMassOperator P_inf (N • A_inf) (N • C_inf) Φ_BEC = 0 ∧
    opHiggsMassOperator P_inf (N • A_inf) (N • C_inf) V_BEC = 0 ∧
    opHiggsMassOperator P_inf (N • A_inf) (N • C_inf) J₅_BEC =
      -((4 : ℤ) • ((N * N) • (V_inf * J₅_BEC))) := by
  intro ι_k P_inf A_inf C_inf Φ_inf J₅_inf V_inf Sig_inf Φ_BEC J₅_BEC V_BEC Sig_BEC
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf, ι_k]; rw [← map_mul, hP_k]
  rcases universal_higgs_goldstone_spin_triad hP_inf (N • A_inf) (N • C_inf) with
    ⟨_, _, _, _, _, _, _, _, _, hMPhi_BEC, hMV_BEC, hMJ_BEC, _⟩
  refine ⟨opHiggsField_zsmul P_inf A_inf C_inf N,
          opAxial_zsmul P_inf A_inf C_inf N,
          opHiggsVEVSq_zsmul P_inf A_inf C_inf N,
          opSpinDipole_zsmul P_inf A_inf C_inf N,
          opHiggsMassOperator_zsmul_mode P_inf A_inf C_inf X N,
          hMPhi_BEC, hMV_BEC, ?_⟩
  change opHiggsMassOperator P_inf (N • A_inf) (N • C_inf) J₅_BEC =
    -((4 : ℤ) • ((N * N) • (V_inf * J₅_BEC)))
  rw [hMJ_BEC]
  change -((4 : ℤ) • (opHiggsVEVSq P_inf (N • A_inf) (N • C_inf) * J₅_BEC)) = _
  rw [opHiggsVEVSq_zsmul, smul_mul_assoc]

/-- **Theorem `LXIII.2` (`colimit_orthogonal_channel_higgs_decoupling`):**
Orthogonal multi-channel additivity and decoupling in `TowerColimit R = (ℕ → R)` for `k₁ ≠ k₂`. -/
theorem colimit_orthogonal_channel_higgs_decoupling
    {p : R} (hp : p * p = p) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) (a₁ c₁ a₂ c₂ : R) :
    let P_inf := colimitVacuum p
    let A₁ := colimitChannel k₁ a₁
    let C₁ := colimitChannel k₁ c₁
    let A₂ := colimitChannel k₂ a₂
    let C₂ := colimitChannel k₂ c₂
    let V₁ := opHiggsVEVSq P_inf A₁ C₁
    let V₂ := opHiggsVEVSq P_inf A₂ C₂
    let J₁ := opAxial P_inf A₁ C₁
    let J₂ := opAxial P_inf A₂ C₂
    opHiggsVEVSq P_inf (A₁ + A₂) (C₁ + C₂) = V₁ + V₂ ∧
    V₁ * V₂ = 0 ∧
    V₂ * V₁ = 0 ∧
    opHiggsMassOperator P_inf (A₁ + A₂) (C₁ + C₂)
      (opHiggsField P_inf (A₁ + A₂) (C₁ + C₂)) = 0 ∧
    opHiggsMassOperator P_inf (A₁ + A₂) (C₁ + C₂)
      (opHiggsVEVSq P_inf (A₁ + A₂) (C₁ + C₂)) = 0 ∧
    opHiggsMassOperator P_inf (A₁ + A₂) (C₁ + C₂)
        (opAxial P_inf (A₁ + A₂) (C₁ + C₂)) =
      -((4 : ℤ) • (V₁ * J₁)) + -((4 : ℤ) • (V₂ * J₂)) := by
  intro P_inf A₁ C₁ A₂ C₂ V₁ V₂ J₁ J₂
  have hP_inf : P_inf * P_inf = P_inf := colimitVacuum_idempotent hp
  rcases colimitChannel_horizon_orthogonal p hne a₁ c₁ a₂ c₂ with ⟨h12, h21, h12', h21'⟩
  have hAdd := multi_channel_orthogonal_mass_gap_additivity P_inf A₁ C₁ A₂ C₂ h12 h21 h12' h21'
  have hDec := multi_channel_orthogonal_dissipator_and_spectral_gap_decoupling
    hP_inf A₁ C₁ A₂ C₂ h12 h21 h12' h21'
  rcases universal_higgs_goldstone_spin_triad hP_inf (A₁ + A₂) (C₁ + C₂) with
    ⟨_, _, _, _, _, _, _, _, _, hMPhi_12, hMV_12, _, _⟩
  rcases universal_higgs_goldstone_spin_triad hP_inf A₁ C₁ with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hMJ_1, _⟩
  rcases universal_higgs_goldstone_spin_triad hP_inf A₂ C₂ with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hMJ_2, _⟩
  refine ⟨hAdd.2.2.1, hDec.1, hDec.2.1, hMPhi_12, hMV_12, ?_⟩
  change opNegativeAdjointSquare P_inf (A₁ + A₂) (C₁ + C₂) (opAxial P_inf (A₁ + A₂) (C₁ + C₂)) =
    -((4 : ℤ) • (V₁ * J₁)) + -((4 : ℤ) • (V₂ * J₂))
  rw [hDec.2.2.2.2.1]
  change opHiggsMassOperator P_inf A₁ C₁ J₁ + opHiggsMassOperator P_inf A₂ C₂ J₂ = _
  rw [hMJ_1, hMJ_2]

end CanonicalTwoSheetedInductiveColimit
