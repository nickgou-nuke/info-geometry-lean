/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PositroidClusterTwistPoset
import InfoGeometry.Core.IdempotentDefectIteration
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Skew associative triple products remain in their Peirce corners. -/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The antisymmetrized associative homotope on the upper Peirce corner. -/
def upperHomotopeBracket (P C A Z : B) : B :=
  opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C)

/-- The same upper-corner bracket written as the ordered triple cross-product
used in the transcript. This is a product in the associative Peirce carrier,
not the cross-product of the nonassociative `ZornVectorMatrix` algebra. -/
def upperCornerCrossProduct (P C A Z : B) : B :=
  conePlus P A * coneMinus P C * conePlus P Z -
    conePlus P Z * coneMinus P C * conePlus P A

/-- The upper homotope bracket is supported in the upper off-diagonal Peirce
corner and is square-zero for an idempotent cut. -/
theorem upperHomotopeBracket_corner_and_square_zero {P : B}
    (hP : P * P = P) (C A Z : B) :
    P * upperHomotopeBracket P C A Z = upperHomotopeBracket P C A Z ∧
    upperHomotopeBracket P C A Z * (1 - P) = upperHomotopeBracket P C A Z ∧
    upperHomotopeBracket P C A Z * upperHomotopeBracket P C A Z = 0 := by
  simp only [upperHomotopeBracket, opKantorAnomaly, conePlus, coneMinus]
  peirce_nf hP
  simp

/-- The upper homotope bracket is alternating in its two cone inputs. This
is a law of the associative Peirce homotope, not of the concrete Zorn
element commutator. -/
theorem upperHomotopeBracket_skew (P C A Z : B) :
    upperHomotopeBracket P C A Z = -upperHomotopeBracket P C Z A := by
  simp [upperHomotopeBracket, opKantorAnomaly, conePlus, coneMinus]

/-- The upper homotope bracket vanishes when its cone inputs agree. -/
theorem upperHomotopeBracket_self (P C A : B) :
    upperHomotopeBracket P C A A = 0 := by
  simp [upperHomotopeBracket, opKantorAnomaly]

/-- Additivity in the first upper-corner input of the fixed-reference
homotope bracket. -/
theorem upperHomotopeBracket_add_left (P C A A' Z : B) :
    upperHomotopeBracket P C (A + A') Z =
      upperHomotopeBracket P C A Z + upperHomotopeBracket P C A' Z := by
  simp only [upperHomotopeBracket, opKantorAnomaly, conePlus, coneMinus]
  noncomm_ring

/-- Additivity in the second upper-corner input of the fixed-reference
homotope bracket. -/
theorem upperHomotopeBracket_add_right (P C A Z Z' : B) :
    upperHomotopeBracket P C A (Z + Z') =
      upperHomotopeBracket P C A Z + upperHomotopeBracket P C A Z' := by
  simp only [upperHomotopeBracket, opKantorAnomaly, conePlus, coneMinus]
  noncomm_ring

/-- Ring homomorphisms transport the upper homotope bracket along with the
idempotent candidate and both of its oriented inputs. -/
theorem map_upperHomotopeBracket {D : Type*} [Ring D] (f : B →+* D)
    (P C A Z : B) :
    f (upperHomotopeBracket P C A Z) =
      upperHomotopeBracket (f P) (f C) (f A) (f Z) := by
  simp [upperHomotopeBracket, opKantorAnomaly, conePlus, coneMinus]

/-- The homotope bracket satisfies Jacobi for every idempotent and every
reference lower-corner element. -/
theorem upper_homotope_jacobi {P : B} (hP : P * P = P) (C A Z W : B) :
    upperHomotopeBracket P C A (upperHomotopeBracket P C Z W) +
      upperHomotopeBracket P C Z (upperHomotopeBracket P C W A) +
      upperHomotopeBracket P C W (upperHomotopeBracket P C A Z) = 0 := by
  simp only [upperHomotopeBracket, opKantorAnomaly, conePlus, coneMinus]
  peirce_nf hP

/-- The explicit associative Peirce triple cross-product satisfies Jacobi.
This theorem concerns the homotope product through a fixed lower-corner
reference, not the commutator or vector cross-product of split octonions. -/
theorem upper_corner_cross_product_jacobi {P : B} (hP : P * P = P)
    (C A Z W : B) :
    upperCornerCrossProduct P C A (upperCornerCrossProduct P C Z W) +
      upperCornerCrossProduct P C Z (upperCornerCrossProduct P C W A) +
      upperCornerCrossProduct P C W (upperCornerCrossProduct P C A Z) = 0 := by
  simpa [upperCornerCrossProduct, upperHomotopeBracket, opKantorAnomaly]
    using upper_homotope_jacobi hP C A Z W

/-- Lower-corner counterpart, written as an ordered triple cross-product
through a fixed upper-corner reference. -/
def lowerCornerCrossProduct (P A Y W : B) : B :=
  coneMinus P Y * conePlus P A * coneMinus P W -
    coneMinus P W * conePlus P A * coneMinus P Y

/-- The lower corner cross-product is supported in the lower off-diagonal
Peirce corner and is square-zero for an idempotent cut. -/
theorem lowerCornerCrossProduct_corner_and_square_zero {P : B}
    (hP : P * P = P) (A Y W : B) :
    (1 - P) * lowerCornerCrossProduct P A Y W = lowerCornerCrossProduct P A Y W ∧
    lowerCornerCrossProduct P A Y W * P = lowerCornerCrossProduct P A Y W ∧
    lowerCornerCrossProduct P A Y W * lowerCornerCrossProduct P A Y W = 0 := by
  simp only [lowerCornerCrossProduct, conePlus, coneMinus]
  peirce_nf hP
  simp

/-- The lower associative Peirce homotope cross-product also satisfies Jacobi. -/
theorem lower_corner_cross_product_jacobi {P : B} (hP : P * P = P)
    (A Y W U : B) :
    lowerCornerCrossProduct P A Y (lowerCornerCrossProduct P A W U) +
      lowerCornerCrossProduct P A W (lowerCornerCrossProduct P A U Y) +
      lowerCornerCrossProduct P A U (lowerCornerCrossProduct P A Y W) = 0 := by
  simp only [lowerCornerCrossProduct, conePlus, coneMinus]
  peirce_nf hP

theorem upper_kantor_anomaly_corner {P : B} (hP : P * P = P)
    (A C Z : B) :
    P * opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C) * (1 - P) =
      opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C) ∧
    opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C) *
      opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C) = 0 := by
  constructor <;> simp only [opKantorAnomaly, conePlus, coneMinus] <;> peirce_nf hP

theorem lower_kantor_anomaly_corner {P : B} (hP : P * P = P)
    (A C Z : B) :
    (1 - P) * opKantorAnomaly (coneMinus P A) (coneMinus P Z) (conePlus P C) * P =
      opKantorAnomaly (coneMinus P A) (coneMinus P Z) (conePlus P C) ∧
    opKantorAnomaly (coneMinus P A) (coneMinus P Z) (conePlus P C) *
      opKantorAnomaly (coneMinus P A) (coneMinus P Z) (conePlus P C) = 0 := by
  constructor <;> simp only [opKantorAnomaly, conePlus, coneMinus] <;> peirce_nf hP

/-- Pairing the upper skew triple with its reference lower corner gives
the commutator of the two associated upper-corner products. -/
theorem upper_anomaly_reference_pairing {P : B} (hP : P * P = P)
    (A C Z : B) :
    opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C) * coneMinus P C =
      comm (qgtPlus P A C) (qgtPlus P Z C) := by
  simp only [opKantorAnomaly, comm, qgtPlus, conePlus, coneMinus]
  peirce_nf hP

/-- Pairing on the left yields the commutator of the lower-corner products.
The order of the two arguments is unchanged; there is no extra minus sign. -/
theorem upper_anomaly_left_reference_pairing (P A C Z : B) :
    coneMinus P C * upperHomotopeBracket P C A Z =
      comm (qgtMinus P A C) (qgtMinus P Z C) := by
  simp only [upperHomotopeBracket, opKantorAnomaly, comm, qgtMinus]
  noncomm_ring

/-- The lower reference corner intertwines the upper and lower commutators.
No inverse or equivalence of the two corners is assumed. -/
theorem reference_corner_commutator_intertwines (P A C Z : B) :
    coneMinus P C * comm (qgtPlus P A C) (qgtPlus P Z C) =
      comm (qgtMinus P A C) (qgtMinus P Z C) * coneMinus P C := by
  simp only [comm, qgtPlus, qgtMinus]
  noncomm_ring

/-- Defect iteration preserves the orthogonal Peirce separation of the two
corner commutators, while the reference cone transports every lower iterate
to its matching upper iterate. -/
theorem reference_corner_commutator_defect_orbits {P : B} (hP : P * P = P)
    (A C Z : B) (n m : ℕ) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
        (comm (qgtPlus P A C) (qgtPlus P Z C)) *
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m]
        (comm (qgtMinus P A C) (qgtMinus P Z C)) = 0 ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m]
        (comm (qgtMinus P A C) (qgtMinus P Z C)) *
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
        (comm (qgtPlus P A C) (qgtPlus P Z C)) = 0 ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
        (comm (qgtMinus P A C) (qgtMinus P Z C)) * coneMinus P C =
      coneMinus P C * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
        (comm (qgtPlus P A C) (qgtPlus P Z C)) := by
  let upper := comm (qgtPlus P A C) (qgtPlus P Z C)
  let lower := comm (qgtMinus P A C) (qgtMinus P Z C)
  have hUpperLeft : P * upper = upper := by
    simp only [upper, comm, qgtPlus, conePlus, coneMinus]
    peirce_nf hP
  have hUpperRight : upper * P = upper := by
    simp only [upper, comm, qgtPlus, conePlus, coneMinus]
    peirce_nf hP
  have hLowerLeft : (1 - P) * lower = lower := by
    simp only [lower, comm, qgtMinus, conePlus, coneMinus]
    peirce_nf hP
  have hLowerRight : lower * (1 - P) = lower := by
    simp only [lower, comm, qgtMinus, conePlus, coneMinus]
    peirce_nf hP
  have hUpperLowerCut : P * (1 - P) = 0 := by simp [mul_sub, hP]
  have hLowerUpperCut : (1 - P) * P = 0 := by simp [sub_mul, hP]
  have hUpperIterLeft (k : ℕ) :
      P * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] upper =
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] upper :=
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_iterates_left_support
      hUpperLeft k
  have hUpperIterRight (k : ℕ) :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] upper * P =
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] upper :=
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_iterates_right_support
      hUpperRight k
  have hLowerIterLeft (k : ℕ) :
      (1 - P) * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] lower =
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] lower :=
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_iterates_left_support
      hLowerLeft k
  have hLowerIterRight (k : ℕ) :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] lower * (1 - P) =
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] lower :=
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_iterates_right_support
      hLowerRight k
  have hUpperLowerZero :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] upper *
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m] lower = 0 := by
    have hCut : P * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m] lower = 0 := by
      calc
        _ = P * ((1 - P) * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m] lower) := by
          exact congrArg (P * ·) (hLowerIterLeft m).symm
        _ = (P * (1 - P)) *
            InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m] lower := by
          rw [← mul_assoc]
        _ = 0 := by rw [hUpperLowerCut, zero_mul]
    calc
      _ = (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] upper * P) *
          InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m] lower := by
        rw [hUpperIterRight n]
      _ = InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] upper *
          (P * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m] lower) := by
        rw [mul_assoc]
      _ = 0 := by rw [hCut, mul_zero]
  have hLowerUpperZero :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m] lower *
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] upper = 0 := by
    have hCut : (1 - P) * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] upper = 0 := by
      calc
        _ = (1 - P) * (P * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] upper) := by
          exact congrArg ((1 - P) * ·) (hUpperIterLeft n).symm
        _ = ((1 - P) * P) *
            InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] upper := by
          rw [← mul_assoc]
        _ = 0 := by rw [hLowerUpperCut, zero_mul]
    calc
      _ = (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m] lower * (1 - P)) *
          InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] upper := by
        rw [hLowerIterRight m]
      _ = InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[m] lower *
          ((1 - P) * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n] upper) := by
        rw [mul_assoc]
      _ = 0 := by rw [hCut, mul_zero]
  have hBase : lower * coneMinus P C = coneMinus P C * upper :=
    (reference_corner_commutator_intertwines P A C Z).symm
  have hOrbit (k : ℕ) :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] lower * coneMinus P C =
        coneMinus P C * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[k] upper := by
    induction k with
    | zero => exact hBase
    | succ k ih =>
        simpa only [Function.iterate_succ_apply'] using
          InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_intertwines ih
  exact ⟨hUpperLowerZero, hLowerUpperZero, hOrbit n⟩

/-! ## Skew tripotent Cayley completion

The split-complex relation `Ω² = -1` can be weakened to `Ω³ = -Ω`. The
resulting polynomial `1 + Ω²` is an idempotent support, and the corrected
Cartan element below is an involution without division. -/

/-- Polynomial Peirce supports associated to a skew-tripoten­t. -/
def quaternionSupport (Ω : B) : B := -(Ω * Ω)

def anisotropicSupport (Ω : B) : B := 1 + Ω * Ω

/-- The division-free involution obtained from `J` and a skew-tripoten­t. -/
def tripotentCayleyInvolution (J Ω : B) : B :=
  J * Ω + J * (1 + Ω * Ω)

/-- The Cayley numerator and its polynomial companion multiply to `2`. -/
theorem skewTripotent_cayley_product (Ω : B) (hΩ : Ω * Ω * Ω = -Ω) :
    (1 + Ω) * (2 - Ω + Ω * Ω) = 2 := by
  have htwo : (2 : B) = 1 + 1 := by norm_num
  calc
    (1 + Ω) * (2 - Ω + Ω * Ω) = 2 + Ω + Ω * Ω * Ω := by
      noncomm_ring
      norm_num
      ac_rfl
    _ = 2 := by rw [hΩ, htwo]; abel

/-- The polynomial `-Ω²` is idempotent when `Ω³ = -Ω`. -/
theorem quaternionSupport_idempotent (Ω : B)
    (hΩ : Ω * Ω * Ω = -Ω) :
    quaternionSupport Ω * quaternionSupport Ω = quaternionSupport Ω := by
  have hΩ4 : Ω * Ω * Ω * Ω = -(Ω * Ω) := by
    calc
      Ω * Ω * Ω * Ω = Ω * (Ω * Ω * Ω) := by noncomm_ring
      _ = Ω * (-Ω) := by rw [hΩ]
      _ = -(Ω * Ω) := by noncomm_ring
  have hΩ4' : (Ω * Ω) * (Ω * Ω) = -(Ω * Ω) := by
    calc
      (Ω * Ω) * (Ω * Ω) = Ω * Ω * Ω * Ω := by noncomm_ring
      _ = -(Ω * Ω) := hΩ4
  simp only [quaternionSupport]
  calc
    -(Ω * Ω) * -(Ω * Ω) = (Ω * Ω) * (Ω * Ω) := by noncomm_ring
    _ = -(Ω * Ω) := hΩ4'

/-- The complementary polynomial `1+Ω²` is idempotent and orthogonal to
`-Ω²`; their sum is the unit. -/
theorem skewTripotent_orthogonal_supports (Ω : B)
    (hΩ : Ω * Ω * Ω = -Ω) :
    quaternionSupport Ω * quaternionSupport Ω = quaternionSupport Ω ∧
    anisotropicSupport Ω * anisotropicSupport Ω = anisotropicSupport Ω ∧
    quaternionSupport Ω * anisotropicSupport Ω = 0 ∧
    anisotropicSupport Ω * quaternionSupport Ω = 0 ∧
    quaternionSupport Ω + anisotropicSupport Ω = 1 := by
  have hΩ4 : Ω * Ω * Ω * Ω = -(Ω * Ω) := by
    calc
      Ω * Ω * Ω * Ω = Ω * (Ω * Ω * Ω) := by noncomm_ring
      _ = Ω * (-Ω) := by rw [hΩ]
      _ = -(Ω * Ω) := by noncomm_ring
  have hΩ4' : (Ω * Ω) * (Ω * Ω) = -(Ω * Ω) := by
    calc
      (Ω * Ω) * (Ω * Ω) = Ω * Ω * Ω * Ω := by noncomm_ring
      _ = -(Ω * Ω) := hΩ4
  refine ⟨quaternionSupport_idempotent Ω hΩ, ?_, ?_, ?_, ?_⟩
  · simp only [anisotropicSupport, add_mul, mul_add, one_mul, mul_one]
    rw [hΩ4']
    abel
  · simp only [quaternionSupport, anisotropicSupport, neg_mul, mul_add, mul_one]
    rw [hΩ4']
    abel
  · simp only [anisotropicSupport, quaternionSupport, add_mul, mul_neg, one_mul]
    rw [hΩ4']
    abel
  · simp [quaternionSupport, anisotropicSupport]

/-- Under the split-quaternion anticommutation relation, the corrected
tripotent Cayley element is an involution over every ring. -/
theorem skewTripotent_cayley_involution (J Ω : B)
    (hJ : J * J = 1) (hΩ : Ω * Ω * Ω = -Ω)
    (hJΩ : J * Ω + Ω * J = 0) :
    tripotentCayleyInvolution J Ω * tripotentCayleyInvolution J Ω = 1 := by
  have hΩJ : Ω * J = -(J * Ω) := by
    calc
      Ω * J = (J * Ω + Ω * J) - J * Ω := by noncomm_ring
      _ = -(J * Ω) := by rw [hJΩ]; noncomm_ring
  have hJΩ' : J * Ω = -(Ω * J) := by
    calc
      J * Ω = (J * Ω + Ω * J) - Ω * J := by noncomm_ring
      _ = -(Ω * J) := by rw [hJΩ]; noncomm_ring
  have hJΩJ : J * Ω * J = -Ω := by
    calc
      J * Ω * J = -(Ω * J) * J := by rw [hJΩ']
      _ = -(Ω * (J * J)) := by
        rw [neg_mul]
        exact congrArg Neg.neg (mul_assoc Ω J J)
      _ = -Ω := by rw [hJ, mul_one]
  have hJΩ2 : J * Ω * Ω = Ω * Ω * J := by
    calc
      J * Ω * Ω = -(Ω * J) * Ω := by rw [hΩJ]; noncomm_ring
      _ = -(Ω * (J * Ω)) := by noncomm_ring
      _ = -(Ω * (-(Ω * J))) := by rw [hJΩ']
      _ = Ω * Ω * J := by noncomm_ring
  have hJΩ2' : J * (Ω * Ω) = Ω * Ω * J := by
    calc
      J * (Ω * Ω) = J * Ω * Ω := by noncomm_ring
      _ = Ω * Ω * J := hJΩ2
  have hΩ4 : Ω * Ω * Ω * Ω = -(Ω * Ω) := by
    calc
      Ω * Ω * Ω * Ω = Ω * (Ω * Ω * Ω) := by noncomm_ring
      _ = Ω * (-Ω) := by rw [hΩ]
      _ = -(Ω * Ω) := by noncomm_ring
  have hJΩ2J : J * (Ω * Ω) * J = Ω * Ω := by
    calc
      J * (Ω * Ω) * J = (Ω * Ω * J) * J := by rw [hJΩ2']
      _ = Ω * Ω * (J * J) := by noncomm_ring
      _ = Ω * Ω := by rw [hJ, mul_one]
  have hJqJ : J * (1 + Ω + Ω * Ω) * J = 1 - Ω + Ω * Ω := by
    simp only [add_mul, mul_add, one_mul, mul_one]
    rw [hJ, hJΩJ, hJΩ2J]
    abel
  have hΩ4' : (Ω * Ω) * (Ω * Ω) = -(Ω * Ω) := by
    calc
      (Ω * Ω) * (Ω * Ω) = Ω * Ω * Ω * Ω := by noncomm_ring
      _ = -(Ω * Ω) := hΩ4
  have hΩ4assoc : Ω * (Ω * (Ω * Ω)) = -(Ω * Ω) := by
    calc
      Ω * (Ω * (Ω * Ω)) = (Ω * Ω) * (Ω * Ω) := by noncomm_ring
      _ = -(Ω * Ω) := hΩ4'
  have hqprod : (1 - Ω + Ω * Ω) * (1 + Ω + Ω * Ω) = 1 := by
    noncomm_ring
    rw [hΩ4assoc]
    abel
  have hTform : tripotentCayleyInvolution J Ω = J * (1 + Ω + Ω * Ω) := by
    simp only [tripotentCayleyInvolution, add_mul]
    noncomm_ring
  rw [hTform]
  calc
    J * (1 + Ω + Ω * Ω) * (J * (1 + Ω + Ω * Ω)) =
        (J * (1 + Ω + Ω * Ω) * J) * (1 + Ω + Ω * Ω) := by noncomm_ring
    _ = 1 := by rw [hJqJ, hqprod]


/-- A cyclic additive functional annihilates the left reference pairing. -/
theorem upper_anomaly_left_reference_pairing_trace_zero
    {R : Type*} [AddCommGroup R] (τ : B →+ R)
    (hcyc : ∀ X Y : B, τ (X * Y) = τ (Y * X)) (P A C Z : B) :
    τ (coneMinus P C * upperHomotopeBracket P C A Z) = 0 := by
  rw [upper_anomaly_left_reference_pairing]
  change τ (qgtMinus P A C * qgtMinus P Z C - qgtMinus P Z C * qgtMinus P A C) = 0
  rw [map_sub, hcyc, sub_self]

/-- Sandwiching the upper homotope bracket between lower-corner elements
produces an element supported in the lower Peirce corner. This is a corner
statement, not an identification with a Zorn cross product. -/
theorem upper_anomaly_lower_sandwich_corner {P : B} (hP : P * P = P)
    (A C Z : B) :
    (1 - P) * (coneMinus P C * upperHomotopeBracket P C A Z * coneMinus P C) * P =
      coneMinus P C * upperHomotopeBracket P C A Z * coneMinus P C := by
  simp only [upperHomotopeBracket, opKantorAnomaly, conePlus, coneMinus]
  peirce_nf hP

/-- Any two such lower-corner sandwiches annihilate in this order, including
when their upper inputs and lower reference elements differ. -/
theorem upper_anomaly_lower_sandwich_mul_zero {P : B} (hP : P * P = P)
    (A C Z A' C' Z' : B) :
    (coneMinus P C * upperHomotopeBracket P C A Z * coneMinus P C) *
      (coneMinus P C' * upperHomotopeBracket P C' A' Z' * coneMinus P C') = 0 := by
  let X := coneMinus P C * upperHomotopeBracket P C A Z * coneMinus P C
  let Y := coneMinus P C' * upperHomotopeBracket P C' A' Z' * coneMinus P C'
  have hX : coneMinus P X = X := upper_anomaly_lower_sandwich_corner hP A C Z
  have hY : coneMinus P Y = Y := upper_anomaly_lower_sandwich_corner hP A' C' Z'
  change X * Y = 0
  calc
    X * Y = coneMinus P X * coneMinus P Y := by rw [hX, hY]
    _ = 0 := coneMinus_mul_coneMinus hP X Y

/-- The same lower-corner sandwich has grading eigenvalue minus two. -/
theorem upper_anomaly_lower_sandwich_grading {P : B} (hP : P * P = P)
    (A C Z : B) :
    comm (invS P) (coneMinus P C * upperHomotopeBracket P C A Z * coneMinus P C) =
      -((2 : ℤ) • (coneMinus P C * upperHomotopeBracket P C A Z * coneMinus P C)) := by
  simp only [upperHomotopeBracket, opKantorAnomaly, conePlus, coneMinus]
  peirce_nf hP

/-- The skew triple has the grading charge of the corner in which it lies. -/
theorem kantor_corner_anomaly_grading {P : B} (hP : P * P = P)
    (A C Z : B) :
    comm (invS P) (opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C)) =
      (2 : ℤ) • opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C) ∧
    comm (invS P) (opKantorAnomaly (coneMinus P A) (coneMinus P Z) (conePlus P C)) =
      -((2 : ℤ) • opKantorAnomaly (coneMinus P A) (coneMinus P Z) (conePlus P C)) := by
  constructor <;> simp only [opKantorAnomaly, comm, invS, conePlus, coneMinus] <;> peirce_nf hP

/-- An upper skew triple followed by any lower-corner element is neutral
for the Peirce grading. -/
theorem upper_anomaly_lower_pair_neutral {P : B} (hP : P * P = P)
    (A C Z W : B) :
    comm (invS P)
      (opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C) * coneMinus P W) = 0 := by
  simp only [opKantorAnomaly, comm, invS, conePlus, coneMinus]
  peirce_nf hP

/-- A cyclic additive functional annihilates the reference-paired triple. -/
theorem upper_anomaly_reference_pairing_trace_zero
    {R : Type*} [AddCommGroup R] (τ : B →+ R)
    (hcyc : ∀ X Y : B, τ (X * Y) = τ (Y * X))
    {P : B} (hP : P * P = P) (A C Z : B) :
    τ (opKantorAnomaly (conePlus P A) (conePlus P Z) (coneMinus P C) * coneMinus P C) = 0 := by
  rw [upper_anomaly_reference_pairing hP]
  change τ (qgtPlus P A C * qgtPlus P Z C - qgtPlus P Z C * qgtPlus P A C) = 0
  rw [map_sub, hcyc, sub_self]

/-- The reference-paired triples obey Jacobi after a further commutator
with the third upper-corner product. -/
theorem upper_anomaly_reference_pairing_jacobi {P : B} (hP : P * P = P)
    (A₁ A₂ A₃ C : B) :
    comm (opKantorAnomaly (conePlus P A₁) (conePlus P A₂) (coneMinus P C) * coneMinus P C)
        (qgtPlus P A₃ C) +
      comm (opKantorAnomaly (conePlus P A₂) (conePlus P A₃) (coneMinus P C) * coneMinus P C)
        (qgtPlus P A₁ C) +
      comm (opKantorAnomaly (conePlus P A₃) (conePlus P A₁) (coneMinus P C) * coneMinus P C)
        (qgtPlus P A₂ C) = 0 := by
  rw [upper_anomaly_reference_pairing hP, upper_anomaly_reference_pairing hP,
    upper_anomaly_reference_pairing hP]
  unfold comm
  noncomm_ring

/-- The cyclic contraction of three upper corners through a fixed lower corner
is the alternating degree-three polynomial in their ordered corner products.
No identification with a color representation or determinant is asserted. -/
theorem upper_anomaly_cyclic_contraction (P : B)
    (A₁ A₂ A₃ C : B) :
    conePlus P A₁ * (coneMinus P C *
      upperHomotopeBracket P C A₂ A₃ * coneMinus P C) +
    conePlus P A₂ * (coneMinus P C *
      upperHomotopeBracket P C A₃ A₁ * coneMinus P C) +
    conePlus P A₃ * (coneMinus P C *
      upperHomotopeBracket P C A₁ A₂ * coneMinus P C) =
    qgtPlus P A₁ C * qgtPlus P A₂ C * qgtPlus P A₃ C -
    qgtPlus P A₁ C * qgtPlus P A₃ C * qgtPlus P A₂ C +
    qgtPlus P A₂ C * qgtPlus P A₃ C * qgtPlus P A₁ C -
    qgtPlus P A₂ C * qgtPlus P A₁ C * qgtPlus P A₃ C +
    qgtPlus P A₃ C * qgtPlus P A₁ C * qgtPlus P A₂ C -
    qgtPlus P A₃ C * qgtPlus P A₂ C * qgtPlus P A₁ C := by
  simp only [upperHomotopeBracket, opKantorAnomaly, qgtPlus]
  noncomm_ring

/-- The cyclic contraction is supported in the upper diagonal corner.
This support statement does not assert color-singlet invariance. -/
theorem upper_anomaly_cyclic_contraction_corner {P : B} (hP : P * P = P)
    (A₁ A₂ A₃ C : B) :
    P * (conePlus P A₁ * (coneMinus P C * upperHomotopeBracket P C A₂ A₃ * coneMinus P C) +
      conePlus P A₂ * (coneMinus P C * upperHomotopeBracket P C A₃ A₁ * coneMinus P C) +
      conePlus P A₃ * (coneMinus P C * upperHomotopeBracket P C A₁ A₂ * coneMinus P C)) * P =
    conePlus P A₁ * (coneMinus P C * upperHomotopeBracket P C A₂ A₃ * coneMinus P C) +
      conePlus P A₂ * (coneMinus P C * upperHomotopeBracket P C A₃ A₁ * coneMinus P C) +
      conePlus P A₃ * (coneMinus P C * upperHomotopeBracket P C A₁ A₂ * coneMinus P C) := by
  simp only [upperHomotopeBracket, opKantorAnomaly, conePlus, coneMinus]
  peirce_nf hP

/-- The cyclic contraction has zero Peirce grading charge. This follows from
its diagonal-corner support, without any color-group assumptions. -/
theorem upper_anomaly_cyclic_contraction_neutral {P : B} (hP : P * P = P)
    (A₁ A₂ A₃ C : B) :
    comm (invS P)
      (conePlus P A₁ * (coneMinus P C * upperHomotopeBracket P C A₂ A₃ * coneMinus P C) +
       conePlus P A₂ * (coneMinus P C * upperHomotopeBracket P C A₃ A₁ * coneMinus P C) +
       conePlus P A₃ * (coneMinus P C * upperHomotopeBracket P C A₁ A₂ * coneMinus P C)) = 0 := by
  have hcorner := upper_anomaly_cyclic_contraction_corner hP A₁ A₂ A₃ C
  conv_lhs => arg 2; rw [← hcorner]
  peirce_nf hP

/-- The cyclic contraction admits the opposite ordering: each commutator of
upper-corner products can be placed to the left of the remaining product. -/
theorem upper_anomaly_cyclic_contraction_right (P A₁ A₂ A₃ C : B) :
    conePlus P A₁ * (coneMinus P C * upperHomotopeBracket P C A₂ A₃ * coneMinus P C) +
      conePlus P A₂ * (coneMinus P C * upperHomotopeBracket P C A₃ A₁ * coneMinus P C) +
      conePlus P A₃ * (coneMinus P C * upperHomotopeBracket P C A₁ A₂ * coneMinus P C) =
    comm (qgtPlus P A₂ C) (qgtPlus P A₃ C) * qgtPlus P A₁ C +
      comm (qgtPlus P A₃ C) (qgtPlus P A₁ C) * qgtPlus P A₂ C +
      comm (qgtPlus P A₁ C) (qgtPlus P A₂ C) * qgtPlus P A₃ C := by
  rw [upper_anomaly_cyclic_contraction]
  unfold comm
  noncomm_ring

/-- Interchanging the first two inputs reverses the cyclic contraction.
This is algebraic alternation, not a fermionic-statistics assertion. -/
theorem upper_anomaly_cyclic_contraction_swap (P A₁ A₂ A₃ C : B) :
    (conePlus P A₂ * (coneMinus P C * upperHomotopeBracket P C A₁ A₃ * coneMinus P C) +
      conePlus P A₁ * (coneMinus P C * upperHomotopeBracket P C A₃ A₂ * coneMinus P C) +
      conePlus P A₃ * (coneMinus P C * upperHomotopeBracket P C A₂ A₁ * coneMinus P C)) =
    -(conePlus P A₁ * (coneMinus P C * upperHomotopeBracket P C A₂ A₃ * coneMinus P C) +
      conePlus P A₂ * (coneMinus P C * upperHomotopeBracket P C A₃ A₁ * coneMinus P C) +
      conePlus P A₃ * (coneMinus P C * upperHomotopeBracket P C A₁ A₂ * coneMinus P C)) := by
  rw [upper_anomaly_cyclic_contraction, upper_anomaly_cyclic_contraction]
  noncomm_ring

/-- The cyclic contraction vanishes when its first two inputs coincide.
The proof works even in characteristic two and does not divide by two. -/
theorem upper_anomaly_cyclic_contraction_repeat (P A Z C : B) :
    conePlus P A * (coneMinus P C * upperHomotopeBracket P C A Z * coneMinus P C) +
      conePlus P A * (coneMinus P C * upperHomotopeBracket P C Z A * coneMinus P C) +
      conePlus P Z * (coneMinus P C * upperHomotopeBracket P C A A * coneMinus P C) = 0 := by
  rw [upper_anomaly_cyclic_contraction]
  noncomm_ring

/-! ## Matrix realization of the ordered associative homotope

The corner multiplication below is represented inside the native matrix ring
over the original, possibly noncommutative coefficient ring. This preserves
the order of factors and makes the antisymmetric information observable. -/

/-- Upper-right embedding of a coefficient into the `2 × 2` matrix ring. -/
def associativeUpperCorner (x : B) : Matrix (Fin 2) (Fin 2) B :=
  !![0, x; 0, 0]

/-- Lower-left embedding used as the middle factor of the homotope. -/
def associativeLowerCorner (x : B) : Matrix (Fin 2) (Fin 2) B :=
  !![0, 0; x, 0]

/-- The upper-corner embedding is injective, so an ordered product recovered
in the matrix algebra retains the original coefficient exactly. -/
theorem associativeUpperCorner_injective :
    Function.Injective (associativeUpperCorner : B → Matrix (Fin 2) (Fin 2) B) := by
  intro x y h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 1) h
  simpa [associativeUpperCorner] using h01

/-- Ordered homotope recovery: upper × lower × upper realizes multiplication
in precisely the stated noncommutative order. -/
theorem associative_homotope_recovers_mul (x y : B) :
    associativeUpperCorner x * associativeLowerCorner (1 : B) *
        associativeUpperCorner y = associativeUpperCorner (x * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [associativeUpperCorner, associativeLowerCorner,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Reversing the two upper factors recovers the reverse product. -/
theorem associative_homotope_recovers_mul_reverse (x y : B) :
    associativeUpperCorner y * associativeLowerCorner (1 : B) *
        associativeUpperCorner x = associativeUpperCorner (y * x) :=
  associative_homotope_recovers_mul y x

/-- The antisymmetrized matrix homotope is exactly the embedded
noncommutative commutator. -/
theorem associative_homotope_recovers_commutator (x y : B) :
    associativeUpperCorner x * associativeLowerCorner (1 : B) *
        associativeUpperCorner y -
      associativeUpperCorner y * associativeLowerCorner (1 : B) *
        associativeUpperCorner x = associativeUpperCorner (x * y - y * x) := by
  rw [associative_homotope_recovers_mul, associative_homotope_recovers_mul_reverse]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [associativeUpperCorner]

/-- The symmetrized KKT product retains only the Jordan part of multiplication. -/
theorem associative_homotope_recovers_anticommutator (x y : B) :
    associativeUpperCorner x * associativeLowerCorner (1 : B) *
        associativeUpperCorner y +
      associativeUpperCorner y * associativeLowerCorner (1 : B) *
        associativeUpperCorner x = associativeUpperCorner (x * y + y * x) := by
  rw [associative_homotope_recovers_mul, associative_homotope_recovers_mul_reverse]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [associativeUpperCorner]

/-- On anticommuting coefficients the symmetrized homotope vanishes, while
the ordered homotope remains the embedded product. -/
theorem associative_homotope_anticommuting_readout (x y : B)
    (hxy : x * y = -(y * x)) :
    (associativeUpperCorner x * associativeLowerCorner (1 : B) *
        associativeUpperCorner y +
      associativeUpperCorner y * associativeLowerCorner (1 : B) *
        associativeUpperCorner x = 0) ∧
    (associativeUpperCorner x * associativeLowerCorner (1 : B) *
        associativeUpperCorner y = associativeUpperCorner (x * y)) := by
  constructor
  · rw [associative_homotope_recovers_anticommutator]
    rw [hxy]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [associativeUpperCorner]
  · exact associative_homotope_recovers_mul x y

/-- The three-graded matrix commutator recovers the KKT triple product in
its ordered noncommutative form. The middle argument is the lower-left
matrix corner; no symmetrization or commutative coefficient assumption is
used. -/
theorem associative_matrix_kkt_triple_product (x y z : B) :
    (associativeUpperCorner x * associativeLowerCorner y -
        associativeLowerCorner y * associativeUpperCorner x) *
        associativeUpperCorner z -
      associativeUpperCorner z *
        (associativeUpperCorner x * associativeLowerCorner y -
          associativeLowerCorner y * associativeUpperCorner x) =
      associativeUpperCorner (x * y * z + z * y * x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [associativeUpperCorner, associativeLowerCorner,
      Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

/-! ## The corrected Peirce Walsh operator

This superoperator keeps the operator order in `K * X * K + J * X`.  The
identities below use only the Cl(1,1) relations and hold in a possibly
noncommutative coefficient ring. -/

/-- The ordered Walsh-type superoperator associated to a Cl(1,1) pair. -/
def peirceWalshOperator (J Ω X : B) : B :=
  (J * Ω) * X * (J * Ω) + J * X

/-- The algebraic relations needed to square the Walsh operator. -/
theorem peirceWalshOperator_square (J Ω X : B)
    (hJ : J * J = 1) (hΩ : Ω * Ω = -1)
    (hanticomm : J * Ω + Ω * J = 0) :
    peirceWalshOperator J Ω (peirceWalshOperator J Ω X) = 2 • X := by
  have hΩJ : Ω * J = -(J * Ω) := by
    calc
      Ω * J = (J * Ω + Ω * J) - J * Ω := by abel
      _ = -(J * Ω) := by rw [hanticomm, zero_sub]
  let K := J * Ω
  have hK2 : K * K = 1 := by
    dsimp [K]
    calc
      (J * Ω) * (J * Ω) = J * (Ω * J) * Ω := by noncomm_ring
      _ = J * (-(J * Ω)) * Ω := by rw [hΩJ]
      _ = 1 := by simp [mul_assoc, hJ, hΩ]
  have hcross : K * J + J * K = 0 := by
    dsimp [K]
    calc
      (J * Ω) * J + J * (J * Ω) = J * (Ω * J) + (J * J) * Ω := by
        noncomm_ring
      _ = J * (-(J * Ω)) + 1 * Ω := by rw [hΩJ, hJ]
      _ = 0 := by
        calc
          J * (-(J * Ω)) + 1 * Ω = J * (-(J * Ω)) + Ω := by simp
          _ = -(J * (J * Ω)) + Ω := by rw [mul_neg]
          _ = -((J * J) * Ω) + Ω := by congr 1; noncomm_ring
          _ = 0 := by rw [hJ]; simp
  change K * (K * X * K + J * X) * K + J * (K * X * K + J * X) = 2 • X
  calc
    K * (K * X * K + J * X) * K + J * (K * X * K + J * X) =
        (K * K) * X * (K * K) + (K * J + J * K) * X * K + (J * J) * X := by
      noncomm_ring
    _ = X + X := by rw [hK2, hcross, hJ]; simp
    _ = 2 • X := by abel

/-- The first four Walsh outputs, with the signs fixed by the operator-order
definition rather than inferred from a mnemonic gate name. -/
theorem peirceWalshOperator_basis (J Ω : B)
    (hJ : J * J = 1) (hΩ : Ω * Ω = -1)
    (hanticomm : J * Ω + Ω * J = 0) :
    peirceWalshOperator J Ω 1 = 1 + J ∧
    peirceWalshOperator J Ω J = 1 - J ∧
    peirceWalshOperator J Ω (J * Ω) = J * Ω + Ω ∧
    peirceWalshOperator J Ω Ω = J * Ω - Ω := by
  have hΩJ : Ω * J = -(J * Ω) := by
    calc
      Ω * J = (J * Ω + Ω * J) - J * Ω := by abel
      _ = -(J * Ω) := by rw [hanticomm, zero_sub]
  have hK2 : (J * Ω) * (J * Ω) = 1 := by
    calc
      (J * Ω) * (J * Ω) = J * (Ω * J) * Ω := by noncomm_ring
      _ = J * (-(J * Ω)) * Ω := by rw [hΩJ]
      _ = 1 := by simp [mul_assoc, hJ, hΩ]
  have hKJ : (J * Ω) * J = -Ω := by
    calc
      (J * Ω) * J = J * (Ω * J) := by noncomm_ring
      _ = J * (-(J * Ω)) := by rw [hΩJ]
      _ = -Ω := by
        calc
          J * (-(J * Ω)) = -(J * (J * Ω)) := by rw [mul_neg]
          _ = -Ω := by rw [← mul_assoc, hJ, one_mul]
  have hJK : J * (J * Ω) = Ω := by
    calc
      J * (J * Ω) = (J * J) * Ω := by noncomm_ring
      _ = Ω := by rw [hJ, one_mul]
  have hOmegaK : Ω * (J * Ω) = J := by
    calc
      Ω * (J * Ω) = (Ω * J) * Ω := by noncomm_ring
      _ = -(J * Ω) * Ω := by rw [hΩJ]
      _ = J := by
        calc
          -(J * Ω) * Ω = -((J * Ω) * Ω) := by rw [neg_mul]
          _ = -(J * (Ω * Ω)) := by congr 1; noncomm_ring
          _ = J := by rw [hΩ]; simp
  have hKJK : (J * Ω) * J * (J * Ω) = -J := by
    calc
      (J * Ω) * J * (J * Ω) = -Ω * (J * Ω) := by rw [hKJ]
      _ = -J := by rw [neg_mul, hOmegaK]
  have hKΩK : (J * Ω) * Ω * (J * Ω) = -Ω := by
    calc
      (J * Ω) * Ω * (J * Ω) = J * (Ω * Ω) * (J * Ω) := by noncomm_ring
      _ = -Ω := by
        rw [hΩ]
        calc
          J * -1 * (J * Ω) = -(J * (J * Ω)) := by noncomm_ring
          _ = -Ω := by rw [hJK]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [peirceWalshOperator, hK2]
  · change (J * Ω) * J * (J * Ω) + J * J = 1 - J
    rw [hKJK, hJ]
    abel
  · change (J * Ω) * (J * Ω) * (J * Ω) + J * (J * Ω) = J * Ω + Ω
    rw [hK2, hJK]
    simp
  · change (J * Ω) * Ω * (J * Ω) + J * Ω = J * Ω - Ω
    rw [hKΩK]
    abel

section MatrixWitness

/-- The `2 × 2` homotope matrix algebra is genuinely noncommutative over every
nontrivial coefficient ring. -/
theorem matTwo_homotope_noncommute [Nontrivial B] :
    ∃ matI matJ : Matrix (Fin 2) (Fin 2) B,
      matI * matJ ≠ matJ * matI := by
  refine ⟨!![(0 : B), 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end MatrixWitness

end InfoGeometry.OperatorAlgebra.PeirceSpine
