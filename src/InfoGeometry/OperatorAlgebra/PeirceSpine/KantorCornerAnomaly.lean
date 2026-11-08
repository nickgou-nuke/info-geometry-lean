/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PositroidClusterTwistPoset
import InfoGeometry.Core.IdempotentDefectIteration

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

/-- The explicit ordered triple formula is exactly the existing upper
homotope bracket. -/
theorem upperHomotopeBracket_eq_upperCornerCrossProduct
    (P C A Z : B) :
    upperHomotopeBracket P C A Z = upperCornerCrossProduct P C A Z := rfl

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

/-- The lower ordered triple formula is the lower-corner instance of the same
associative Kantor skew anomaly. -/
theorem lowerCornerCrossProduct_eq_opKantorAnomaly (P A Y W : B) :
    lowerCornerCrossProduct P A Y W =
      opKantorAnomaly (coneMinus P Y) (coneMinus P W) (conePlus P A) := rfl

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

/-- The Lie pairing of the upper Kantor anomaly with its reference lower
corner is the mixed spin/metric commutator. The order is fixed by the two
corner pairings above. -/
theorem upper_anomaly_reference_commutator {P : B} (hP : P * P = P)
    (A C Z : B) :
    comm (upperHomotopeBracket P C A Z) (coneMinus P C) =
      comm (genSig P A C) (genV P Z C) := by
  simp only [upperHomotopeBracket, opKantorAnomaly, comm, genSig, genV,
    anticomm, conePlus, coneMinus]
  peirce_nf hP

/-- The Jordan pairing of the upper Kantor anomaly with its reference lower
corner is the commutator of the two uncertainty generators. -/
theorem upper_anomaly_reference_anticommutator {P : B} (hP : P * P = P)
    (A C Z : B) :
    anticomm (upperHomotopeBracket P C A Z) (coneMinus P C) =
      comm (genSig P A C) (genSig P Z C) := by
  simp only [upperHomotopeBracket, opKantorAnomaly, comm, anticomm,
    genSig, conePlus, coneMinus]
  peirce_nf hP

/-- The lower reference corner intertwines the upper and lower commutators.
No inverse or equivalence of the two corners is assumed. -/
theorem reference_corner_commutator_intertwines (P A C Z : B) :
    coneMinus P C * comm (qgtPlus P A C) (qgtPlus P Z C) =
      comm (qgtMinus P A C) (qgtMinus P Z C) * coneMinus P C := by
  simp only [comm, qgtPlus, qgtMinus]
  noncomm_ring

/-- Every finite idempotency-defect iterate of the two corner commutators
is intertwined by the same lower reference corner. -/
theorem reference_corner_commutator_defect_iterates (P A C Z : B) (n : ℕ) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
        (comm (qgtMinus P A C) (qgtMinus P Z C)) * coneMinus P C =
      coneMinus P C * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
        (comm (qgtPlus P A C) (qgtPlus P Z C)) := by
  exact InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_iterates_intertwines
    (reference_corner_commutator_intertwines P A C Z).symm n

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

end InfoGeometry.OperatorAlgebra.PeirceSpine
