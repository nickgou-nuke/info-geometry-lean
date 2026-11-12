/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarMetricNondegeneracy
import Mathlib.Algebra.Star.Unitary

/-!
# Adjoint defects of the unipotent Peirce daughter

The existing upper chart uses `(1+N) P (1-N) = P-N`. Its adjoint defect
and Gram defect are computed in the original noncommutative star ring.
The opposite conjugation has the opposite sign. Self-adjoint or
skew-adjoint amplitudes remove the selected corner's commutator blind spot.
Proper star pairing then detects zero Gram coupling, not injectivity or a
uniform spectral bound. No bundle transition cocycle is assumed or built.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Reversing the upper shear reverses the sign of its daughter. -/
theorem conjPlusInv_cut {P : B} (hP : P * P = P) (A : B) :
    conjPlusInv P A P = P + conePlus P A := by
  simp only [conjPlusInv]
  peirce_nf hP

section Star

variable [StarRing B] {P : B}

/-- The star defect of the existing upper chart is the skew generator. -/
theorem projChartPlus_star_defect (hPs : star P = P) (A : B) :
    star (projChartPlus P A) - projChartPlus P A = genJ P A (star A) := by
  simp only [projChartPlus, star_sub, hPs, star_conePlus hPs, genJ]
  abel

/-- A self-adjoint upper daughter must have zero upper corner, even
without an order, a norm, or properness of the star pairing. -/
theorem projChartPlus_isSelfAdjoint_iff
    (hP : P * P = P) (hPs : star P = P) (A : B) :
    IsSelfAdjoint (projChartPlus P A) ↔ conePlus P A = 0 := by
  constructor
  · intro h
    have hJ : genJ P A (star A) = 0 := by
      rw [← projChartPlus_star_defect hPs A, h.star_eq, sub_self]
    have hread := congrArg (fun X : B => P * X) hJ
    simpa only [genJ, mul_sub, P_mul_conePlus hP,
      P_mul_coneMinus hP, sub_zero, mul_zero] using hread
  · intro h
    simpa only [projChartPlus, h, sub_zero] using (show IsSelfAdjoint P from hPs)

/-- The nontrivial upper shear is not unitary for a self-adjoint cut. -/
theorem one_add_conePlus_mem_unitary_iff
    (hP : P * P = P) (hPs : star P = P) (A : B) :
    1 + conePlus P A ∈ unitary B ↔ conePlus P A = 0 := by
  constructor
  · intro h
    calc
      conePlus P A =
          P * (star (1 + conePlus P A) * (1 + conePlus P A)) * (1 - P) := by
        simp only [star_add, star_one, star_conePlus hPs]
        peirce_nf hP
      _ = P * 1 * (1 - P) := by rw [Unitary.star_mul_self_of_mem h]
      _ = 0 := by peirce_nf hP
  · intro h
    simp [h]

/-- The daughter's Gram product keeps the upper-corner Gram term. -/
theorem projChartPlus_gram (hP : P * P = P) (hPs : star P = P) (A : B) :
    projChartPlus P A * star (projChartPlus P A) =
      P + conePlus P A * coneMinus P (star A) := by
  simp only [projChartPlus, star_sub, hPs, star_conePlus hPs]
  peirce_nf hP

/-- Squaring the Gram product gives its exact idempotency defect. -/
theorem projChartPlus_gram_defect
    (hP : P * P = P) (hPs : star P = P) (A : B) :
    (projChartPlus P A * star (projChartPlus P A)) ^ 2 -
        projChartPlus P A * star (projChartPlus P A) =
      (conePlus P A * coneMinus P (star A)) ^ 2 +
        conePlus P A * coneMinus P (star A) := by
  rw [projChartPlus_gram hP hPs A]
  simp only [pow_two]
  peirce_nf hP

/-- The Gram defect is an actual star square. This algebraic identity
does not presuppose that the star ring carries an order. -/
theorem projChartPlus_gram_defect_star_square
    (hP : P * P = P) (hPs : star P = P) (A : B) :
    (projChartPlus P A * star (projChartPlus P A)) ^ 2 -
        projChartPlus P A * star (projChartPlus P A) =
      (conePlus P A * coneMinus P (star A) + conePlus P A) *
        star (conePlus P A * coneMinus P (star A) + conePlus P A) := by
  rw [projChartPlus_gram_defect hP hPs A]
  simp only [star_add, star_mul, star_coneMinus hPs, star_conePlus hPs,
    star_star, pow_two]
  peirce_nf hP

/-- Properness detects the nonzero Gram defect of a nontrivial daughter. -/
theorem projChartPlus_gram_defect_eq_zero_iff
    (hP : P * P = P) (hPs : star P = P)
    (hproper : ∀ X : B, star X * X = 0 → X = 0) (A : B) :
    (projChartPlus P A * star (projChartPlus P A)) ^ 2 -
        projChartPlus P A * star (projChartPlus P A) = 0 ↔
      conePlus P A = 0 := by
  constructor
  · intro h
    rw [projChartPlus_gram_defect_star_square hP hPs A] at h
    have hz : conePlus P A * coneMinus P (star A) + conePlus P A = 0 := by
      have hs := hproper
        (star (conePlus P A * coneMinus P (star A) + conePlus P A))
        (by simpa only [star_star] using h)
      simpa only [star_star, star_zero] using congrArg star hs
    calc
      conePlus P A =
          (conePlus P A * coneMinus P (star A) + conePlus P A) * (1 - P) := by
        peirce_nf hP
      _ = 0 := by rw [hz, zero_mul]
  · intro h
    rw [projChartPlus_gram_defect hP hPs A]
    simp [h]

/-- Once the upper corner vanishes, star symmetry of the amplitude also
forces the lower corner to vanish. -/
theorem coneMinus_eq_zero_of_conePlus_eq_zero (hPs : star P = P)
    {A : B} (hA : star A = A ∨ star A = -A) (hN : conePlus P A = 0) :
    coneMinus P A = 0 := by
  have hstar := congrArg star hN
  rw [star_conePlus hPs, star_zero] at hstar
  rcases hA with hA | hA
  · simpa only [hA] using hstar
  · simpa only [hA, coneMinus_neg, neg_eq_zero] using hstar

/-- A self-adjoint or skew-adjoint amplitude has no one-sided blind spot. -/
theorem comm_cut_eq_zero_iff_conePlus_eq_zero
    (hP : P * P = P) (hPs : star P = P)
    {A : B} (hA : star A = A ∨ star A = -A) :
    comm P A = 0 ↔ conePlus P A = 0 := by
  have hsplit : comm P A = conePlus P A - coneMinus P A := by
    simp only [comm, conePlus, coneMinus]
    noncomm_ring
  constructor
  · intro h
    have hh := congrArg (fun X : B => P * X) h
    rw [hsplit, mul_sub, P_mul_conePlus hP, P_mul_coneMinus hP,
      sub_zero, mul_zero] at hh
    exact hh
  · intro h
    rw [hsplit, h, coneMinus_eq_zero_of_conePlus_eq_zero hPs hA h, sub_zero]

/-- The existing faithful Gram criterion now detects the entire cut
commutator, under the amplitude's explicit star relation. -/
theorem genV_eq_zero_iff_comm_cut_eq_zero
    (hP : P * P = P) (hPs : star P = P)
    (hproper : ∀ X : B, star X * X = 0 → X = 0)
    {A : B} (hA : star A = A ∨ star A = -A) :
    genV P A (star A) = 0 ↔ comm P A = 0 := by
  rw [StarMetricNondegeneracy.genV_eq_zero_iff_conePlus_eq_zero hP hPs hproper,
    comm_cut_eq_zero_iff_conePlus_eq_zero hP hPs hA]

end Star

end InfoGeometry.OperatorAlgebra.PeirceSpine
