/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.IndividuatedCayley
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Rational unitary transport of a Peirce cut

Invertibility of `1+V` constructs the inverse of `1-J`; it is not a field
assuming the desired Cayley result. For the adjoint-paired corners, the
existing generic starred-ring resolvent proves native unitary membership.
The resulting star-algebra automorphism transports the cut to a self-adjoint
idempotent with the exact rational formula. Only relative commutation of
`V` with the Peirce generators is used. No scalar normalization, square root,
ambient centrality, or analytic hypothesis is needed.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The rational Cayley value at the skew Peirce generator. -/
def peirceCayley (P A C : B) [Invertible (1 + genV P A C)] : B :=
  (1 - genV P A C + (2 : ℤ) • genJ P A C) * ⅟(1 + genV P A C)

section Ring

variable {P : B} (hP : P * P = P) (A C : B)

/-- The plus and minus factors of the skew generator multiply to `1+V`. -/
theorem cayley_factor_product :
    (1 - genJ P A C) * (1 + genJ P A C) = 1 + genV P A C := by
  peirce_nf hP

/-- The reversed factor order gives the same denominator. -/
theorem cayley_factor_product_rev :
    (1 + genJ P A C) * (1 - genJ P A C) = 1 + genV P A C := by
  peirce_nf hP

variable [Invertible (1 + genV P A C)]

/-- Construct the right inverse of `1-J` from the inverse of `1+V`. -/
theorem cayley_denominator_right_inverse :
    (1 - genJ P A C) *
      ((1 + genJ P A C) * ⅟(1 + genV P A C)) = 1 := by
  rw [← mul_assoc, cayley_factor_product hP A C, mul_invOf_self]

/-- Relative centrality constructs the left inverse as well. -/
theorem cayley_denominator_left_inverse :
    ((1 + genJ P A C) * ⅟(1 + genV P A C)) *
      (1 - genJ P A C) = 1 := by
  have hcomm : Commute (1 - genJ P A C) (1 + genV P A C) := by
    change (1 - genJ P A C) * (1 + genV P A C) =
      (1 + genV P A C) * (1 - genJ P A C)
    peirce_nf hP
  rw [mul_assoc, ← hcomm.invOf_right.eq, ← mul_assoc,
    cayley_factor_product_rev hP A C, mul_invOf_self]

/-- The displayed rational polynomial equals the actual Cayley numerator
times the constructed denominator inverse. -/
theorem peirceCayley_eq_product :
    peirceCayley P A C =
      (1 + genJ P A C) * ((1 + genJ P A C) * ⅟(1 + genV P A C)) := by
  have hnum : 1 - genV P A C + (2 : ℤ) • genJ P A C =
      (1 + genJ P A C) * (1 + genJ P A C) := by
    peirce_nf hP
  rw [peirceCayley, hnum, mul_assoc]

/-- The constructed rational value satisfies the defining Cayley equation. -/
theorem peirceCayley_mul_one_sub_genJ :
    peirceCayley P A C * (1 - genJ P A C) = 1 + genJ P A C := by
  rw [peirceCayley_eq_product hP A C, mul_assoc,
    cayley_denominator_left_inverse hP A C, mul_one]

end Ring

section Star

variable [StarRing B] {P : B} (hP : P * P = P) (hPs : star P = P)
variable (X : B) [Invertible (1 + genV P X (star X))]

/-- The existing generic resolvent proves unitarity after both inverse
fields have been constructed from the invertibility of `1+V`. -/
theorem peirceCayley_mem_unitary : peirceCayley P X (star X) ∈ unitary B := by
  let R : IndividuatedCayley.VerifiedUnitaryResolvent B (-genJ P X (star X)) 1 :=
    { denomInv := (1 + genJ P X (star X)) * ⅟(1 + genV P X (star X))
      denom_right := by
        simpa only [← sub_eq_add_neg] using cayley_denominator_right_inverse hP X (star X)
      denom_left := by
        simpa only [← sub_eq_add_neg] using cayley_denominator_left_inverse hP X (star X)
      D_phase_linear := by simp [IndividuatedCayley.PhaseLinear]
      D_selfAdjoint := by simp
      K_skewAdjoint := by rw [star_neg, star_genJ hPs] }
  rw [Unitary.mem_iff, peirceCayley_eq_product hP X (star X)]
  simpa only [IndividuatedCayley.boundedCayley,
    IndividuatedCayley.VerifiedUnitaryResolvent.toVerifiedPhaseResolvent,
    sub_neg_eq_add, R] using R.boundedCayley_is_unitary

/-- The adjoint has the opposite Cayley numerator and the same denominator. -/
theorem star_peirceCayley :
    star (peirceCayley P X (star X)) =
      (1 - genV P X (star X) - (2 : ℤ) • genJ P X (star X)) *
        ⅟(1 + genV P X (star X)) := by
  have hden : IsSelfAdjoint (1 + genV P X (star X)) := by
    change star (1 + genV P X (star X)) = 1 + genV P X (star X)
    rw [star_add, star_one, star_genV hPs]
  have hcomm : Commute (1 + genV P X (star X))
      (1 - genV P X (star X) - (2 : ℤ) • genJ P X (star X)) := by
    change (1 + genV P X (star X)) *
        (1 - genV P X (star X) - (2 : ℤ) • genJ P X (star X)) =
      (1 - genV P X (star X) - (2 : ℤ) • genJ P X (star X)) *
        (1 + genV P X (star X))
    peirce_nf hP
  simp only [peirceCayley, star_mul, hden.invOf.star_eq, star_add, star_sub,
    star_one, star_genV hPs, star_zsmul, star_genJ hPs, smul_neg, ← sub_eq_add_neg]
  exact hcomm.invOf_left.eq

/-- Conjugation by the constructed unitary is a native star-algebra
automorphism of the entire original ring, over its integer scalars. -/
def peirceCayleyAut : B ≃⋆ₐ[ℤ] B :=
  Unitary.conjStarAlgAut ℤ B ⟨peirceCayley P X (star X),
    peirceCayley_mem_unitary hP hPs X⟩

@[simp]
theorem peirceCayleyAut_apply (Y : B) :
    peirceCayleyAut hP hPs X Y =
      peirceCayley P X (star X) * Y * star (peirceCayley P X (star X)) := rfl

/-- The unitary transports the cut's actual idempotency. -/
theorem peirceCayley_conjugate_isIdempotent :
    IsIdempotentElem
      (peirceCayley P X (star X) * P * star (peirceCayley P X (star X))) :=
  (show IsIdempotentElem P from hP).map (peirceCayleyAut hP hPs X)

/-- Unitary transport retains self-adjointness of the cut. -/
theorem peirceCayley_conjugate_isSelfAdjoint :
    IsSelfAdjoint
      (peirceCayley P X (star X) * P * star (peirceCayley P X (star X))) :=
  (show IsSelfAdjoint P from hPs).conjugate _

/-- The exact rational daughter formula, including the sign of the mixed
term, holds without requiring that the ambient ring be commutative. -/
theorem peirceCayley_conjugate_cut :
    peirceCayley P X (star X) * P * star (peirceCayley P X (star X)) =
      ((1 - genV P X (star X)) ^ 2 * P +
        (4 : ℤ) • (genV P X (star X) * (1 - P)) -
        (2 : ℤ) • ((1 - genV P X (star X)) * genPhi P X (star X))) *
          (⅟(1 + genV P X (star X))) ^ 2 := by
  have hcut : Commute (1 + genV P X (star X)) P := by
    change (1 + genV P X (star X)) * P = P * (1 + genV P X (star X))
    peirce_nf hP
  have hnum : Commute (1 + genV P X (star X))
      (1 - genV P X (star X) - (2 : ℤ) • genJ P X (star X)) := by
    change (1 + genV P X (star X)) *
        (1 - genV P X (star X) - (2 : ℤ) • genJ P X (star X)) =
      (1 - genV P X (star X) - (2 : ℤ) • genJ P X (star X)) *
        (1 + genV P X (star X))
    peirce_nf hP
  have hpoly :
      (1 - genV P X (star X) + (2 : ℤ) • genJ P X (star X)) * P *
          (1 - genV P X (star X) - (2 : ℤ) • genJ P X (star X)) =
        (1 - genV P X (star X)) ^ 2 * P +
          (4 : ℤ) • (genV P X (star X) * (1 - P)) -
          (2 : ℤ) • ((1 - genV P X (star X)) * genPhi P X (star X)) := by
    simp only [pow_two]
    peirce_nf hP
  rw [star_peirceCayley hP hPs X, peirceCayley, ← hpoly, pow_two]
  let F := 1 - genV P X (star X) + (2 : ℤ) • genJ P X (star X)
  let G := 1 - genV P X (star X) - (2 : ℤ) • genJ P X (star X)
  let d := ⅟(1 + genV P X (star X))
  have hdP : d * P = P * d := hcut.invOf_left.eq
  have hdG : d * G = G * d := hnum.invOf_left.eq
  change F * d * P * (G * d) = (F * P * G) * (d * d)
  calc
    F * d * P * (G * d) = F * (d * P) * (G * d) := by simp only [mul_assoc]
    _ = F * (P * d) * (G * d) := by rw [hdP]
    _ = F * P * (d * G) * d := by simp only [mul_assoc]
    _ = F * P * (G * d) * d := by rw [hdG]
    _ = (F * P * G) * (d * d) := by simp only [mul_assoc]

/-- On `V=1`, the rational daughter is exactly the complementary cut. -/
theorem peirceCayley_conjugate_cut_of_mass_one
    (hV : genV P X (star X) = 1) :
    peirceCayley P X (star X) * P * star (peirceCayley P X (star X)) = 1 - P := by
  have hu : peirceCayley P X (star X) = genJ P X (star X) := by
    unfold peirceCayley
    have hn : 1 - genV P X (star X) + (2 : ℤ) • genJ P X (star X) =
        (2 : ℤ) • genJ P X (star X) := by rw [hV, sub_self, zero_add]
    have hs : (2 : ℤ) • genJ P X (star X) =
        genJ P X (star X) * (1 + genV P X (star X)) := by
      rw [hV]
      simp only [two_zsmul, mul_add, mul_one]
    rw [hn]
    calc
      (2 : ℤ) • genJ P X (star X) * ⅟(1 + genV P X (star X)) =
          genJ P X (star X) * ((1 + genV P X (star X)) *
            ⅟(1 + genV P X (star X))) := by
        rw [hs, mul_assoc]
      _ = genJ P X (star X) := by rw [mul_invOf_self, mul_one]
  rw [hu, star_genJ hPs]
  calc
    genJ P X (star X) * P * (-genJ P X (star X)) =
        genV P X (star X) * (1 - P) := by peirce_nf hP
    _ = 1 - P := by rw [hV, one_mul]

end Star

end InfoGeometry.OperatorAlgebra.PeirceSpine
