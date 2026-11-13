/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Clifford.OperatorCliffordWalsh
import InfoGeometry.OperatorAlgebra.PeirceAffinity
import InfoGeometry.OperatorAlgebra.PeirceLowerProjection
import InfoGeometry.OperatorAlgebra.StarSymplecticBlocks

/-!
# Matrix realizations of ordered affinity transport

These bridges apply the generic affinity laws to the constructed squeeze
units, and the coefficient convolution to actual full matrix products.
The coefficient ring remains arbitrary and may itself be an operator ring.
The canonical Peirce mask is also identified entrywise; an explicit matrix
unit calculation shows why the additive projection is not a ring map.
-/

namespace InfoGeometry.OperatorAlgebra.MatrixPeirceAffinity

open InfoGeometry.Clifford
open InfoGeometry.Clifford.OperatorCliffordWalsh
open PeirceAffinity PeirceLowerProjection StarSymplecticBlocks

variable {A : Type*} [Ring A]

/-- The generic lower projection is the usual lower triangular entry mask. -/
theorem lowerProjection_matrix (X : Matrix (Fin 2) (Fin 2) A) :
    lowerProjection (Matrix.single 0 0 1) X = !![X 0 0, 0; X 1 0, X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [lowerProjection_apply, PeirceSpine.conePlus, Matrix.sub_apply,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [Matrix.one_apply]

/-- The projection is not multiplicative even on two elementary matrices. -/
theorem lowerProjection_not_multiplicative [Nontrivial A] :
    lowerProjection (Matrix.single 0 0 1)
        ((Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) A) * Matrix.single 1 0 1) ≠
      lowerProjection (Matrix.single 0 0 1) (Matrix.single 0 1 1) *
        lowerProjection (Matrix.single 0 0 1) (Matrix.single 1 0 1) := by
  intro h
  have h00 := congrArg (fun X : Matrix (Fin 2) (Fin 2) A => X 0 0) h
  simp only [lowerProjection_matrix] at h00
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two] at h00

section Star

variable [StarRing A]

/-- The constructed shifted squeeze supplies the required biorthogonal partner. -/
theorem affinity_squeeze (q k : Matrix (Fin 2) (Fin 2) A) (u : Aˣ) :
    affinity (q * (squeezeUnit u : Matrix (Fin 2) (Fin 2) A))
        (k * (J_mat * (squeezeUnit u : Matrix (Fin 2) (Fin 2) A) * J_mat)) =
      affinity q k :=
  affinity_biorthogonal q k _ _ (squeeze_mul_star_shift_squeeze u)

/-- Actual squeeze preservation discharges the generic form-congruence hypothesis. -/
theorem twistedAffinity_squeeze (q k : Matrix (Fin 2) (Fin 2) A) (u : Aˣ) :
    twistedAffinity (-K_mat)
        (q * star (squeezeUnit u : Matrix (Fin 2) (Fin 2) A))
        (k * star (squeezeUnit u : Matrix (Fin 2) (Fin 2) A)) =
      twistedAffinity (-K_mat) q k :=
  twistedAffinity_congruence (-K_mat) q k _ (squeeze_preserves u)

/-- The concrete skew form reverses the twisted pairing under star and input swap. -/
theorem twistedAffinity_star_swap (q k : Matrix (Fin 2) (Fin 2) A) :
    star (twistedAffinity (-K_mat) q k) = -twistedAffinity (-K_mat) k q :=
  twistedAffinity_star_of_skew star_skewForm q k

/-- The ordered coefficient product applies to the actual star pairing. -/
theorem convolution_affinity (q k : Matrix (Fin 2) (Fin 2) A) :
    convolution (coefficients q) (coefficients (star k)) =
      coefficients (affinity q k) + coefficients (affinity q k) :=
  convolution_coefficients q (star k)

/-- Raw convolution reconstructs four copies of the affinity, with no inverse of two. -/
theorem synthesis_convolution_affinity (q k : Matrix (Fin 2) (Fin 2) A) :
    synthesis (convolution (coefficients q) (coefficients (star k))) =
      (affinity q k + affinity q k) + (affinity q k + affinity q k) :=
  synthesis_convolution_coefficients q (star k)

/-- Normalization makes coefficient convolution exactly the full operator pairing. -/
theorem normalizedCoordinates_affinity [Invertible (2 : A)]
    (q k : Matrix (Fin 2) (Fin 2) A) :
    normalizedCoordinates (affinity q k) =
      convolution (normalizedCoordinates q) (normalizedCoordinates (star k)) :=
  normalizedCoordinates_mul q (star k)

end Star

end InfoGeometry.OperatorAlgebra.MatrixPeirceAffinity
