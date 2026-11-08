/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinCommutant
import InfoGeometry.QuantumContext.MarkovTwoSidedGroupInverse

/-!
# Commuting actions in the Markov Drazin commutant

On the full matrix module, any endomorphism that commutes with the two-sided
Markov Laplacian also commutes with its group inverse and range projector.
For left multiplication by a matrix `S`, commuting with the two-sided
Laplacian follows from the explicit compatibility equation
`S * (1 - P) = (1 - P) * S`. No skew-adjointness or reversibility claim is
made by these algebraic commutant results.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovSandwichDrazinCommutant

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Canonical.DrazinCommutant
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0
open InfoGeometry.QuantumContext.MarkovTwoSidedGroupInverse

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem leftAction_eq_cornerMap (S : MatrixCarrier (ι := ι)) :
    mulLeftLinearMap ι ℝ S = cornerMap S 1 := by
  ext X
  simp [cornerMap, mulLeftLinearMap, mulRightLinearMap]

/-- A matrix action commuting with the Markov Laplacian commutes with the
full-matrix two-sided Markov Laplacian `X ↦ (1-P) * (X * (1-P))`. -/
theorem leftAction_commutes_markovSandwich
    (P S : MatrixCarrier (ι := ι))
    (hSL : S * (1 - P) = (1 - P) * S) :
    mulLeftLinearMap ι ℝ S * cornerMap (1 - P) (1 - P) =
      cornerMap (1 - P) (1 - P) * mulLeftLinearMap ι ℝ S := by
  rw [leftAction_eq_cornerMap]
  rw [cornerMap_mul, cornerMap_mul]
  simp [hSL]

/-- Any endomorphism commuting with a Markov sandwich Laplacian commutes
with the corresponding two-sided group inverse. This is the Drazin
commutant theorem specialized to the full matrix carrier. -/
theorem commutes_markovSandwich_groupInverse_of_commutes
    (P G : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G)
    (J : MatrixEnd (ι := ι))
    (hJ : J * cornerMap (1 - P) (1 - P) =
      cornerMap (1 - P) (1 - P) * J) :
    J * cornerMap G G = cornerMap G G * J := by
  have hD := (markovSandwich_groupInverse P G hG).toDrazin
  exact (inverse_commutes_of_commutes hD J hJ.symm).symm

/-- The two-sided Markov range idempotent commutes with every endomorphism
that commutes with the two-sided Laplacian. -/
theorem commutes_markovSandwich_rangeProjector_of_commutes
    (P G : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G)
    (J : MatrixEnd (ι := ι))
    (hJ : J * cornerMap (1 - P) (1 - P) =
      cornerMap (1 - P) (1 - P) * J) :
    J * (cornerMap (1 - P) (1 - P) * cornerMap G G) =
      (cornerMap (1 - P) (1 - P) * cornerMap G G) * J := by
  have hJB := hJ
  have hJG := commutes_markovSandwich_groupInverse_of_commutes P G hG J hJ
  calc
    J * (cornerMap (1 - P) (1 - P) * cornerMap G G) =
        (J * cornerMap (1 - P) (1 - P)) * cornerMap G G := by rw [mul_assoc]
    _ = (cornerMap (1 - P) (1 - P) * J) * cornerMap G G := by rw [hJB]
    _ = cornerMap (1 - P) (1 - P) * (J * cornerMap G G) := by rw [mul_assoc]
    _ = cornerMap (1 - P) (1 - P) * (cornerMap G G * J) := by rw [hJG]
    _ = (cornerMap (1 - P) (1 - P) * cornerMap G G) * J := by rw [mul_assoc]

/-- A left-multiplication action satisfying the stated compatibility with
`1-P` commutes
with the two-sided Markov group inverse and its range projector. -/
theorem leftAction_commutes_markovSandwich_groupInverse_and_projector
    (P G S : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G)
    (hSL : S * (1 - P) = (1 - P) * S) :
    mulLeftLinearMap ι ℝ S * cornerMap G G =
      cornerMap G G * mulLeftLinearMap ι ℝ S ∧
    mulLeftLinearMap ι ℝ S *
        (cornerMap (1 - P) (1 - P) * cornerMap G G) =
      (cornerMap (1 - P) (1 - P) * cornerMap G G) *
        mulLeftLinearMap ι ℝ S := by
  have hJ := leftAction_commutes_markovSandwich P S hSL
  exact ⟨commutes_markovSandwich_groupInverse_of_commutes P G hG
      (mulLeftLinearMap ι ℝ S) hJ,
    commutes_markovSandwich_rangeProjector_of_commutes P G hG
      (mulLeftLinearMap ι ℝ S) hJ⟩

end InfoGeometry.QuantumContext.MarkovSandwichDrazinCommutant
