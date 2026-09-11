import InfoGeometry.Lie.CanonicalZornCartanAdjointRootBrackets
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornCartanAdjointRootVanishing

abbrev Der := CanonicalZornCartanAdjointRootDecomposition.Der

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

theorem jointEigenspace_eq_bot_of_not_mem_rootWeight_range
    (χ : Weight) (hχ : χ ∉ Set.range (rootWeight : Fin 14 → Weight)) :
    jointEigenspace χ = ⊥ := by
  apply le_antisymm
  · intro D hD
    let p : Params := canonicalParameterLinearEquiv.symm D
    have hp (k : TracelessWeight) :
        adCartanCoordinates k p = χ k • p := by
      have htransport := congrArg
        (fun X : Der => (canonicalParameterLinearEquiv.symm X : Params)) (hD k)
      change canonicalParameterLinearEquiv.symm (adCartan k D) =
        canonicalParameterLinearEquiv.symm (χ k • D) at htransport
      rw [map_smul] at htransport
      simpa [p, adCartanCoordinates] using htransport
    have hpzero : p = 0 := by
      funext i
      have hroot : rootWeight i ≠ χ := by
        intro h
        exact hχ ⟨i, h⟩
      obtain ⟨k, hk⟩ : ∃ k : TracelessWeight, rootWeight i k ≠ χ k := by
        by_contra hn
        push_neg at hn
        exact hroot (by
          ext k
          exact hn k)
      have hpi := congrFun (hp k) i
      rw [adCartanCoordinates_apply_diagonal] at hpi
      have hmul :
          (adCartanDiagonalCoefficient k i - χ k) * p i = 0 := by
        have hmul' :
            adCartanDiagonalCoefficient k i * p i = χ k * p i := by
          simpa [smul_eq_mul] using hpi
        linarith
      rcases mul_eq_zero.mp hmul with hcoeff | hpi
      · exact False.elim (hk (by
          simpa [rootWeight_eq_adCartanDiagonalCoefficient] using
            sub_eq_zero.mp hcoeff))
      · exact hpi
    have : D = 0 := by
      apply canonicalParameterLinearEquiv.symm.injective
      simpa [p] using hpzero
    rw [this]
    exact Submodule.zero_mem _
  · exact bot_le

theorem rootDerivation_bracket_eq_zero_of_sum_not_mem_rootWeight_range
    (i j : nonzeroIndex)
    (hχ : rootWeight i.1 + rootWeight j.1 ∉
      Set.range (rootWeight : Fin 14 → Weight)) :
    ⁅rootDerivation i.1, rootDerivation j.1⁆ = 0 := by
  have hi : rootDerivation i.1 ∈ jointEigenspace (rootWeight i.1) := by
    rw [mem_jointEigenspace_iff]
    intro H
    exact adCartan_rootDerivation H i.1
  have hj : rootDerivation j.1 ∈ jointEigenspace (rootWeight j.1) := by
    rw [mem_jointEigenspace_iff]
    intro H
    exact adCartan_rootDerivation H j.1
  have hbracket := lie_mem_jointEigenspace_add
    (rootWeight i.1) (rootWeight j.1) hi hj
  rw [jointEigenspace_eq_bot_of_not_mem_rootWeight_range _ hχ] at hbracket
  exact (Submodule.mem_bot ℝ).mp hbracket

end InfoGeometry.Lie.CanonicalZornCartanAdjointRootVanishing
