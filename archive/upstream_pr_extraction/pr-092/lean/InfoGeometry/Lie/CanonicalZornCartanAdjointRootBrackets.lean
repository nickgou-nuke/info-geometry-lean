import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-!
# Bracket transport between the native Cartan root spaces

This owner records the intrinsic grading consequence of the simultaneous
adjoint eigenspace calculation.  It does not choose structure constants or
claim a Chevalley normalization: brackets are placed in the appropriate
one-dimensional root space by the native Lie-eigenspace lemma.
-/

namespace InfoGeometry.Lie.CanonicalZornCartanAdjointRootBrackets

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum

theorem rootDerivation_bracket_mem_rootSpace_of_add
    (i j k : nonzeroIndex)
    (hweight : rootWeight k.1 = rootWeight i.1 + rootWeight j.1) :
    ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈ rootSpace k.1 := by
  have hi : rootDerivation i.1 ∈ jointEigenspace (rootWeight i.1) := by
    rw [mem_jointEigenspace_iff]
    intro H
    exact adCartan_rootDerivation H i.1
  have hj : rootDerivation j.1 ∈ jointEigenspace (rootWeight j.1) := by
    rw [mem_jointEigenspace_iff]
    intro H
    exact adCartan_rootDerivation H j.1
  have hmem :
      ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈
        jointEigenspace (rootWeight i.1 + rootWeight j.1) := by
    exact lie_mem_jointEigenspace_add
      (rootWeight i.1) (rootWeight j.1) hi hj
  rw [← hweight] at hmem
  rw [rootSpace_eq_jointEigenspace k]
  exact hmem

theorem rootDerivation_bracket_eq_smul_of_add
    (i j k : nonzeroIndex)
    (hweight : rootWeight k.1 = rootWeight i.1 + rootWeight j.1) :
    ∃ c : ℝ,
      ⁅rootDerivation i.1, rootDerivation j.1⁆ =
        c • rootDerivation k.1 := by
  have hmem := rootDerivation_bracket_mem_rootSpace_of_add i j k hweight
  have hspan := jointEigenspace_eq_span_rootDerivation k.1 k.2.1 k.2.2
  have hmem' :
      ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈
        ℝ ∙ rootDerivation k.1 := by
    rw [← hspan, ← rootSpace_eq_jointEigenspace k]
    exact hmem
  rcases (Submodule.mem_span_singleton.mp hmem') with ⟨c, hc⟩
  exact ⟨c, hc.symm⟩

end InfoGeometry.Lie.CanonicalZornCartanAdjointRootBrackets
