import InfoGeometry.Canonical.SplitOctonionThreeColorCausalMatrixRepresentation
import InfoGeometry.Canonical.SplitOctonionThreeColorDiracCore

namespace InfoGeometry.Canonical

open SplitOctonionColour

noncomputable section

/-!
# Matrix readout of the native colour Dirac element

The existing causal matrix map is deliberately a `LinearEquiv`: it records
the four-dimensional vector-space readout, not yet an algebra equivalence.
This owner connects that readout to the native split-octonion Dirac element.
-/

theorem threeColorCausalMatrixEquiv_colorDirac
    (c : SplitOctonionColour) (a b : ℚ) :
    threeColorCausalMatrixEquiv c
        ⟨colorDirac c a b, colorDirac_mem_colorCore c a b⟩ =
      a • Matrix.stdBasis ℚ (Fin 2) (Fin 2) (0, 1) +
        b • Matrix.stdBasis ℚ (Fin 2) (Fin 2) (1, 0) := by
  have hDirac :
      (⟨colorDirac c a b, colorDirac_mem_colorCore c a b⟩ : colorCore c) =
        a • colorPolarizedGenerator c 2 +
          b • colorPolarizedGenerator c 3 := by
    rfl
  rw [hDirac, map_add, map_smul, map_smul,
    threeColorCausalMatrixEquiv_generator_apply,
    threeColorCausalMatrixEquiv_generator_apply]
  rfl

end

end InfoGeometry.Canonical
