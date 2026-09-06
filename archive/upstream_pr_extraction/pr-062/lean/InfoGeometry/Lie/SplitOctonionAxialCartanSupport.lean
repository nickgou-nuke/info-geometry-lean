import InfoGeometry.Lie.SplitOctonionAxialCartanFlow
import InfoGeometry.Lie.SplitOctonionAxialSupportGrading

/-!
# Cartan compatibility with the active/defect split

The traceless multiplication-preserving Cartan flow is compared with the
already-proved Drazin active-support projector only downstream of both owners,
avoiding an import cycle.  This is the projector-level Erlangen statement.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialCartanSupport

open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Lie.SplitOctonionAxialSupportGrading
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
open InfoGeometry.Lie.SplitOctonionAxialDrazinDefect
open InfoGeometry.Singular.Drazin
open InfoGeometry.Canonical.ZornMatrix

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

/-- The traceless Cartan flow preserves the Drazin active-support splitting. -/
theorem axialCartanFlow_commutes_activeSupport
    (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    axialActiveSupport (axialCartanFlow k t Z) =
      axialCartanFlow k t (axialActiveSupport Z) := by
  ext i <;> simp [axialActiveSupport_apply, axialCartanFlow]

/-! ## Direct Drazin-projector readout -/

theorem axialCartanFlow_commutes_drazinProjector
    (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    Drazin_Projector axialGrading axialGrading 1
        axialGrading_isDrazinInverse (axialCartanFlow k t Z) =
      axialCartanFlow k t
        (Drazin_Projector axialGrading axialGrading 1
          axialGrading_isDrazinInverse Z) := by
  rw [← axialActiveSupport_eq_drazinProjector]
  exact axialCartanFlow_commutes_activeSupport k t Z

/-- The complementary stationary/Drazin-defect projector is preserved too. -/
theorem axialCartanFlow_commutes_PZero
    (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    axialPZero (axialCartanFlow k t Z) =
      axialCartanFlow k t (axialPZero Z) := by
  ext i <;> simp [axialPZero_apply, axialCartanFlow]

theorem axialCartanFlow_commutes_drazinDefect
    (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    (1 - Drazin_Projector axialGrading axialGrading 1
        axialGrading_isDrazinInverse) (axialCartanFlow k t Z) =
      axialCartanFlow k t
        ((1 - Drazin_Projector axialGrading axialGrading 1
          axialGrading_isDrazinInverse) Z) := by
  rw [axial_drazinComplement_eq_PZero]
  exact axialCartanFlow_commutes_PZero k t Z

/-- The upper/color Peirce channel is invariant under the Cartan flow. -/
theorem axialCartanFlow_commutes_PPlus
    (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    axialPPlus (axialCartanFlow k t Z) =
      axialCartanFlow k t (axialPPlus Z) := by
  ext i <;> simp [axialPPlus_apply, colorProject_apply, axialCartanFlow]

/-- The lower/anticolor Peirce channel is invariant under the Cartan flow. -/
theorem axialCartanFlow_commutes_PMinus
    (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    axialPMinus (axialCartanFlow k t Z) =
      axialCartanFlow k t (axialPMinus Z) := by
  ext i <;> simp [axialPMinus_apply, anticolorProject_apply, axialCartanFlow]

theorem axialCartanFlow_maps_PPlus_range
    (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    axialCartanFlow k t (axialPPlus Z) ∈ LinearMap.range axialPPlus := by
  rw [← axialCartanFlow_commutes_PPlus]
  exact ⟨axialCartanFlow k t Z, rfl⟩

theorem axialCartanFlow_maps_PMinus_range
    (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    axialCartanFlow k t (axialPMinus Z) ∈ LinearMap.range axialPMinus := by
  rw [← axialCartanFlow_commutes_PMinus]
  exact ⟨axialCartanFlow k t Z, rfl⟩

theorem axialCartanFlow_preserves_PPlus_submodule
    (k : Fin 3 → ℝ) (t : ℝ) {Z : CZ}
    (hZ : Z ∈ LinearMap.range axialPPlus) :
    axialCartanFlow k t Z ∈ LinearMap.range axialPPlus := by
  rcases hZ with ⟨Y, rfl⟩
  exact axialCartanFlow_maps_PPlus_range k t Y

theorem axialCartanFlow_preserves_PMinus_submodule
    (k : Fin 3 → ℝ) (t : ℝ) {Z : CZ}
    (hZ : Z ∈ LinearMap.range axialPMinus) :
    axialCartanFlow k t Z ∈ LinearMap.range axialPMinus := by
  rcases hZ with ⟨Y, rfl⟩
  exact axialCartanFlow_maps_PMinus_range k t Y

theorem axialCartanFlow_preserves_PZero_submodule
    (k : Fin 3 → ℝ) (t : ℝ) {Z : CZ}
    (hZ : Z ∈ LinearMap.range axialPZero) :
    axialCartanFlow k t Z ∈ LinearMap.range axialPZero := by
  rcases hZ with ⟨Y, rfl⟩
  rw [← axialCartanFlow_commutes_PZero]
  exact ⟨axialCartanFlow k t Y, rfl⟩

/-- Consequently the Cartan flow commutes with the active/defect involution
`Gamma = 2 Q - I`. -/
theorem axialCartanFlow_commutes_activeDefectInvolution
    (k : Fin 3 → ℝ) (t : ℝ) (Z : CZ) :
    axialActiveDefectInvolution (axialCartanFlow k t Z) =
      axialCartanFlow k t (axialActiveDefectInvolution Z) := by
  ext i <;> simp [axialActiveDefectInvolution_apply, axialCartanFlow]

/-- On the active support, the multiplication-preserving Cartan flow also
preserves the native Zorn determinant, hence the transported Klein null cone. -/
theorem axialCartanFlow_preserves_active_det
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (Z : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (axialActiveSupport (axialCartanFlow k t Z)) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (axialActiveSupport Z) := by
  rw [axialCartanFlow_commutes_activeSupport]
  exact axialCartanCompositionAut_preserves_det k hk t (axialActiveSupport Z)

theorem axialCartanFlow_active_det_eq_zero_iff
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (Z : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (axialActiveSupport (axialCartanFlow k t Z)) = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (axialActiveSupport Z) = 0 := by
  rw [axialCartanFlow_preserves_active_det k hk t Z]


end InfoGeometry.Lie.SplitOctonionAxialCartanSupport
