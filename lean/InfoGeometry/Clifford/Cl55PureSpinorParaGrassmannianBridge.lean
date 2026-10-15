import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge
import InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
import InfoGeometry.Canonical.SuperGrassmannianManifold

/-!
# The split `(5,5)` pure-spinor vacuum as a para-Grassmannian sheet

This module connects three existing owners without identifying their carriers:

* `Clifford55.Q55` and its Clifford algebra;
* the neutral `V5 × V5*` exterior-spinor representation and its vacuum
  annihilator;
* the para-complex sheets and idempotent projectors from
  `SuperGrassmannianManifold`.

The connection is explicit: the negative para-complex sheet is the range of
the vacuum sheet projector, equals the annihilator of the exterior vacuum,
and is therefore the maximal-neutral Grassmannian point already attached to
the projective pure-spinor vacuum. Under `neutralToV55`, every vector in that
sheet is null for `Q55`. This is a concrete `(5,5)` statement; no converse
pure-spinor classification or supermanifold structure is claimed.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55PureSpinorParaGrassmannianBridge

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
open InfoGeometry.Canonical.SuperGrassmannianManifold
open scoped LinearAlgebra.Projectivization

abbrev V5 := InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.V5
abbrev NeutralSpace :=
  InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.NeutralSpace
abbrev Spinor := InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.Spinor

/-- The neutral metric with the sign compatible with the repository's
para-symplectic form and para-complex involution. -/
def neutralParaMetric :
    LinearMap.BilinForm ℝ NeutralSpace :=
  -InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin
    (E := V5)

/-- The canonical neutral phase-space data form a para-Kähler structure. -/
theorem neutralPhaseSpace_paraKahler :
    ParaKahlerStructure neutralParaMetric
      (InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralOmega (E := V5))
      (InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution
        (E := V5)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp [neutralParaMetric,
      InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin_apply]
    ring
  · exact InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralOmega_skew
  · intro X Y
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp [neutralParaMetric,
      InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin_apply,
      InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralOmega_apply,
      InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution_apply]
    ring
  · intro X Y
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp [InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralOmega_apply,
      InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution_apply]
    ring

/-- The canonical neutral para-complex map is an involution. -/
theorem neutralPhaseSpace_paraComplex :
    ParaComplexStructure
      (InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution
        (E := V5)) := by
  refine ⟨?_⟩
  intro X
  rcases X with ⟨x, ξ⟩
  simp [InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution]

/-- Projection onto the dual (negative) Lagrangian sheet. -/
def vacuumSheetProjector : Module.End ℝ NeutralSpace where
  toFun X := (0, X.2)
  map_add' X Y := by
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp
  map_smul' c X := by
    rcases X with ⟨x, ξ⟩
    simp

@[simp] theorem vacuumSheetProjector_apply (X : NeutralSpace) :
    vacuumSheetProjector X = (0, X.2) := by
  simp [vacuumSheetProjector]

/-- The vacuum sheet projection is an idempotent in the native
`SuperGrassmannianManifold` projector interface. -/
theorem vacuumSheetProjector_isGrassmannianProjector :
    GrassmannianProjector vacuumSheetProjector := by
  refine ⟨?_⟩
  intro X
  rcases X with ⟨x, ξ⟩
  simp [vacuumSheetProjector]

/-- The range of the sheet projection is exactly the negative eigensheet of
the neutral para-complex involution. -/
theorem vacuumSheetProjector_range_eq_negativeSheet :
    LinearMap.range vacuumSheetProjector =
      LinearMap.ker
        (InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution
          (E := V5) + (LinearMap.id : NeutralSpace →ₗ[ℝ] NeutralSpace)) := by
  ext X
  rcases X with ⟨x, ξ⟩
  constructor
  · rintro ⟨Y, hY⟩
    change vacuumSheetProjector Y = (x, ξ) at hY
    rcases Y with ⟨y, η⟩
    have hx : x = 0 := by
      have := congrArg Prod.fst hY
      simpa [vacuumSheetProjector] using this.symm
    subst x
    change (InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution
        (E := V5) + (LinearMap.id : NeutralSpace →ₗ[ℝ] NeutralSpace)) (0, ξ) = 0
    simp [InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution]
  · intro h
    change (InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution
        (E := V5) + (LinearMap.id : NeutralSpace →ₗ[ℝ] NeutralSpace)) (x, ξ) = 0 at h
    have hx2 : x + x = 0 := by
      have := congrArg Prod.fst h
      simpa [InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution] using this
    have hx : x = 0 := by
      have hmul : (2 : ℝ) • x = 0 := by simpa [two_smul] using hx2
      exact (smul_eq_zero.mp hmul).resolve_left (by norm_num)
    subst x
    refine ⟨(0, ξ), ?_⟩
    rfl

/-- The negative para-complex sheet is the annihilator of the exterior vacuum.
-/
theorem vacuumSheetProjector_range_eq_vacuumAnnihilator :
    LinearMap.range vacuumSheetProjector = neutralAnnihilator (1 : Spinor) := by
  rw [vacuumSheetProjector_range_eq_negativeSheet]
  rw [vacuum_neutralAnnihilator_eq_dualVacuumEmbedding_range]
  ext X
  rcases X with ⟨x, ξ⟩
  constructor
  · intro h
    change (InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution
        (E := V5) + (LinearMap.id : NeutralSpace →ₗ[ℝ] NeutralSpace)) (x, ξ) = 0 at h
    have hx2 : x + x = 0 := by
      have := congrArg Prod.fst h
      simpa [InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution] using this
    have hx : x = 0 := by
      have hmul : (2 : ℝ) • x = 0 := by simpa [two_smul] using hx2
      exact (smul_eq_zero.mp hmul).resolve_left (by norm_num)
    subst x
    exact ⟨ξ, rfl⟩
  · rintro ⟨φ, hφ⟩
    have hx : x = 0 := by
      have := congrArg Prod.fst hφ
      simpa [dualVacuumEmbedding] using this.symm
    subst x
    change (InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution
        (E := V5) + (LinearMap.id : NeutralSpace →ₗ[ℝ] NeutralSpace)) (0, ξ) = 0
    simp [InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralParaInvolution]

/-- Consequently, the range of the projector is a maximal neutral totally
null subspace, so it is an actual point of the repository's finite
maximal-neutral Grassmannian. -/
theorem vacuumSheetProjector_range_isMaximalNeutralTotallyNull :
    IsMaximalNeutralTotallyNull (LinearMap.range vacuumSheetProjector) := by
  rw [vacuumSheetProjector_range_eq_vacuumAnnihilator]
  exact vacuum_neutralAnnihilator_isMaximalNeutralTotallyNull

/-- The projective pure-spinor Grassmannian point of the vacuum is precisely
the maximal-neutral range of the para-sheet projector. -/
theorem projectiveVacuumGrassmannianPoint_range_eq :
    (projectivePureSpinorGrassmannianPoint
      ⟨Projectivization.mk ℝ (1 : Spinor) one_ne_zero,
        projective_vacuum_isPureSpinor⟩).1 =
      LinearMap.range vacuumSheetProjector := by
  rw [vacuum_projectivePureSpinorGrassmannianPoint]
  exact vacuumSheetProjector_range_eq_vacuumAnnihilator.symm

/-- The vacuum sheet remains null after transport to the actual symmetric
split quadratic space `Q55`. -/
theorem Q55_neutralToV55_vacuumSheet_null (φ : Module.Dual ℝ V5) :
    InfoGeometry.Clifford.Clifford55.Q55
      (InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry.neutralToV55
        (vacuumSheetProjector (0, φ))) = 0 := by
  rw [InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry.q55_neutralToV55]
  simpa [vacuumSheetProjector] using
    (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_fst_zero
      (E := V5) φ)

/-- The same null vacuum sheet, transported through the existing `Q55 ≃
Qsplit 5` isometry, is null in the recursive symmetric split tower itself. -/
theorem Qsplit5_neutralToSplit_vacuumSheet_null
    (φ : Module.Dual ℝ V5) :
    InfoGeometry.CliffordTower.Qsplit 5
      (InfoGeometry.Clifford.Clifford55.q55ToSplit5
        (InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry.neutralToV55
          (vacuumSheetProjector (0, φ)))) = 0 := by
  rw [InfoGeometry.Clifford.Clifford55.qsplit5_q55ToSplit5,
    Q55_neutralToV55_vacuumSheet_null]

end InfoGeometry.Clifford.Cl55PureSpinorParaGrassmannianBridge
