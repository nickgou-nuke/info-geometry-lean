import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.DyadicDirectLimitRealTopological
import InfoGeometry.Canonical.RealUHFProjectionRankSystem
import InfoGeometry.Canonical.RealUHFProjectionRankCompletionReadoutSquare

/-!
# Completion bridge for the dyadic direct limit

This owner connects the transported dyadic direct-limit topology to the
uniform-space completion of its dyadic-rational model.  It does not identify
this completion with a UHF or C*-algebraic completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.DyadicDirectLimitCompletionTopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DyadicDirectLimitRealTopological
open InfoGeometry.Canonical.RealUHFProjectionRankSystem
open InfoGeometry.Canonical.RealUHFProjectionRankCompletionReadoutSquare
open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

def dyadicDirectLimitCompletionReadout :
    DyadicDirectLimit → UniformSpace.Completion DyadicRational :=
  fun x => (dyadicDirectLimitEquiv x : UniformSpace.Completion DyadicRational)

theorem continuous_dyadicDirectLimitCompletionReadout :
    Continuous dyadicDirectLimitCompletionReadout := by
  exact (UniformSpace.Completion.continuous_coe
    (α := DyadicRational)).comp
    continuous_dyadicDirectLimitEquiv

def dyadicDirectLimitCompletionReadoutTopCatHom :
    TopCat.of DyadicDirectLimit ⟶
      TopCat.of (UniformSpace.Completion DyadicRational) :=
  TopCat.ofHom
    { toFun := dyadicDirectLimitCompletionReadout
      continuous_toFun := continuous_dyadicDirectLimitCompletionReadout }

@[simp] theorem dyadicDirectLimitCompletionReadoutTopCatHom_apply
    (x : DyadicDirectLimit) :
    dyadicDirectLimitCompletionReadoutTopCatHom x =
      dyadicDirectLimitCompletionReadout x := rfl

noncomputable def dyadicRationalCompletionRealTopCatIso :
    TopCat.of (UniformSpace.Completion DyadicRational) ≅ TopCat.of ℝ :=
  TopCat.isoOfHomeo dyadicRationalCompletionRealHomeomorph

theorem dyadicDirectLimitCompletionReadout_real_square
    (x : DyadicDirectLimit) :
    dyadicRationalCompletionRealHomeomorph
        (dyadicDirectLimitCompletionReadout x) =
      dyadicDirectLimitRealReadout x := by
  change dyadicRationalCompletionRealExtension
      (dyadicDirectLimitEquiv x : UniformSpace.Completion DyadicRational) = _
  rw [dyadicRationalCompletionRealExtension_coe]
  rfl

theorem dyadicDirectLimitCompletionReadout_real_square_topCat
    (x : DyadicDirectLimit) :
    dyadicRationalCompletionRealHomeomorph
        (dyadicDirectLimitCompletionReadoutTopCatHom x) =
      dyadicDirectLimitRealReadoutTopCatHom x := by
  exact dyadicDirectLimitCompletionReadout_real_square x

theorem dyadicDirectLimitCompletionReadout_topCat_factorization :
    dyadicDirectLimitCompletionReadoutTopCatHom ≫
        dyadicRationalCompletionRealTopCatIso.hom =
      dyadicDirectLimitRealReadoutTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rw [TopCat.comp_app]
  exact dyadicDirectLimitCompletionReadout_real_square x

theorem projectionRankSystem_completion_real_readout
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    dyadicRationalCompletionRealHomeomorph
        (dyadicDirectLimitCompletionReadout (S.dimensionClass n)) =
      ((S.normalizedReadout n : DyadicRational) : ℚ) := by
  rw [dyadicDirectLimitCompletionReadout_real_square]
  simp only [dyadicDirectLimitRealReadout]
  rw [S.dimensionClass_readout]

theorem projectionRankSystem_completion_real_readout_stable
    (S : RealUHFProjectionRankSystem) (n k : ℕ) :
    dyadicRationalCompletionRealHomeomorph
        (dyadicDirectLimitCompletionReadout (S.dimensionClass (n + k))) =
      ((S.normalizedReadout n : DyadicRational) : ℚ) := by
  rw [projectionRankSystem_completion_real_readout]
  rw [S.normalizedReadout_add n k]

theorem projectionRankSystem_completion_real_readout_eq_bounded
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    dyadicRationalCompletionRealHomeomorph
        (dyadicDirectLimitCompletionReadout (S.dimensionClass n)) =
      (normalizedRealReadout S : ℝ) := by
  rw [projectionRankSystem_completion_real_readout]
  have h := congrArg (fun q : RealUnitInterval => (q : ℝ))
    (normalizedRealReadout_eq_stage S n)
  simpa [dyadicToRealInterval] using h

end InfoGeometry.Canonical.DyadicDirectLimitCompletionTopologicalBridge

end
