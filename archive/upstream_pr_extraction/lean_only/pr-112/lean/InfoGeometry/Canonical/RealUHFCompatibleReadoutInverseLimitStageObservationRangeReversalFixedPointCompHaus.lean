import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPoint
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus

/-!
# Compact-Hausdorff packaging of fixed-point reversal on observation ranges

At a reversal-fixed inverse-limit point, the induced action on the scalar
observation range is the identity on its underlying readout values.  This
owner packages that fixed-point restriction as a `CompHaus` isomorphism and
records its image under the forgetful functor to `TopCat`.

The compactness assumptions are local to the finite-stage range.  No compact
structure on the full inverse-limit carrier is inferred without hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPointCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPoint
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev inverseLimitCarrier := (limit readoutDiagram).carrier
abbrev flow := scalarDilationSymbolicLatentFlow

variable [CompactSpace inverseLimitCarrier] [T2Space inverseLimitCarrier]

noncomputable def fixedPointRangeMirrorCompHausIso
    (R : SymbolicLatentModularReversal flow)
    (ρ : inverseLimitCarrier) (hρ : R.involution ρ = ρ)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (n : ℕ) (X : MatStage n) :
    stageObservationRangeCompHaus ρ n X ≅
      stageObservationRangeCompHaus ρ n X :=
  Iso.refl _

@[simp] theorem fixedPointRangeMirrorCompHausIso_hom_apply
    (R : SymbolicLatentModularReversal flow)
    (ρ : inverseLimitCarrier) (hρ : R.involution ρ = ρ)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (n : ℕ) (X : MatStage n)
    (z : stageObservationRangeCompHaus ρ n X) :
    (fixedPointRangeMirrorCompHausIso R ρ hρ hreadout n X).hom z = z := by
  rfl

theorem fixedPointRangeMirrorCompHausIso_forget
    (R : SymbolicLatentModularReversal flow)
    (ρ : inverseLimitCarrier) (hρ : R.involution ρ = ρ)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (n : ℕ) (X : MatStage n) :
    compHausToTop.map (fixedPointRangeMirrorCompHausIso R ρ hρ hreadout n X).hom =
      𝟙 (TopCat.of (stageObservationRange ρ n X)) := by
  rfl


end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPointCompHaus
