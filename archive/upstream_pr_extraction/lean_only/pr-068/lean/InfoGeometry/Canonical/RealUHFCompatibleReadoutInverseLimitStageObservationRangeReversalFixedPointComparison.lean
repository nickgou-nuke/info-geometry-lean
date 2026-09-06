import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalCompHaus
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPointCompHaus

/-!
# Fixed-point comparison for reversal range isomorphisms

At a reversal-fixed base point, the general reversal range isomorphism has the
same underlying scalar map as the fixed-point identity isomorphism.  The two
dependent targets are compared explicitly with `eqToHom`.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPointComparison

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPointCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev inverseLimitCarrier := (limit readoutDiagram).carrier
abbrev flow := scalarDilationSymbolicLatentFlow

variable [CompactSpace inverseLimitCarrier] [T2Space inverseLimitCarrier]

theorem observationRangeEqToHom_val
    {x y : inverseLimitCarrier} (n : ℕ) (X : MatStage n)
    (h : x = y)
    (z : stageObservationRangeCompHaus x n X) :
    (ConcreteCategory.hom
      (CategoryTheory.eqToHom
        (congrArg (fun w => stageObservationRangeCompHaus w n X) h)) z).1 =
      z.1 := by
  cases h
  rfl

theorem reversalRangeIso_eq_fixedPointIso_after_transport
    (R : SymbolicLatentModularReversal flow)
    (ρ : inverseLimitCarrier) (hρ : R.involution ρ = ρ)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (n : ℕ) (X : MatStage n) :
    (stageObservationRangeReversalCompHausIso R hreadout ρ n X).hom =
      (fixedPointRangeMirrorCompHausIso R ρ hρ hreadout n X).hom ≫
        CategoryTheory.eqToHom
          (congrArg (fun z => stageObservationRangeCompHaus z n X)
            hρ.symm) := by
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  change
    ((stageObservationRangeReversalCompHausIso R hreadout ρ n X).hom z).1 =
      ((CategoryTheory.eqToHom
        (congrArg (fun w => stageObservationRangeCompHaus w n X) hρ.symm))
        ((fixedPointRangeMirrorCompHausIso R ρ hρ hreadout n X).hom z)).1
  rw [stageObservationRangeReversalCompHausIso_hom_apply]
  change z.1 =
    ((CategoryTheory.eqToHom
      (congrArg (fun w => stageObservationRangeCompHaus w n X) hρ.symm)) z).1
  exact (observationRangeEqToHom_val n X hρ.symm z).symm

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPointComparison

end
