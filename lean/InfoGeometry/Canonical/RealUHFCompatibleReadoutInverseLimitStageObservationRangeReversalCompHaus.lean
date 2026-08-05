import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalHomeomorph
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff mirror transport of finite-stage observation ranges

The reversal itself and the readout covariance are supplied by the existing
`SymbolicLatentModularReversal` interface.  This owner only packages the
resulting native range homeomorphism in `CompHaus`; it does not manufacture a
mirror or infer a KMS/modular interpretation.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalHomeomorph
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev inverseLimitCarrier := (limit readoutDiagram).carrier
abbrev flow := scalarDilationSymbolicLatentFlow

variable [CompactSpace inverseLimitCarrier] [T2Space inverseLimitCarrier]

noncomputable def stageObservationRangeReversalCompHausIso
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) :
    stageObservationRangeCompHaus ρ n X ≅
      stageObservationRangeCompHaus (R.involution ρ) n X :=
  CompHausLike.isoOfHomeo
    (P := fun _ : TopCat => True)
    (X := stageObservationRangeCompHaus ρ n X)
    (Y := stageObservationRangeCompHaus (R.involution ρ) n X)
    (stageObservationRangeReversalHomeomorph R hreadout ρ n X)

@[simp] theorem stageObservationRangeReversalCompHausIso_hom_apply
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
    (z : stageObservationRangeCompHaus ρ n X) :
    (stageObservationRangeReversalCompHausIso R hreadout ρ n X).hom z =
      ⟨z.1, (stageObservationRangeReversalHomeomorph
        R hreadout ρ n X z).property⟩ := by
  apply Subtype.ext
  exact stageObservationRangeReversalHomeomorph_apply
    R hreadout ρ n X z

theorem stageObservationRangeReversalCompHausIso_hom_forget
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) :
    compHausToTop.map
        (stageObservationRangeReversalCompHausIso R hreadout ρ n X).hom =
      TopCat.ofHom
        { toFun := stageObservationRangeReversalHomeomorph R hreadout ρ n X
          continuous_toFun :=
        (stageObservationRangeReversalHomeomorph R hreadout ρ n X).continuous } := by
  rfl

theorem stageObservationRangeReversalCompHausIso_involutive_apply
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
    (z : stageObservationRangeCompHaus ρ n X) :
    (((stageObservationRangeReversalCompHausIso R hreadout ρ n X).hom ≫
        (stageObservationRangeReversalCompHausIso R hreadout
          (R.involution ρ) n X).hom) z).1 = z.1 := by
  change z.1 = z.1
  rfl

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalCompHaus

end
