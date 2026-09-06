import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalHomeomorph

/-!
# Fixed-point restriction of reversal on finite-stage observation ranges

When the base inverse-limit point is fixed by a modular reversal and the
finite-stage readout is reversal-covariant, the induced mirror acts on the
same real observation range.  The result is stated at the topological range
level only; it does not infer a Hilbert-space or operator-algebraic symmetry.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPoint

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalHomeomorph
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev inverseLimitCarrier := (limit readoutDiagram).carrier
abbrev flow := scalarDilationSymbolicLatentFlow

variable [T2Space inverseLimitCarrier]

def fixedPointRangeMirrorPoint
    (R : SymbolicLatentModularReversal flow)
    (ρ : inverseLimitCarrier) (hρ : R.involution ρ = ρ)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (n : ℕ) (X : MatStage n)
    (z : stageObservationRange ρ n X) :
    stageObservationRange ρ n X := z

noncomputable def fixedPointRangeMirrorHomeomorph
    (R : SymbolicLatentModularReversal flow)
    (ρ : inverseLimitCarrier) (hρ : R.involution ρ = ρ)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (n : ℕ) (X : MatStage n) :
    stageObservationRange ρ n X ≃ₜ stageObservationRange ρ n X :=
  Homeomorph.refl _

@[simp] theorem fixedPointRangeMirrorHomeomorph_apply
    (R : SymbolicLatentModularReversal flow)
    (ρ : inverseLimitCarrier) (hρ : R.involution ρ = ρ)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (n : ℕ) (X : MatStage n)
    (z : stageObservationRange ρ n X) :
    (fixedPointRangeMirrorHomeomorph R ρ hρ hreadout n X z).1 = z.1 := by
  rfl

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFixedPoint

end
