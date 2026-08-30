import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowHomeomorph
import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosure

/-!
# Reversal transport of finite-stage observation ranges

This owner packages a theorem-honest mirror action on finite-stage readout
ranges.  The ambient involution is supplied as a modular reversal, while the
readout covariance is explicit data.  No parity, KMS, or operator-algebraic
interpretation is inferred from the involution alone.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalHomeomorph

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev inverseLimitCarrier := (limit readoutDiagram).carrier
abbrev flow := scalarDilationSymbolicLatentFlow

variable [T2Space inverseLimitCarrier]

def reversalTransportedRangePoint
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
    (z : stageObservationRange ρ n X) :
    stageObservationRange (R.involution ρ) n X := by
  let y : SymbolicLatentModularOrbitClosure flow ρ :=
    Classical.choose z.property
  have hy : orbitClosureStageObservationTopCatHom ρ n X y = z.1 :=
    Classical.choose_spec z.property
  refine ⟨z.1, ?_⟩
  refine ⟨R.orbitClosureHomeomorph ρ y, ?_⟩
  change orbitClosureStageObservationTopCatHom (R.involution ρ) n X
      (R.orbitClosureHomeomorph ρ y) = z.1
  rw [hreadout ρ n X y, hy]

def reversalTransportedRangePointInv
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
    (z : stageObservationRange (R.involution ρ) n X) :
    stageObservationRange ρ n X := by
  let y : SymbolicLatentModularOrbitClosure flow (R.involution ρ) :=
    Classical.choose z.property
  have hy :
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X y = z.1 :=
    Classical.choose_spec z.property
  let y0 : SymbolicLatentModularOrbitClosure flow ρ :=
    ⟨(R.orbitClosureHomeomorph (R.involution ρ) y).1, by
      have hm := (R.orbitClosureHomeomorph (R.involution ρ) y).property
      simpa [R.involution.involutive ρ] using hm⟩
  have hreadoutInv :
      orbitClosureStageObservationTopCatHom ρ n X y0 = z.1 := by
    have h := hreadout (R.involution ρ) n X y
    simpa [y0, R.involution.involutive ρ] using h.trans hy
  exact ⟨z.1, ⟨y0, hreadoutInv⟩⟩

noncomputable def stageObservationRangeReversalHomeomorph
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) :
    stageObservationRange ρ n X ≃ₜ
      stageObservationRange (R.involution ρ) n X where
  toFun := reversalTransportedRangePoint R hreadout ρ n X
  invFun := reversalTransportedRangePointInv R hreadout ρ n X
  left_inv := by
    intro z
    apply Subtype.ext
    change z.1 = z.1
    rfl
  right_inv := by
    intro z
    apply Subtype.ext
    change z.1 = z.1
    rfl
  continuous_toFun := by
    let f : stageObservationRange ρ n X →
        stageObservationRange (R.involution ρ) n X := fun z =>
      ⟨z.1, (reversalTransportedRangePoint R hreadout ρ n X z).property⟩
    have hf : Continuous f := by
      exact continuous_subtype_val.subtype_mk
        (fun z => (reversalTransportedRangePoint R hreadout ρ n X z).property)
    have hfun : f = reversalTransportedRangePoint R hreadout ρ n X := by
      funext z
      apply Subtype.ext
      rfl
    rw [← hfun]
    exact hf
  continuous_invFun := by
    let f : stageObservationRange (R.involution ρ) n X →
        stageObservationRange ρ n X := fun z =>
      ⟨z.1, (reversalTransportedRangePointInv R hreadout ρ n X z).property⟩
    have hf : Continuous f := by
      exact continuous_subtype_val.subtype_mk
        (fun z => (reversalTransportedRangePointInv R hreadout ρ n X z).property)
    have hfun : f = reversalTransportedRangePointInv R hreadout ρ n X := by
      funext z
      apply Subtype.ext
      rfl
    rw [← hfun]
    exact hf

@[simp] theorem stageObservationRangeReversalHomeomorph_apply
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
    (z : stageObservationRange ρ n X) :
    (stageObservationRangeReversalHomeomorph R hreadout ρ n X z).1 = z.1 := by
  change z.1 = z.1
  rfl

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalHomeomorph
end
