import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalCompHaus

/-!
# Obstruction to naive reversal-flow covariance on scalar ranges

The reversal transport preserves the scalar readout, while the dilation flow
multiplies it by `exp t`.  This owner records the exact scalar obstruction to
postulating a reversal-flow square without an additional covariance law.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFlowObstructionCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalCompHaus
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

theorem scalar_obstruction_of_reversal_flow_square
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (hsquare : ∀ z : stageObservationRangeCompHaus ρ n X,
      ((CategoryTheory.eqToHom
        (congrArg (fun w => stageObservationRangeCompHaus w n X)
          (R.reverses_flow t ρ)))
        ((stageObservationRangeReversalCompHausIso R hreadout
          (flow.act t ρ) n X).hom
          ((stageObservationRangeFlowCompHausIso ρ n X t).hom z))).1 =
      ((stageObservationRangeFlowCompHausIso (R.involution ρ) n X (-t)).hom
        ((stageObservationRangeReversalCompHausIso R hreadout ρ n X).hom z)).1) :
    ∀ z : stageObservationRangeCompHaus ρ n X,
      (Real.exp t - Real.exp (-t)) * z.1 = 0 := by
  intro z
  have hs := hsquare z
  have htransport := observationRangeEqToHom_val n X
    (R.reverses_flow t ρ)
    ((stageObservationRangeReversalCompHausIso R hreadout
      (flow.act t ρ) n X).hom
      ((stageObservationRangeFlowCompHausIso ρ n X t).hom z))
  rw [htransport] at hs
  rw [stageObservationRangeReversalCompHausIso_hom_apply] at hs
  rw [stageObservationRangeFlowCompHausIso_hom_apply] at hs
  rw [stageObservationRangeFlowCompHausIso_hom_apply] at hs
  rw [stageObservationRangeReversalCompHausIso_hom_apply] at hs
  linarith

theorem stageObservationRange_zero_of_reversal_flow_square
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (ht : t ≠ 0)
    (hsquare : ∀ z : stageObservationRangeCompHaus ρ n X,
      ((CategoryTheory.eqToHom
        (congrArg (fun w => stageObservationRangeCompHaus w n X)
          (R.reverses_flow t ρ)))
        ((stageObservationRangeReversalCompHausIso R hreadout
          (flow.act t ρ) n X).hom
          ((stageObservationRangeFlowCompHausIso ρ n X t).hom z))).1 =
      ((stageObservationRangeFlowCompHausIso (R.involution ρ) n X (-t)).hom
        ((stageObservationRangeReversalCompHausIso R hreadout ρ n X).hom z)).1) :
    ∀ z : stageObservationRangeCompHaus ρ n X, z.1 = 0 := by
  have hcoeff : Real.exp t - Real.exp (-t) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hexp
    apply ht
    have harg : t = -t := Real.exp_injective hexp
    linarith
  intro z
  rcases mul_eq_zero.mp
      (scalar_obstruction_of_reversal_flow_square
        R hreadout ρ n X t hsquare z) with h | h
  · exact (hcoeff h).elim
  · exact h

theorem no_reversal_flow_square_on_nontrivial_range
    (R : SymbolicLatentModularReversal flow)
    (hreadout : ∀ (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n)
      (y : SymbolicLatentModularOrbitClosure flow ρ),
      orbitClosureStageObservationTopCatHom (R.involution ρ) n X
          (R.orbitClosureHomeomorph ρ y) =
        orbitClosureStageObservationTopCatHom ρ n X y)
    (ρ : inverseLimitCarrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (ht : t ≠ 0)
    (hnontrivial : ∃ z : stageObservationRangeCompHaus ρ n X, z.1 ≠ 0)
    (hsquare : ∀ z : stageObservationRangeCompHaus ρ n X,
      ((CategoryTheory.eqToHom
        (congrArg (fun w => stageObservationRangeCompHaus w n X)
          (R.reverses_flow t ρ)))
        ((stageObservationRangeReversalCompHausIso R hreadout
          (flow.act t ρ) n X).hom
          ((stageObservationRangeFlowCompHausIso ρ n X t).hom z))).1 =
      ((stageObservationRangeFlowCompHausIso (R.involution ρ) n X (-t)).hom
        ((stageObservationRangeReversalCompHausIso R hreadout ρ n X).hom z)).1) :
    False := by
  obtain ⟨z, hz⟩ := hnontrivial
  exact hz
    (stageObservationRange_zero_of_reversal_flow_square
      R hreadout ρ n X t ht hsquare z)


end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFlowObstructionCompHaus
