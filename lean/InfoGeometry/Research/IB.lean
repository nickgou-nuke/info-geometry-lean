import InfoGeometry.Assumptions.IB
import InfoGeometry.EntropicInference

/-!
# Research.IB

Domain module for the Information Bottleneck (IB) research API extracted from
historical `InfoGeometry/New.lean`.

Import boundary:
- constructive finite-probability primitives from `InfoGeometry.EntropicInference`
- IB draft interface from `InfoGeometry.Assumptions.IB`

This module is intentionally noncanonical and kept outside `InfoGeometry.Library`.
-/

namespace InfoGeometry.Research.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]

/-- Local finite-probability alias used by legacy IB wrappers. -/
abbrev FinProb (α : Type) [Fintype α] := InfoGeometry.EntropicInference.FinProb α

@[deprecated InfoGeometry.Assumptions.IB.IBProblem (since := "2026-02-25")]
abbrev IBProblem : Type :=
  InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y)

@[deprecated InfoGeometry.Assumptions.IB.KLKernel (since := "2026-02-25")]
noncomputable abbrev KLKernel (pX : FinProb X) (p q : X → FinProb T) : ℝ :=
  InfoGeometry.Assumptions.IB.KLKernel (X := X) (T := T) pX p q

@[deprecated InfoGeometry.Assumptions.IB.jointYT (since := "2026-02-25")]
noncomputable abbrev jointYT
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : FinProb (Y × T) :=
  InfoGeometry.Assumptions.IB.jointYT (X := X) (Y := Y) (T := T) prob pT_givenX

@[deprecated InfoGeometry.Assumptions.IB.inducedMProjection (since := "2026-02-25")]
noncomputable abbrev inducedMProjection
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (t : T) : FinProb Y :=
  InfoGeometry.Assumptions.IB.inducedMProjection
    (X := X) (Y := Y) (T := T) prob pT_givenX t

@[deprecated InfoGeometry.Assumptions.IB.energy (since := "2026-02-25")]
noncomputable abbrev energy
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) (t : T) : ℝ :=
  InfoGeometry.Assumptions.IB.energy (X := X) (Y := Y) (T := T) prob pT_givenX x t

@[deprecated InfoGeometry.Assumptions.IB.partitionFunction (since := "2026-02-25")]
noncomputable abbrev partitionFunction
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) : ℝ :=
  InfoGeometry.Assumptions.IB.partitionFunction (X := X) (Y := Y) (T := T) prob pT_givenX x

@[deprecated InfoGeometry.Assumptions.IB.exponentialTilt (since := "2026-02-25")]
noncomputable abbrev exponentialTilt
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) : FinProb T :=
  InfoGeometry.Assumptions.IB.exponentialTilt (X := X) (Y := Y) (T := T) prob pT_givenX x

@[deprecated InfoGeometry.Assumptions.IB.argmin_exponentialTilt (since := "2026-02-25")]
abbrev argmin_exponentialTilt
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : Prop :=
  InfoGeometry.Assumptions.IB.argmin_exponentialTilt (X := X) (Y := Y) (T := T) prob pT_givenX

@[deprecated InfoGeometry.Assumptions.IB.ibLagrangian (since := "2026-02-25")]
noncomputable abbrev ibLagrangian
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : ℝ :=
  InfoGeometry.Assumptions.IB.ibLagrangian (X := X) (Y := Y) (T := T) prob pT_givenX

@[deprecated InfoGeometry.Assumptions.IB.ibIteration (since := "2026-02-25")]
noncomputable abbrev ibIteration
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y)) :
    (X → FinProb T) → (X → FinProb T) :=
  InfoGeometry.Assumptions.IB.ibIteration (X := X) (Y := Y) (T := T) prob

@[deprecated InfoGeometry.Assumptions.IB.ib_stationary_point_gibbs (since := "2026-02-25")]
abbrev ib_stationary_point_gibbs
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : Prop :=
  InfoGeometry.Assumptions.IB.ib_stationary_point_gibbs
    (X := X) (Y := Y) (T := T) prob pT_givenX

@[deprecated InfoGeometry.Assumptions.IB.ib_convergence (since := "2026-02-25")]
abbrev ib_convergence
    (prob : InfoGeometry.Assumptions.IB.IBProblem (X := X) (Y := Y))
    (p_opt : X → FinProb T) : Prop :=
  InfoGeometry.Assumptions.IB.ib_convergence (X := X) (Y := Y) (T := T) prob p_opt

end InfoGeometry.Research.IB
