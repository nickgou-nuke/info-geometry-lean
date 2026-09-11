import InfoGeometry.Canonical.ColimitTraceFormula
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.FiniteCovarianceMajoranaBlock

/-!
# The finite-stage Primon matrix tower

This file is a small application-facing facade for the existing matrix trace
tower.  Its stages are `M_(2^n)(ℂ)`, its bonding map is the native Kronecker
embedding `A ↦ A ⊗ I₂`, and its trace is the already descended normalized
trace on the algebraic direct limit.

The finite real covariance/Majorana block is kept as a separate local
two-level readout.  No tensor-product C*-completion, Gibbs state, spectral
trace formula, or claim about zeta zeros is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimonColimitAlgebra

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.ColimitTraceFormula
open InfoGeometry.Krein.FiniteCovarianceMajoranaBlock

abbrev PrimonStage (n : ℕ) := MatrixStage n
abbrev PrimonCarrier := Carrier

/-- The canonical successor embedding `A ↦ A ⊗ I₂`, transported to `M_(2^(n+1))`.
-/
noncomputable def primonBond (n : ℕ) :
    PrimonStage n →⋆ₐ[ℂ] PrimonStage (n + 1) :=
  concreteStep n

@[simp] theorem primonBond_trace (n : ℕ) (A : PrimonStage n) :
    matrixTraceState (n + 1) (primonBond n A) = matrixTraceState n A := by
exact concreteData.trace_compatible n A

theorem primonBond_injective (n : ℕ) :
    Function.Injective (primonBond n) := by
  exact concreteStep_injective n

/-- The normalized trace on the Primon colimit, using the existing descent. -/
noncomputable def primonTrace : PrimonCarrier →ₗ[ℂ] ℂ :=
  normalizedColimitTrace

@[simp] theorem primonTrace_stage (n : ℕ) (A : PrimonStage n) :
    primonTrace (stageInjection n A) = matrixTraceState n A := by
  exact normalizedColimitTrace_stage n A

theorem primonTrace_one : primonTrace (1 : PrimonCarrier) = 1 := by
  exact normalizedColimitTrace_one

theorem primonTrace_cyclic (x y : PrimonCarrier) :
    primonTrace (x * y) = primonTrace (y * x) := by
  exact normalizedColimitTrace_cyclic x y

theorem primonTrace_commutator_zero (x y : PrimonCarrier) :
    primonTrace (x * y - y * x) = 0 := by
  exact normalizedColimitTrace_commutator_zero x y

theorem primonTrace_star (x : PrimonCarrier) :
    primonTrace (star x) = star (primonTrace x) := by
  exact normalizedColimitTrace_star x

theorem primonTrace_positive (x : PrimonCarrier) :
    0 ≤ (primonTrace (star x * x)).re := by
  exact normalizedColimitTrace_positive x

theorem covarianceMajorana_stage_one
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    fundamentalSymmetry c * fundamentalSymmetry c =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      complexAxis * complexAxis =
        -(1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      complexAxis * fundamentalSymmetry c =
        -(fundamentalSymmetry c * complexAxis) := by
  exact covarianceMajorana_split_quaternionic_relations hc hc1

end InfoGeometry.Canonical.PrimonColimitAlgebra
