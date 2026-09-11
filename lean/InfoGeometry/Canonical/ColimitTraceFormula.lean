import InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixTraceColimitComparison

/-!
# Trace readouts and theorem targets on the matrix colimit

The normalized matrix trace and its descent are owned by
`CuntzMatrixAlgebraicTraceFunctional` and `CuntzMatrixTraceTower`.  This file
is only the small capstone interface: it exposes the descended trace together
with its algebraic consequences and records the analytic spectral formula as
an explicit target structure.

In particular, no Weil explicit formula, resolvent identity, positivity
argument for zeta zeros, or Riemann-Hypothesis conclusion is inferred here.
Those statements require additional analytic hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.ColimitTraceFormula

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

abbrev ColimitCarrier := Carrier

/-! ## The already-descended normalized trace -/

noncomputable def normalizedColimitTrace : ColimitCarrier →ₗ[ℂ] ℂ :=
  traceFunctional

@[simp]
theorem normalizedColimitTrace_stage (n : ℕ) (A : MatrixStage n) :
    normalizedColimitTrace (stageInjection n A) =
      matrixTraceState n A := by
  exact traceFunctional_stage n A

theorem normalizedColimitTrace_one :
    normalizedColimitTrace (1 : ColimitCarrier) = 1 := by
  exact traceFunctional_one

theorem normalizedColimitTrace_cyclic
    (x y : ColimitCarrier) :
    normalizedColimitTrace (x * y) =
      normalizedColimitTrace (y * x) := by
  exact traceFunctional_cyclic x y

theorem normalizedColimitTrace_commutator_zero
    (x y : ColimitCarrier) :
    normalizedColimitTrace (x * y - y * x) = 0 := by
  exact traceFunctional_commutator_zero x y

theorem normalizedColimitTrace_star
    (x : ColimitCarrier) :
    normalizedColimitTrace (star x) =
      star (normalizedColimitTrace x) := by
  exact traceFunctional_star x

theorem normalizedColimitTrace_positive
    (x : ColimitCarrier) :
    0 ≤ (normalizedColimitTrace (star x * x)).re := by
  exact traceFunctional_positive x

/-! ## Pointwise transport of an already-proved spectral comparison -/

theorem spectralAction_eq_zero_of_agreement
    (action arithmetic : ℂ → ℂ)
    (hagreement : ∀ s, action s = arithmetic s)
    (s : ℂ)
    (harithmetic_zero : arithmetic s = 0) :
    action s = 0 := by
  exact Eq.trans (hagreement s) (by assumption)

end InfoGeometry.Canonical.ColimitTraceFormula
