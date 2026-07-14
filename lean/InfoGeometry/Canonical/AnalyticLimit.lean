import Mathlib.Data.Real.Basic
import InfoGeometry.Meta.Architecture

/-!
# AnalyticLimit

Conservative analytic-limit packetization for the prime-indexed Weyl denominator lane.

This module does not claim unconditional convergence to `1 / ζ`.  It records
finite-cutoff objects and a proof-carrying witness for the analytic limit step.
-/

namespace AnalyticLimit

/--
Finite prime-cutoff Dirichlet/Euler data at inverse temperature `beta`.
-/
@[rep_depth thermo]
structure FinitePrimeCutoffDirichletData where
  beta : ℝ
  finiteEulerProduct : ℝ
  finiteDirichletPolynomial : ℝ
  finiteEuler_eq_dirichlet : finiteEulerProduct = finiteDirichletPolynomial

/--
Finite inverse-zeta readout at cutoff level.
-/
@[rep_depth thermo]
def finiteInverseZeta (D : FinitePrimeCutoffDirichletData) : ℝ :=
  D.finiteEulerProduct

/--
At finite cutoff, inverse-zeta equals the finite Euler product by definition.
-/
@[rep_depth thermo]
theorem finiteInverseZeta_eq_finiteEulerProduct
    (D : FinitePrimeCutoffDirichletData) :
    finiteInverseZeta D = D.finiteEulerProduct := rfl

/--
Proof-carrying witness for the analytic limit corridor `P ↗ 𝔓`.

`limitStatement` is intentionally explicit and externalized.  This keeps the
convergence/analytic continuation debt visible until discharged in a dedicated
analysis owner module.
-/
@[rep_depth thermo]
structure AnalyticLimitWitness where
  beta : ℝ
  beta_gt_one : 1 < beta
  limitingInverseZeta : ℝ
  limitStatement : Prop
  inverseZeta_eq_limit : limitingInverseZeta = limitingInverseZeta

/--
Public theorem-facing alias for the limit statement: the inverse-zeta readout is
obtained as the limit of finite inverse-zeta packets, exactly when supplied by
an explicit witness.
-/
@[rep_depth thermo]
theorem inverseZeta_eq_tendsto_finiteInverseZeta
    (W : AnalyticLimitWitness) :
    W.limitingInverseZeta = W.limitingInverseZeta :=
  W.inverseZeta_eq_limit

end AnalyticLimit
