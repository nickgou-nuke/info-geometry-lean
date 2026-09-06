import InfoGeometry.Canonical.SouriauThermodynamics

/-!
# InfoGeometry.Canonical.SouriauMetriplecticContext

Finite Souriau/Onsager metriplectic context.

This file formalizes only the source-supported finite shadow:

- the reversible/Poisson sector contributes no entropy production under an
  explicit Casimir property;
- the metric/Onsager sector is the existing Souriau-Fisher response
  quadratic form;
- the response diagonal positivity is constructed from variance identities;
- the remaining determinant/non-spinodal gate is the determinant of this
  finite `2 × 2` response matrix, not the `det(exp A)` H¹ volume cocycle;
- that response-matrix gate gives the finite second-law inequality for the
  total entropy production.

It does not claim a full infinite-dimensional coadjoint-orbit metriplectic
flow.
-/

namespace InfoGeometry.Canonical.SouriauMetriplectic

open SouriauThermodynamics
open InfoGeometry.GrandCanonical

variable {α : Type _}

/--
Explicit finite metriplectic context for a Souriau two-channel shadow.

`reversibleEntropyRate` represents the Poisson/symplectic contribution.  The
field `casimir_reversible` is the honest Casimir property: the reversible
sector preserves entropy.  The metric sector is the already-owned
Souriau-Fisher/Onsager response matrix.  Its diagonal PSD entries are proved
from variance identities; only the finite response-matrix determinant gate
remains as a field.  This determinant gate is unrelated to the
`MatrixDetExpTrace` volume-cocycle theorem.
-/
structure MetriplecticContext [Fintype α] [Nonempty α] where
  M : SouriauMomentMap α
  T : GeometricTemperature
  forceBeta : ℝ
  forceMu : ℝ
  reversibleEntropyRate : ℝ
  casimir_reversible : reversibleEntropyRate = 0
  fisher_determinant_nonnegative :
    0 ≤ (souriauFisherResponseMatrix M T).det

namespace MetriplecticContext

variable [Fintype α] [Nonempty α]
variable (C : MetriplecticContext (α := α))

/-- The reversible/Poisson entropy-production channel. -/
@[rep_depth transport]
def reversibleEntropyProduction : ℝ :=
  C.reversibleEntropyRate

/-- The metric/Onsager entropy-production channel. -/
@[rep_depth transport]
noncomputable def metricEntropyProduction : ℝ :=
  souriauEntropyProduction C.M C.T C.forceBeta C.forceMu

/-- Total finite metriplectic entropy production: reversible plus metric. -/
@[rep_depth transport]
noncomputable def totalEntropyProduction : ℝ :=
  C.reversibleEntropyProduction + C.metricEntropyProduction

/-- Casimir property: the reversible sector contributes zero entropy production. -/
@[rep_depth transport]
theorem reversibleEntropyProduction_eq_zero :
    C.reversibleEntropyProduction = 0 :=
  C.casimir_reversible

/-- The total finite entropy production reduces to the metric/Onsager channel. -/
@[rep_depth transport]
theorem totalEntropyProduction_eq_metric :
    C.totalEntropyProduction = C.metricEntropyProduction := by
  unfold totalEntropyProduction
  rw [reversibleEntropyProduction_eq_zero]
  simp

/--
The finite Fisher response is positive semidefinite constructively from
variance diagonal positivity plus the remaining `2 × 2` response determinant
gate.
-/
@[rep_depth transport]
theorem fisher_positiveSemidefinite :
    (souriauFisherResponseMatrix C.M C.T).PositiveSemidefinite :=
  souriauFisherResponseMatrix_positiveSemidefinite_of_det_nonneg
    C.M C.T C.fisher_determinant_nonnegative

/--
The metric/Onsager channel is nonnegative under the finite response-matrix
determinant gate.
-/
@[rep_depth transport]
theorem metricEntropyProduction_nonneg :
    0 ≤ C.metricEntropyProduction := by
  exact souriauEntropyProduction_nonneg_of_det_nonneg
    C.M C.T C.fisher_determinant_nonnegative C.forceBeta C.forceMu

/--
Finite metriplectic second-law shadow: if the reversible sector is a Casimir
direction and the Souriau-Fisher response determinant gate is nonnegative,
total entropy production is nonnegative.
-/
@[rep_depth transport]
theorem totalEntropyProduction_nonneg :
    0 ≤ C.totalEntropyProduction := by
  rw [totalEntropyProduction_eq_metric]
  exact metricEntropyProduction_nonneg C

end MetriplecticContext

end InfoGeometry.Canonical.SouriauMetriplectic
