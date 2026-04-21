import InfoGeometry.Canonical.SouriauThermodynamics

/-!
# InfoGeometry.Canonical.SouriauMetriplecticContext

Finite Souriau/Onsager metriplectic context.

This file formalizes only the source-supported finite shadow:

- the reversible/Poisson sector contributes no entropy production under an
  explicit Casimir hypothesis;
- the metric/Onsager sector is the existing Souriau-Fisher response
  quadratic form;
- the response diagonal positivity is constructed from variance identities;
- the remaining determinant/non-spinodal gate gives the finite second-law
  inequality for the total entropy production.

It does not claim a full infinite-dimensional coadjoint-orbit metriplectic
flow.
-/

namespace InfoGeometry.Canonical.SouriauMetriplectic

open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.GrandCanonical

variable {α : Type _}

/--
Explicit finite metriplectic context for a Souriau two-channel shadow.

`reversibleEntropyRate` represents the Poisson/symplectic contribution.  The
field `casimir_reversible` is the honest Casimir hypothesis: the reversible
sector preserves entropy.  The metric sector is the already-owned
Souriau-Fisher/Onsager response matrix.  Its diagonal PSD entries are proved
from variance identities; only the determinant gate remains as a field.
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
@[rep_depth thermo]
def reversibleEntropyProduction : ℝ :=
  C.reversibleEntropyRate

/-- The metric/Onsager entropy-production channel. -/
@[rep_depth thermo]
noncomputable def metricEntropyProduction : ℝ :=
  souriauEntropyProduction C.M C.T C.forceBeta C.forceMu

/-- Total finite metriplectic entropy production: reversible plus metric. -/
@[rep_depth thermo]
noncomputable def totalEntropyProduction : ℝ :=
  C.reversibleEntropyProduction + C.metricEntropyProduction

/-- Casimir hypothesis: the reversible sector contributes zero entropy production. -/
@[rep_depth thermo]
theorem reversibleEntropyProduction_eq_zero :
    C.reversibleEntropyProduction = 0 :=
  C.casimir_reversible

/-- The total finite entropy production reduces to the metric/Onsager channel. -/
@[rep_depth thermo]
theorem totalEntropyProduction_eq_metric :
    C.totalEntropyProduction = C.metricEntropyProduction := by
  unfold totalEntropyProduction
  rw [reversibleEntropyProduction_eq_zero]
  simp

/--
The finite Fisher response is positive semidefinite constructively from
variance diagonal positivity plus the remaining determinant gate.
-/
@[rep_depth thermo]
theorem fisher_positiveSemidefinite :
    (souriauFisherResponseMatrix C.M C.T).PositiveSemidefinite :=
  souriauFisherResponseMatrix_positiveSemidefinite_of_det_nonneg
    C.M C.T C.fisher_determinant_nonnegative

/-- The metric/Onsager channel is nonnegative under the determinant-gated Fisher response. -/
@[rep_depth thermo]
theorem metricEntropyProduction_nonneg :
    0 ≤ C.metricEntropyProduction := by
  exact souriauEntropyProduction_nonneg_of_det_nonneg
    C.M C.T C.fisher_determinant_nonnegative C.forceBeta C.forceMu

/--
Finite metriplectic second-law shadow: if the reversible sector is a Casimir
direction and the Souriau-Fisher determinant gate is nonnegative, total
entropy production is nonnegative.
-/
@[rep_depth thermo]
theorem totalEntropyProduction_nonneg :
    0 ≤ C.totalEntropyProduction := by
  rw [totalEntropyProduction_eq_metric]
  exact metricEntropyProduction_nonneg C

end MetriplecticContext

end InfoGeometry.Canonical.SouriauMetriplectic
