import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.TwoParticleAnnihilationDerivationBridge
import InfoGeometry.Canonical.EulerCharacteristicBettiIndexBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: BRST Operator Nilpotency Q_BRST² = 0 Implies Range is Submodule of Kernel (im Q_BRST ≤ ker Q_BRST). -/
theorem brst_range_le_ker
    (q_brst : Module.End R (ExteriorAlgebra R V))
    (hq2 : q_brst.comp q_brst = 0) :
    LinearMap.range q_brst ≤ LinearMap.ker q_brst :=
  range_d_le_ker_d q_brst hq2

/-- **Definition**: Physical Quantum Gauge Hilbert Space H_phys = ker(Q_BRST) / range(Q_BRST). -/
def physicalGaugeStateModule
    (q_brst : Module.End R (ExteriorAlgebra R V)) : Type _ :=
  LinearMap.ker q_brst ⧸ (LinearMap.range q_brst).comap (LinearMap.ker q_brst).subtype

/-- **Theorem**: BRST Ghost Transformation Exact Form Decoupling Q_BRST(Q_BRST χ) = 0. -/
theorem brst_ghost_decoupling
    (q_brst : Module.End R (ExteriorAlgebra R V))
    (hq2 : q_brst.comp q_brst = 0) (chi : ExteriorAlgebra R V) :
    q_brst (q_brst chi) = 0 :=
  exact_form_range_zero q_brst hq2 chi

end InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
