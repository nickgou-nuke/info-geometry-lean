import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.BRSTExactClassZeroBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Literal BRST Exact State Ghost Decoupling [Q_BRST χ] = 0 in Algebraic BRST Physical-State Quotient H_Q = ker Q / im Q. -/
theorem brst_exact_state_class_eq_zero
    (q : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (chi : ExteriorAlgebra R V) :
    Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2))
      ⟨q chi, by
        have h := LinearMap.congr_fun hq2 chi
        rw [LinearMap.mem_ker]
        exact h⟩ = (Submodule.Quotient.mk 0 : brstCohomologyModule q hq2) :=
  exact_state_class_eq_zero q hq2 chi

end InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
