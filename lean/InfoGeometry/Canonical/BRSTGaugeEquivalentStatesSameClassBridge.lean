import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.BRSTGaugeEquivalentStatesSameClassBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.BRSTExactClassZeroBridge
open InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: BRST Gauge Equivalent States Have Identical Cohomology Classes [ψ + Q χ] = [ψ] in H_Q = ker Q / im Q. -/
theorem brst_gauge_equivalent_states_same_class
    (q : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (psi : LinearMap.ker q)
    (chi : ExteriorAlgebra R V) :
    Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2))
      ⟨psi.1 + q chi, by
        rw [LinearMap.mem_ker]
        rw [LinearMap.map_add]
        have hpsi : q psi.1 = 0 := psi.2
        have hqchi : q (q chi) = 0 := LinearMap.congr_fun hq2 chi
        rw [hpsi, hqchi, add_zero]⟩ =
    (Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2)) psi : brstCohomologyModule q hq2) := by
  rw [Submodule.Quotient.eq]
  use ⟨q chi, LinearMap.mem_range_self q chi⟩
  ext
  dsimp [brstExactToClosed]
  simp

end InfoGeometry.Canonical.BRSTGaugeEquivalentStatesSameClassBridge
