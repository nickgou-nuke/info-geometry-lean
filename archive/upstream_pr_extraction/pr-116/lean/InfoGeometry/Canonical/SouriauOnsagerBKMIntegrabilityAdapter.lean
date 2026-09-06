import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

/-!
# Integrability adapter for the finite Kubo--Mori pairing

The finite BKM owner deliberately exposes interval integrability as an
analytic hypothesis.  This adapter discharges that hypothesis whenever the
specific integrand is known to be continuous, without asserting continuity
of continuous-functional-calculus powers globally.
-/

namespace SouriauOnsagerBKM

open MeasureTheory
open scoped Interval

variable {n : ℕ}

theorem kuboMoriPairing_conj_symm_of_continuous
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n)
    (h_continuous : Continuous (D.kuboMoriIntegrand A B)) :
    star (D.kuboMoriPairing A B) = D.kuboMoriPairing B A := by
  apply D.kuboMoriPairing_conj_symm A B
  exact h_continuous.intervalIntegrable 0 1

end SouriauOnsagerBKM
