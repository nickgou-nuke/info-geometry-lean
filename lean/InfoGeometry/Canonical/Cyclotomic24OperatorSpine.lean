import Mathlib
import InfoGeometry.Canonical.CyclotomicOperatorSpine

/-!
# Compatibility and integer-polynomial view of the 24-fold spine

The operator-level owner is `CyclotomicOperatorSpine`.  This file supplies
the upstream integer-polynomial presentation without asserting a spectral
realization for any particular physical operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cyclotomic24OperatorSpine

open Polynomial

def master25 : ℤ[X] := X * (X ^ 24 - 1)

theorem master25_explicit_factorization :
    master25 = X * (X - 1) * (X + 1) * (X ^ 2 + X + 1) *
      (X ^ 2 + 1) * (X ^ 2 - X + 1) * (X ^ 4 + 1) *
      (X ^ 4 - X ^ 2 + 1) * (X ^ 8 - X ^ 4 + 1) := by
  unfold master25
  ring

theorem tripotent_dvd_master25 : X ^ 3 - X ∣ master25 := by
  refine ⟨X ^ 22 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 12 +
      X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + 1, ?_⟩
  unfold master25
  ring

theorem phi24_dvd_master25 : X ^ 8 - X ^ 4 + 1 ∣ master25 := by
  refine ⟨X * (X ^ 16 + X ^ 12 - X ^ 4 - 1), ?_⟩
  unfold master25
  ring

end InfoGeometry.Canonical.Cyclotomic24OperatorSpine
