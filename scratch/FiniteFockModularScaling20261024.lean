/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import scratch.FiniteFockCLMReflexivePair20261024
import InfoGeometry.Canonical.RootsOfZeroUnityMoebiusModularG22
import InfoGeometry.Canonical.PeirceWeightedTrace

/-! Stream2 scaling on the actual finite Fock CLMs and its native support weight.
Uncompiled sandbox. Sandwiches below require no reciprocal-weight assumption
and are not asserted to be inverse conjugations. -/
noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford
open InfoGeometry.Canonical.RootsOfZeroUnityMoebiusModularG22
open InfoGeometry.Canonical.PeirceWeightedTrace
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

variable (n : ℕ) (i : Fin n)
local notation "D" => fockIntActionCLM n i
local notation "C" => fockExtActionCLM n i

/-- The native weight uses occupation first and coordinate vacancy second. -/
theorem fock_hyperbolicModularFlow_eq_supportWeight (lam mu : ℝ) :
    hyperbolicModularFlow D C lam mu = supportWeight mu lam D C := by
  simp only [hyperbolicModularFlow, harmonicZeroPole, activeSimplex,
    polePlus, poleMinus, fock_coordinate_CLM_CAR, sub_self, add_zero, supportWeight]
  exact add_comm _ _

/-- Direct readback on every original spinor, for arbitrary real coefficients. -/
theorem fock_hyperbolicModularFlow_apply (lam mu : ℝ)
    (x : SpinorSpace (Vector n)) :
    hyperbolicModularFlow D C lam mu x = lam • D (C x) + mu • C (D x) := by
  rw [fock_hyperbolicModularFlow_eq_supportWeight]
  change mu • C (D x) + lam • D (C x) = lam • D (C x) + mu • C (D x)
  exact add_comm _ _

/-- Raw sandwich scaling of contraction; no lam*mu=1 assumption. -/
theorem fock_hyperbolicModularFlow_sandwich_int (lam mu : ℝ) :
    hyperbolicModularFlow D C lam mu * D * hyperbolicModularFlow D C mu lam =
      (lam * lam) • D := by
  exact hyperbolicModularFlow_conj_d
    (fockIntActionCLM_sq_zero n i) (fockIntActionCLM_reflexive n i) lam mu

/-- Raw sandwich scaling of creation; the coefficient is mu squared. -/
theorem fock_hyperbolicModularFlow_sandwich_ext (lam mu : ℝ) :
    hyperbolicModularFlow D C lam mu * C * hyperbolicModularFlow D C mu lam =
      (mu * mu) • C := by
  exact hyperbolicModularFlow_conj_B
    (fockExtActionCLM_sq_zero n i) (fockExtActionCLM_reflexive n i) lam mu

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
