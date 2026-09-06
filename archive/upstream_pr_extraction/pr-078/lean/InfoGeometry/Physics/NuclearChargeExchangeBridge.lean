import Mathlib.Tactic
import InfoGeometry.Physics.IsospinMirrorDynamics

/-!
# Nuclear proton--neutron charge exchange

The proton/neutron exchange is an involutive state-space readout.  It is not
introduced as an additional Lie generator; its action is recorded on the
existing `Nucleus` carrier and on the derived isospin observables.
-/

namespace InfoGeometry.Physics.NuclearChargeExchangeBridge

open InfoGeometry.Physics

noncomputable section

/-- Exchange proton and neutron numbers in a nucleus. -/
def chargeExchange (nuc : Nucleus) : Nucleus := (nuc.N, nuc.Z)

@[simp]
theorem chargeExchange_involutive (nuc : Nucleus) :
    chargeExchange (chargeExchange nuc) = nuc := by
  rfl

@[simp]
theorem chargeExchange_preserves_mass (nuc : Nucleus) :
    (chargeExchange nuc).A = nuc.A := by
  simp [chargeExchange, Nucleus.A, add_comm]

@[simp]
theorem chargeExchange_negates_twoTz (nuc : Nucleus) :
    (chargeExchange nuc).twoTz = -nuc.twoTz := by
  simp [chargeExchange, Nucleus.twoTz]

/-- Charge-symmetric observables are invariant under proton--neutron exchange. -/
def IsChargeExchangeInvariant (f : Nucleus → ℝ) : Prop :=
  ∀ nuc, f (chargeExchange nuc) = f nuc

theorem constant_isChargeExchangeInvariant (c : ℝ) :
    IsChargeExchangeInvariant (fun _ : Nucleus => c) := by
  intro nuc
  rfl

end

end InfoGeometry.Physics.NuclearChargeExchangeBridge
