import Mathlib
import InfoGeometry.Canonical.Drazin
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Meta.Architecture

/-!
# Drazin modular persistence

Drazin support as a modular fixed-point horizon.

Principle:

* the Drazin support `p = A * Aᴰ` is the algebraic support of persistence;
* modular fixedness upgrades that support to a physical horizon;
* horizon zero modes are observables localized on that Drazin horizon;
* Fierz residual vanishing is not inferred from modular fixedness alone, but
  from an explicit compatibility witness for horizon zero-mode channels.

This file is an abstract socket.  It does not replace the repo's concrete
Drazin, modular-flow, or Fierz readout owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinModularPersistence

open InfoGeometry.Canonical.Drazin
open InfoGeometry.OperatorAlgebra.Thermodynamics

/-- The theorem-safe zero-mode condition for an abstract modular flow. -/
@[rep_depth operator]
def IsModularZeroMode
    {Obs : Type*} [Ring Obs]
    (flow : ModularFlow Obs)
    (x : Obs) : Prop :=
  ∀ t : ℝ, flow.flow t x = x

/--
Drazin inverse/support data.

`AD` is the Drazin inverse candidate and `p = A * AD` is the Drazin support.
The index is included for general Drazin theory; group-invertible cases use
index `1`.
-/
@[rep_depth operator]
structure DrazinSupportData
    (Obs : Type*) [Ring Obs] [Star Obs] where
  A : Obs
  AD : Obs
  p : Obs
  index : ℕ
  drazin_True : IsDrazinInverse A AD index
  p_def : p = A * AD
  p_self_adjoint : star p = p

namespace DrazinSupportData

variable {Obs : Type*} [Ring Obs] [Star Obs]
variable (D : DrazinSupportData Obs)

/-- The Drazin support is idempotent. -/
@[rep_depth operator]
theorem p_idempotent :
    D.p * D.p = D.p := by
  rw [D.p_def]
  simpa [IsDrazinInverse.projection] using
    IsDrazinInverse.projection_is_idempotent D.drazin_True

/-- The Drazin complementary projector. -/
@[rep_depth operator]
def q : Obs :=
  1 - D.p

end DrazinSupportData

/--
A Drazin support becomes a physical horizon exactly when it is fixed by the
modular flow.
-/
@[rep_depth operator]
def IsPhysicalHorizon
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs) : Prop :=
  IsModularZeroMode flow D.p

/--
Alias for the physical interpretation:
a Drazin support acts as a modular stability filter exactly when its support
projector is fixed by the modular flow.

This is not a redefinition of the Drazin projector.  It is the extra
modular-zero condition on the already algebraic Drazin support.
-/
@[rep_depth operator]
abbrev IsDrazinModularStabilityFilter
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs) : Prop :=
  IsPhysicalHorizon flow D