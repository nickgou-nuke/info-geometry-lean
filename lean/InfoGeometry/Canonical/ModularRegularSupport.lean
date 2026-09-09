import Mathlib.Data.Real.Basic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ModularRegularSupport

Theorem-safe socket for the statement:

* the regular support is fixed by a modular/spectral flow;
* the complementary support is therefore fixed when the flow is unital and
  subtraction-preserving;
* this complement may still be excluded from a chosen regular kinetic readout.

The file deliberately proves only the support-complement invariance law.  Any
thermodynamic interpretation of the complement as noise, residue, memory, or
central charge remains attached to the chosen readout packet.
-/

noncomputable section

namespace InfoGeometry.Canonical

/--
Abstract modular-flow packet for a regular support.

`regularSupport` is the support fixed by the flow.  The complement
`1 - regularSupport` is derived as `noiseSupport`.
-/
@[rep_depth krein]
structure ModularRegularSupport (Op : Type*) [Ring Op] where
  modularFlow : ℝ → Op → Op
  regularSupport : Op
  flow_one : ∀ t : ℝ, modularFlow t 1 = 1
  flow_sub : ∀ (t : ℝ) (X Y : Op),
    modularFlow t (X - Y) = modularFlow t X - modularFlow t Y
  regular_invariant : ∀ t : ℝ, modularFlow t regularSupport = regularSupport

namespace ModularRegularSupport

variable {Op : Type*} [Ring Op] (M : ModularRegularSupport Op)

/-- Complementary support relative to the regular modular support. -/
@[rep_depth krein]
def noiseSupport : Op :=
  1 - M.regularSupport

/--
If the flow fixes the regular support and preserves `1` and subtraction, it
also fixes the complementary support.
-/
@[rep_depth krein]
theorem noise_invariant :
    ∀ t : ℝ, M.modularFlow t M.noiseSupport = M.noiseSupport := by
  intro t
  calc
    M.modularFlow t M.noiseSupport
        = M.modularFlow t (1 - M.regularSupport) := rfl
    _ = M.modularFlow t 1 - M.modularFlow t M.regularSupport := by
          rw [M.flow_sub]
    _ = 1 - M.regularSupport := by
          rw [M.flow_one, M.regular_invariant]
    _ = M.noiseSupport := rfl

end ModularRegularSupport

end InfoGeometry.Canonical

