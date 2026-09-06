import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic

namespace InfoGeometry.Topology.CFT

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (L : ℤ → (V →ₗ[ℂ] V))

/--
A primary field (or highest weight state) of conformal dimension `Δ`.
This encodes the structural conditions:
1. Annihilated by positive modes: `L_n v = 0` for `n > 0`.
2. Eigenstate of `L_0`: `L_0 v = Δ • v`.
-/
def IsPrimaryState (v : V) (Δ : ℂ) : Prop :=
  (∀ (n : ℤ), n > 0 → L n v = 0) ∧
    L 0 v = Δ • v

namespace IsPrimaryState

/-- Compatibility projection for annihilation by positive Virasoro modes. -/
theorem annihilated_positive
    (h : IsPrimaryState L v Δ) : ∀ (n : ℤ), n > 0 → L n v = 0 :=
  h.1

/-- Compatibility projection for the highest-weight eigenvalue law. -/
theorem eigenstate_zero
    (h : IsPrimaryState L v Δ) : L 0 v = Δ • v :=
  h.2

end IsPrimaryState

/--
The State-Field correspondence structurally maps a state `v` to a field `V(z)`.
In a simplified structural setting, this associates to each state a field operator.
Here we represent a field operator as a function from the complex plane
to endomorphisms of `V`.
-/
structure StateFieldCorrespondence (L : ℤ → (V →ₗ[ℂ] V)) where
  /-- The map from states to fields -/
  fieldMap : V → (ℂ → (V →ₗ[ℂ] V))
  /-- Vacuum state -/
  vacuum : V
  /-- Vacuum is invariant under global conformal transformations (L_0, L_1, L_{-1}) -/
  vacuum_invariant_zero : L 0 vacuum = 0
  vacuum_invariant_one : L 1 vacuum = 0
  vacuum_invariant_neg_one : L (-1) vacuum = 0
  /-- State-field correspondence applied to the vacuum yields the identity -/
  field_vacuum : ∀ z : ℂ, fieldMap vacuum z = LinearMap.id
  /-- Applying the field to the vacuum at z=0 recovers the state -/
  state_recovery : ∀ v : V, fieldMap v 0 vacuum = v

end InfoGeometry.Topology.CFT
