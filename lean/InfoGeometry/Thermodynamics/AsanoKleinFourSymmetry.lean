import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

open scoped ComplexConjugate

/-!
# InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry

V4 CPT/Mobius compactification of the Asano symmetry group.

This module formalizes the Klein-four action on the fugacity plane. By
exploiting inversion and conjugation symmetries of the Lee-Yang/Asano
forbidden sets, it reduces the global analytic covering argument to a finite
orbit check over endpoint representatives.

Honest status: this module provides the topological reduction skeleton. The
actual global nondegenerate Asano theorem remains deferred as socket debt.
-/

noncomputable section

namespace InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry

/-- The `V4` (Klein-four) symmetry group generators for the Asano chart. -/
@[rep_depth thermo]
inductive V4
| id
| inv
| conj
| cpt
deriving DecidableEq, Repr

/-- The native action of `V4` on the complex fugacity plane. -/
@[rep_depth thermo]
def v4Action (g : V4) (z : ℂ) : ℂ :=
  match g with
  | V4.id => z
  | V4.inv => z⁻¹
  | V4.conj => conj z
  | V4.cpt => (conj z)⁻¹

/-- A set of complex roots is `V4`-symmetric if it is closed under the action. -/
@[rep_depth thermo]
def IsV4Symmetric (S : Set ℂ) : Prop :=
  ∀ (g : V4) (z : ℂ), z ∈ S → v4Action g z ∈ S

/--
The structural witness for `V4` compactification.

It asserts that checking the condition at the boundary representatives of the
`V4` fundamental domain is logically equivalent to checking the global analytic
condition.
-/
@[socket_debt_tag, rep_depth thermo]
structure AsanoCompactificationWitness
    (AsanoRootCondition EndpointRepresentativeCheck : ℂ → Set ℂ → Prop) where
  /-- The endpoints capture the full degrees of freedom of the `V4` orbit. -/
  orbit_reduction :
    ∀ (z : ℂ) (S : Set ℂ), IsV4Symmetric S →
    (EndpointRepresentativeCheck z S ↔ AsanoRootCondition (v4Action V4.id z) S)

/--
Capstone reduction: if the finite endpoint check holds, the global condition
holds as well.
-/
@[rep_depth thermo, capstone]
theorem asano_nondegenerate_orbit_reduction
    (W : AsanoCompactificationWitness AsanoRootCondition EndpointRepresentativeCheck)
    (S : Set ℂ) (hSymm : IsV4Symmetric S)
    (z : ℂ)
    (h_endpoint : EndpointRepresentativeCheck z S) :
    AsanoRootCondition z S := by
  have h_equiv := W.orbit_reduction z S hSymm
  have h_id : v4Action V4.id z = z := rfl
  rw [h_id] at h_equiv
  exact h_equiv.mp h_endpoint

end InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry
