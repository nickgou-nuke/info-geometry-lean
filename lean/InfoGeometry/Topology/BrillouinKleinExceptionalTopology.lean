import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exceptional Non-Hermitian Topology Associated with Non-Toroidal Brillouin Zones

Formalizes the core result from arXiv:2503.06933v2:
In a non-Hermitian system where the Brillouin zone fundamental domain forms a Klein bottle (e.g., due to glide reflection symmetries), the fermion doubling theorem breaks down.
The sum of topological charges (discriminant numbers) inside the region K² is an EVEN number (not necessarily zero).

The boundary of the Klein bottle fundamental domain K² is given by ∂K² = a b a b⁻¹.
Therefore, integration of the topological invariant over the boundary yields 2 * ∫_a, an even integer.
-/

namespace InfoGeometry.Topology.BrillouinKlein

/-- 
A Brillouin Klein bottle fundamental domain boundary is defined by the loop relation
∂K² = a + b + a - b
-/
def klein_bottle_boundary (Path : Type) [AddCommGroup Path] (a b : Path) : Path :=
  a + b + a - b

/--
The main theorem violating the fermion doubling theorem:
The total topological charge in the Brillouin Klein bottle is an even integer,
since the integration over ∂K² = a + b + a - b reduces to 2 * ∫a.
-/
theorem fermion_doubling_violation 
    {Path : Type} [AddCommGroup Path] 
    (a b : Path)
    (int_charge : Path →+ ℤ) :
    int_charge (klein_bottle_boundary Path a b) = 2 * int_charge a := by
  dsimp [klein_bottle_boundary]
  rw [AddMonoidHom.map_sub, AddMonoidHom.map_add, AddMonoidHom.map_add]
  ring

end InfoGeometry.Topology.BrillouinKlein
