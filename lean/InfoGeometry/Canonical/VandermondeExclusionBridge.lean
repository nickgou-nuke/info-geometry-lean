import Mathlib.LinearAlgebra.Vandermonde
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.VandermondeExclusionBridge

Finite Vandermonde exclusion shadow for the fermionic/determinantal corridor.

This file is intentionally narrow.  It packages the exact finite-dimensional
`Matrix.vandermonde` determinant identities from mathlib as the owner surface
for the exclusion/zero-locus lane:

* collision of two nodes forces the Vandermonde determinant to vanish;
* nonvanishing of the determinant is equivalent to injectivity of the node map.

It does **not** claim to formalize CAR, Slater determinants, AQFT, or Type III
operator algebras.  Those remain owned elsewhere or explicit debt.
-/

namespace InfoGeometry.Canonical.VandermondeExclusionBridge

open scoped Matrix

universe u

section CommRing

variable {R : Type u} [CommRing R] {n : ℕ}

/--
Finite Vandermonde exclusion witness.

The `nodes` field is the finite list of coordinates/weights whose pairwise
collisions are detected by the Vandermonde determinant.
-/
@[rep_depth thermo]
structure FiniteVandermondeExclusionWitness where
  nodes : Fin n → R

namespace FiniteVandermondeExclusionWitness

variable (W : FiniteVandermondeExclusionWitness (R := R) (n := n))

/-- The finite Vandermonde matrix attached to the witness nodes. -/
@[rep_depth thermo]
def matrix : Matrix (Fin n) (Fin n) R :=
  Matrix.vandermonde W.nodes

/-- The determinant readout of the witness matrix. -/
@[rep_depth thermo]
def determinant : R :=
  W.matrix.det

/-- The determinant is the exact Vandermonde separation product. -/
@[rep_depth thermo]
theorem determinant_eq_pairwise_separation :
    W.determinant = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (W.nodes j - W.nodes i) := by
  unfold determinant matrix
  simpa using Matrix.det_vandermonde W.nodes

end FiniteVandermondeExclusionWitness

end CommRing

section Domain

variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

namespace FiniteVandermondeExclusionWitness

variable (W : FiniteVandermondeExclusionWitness (R := R) (n := n))

/--
Zero-locus theorem for the finite Vandermonde shadow.

The determinant vanishes exactly when two distinct nodes collide.
-/
@[rep_depth thermo]
theorem determinant_eq_zero_iff_collision :
    W.determinant = 0 ↔ ∃ i j : Fin n, W.nodes i = W.nodes j ∧ i ≠ j := by
  unfold determinant matrix
  simpa using (Matrix.det_vandermonde_eq_zero_iff (v := W.nodes))

/--
Injectivity theorem for the finite Vandermonde shadow.

The determinant is nonzero exactly when the node map is injective.
-/
@[rep_depth thermo]
theorem determinant_ne_zero_iff_injective :
    W.determinant ≠ 0 ↔ Function.Injective W.nodes := by
  unfold determinant matrix
  simpa using (Matrix.det_vandermonde_ne_zero_iff (v := W.nodes))

/--
Finite Pauli/exclusion shadow:
if two distinct nodes coincide, the Vandermonde determinant collapses to zero.
-/
@[rep_depth thermo]
theorem collision_forces_determinant_zero
    {i j : Fin n} (hij : i ≠ j) (hEq : W.nodes i = W.nodes j) :
    W.determinant = 0 := by
  rw [W.determinant_eq_zero_iff_collision]
  exact ⟨i, j, hEq, hij⟩

/--
Contrapositive exclusion shadow:
if the determinant is nonzero, distinct indices cannot occupy the same node.
-/
@[rep_depth thermo]
theorem determinant_ne_zero_forbids_collision
    (hdet : W.determinant ≠ 0) {i j : Fin n} (hEq : W.nodes i = W.nodes j) :
    i = j := by
  exact (W.determinant_ne_zero_iff_injective.mp hdet) hEq

/--
Packet form of the finite exclusion shadow.
-/
@[rep_depth thermo]
theorem exclusion_packet :
    (W.determinant ≠ 0 ↔ Function.Injective W.nodes) ∧
      (W.determinant = 0 ↔ ∃ i j : Fin n, W.nodes i = W.nodes j ∧ i ≠ j) := by
  exact ⟨W.determinant_ne_zero_iff_injective, W.determinant_eq_zero_iff_collision⟩

end FiniteVandermondeExclusionWitness

end Domain

end InfoGeometry.Canonical.VandermondeExclusionBridge
