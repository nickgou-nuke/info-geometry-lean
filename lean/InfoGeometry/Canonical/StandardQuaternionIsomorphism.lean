import Mathlib.Tactic

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
Quaternion multiplication identities for the proposed even-Clifford basis markers.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
This file proves the quaternion-side multiplication table only; it does not yet
construct an algebra equivalence from an even Clifford algebra.
-/

namespace InfoGeometry.Canonical.StandardQuaternionIsomorphism

open Quaternion

/--
We formalize a parallel, standalone version of the isomorphism between
the standard real even Clifford algebra Cl⁺(3,0; ℝ) and the Quaternions ℍ.

The basis elements of Cl⁺(3,0; ℝ) are {1, e₁e₂, e₂e₃, e₃e₁}.
To form a strict algebra isomorphism with the standard Quaternions (where ij = k),
we must map the generators carefully to account for the Clifford cross-terms:
  φ(e₂e₃) = i
  φ(e₃e₁) = j
  φ(e₁e₂) = -k
-/

def e23 : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def e31 : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def e12 : Quaternion ℝ := ⟨0, 0, 0, -1⟩

theorem e23_sq : e23 * e23 = -1 := by ext <;> simp [e23]
theorem e31_sq : e31 * e31 = -1 := by ext <;> simp [e31]
theorem e12_sq : e12 * e12 = -1 := by ext <;> simp [e12]

theorem cross_12_23 : e12 * e23 = -e31 := by ext <;> simp [e12, e23, e31]
theorem cross_23_31 : e23 * e31 = -e12 := by ext <;> simp [e12, e23, e31]
theorem cross_31_12 : e31 * e12 = -e23 := by ext <;> simp [e12, e23, e31]

end InfoGeometry.Canonical.StandardQuaternionIsomorphism
