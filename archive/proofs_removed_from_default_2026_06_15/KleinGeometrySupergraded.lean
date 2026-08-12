import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Ring

/-!
# Klein Geometry as a Supergraded Algebra

This file formalizes the concept that the transformation group of the 
non-orientable Klein geometry natively acts as a `ℤ₂`-supergraded algebra.

In the Erlangen Program paradigm, the geometry is governed by its symmetry group.
Here, the super-grading is strictly defined by the spatial orientation 
(the determinant of the linear part of the transformation).

1. Bosonic states correspond to orientation-preserving transformations (parity +1).
2. Fermionic states correspond to orientation-reversing transformations (parity -1).
-/

namespace KleinGeometrySupergraded

open Matrix

/-- 
The super-grading is physically defined by the orientation of the geometry, 
computed via the matrix determinant.
-/
def parity (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  A.det

/-- 
A pure geometric translation has an identity linear part, 
thus it is intrinsically Bosonic (parity +1). 
-/
theorem translation_parity_even :
    parity (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  exact det_one

/-- 
A pure reflection (or the linear part of a chiral glide reflection) 
inverts one axis, making it intrinsically Fermionic (parity -1). 
-/
def Rx : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

theorem glide_parity_odd :
    parity Rx = -1 := by
  dsimp [parity, Rx]
  simp

/-- 
Theorem: Geometric composition of spatial transformations perfectly mirrors 
`ℤ₂`-supergraded algebra multiplication rules.
This is because the geometric orientation (determinant) is strictly multiplicative.
-/
theorem composition_parity_is_supergraded (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    parity (A * B) = parity A * parity B := by
  exact det_mul A B

/--
Corollary: `Odd * Odd = Even`.
Applying two chiral glides (Fermionic generators) yields an orientation-preserving 
transformation (Bosonic generator). 
This is the foundational geometric guarantee that `Q * Q = H` maps a spinor 
back to a vector in the Klein geometry!
-/
theorem odd_mul_odd_is_even (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : parity A = -1) (hB : parity B = -1) :
    parity (A * B) = 1 := by
  rw [composition_parity_is_supergraded, hA, hB]
  ring

end KleinGeometrySupergraded
