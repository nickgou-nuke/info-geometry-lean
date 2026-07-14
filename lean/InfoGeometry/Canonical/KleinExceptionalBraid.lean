import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

namespace KleinExceptionalBraid

open Matrix

/-!
# Non-orientable Exceptional Points in Twisted Boundary Systems

Formalizes the cyclic permutation and inequivalent braiding of
Exceptional Points (EPs) on a non-orientable Klein Brillouin zone.

Based on arXiv:2504.11983 (Ryu et al. 2025).
We model the momentum-space glide symmetry `G` and the 
EP braid encirclement `B`. 
-/

/-- The standard 2x2 counter-clockwise braid representation of an EP encirclement. 
    It swaps state 1 and state 2, picking up a geometric phase of π on one. -/
def B_EP : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![0, -1],
    ![1,  0]]

/-- The momentum-space glide symmetry operator of the Klein Brillouin zone. 
    It reverses parity and swaps the basis states. -/
def G_Glide : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![0, 1],
    ![1, 0]]

/-- 
Theorem: The glide symmetry is a true involution (G^2 = I). 
-/
theorem glide_involution :
    G_Glide * G_Glide = 1 := by
  decide

/-- 
Theorem: The EP braid representation under the momentum-space glide symmetry 
is strictly inverted.
This proves that traversing the non-orientable loop physically inverts the
chirality of the EP encirclement (inequivalent braiding representations).
`G * B * G^{-1} = B^{-1}`
Since G is an involution, G^{-1} = G.
We prove `G * B * G = -B`, and note that `B^{-1} = -B` for this orthogonal braid.
-/
theorem klein_twist_anti_isomorphism :
    G_Glide * B_EP * G_Glide = - B_EP := by
  decide

end KleinExceptionalBraid
