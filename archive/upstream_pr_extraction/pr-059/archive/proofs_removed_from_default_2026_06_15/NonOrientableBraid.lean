import Mathlib.Algebra.Group.Defs

/-!
# Non-Orientable Braid Topology

Formalizes the topological invariants of Exceptional Points on non-orientable 
manifolds (Klein Bottle and Real Projective Plane RP²) as outlined in 
J. Lukas K. König's thesis.
-/

namespace NonOrientableBraid

variable {B : Type*} [Group B]

/-- 
The fundamental domain of the Brillouin Klein Bottle K². 
The topological charge evaluates to Bx * By * Bx * By⁻¹.
-/
def klein_bottle_charge (Bx By : B) : B :=
  Bx * By * Bx * By⁻¹

/-- 
The fundamental domain of the Real Projective Plane RP². 
The topological charge evaluates to X².
-/
def rp2_charge (X : B) : B :=
  X * X

/-- 
In the Abelian (Hermitian) limit, the Klein bottle constraint reduces 
to Bx², accumulating charge instead of canceling it.
-/
theorem abelian_klein_accumulation (Bx By : B) (h_comm : Commute Bx By) : 
    klein_bottle_charge Bx By = Bx * Bx := by
  dsimp [klein_bottle_charge]
  have h_eq : Bx * By = By * Bx := h_comm.eq
  calc
    Bx * By * Bx * By⁻¹ = By * Bx * Bx * By⁻¹ := by rw [h_eq]
    _ = By * (Bx * Bx) * By⁻¹ := by group
    _ = (Bx * Bx) * By * By⁻¹ := by
      -- Since Bx and By commute, (Bx*Bx) and By also commute
      have h_comm2 : Commute (Bx * Bx) By := Commute.mul_left h_comm h_comm
      rw [h_comm2.eq]
    _ = Bx * Bx := by group

end NonOrientableBraid
