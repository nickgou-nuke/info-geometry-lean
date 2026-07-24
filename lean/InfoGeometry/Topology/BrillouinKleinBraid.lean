import Mathlib

/-!
# Braiding Topology of EPs in Brillouin Klein Bottles

Formalizes the braiding topology equations from arXiv:2503.06933v2.
The composite of braidings around all EPs in the Klein bottle fundamental domain K²
equals the braiding along the boundary ∂K² = a b a b⁻¹.

Therefore, for n EPs with braid group elements b_1, b_2, ..., b_n, we have:
b_1 b_2 ... b_n = b_a b_b b_a b_b⁻¹
-/

namespace InfoGeometry.Topology.BrillouinKleinBraid

/-- 
The braiding constraint for n Exceptional Points inside a Brillouin Klein Bottle.
The product of the n braid elements equals the boundary word `a * b * a * b⁻¹`.
We represent the Braid group elements as an abstract Group `G`.
-/
def klein_braid_constraint 
    {G : Type} [Group G] 
    (ep_braids : List G) 
    (b_a b_b : G) : Prop :=
  ep_braids.prod = b_a * b_b * b_a * b_b⁻¹

/--
The 2-band case (N=2): The braid group B_2 is abelian (isomorphic to ℤ).
Thus `b_a * b_b * b_a * b_b⁻¹ = b_a * b_a * b_b * b_b⁻¹ = b_a²`.
This further confirms the failure of the fermion doubling theorem since the discriminant
is doubled.
-/
theorem klein_braid_constraint_abelian 
    {G : Type} [CommGroup G] 
    (ep_braids : List G) 
    (b_a b_b : G) 
    (h : klein_braid_constraint ep_braids b_a b_b) : 
    ep_braids.prod = b_a ^ 2 := by
  dsimp [klein_braid_constraint] at h
  rw [h]
  -- We have b_a * b_b * b_a * b_b⁻¹
  have h_comm : b_b * b_a = b_a * b_b := mul_comm b_b b_a
  rw [mul_assoc b_a b_b b_a, h_comm, ← mul_assoc b_a b_a b_b, mul_assoc (b_a * b_a) b_b b_b⁻¹, mul_inv_cancel, mul_one]
  exact sq b_a |>.symm

end InfoGeometry.Topology.BrillouinKleinBraid
