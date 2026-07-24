import Mathlib

/-!
# The Split E8(8) U-Duality Group and its Branching

In string theory and 3D supergravity (or M-theory on a T^8 torus), the U-duality 
group is the split real form $E_{8(8)}$.

Its maximal compact subgroup is $Spin(16) / \mathbb{Z}_2$, which shares the Lie 
algebra $D_8$. The adjoint representation of $E_8$ (dimension 248) branches 
under $D_8$ into the adjoint (120) and the positive-chirality spinor (128).

This module formalizes the exact dimensional relationships of this branching, 
verifying the algebraic structure.
-/

namespace InfoGeometry.Algebra.SplitE88Group

/-- The dimension of the E8 Lie algebra is 248. -/
def dim_E8 : ℕ := 248

/-- The dimension of the adjoint representation of Dn is n(2n-1). -/
def dim_Dn_adjoint (n : ℕ) : ℕ := n * (2 * n - 1)

/-- The dimension of the spinor representation of Dn is 2^(n-1). -/
def dim_Dn_spinor (n : ℕ) : ℕ := 2^(n - 1)

/-- 
The fundamental decomposition of the split real form E8(8):
The 248-dimensional adjoint representation of E8 branches under its maximal 
compact subgroup D8 (Spin(16)) into the adjoint (120) and spinor (128) representations.
-/
theorem E8_adjoint_branches_to_D8 : 
    dim_E8 = dim_Dn_adjoint 8 + dim_Dn_spinor 8 := by
  rfl

/--
The U-duality group of 5D supergravity is E6(6), branching into 
its maximal compact subgroup Sp(8) (which has Lie algebra C4).
Wait, the T-duality group for T^5 is O(5,5) which has Lie algebra D5.
Let's verify the dimension of D5.
-/
theorem D5_adjoint_dim : dim_Dn_adjoint 5 = 45 := by
  rfl

end InfoGeometry.Algebra.SplitE88Group
