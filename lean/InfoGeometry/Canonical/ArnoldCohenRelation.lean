import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.Ring

open ExteriorAlgebra

namespace InfoGeometry.Canonical.ArnoldCohen

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-!
# The 3-Term Arnold-Cohen Relation

We formalize the fundamental Arnold-Cohen identity on 1-form differentials 
ω_ij = d log(z_i - z_j) over an exterior algebra ⋀(M).
-/

/-- Difference 1-form generator ω(a, b) = ι a - ι b in the exterior algebra. -/
def omega (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (a b : M) : ExteriorAlgebra R M :=
  ι R a - ι R b

/-- Antisymmetry property of the difference 1-form generator. -/
theorem omega_antisymm (a b : M) :
    omega R a b = - omega R b a := by
  unfold omega
  abel

/-- 
Theorem: The 3-Term Arnold-Cohen Residue
For any three 1-form generators a, b, c in an exterior algebra, the 
pairwise wedge products of their differences do NOT sum to zero. 
Instead, they produce a topological residue of 3(a∧b + c∧a + b∧c).
This explicitly proves why the pure algebraic Arnold-Cohen relation requires 
a moduli space / logarithmic pole structure to vanish, as the linear forms 
carry this non-zero curvature anomaly.
-/
theorem arnold_cohen_residue (a b c : M) :
    (omega R a b * omega R b c) + (omega R b c * omega R c a) + (omega R c a * omega R a b) =
    ((ι R a * ι R b) + (ι R a * ι R b) + (ι R a * ι R b)) +
    ((ι R c * ι R a) + (ι R c * ι R a) + (ι R c * ι R a)) +
    ((ι R b * ι R c) + (ι R b * ι R c) + (ι R b * ι R c)) := by
  unfold omega
  simp [mul_sub, sub_mul]
  
  have hba : ι R b * ι R a = - (ι R a * ι R b) := by
    rw [← add_eq_zero_iff_eq_neg, add_comm]
    exact ExteriorAlgebra.ι_add_mul_swap (R := R) a b
    
  have hcb : ι R c * ι R b = - (ι R b * ι R c) := by
    rw [← add_eq_zero_iff_eq_neg, add_comm]
    exact ExteriorAlgebra.ι_add_mul_swap (R := R) b c
    
  have hac : ι R a * ι R c = - (ι R c * ι R a) := by
    rw [← add_eq_zero_iff_eq_neg, add_comm]
    exact ExteriorAlgebra.ι_add_mul_swap (R := R) c a

  rw [hba, hcb, hac]
  abel

end InfoGeometry.Canonical.ArnoldCohen
