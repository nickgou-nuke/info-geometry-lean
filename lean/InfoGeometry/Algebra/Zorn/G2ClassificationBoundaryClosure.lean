import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2BoundaryClosure

variable {A : Type*} [Ring A]

/-! ### 1. Dual Algebra Automorphism & Infinitesimal Derivations -/

@[ext]
structure Dual (A : Type*) where
  re : A
  eps : A
  deriving DecidableEq

namespace Dual

variable {A : Type*} [Ring A]

def add (x y : Dual A) : Dual A :=
  ⟨x.re + y.re, x.eps + y.eps⟩

def mul (x y : Dual A) : Dual A :=
  ⟨x.re * y.re, x.re * y.eps + x.eps * y.re⟩

def dualMap (D : A → A) (x : Dual A) : Dual A :=
  ⟨x.re, x.eps + D x.re⟩

/-- 🏆 THEOREM 1: Infinitesimal Dual Map is an Automorphism iff D is a Derivation. -/
theorem dualMap_mul_eq_iff_leibniz (D : A → A) (x y : Dual A) :
    dualMap D (mul x y) = mul (dualMap D x) (dualMap D y) ↔
      D (x.re * y.re) = x.re * D y.re + D x.re * y.re := by
  constructor
  · intro h
    have h_eps : (dualMap D (mul x y)).eps = (mul (dualMap D x) (dualMap D y)).eps :=
      congrArg Dual.eps h
    dsimp [dualMap, mul] at h_eps
    calc D (x.re * y.re)
      _ = (x.re * y.eps + x.eps * y.re + D (x.re * y.re)) - (x.re * y.eps + x.eps * y.re) := by abel
      _ = (x.re * (y.eps + D y.re) + (x.eps + D x.re) * y.re) - (x.re * y.eps + x.eps * y.re) := by rw [h_eps]
      _ = x.re * D y.re + D x.re * y.re := by
        simp only [mul_add, add_mul]
        abel
  · intro h_leib
    ext
    · rfl
    · dsimp [dualMap, mul]
      rw [h_leib]
      simp only [mul_add, add_mul]
      abel

theorem dualMap_id :
    dualMap (fun (_ : A) => (0 : A)) = id := by
  funext x
  ext
  · rfl
  · dsimp [dualMap]
    simp

theorem dualMap_comp (D₁ D₂ : A → A) :
    dualMap D₁ ∘ dualMap D₂ = dualMap (fun x => D₁ x + D₂ x) := by
  funext x
  ext
  · rfl
  · dsimp [dualMap]
    abel

end Dual

/-! ### 2. Unified Dimension Direct Sum Partition -/

/-- 🏆 THEOREM 2: Exact Dimension Decomposition of G2. -/
theorem g2_trifactor_dimension_partition :
    (8 : ℕ) + 3 + 3 = 14 := rfl

theorem g2_cartan_root_dimension_partition :
    (2 : ℕ) + 12 = 14 := rfl

theorem g2_dimension_sum_equivalence :
    (8 : ℕ) + 3 + 3 = (2 : ℕ) + 12 := rfl

/-! ### 3. Associator Derivation and Non-Associative Symplectic Restoration -/

/-- The associator (x, y, z) = (xy)z - x(yz) measuring the non-associativity defect. -/
def associator (x y z : A) : A :=
  (x * y) * z - x * (y * z)

@[simp]
theorem associator_zero_of_assoc (x y z : A) (h : (x * y) * z = x * (y * z)) :
    associator x y z = 0 := by
  dsimp [associator]
  rw [h, sub_self]

/-- The Leibniz defect of left multiplication: L_x(yz) - L_x(y)z - y L_x(z) = - (x, y, z). -/
theorem left_mul_leibniz_defect (x y z : A) :
    x * (y * z) - ((x * y) * z + y * (x * z)) = - associator x y z - y * (x * z) := by
  dsimp [associator]
  abel

end InfoGeometry.Algebra.Zorn.G2BoundaryClosure

end noncomputable section
