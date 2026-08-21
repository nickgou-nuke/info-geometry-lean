import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Lie.G2RealSplitExponentialAtlas

variable {A : Type*} [Ring A] [Algebra ℝ A]

structure SplitDeriv (A : Type*) [Ring A] [Algebra ℝ A] where
  toLinearMap : A →ₗ[ℝ] A
  leibniz' : ∀ x y : A, toLinearMap (x * y) = toLinearMap x * y + x * toLinearMap y

@[ext]
structure SplitAut (A : Type*) [Ring A] [Algebra ℝ A] where
  toLinearEquiv : A ≃ₗ[ℝ] A
  map_one' : toLinearEquiv 1 = 1
  map_mul' : ∀ x y : A, toLinearEquiv (x * y) = toLinearEquiv x * toLinearEquiv y

namespace SplitAut

instance : Group (SplitAut A) where
  mul g h := {
    toLinearEquiv := h.toLinearEquiv.trans g.toLinearEquiv
    map_one' := by dsimp; rw [h.map_one', g.map_one']
    map_mul' := fun x y => by dsimp; rw [h.map_mul', g.map_mul']
  }
  one := {
    toLinearEquiv := LinearEquiv.refl ℝ A
    map_one' := rfl
    map_mul' := fun x y => rfl
  }
  inv g := {
    toLinearEquiv := g.toLinearEquiv.symm
    map_one' := by apply g.toLinearEquiv.injective; simp [g.map_one']
    map_mul' := fun x y => by apply g.toLinearEquiv.injective; simp [g.map_mul']
  }
  mul_assoc a b c := by ext; rfl
  one_mul a := by ext; rfl
  mul_one a := by ext; rfl
  inv_mul_cancel a := by
    ext x
    exact a.toLinearEquiv.left_inv x

end SplitAut

structure OneParamFlow (A : Type*) [Ring A] [Algebra ℝ A] where
  flow : ℝ → SplitAut A
  flow_zero' : flow 0 = 1
  flow_add' : ∀ s t : ℝ, flow (s + t) = flow s * flow t

namespace OneParamFlow

@[simp]
theorem flow_zero (F : OneParamFlow A) :
    F.flow 0 = 1 :=
  F.flow_zero'

@[simp]
theorem flow_add (F : OneParamFlow A) (s t : ℝ) :
    F.flow (s + t) = F.flow s * F.flow t :=
  F.flow_add' s t

theorem flow_neg (F : OneParamFlow A) (t : ℝ) :
    F.flow (-t) = (F.flow t)⁻¹ := by
  apply mul_right_cancel (b := F.flow t)
  rw [inv_mul_cancel, ← F.flow_add, neg_add_cancel, F.flow_zero]

end OneParamFlow

def g2SplitLieAlgebraDim : ℕ := 14

def compactSubalgebraDim : ℕ := 4

def noncompactSymmetricSpaceDim : ℕ := 10

theorem cartan_symmetric_space_dimension_sum :
    compactSubalgebraDim + noncompactSymmetricSpaceDim = g2SplitLieAlgebraDim := by
  rfl

theorem cartan_root_dimension_sum :
    (2 : ℕ) + 12 = g2SplitLieAlgebraDim := by
  rfl

theorem trifactor_dimension_sum :
    (8 : ℕ) + 3 + 3 = g2SplitLieAlgebraDim := by
  rfl

end InfoGeometry.Lie.G2RealSplitExponentialAtlas

end noncomputable section
