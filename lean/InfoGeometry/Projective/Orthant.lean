import InfoGeometry.Projective.SelfDualCone
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Pi
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Topology.Order.Basic

/-!
# Positive Orthant as a Self-Dual Cone

This module implements the standard positive orthant as a `SelfDualCone`.
The orthant is defined on `EuclideanSpace ℝ α`. To satisfy the `ProperCone.positive` 
requirements, we locally provide the pointwise order structure.
-/

noncomputable section

namespace InfoGeometry.Projective

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! 
Inject order typeclasses for `EuclideanSpace` locally.
This avoids global diamonds while satisfying `ProperCone.positive`.
-/

local instance : PartialOrder (EuclideanSpace ℝ α) where
  le x y := ∀ i, x i ≤ y i
  le_refl x i := le_rfl
  le_trans x y z h1 h2 i := le_trans (h1 i) (h2 i)
  le_antisymm x y h1 h2 := by ext i; exact le_antisymm (h1 i) (h2 i)

local instance : OrderedAddCommGroup (EuclideanSpace ℝ α) where
  add_le_add_left := fun a b hab c i => add_le_add_left (hab i) (c i)

local instance : PosSMulMono ℝ (EuclideanSpace ℝ α) where
  smul_le_smul_of_nonneg_left := fun {a x y} ha hxy i => 
    mul_le_mul_of_nonneg_left (hxy i) ha

local instance : OrderClosedTopology (EuclideanSpace ℝ α) where
  isClosed_le' := by
    have eq : {p : EuclideanSpace ℝ α × EuclideanSpace ℝ α | p.1 ≤ p.2} = 
              ⋂ i, {p | p.1 i ≤ p.2 i} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rfl
    rw [eq]
    apply isClosed_iInter
    intro i
    have heval : Continuous (fun x : EuclideanSpace ℝ α => x i) := by
      have h_inner : (fun x : EuclideanSpace ℝ α => x i) = fun x => inner (EuclideanSpace.single i (1 : ℝ)) x := by
        ext x
        simp [EuclideanSpace.inner_single_left]
      rw [h_inner]
      exact continuous_inner continuous_const continuous_id
    have h1 : Continuous (fun (p : EuclideanSpace ℝ α × EuclideanSpace ℝ α) => p.1 i) := 
      heval.comp continuous_fst
    have h2 : Continuous (fun (p : EuclideanSpace ℝ α × EuclideanSpace ℝ α) => p.2 i) := 
      heval.comp continuous_snd
    exact isClosed_le h1 h2

/-- 
The standard positive orthant in `EuclideanSpace ℝ α` is a self-dual cone.
-/
def positiveOrthant : SelfDualCone (EuclideanSpace ℝ α) where
  cone := ProperCone.positive ℝ (EuclideanSpace ℝ α)
  self_dual := by
    ext x
    rw [ProperCone.mem_innerDual, ProperCone.mem_positive]
    constructor
    · intro h i
      specialize h (EuclideanSpace.single i (1 : ℝ))
      have h_pos : EuclideanSpace.single i 1 ∈ ProperCone.positive ℝ (EuclideanSpace ℝ α) := by
        rw [ProperCone.mem_positive]
        intro j
        by_cases hij : j = i <;> simp [hij, EuclideanSpace.single, Pi.single]
      specialize h h_pos
      simpa [EuclideanSpace.inner_single_left] using h
    · intro hx y hy
      rw [ProperCone.mem_positive] at hx hy
      simp [PiLp.inner_apply]
      apply Finset.sum_nonneg
      intro i _hi
      exact mul_nonneg (hx i) (hy i)

end InfoGeometry.Projective
