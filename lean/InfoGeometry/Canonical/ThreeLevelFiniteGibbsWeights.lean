import InfoGeometry.Canonical.ThreeLevelFiniteGibbs
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped BigOperators

namespace InfoGeometry.Canonical

namespace ThreeLevelFiniteGibbs

variable {SuperSector Sector : Type*}
  [Fintype SuperSector] [Nonempty SuperSector]
  [Fintype Sector] [Nonempty Sector] [DecidableEq SuperSector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- Conditional Gibbs weight inside one sector. -/
noncomputable def conditionalWeight
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (x : State s) : ℝ :=
  canonicalWeight State energy β s x / canonicalPartition State energy β s

/-- Sector weight inside one super-sector fiber. -/
noncomputable def fiberSectorWeight
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (g : SuperSector) (s : Sector) : ℝ :=
  middleNumerator State energy particleNumber β μ s /
    superPartition State super energy particleNumber β μ g

/-- Outer Gibbs weight of a super-sector. -/
noncomputable def outerWeight
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) (g : SuperSector) : ℝ :=
  outerNumerator State super energy particleNumber superNumber β μ ν g /
    grandPartition State super energy particleNumber superNumber β μ ν

/-- Conditional sector weights normalize on each super-sector fiber. -/
theorem sum_fiberSectorWeight_eq_one
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) :
    (superFiber super g).sum (fun s => fiberSectorWeight State super energy particleNumber β μ g s) = 1 := by
  classical
  unfold fiberSectorWeight
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [show (superFiber super g).sum (fun s => middleNumerator State energy particleNumber β μ s) =
      superPartition State super energy particleNumber β μ g by rfl]
  rw [mul_inv_cancel₀ (ne_of_gt (superPartition_pos State super energy particleNumber β μ
    fiber_nonempty g))]

/-- Outer weights normalize over super-sectors. -/
theorem sum_outerWeight_eq_one
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    (∑ g, outerWeight State super energy particleNumber superNumber β μ ν g) = 1 := by
  classical
  unfold outerWeight
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [show (∑ g, outerNumerator State super energy particleNumber superNumber β μ ν g) =
      grandPartition State super energy particleNumber superNumber β μ ν by rfl]
  rw [mul_inv_cancel₀ (ne_of_gt (grandPartition_pos State super energy particleNumber superNumber
    β μ ν fiber_nonempty))]

end ThreeLevelFiniteGibbs

end InfoGeometry.Canonical
