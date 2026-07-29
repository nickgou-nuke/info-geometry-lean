import InfoGeometry.Canonical.ThreeLevelFiniteGibbsVariational
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace InfoGeometry.Canonical

namespace ThreeLevelFiniteGibbs

variable {SuperSector Sector : Type*}
  [Fintype SuperSector] [Nonempty SuperSector]
  [Fintype Sector] [Nonempty Sector] [DecidableEq SuperSector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- Shannon entropy of a finite weight function. -/
noncomputable def finiteEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

/-- Entropy of the outer super-sector distribution. -/
noncomputable def outerEntropy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) : ℝ :=
  finiteEntropy (fun g => outerWeight State super energy particleNumber superNumber β μ ν g)

/-- Entropy inside one retained super-sector fiber. -/
noncomputable def fiberEntropy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (g : SuperSector) : ℝ :=
  finiteEntropy (fun s => fiberSectorWeight State super energy particleNumber β μ g s)

/-- Entropy inside one sector conditioned on a fixed sector state. -/
noncomputable def conditionalEntropy
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) : ℝ :=
  finiteEntropy (fun x => conditionalWeight State energy β s x)

/-- Product-form three-level joint weight. -/
noncomputable def layeredJointWeight
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (g : SuperSector) (s : Sector) (x : State s) : ℝ :=
  outerWeight State super energy particleNumber superNumber β μ ν g *
    fiberSectorWeight State super energy particleNumber β μ g s *
    conditionalWeight State energy β s x

/-- The conditional Gibbs weights normalize inside each sector. -/
theorem sum_conditionalWeight_eq_one
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) :
    ∑ x, conditionalWeight State energy β s x = 1 := by
  classical
  unfold conditionalWeight
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (canonicalPartition_pos State energy β s))

/-- The product-form three-level joint weight normalizes. -/
theorem sum_layeredJointWeight_eq_one
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    (∑ g, (superFiber super g).sum (fun s => ∑ x,
      layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)) = 1 := by
  classical
  unfold layeredJointWeight
  have hinner :
      ∀ g s,
        ∑ x, outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberSectorWeight State super energy particleNumber β μ g s *
          conditionalWeight State energy β s x =
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s := by
    intro g s
    rw [Finset.mul_sum]
    rw [sum_conditionalWeight_eq_one State energy β s]
    ring
  calc
    (∑ g, (superFiber super g).sum (fun s => ∑ x,
      layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)) =
        ∑ g, (superFiber super g).sum (fun s =>
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s) := by
          apply Finset.sum_congr rfl
          intro g hg
          apply Finset.sum_congr rfl
          intro s hs
          exact hinner g s
    _ = ∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          (superFiber super g).sum (fun s =>
            fiberSectorWeight State super energy particleNumber β μ g s) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ g, outerWeight State super energy particleNumber superNumber β μ ν g := by
          rw [sum_fiberSectorWeight_eq_one State super energy particleNumber β μ
            fiber_nonempty]
    _ = 1 := by
          exact sum_outerWeight_eq_one State super energy particleNumber superNumber β μ ν
            fiber_nonempty

end ThreeLevelFiniteGibbs

end InfoGeometry.Canonical
