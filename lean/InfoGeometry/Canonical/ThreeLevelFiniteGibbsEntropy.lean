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

/-- Conditional weights are strictly positive. -/
theorem conditionalWeight_pos
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (x : State s) :
    0 < conditionalWeight State energy β s x := by
  unfold conditionalWeight
  exact div_pos (Real.exp_pos _)
    (canonicalPartition_pos State energy β s)

/-- Fiber-sector weights are strictly positive on each retained fiber. -/
theorem fiberSectorWeight_pos
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) (s : Sector) :
    0 < fiberSectorWeight State super energy particleNumber β μ g s := by
  unfold fiberSectorWeight
  exact div_pos (middleNumerator_pos State energy particleNumber β μ s)
    (superPartition_pos State super energy particleNumber β μ fiber_nonempty g)

/-- Outer super-sector weights are strictly positive. -/
theorem outerWeight_pos
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) :
    0 < outerWeight State super energy particleNumber superNumber β μ ν g := by
  unfold outerWeight
  exact div_pos (outerNumerator_pos State super energy particleNumber superNumber
    β μ ν fiber_nonempty g)
      (grandPartition_pos State super energy particleNumber superNumber β μ ν fiber_nonempty)

/-- The product-form joint weight is the product of the three normalized layers. -/
omit [Nonempty SuperSector] [Nonempty Sector] [∀ (s : Sector), Nonempty (State s)] in
theorem layeredJointWeight_eq_outerWeight_mul_fiberSectorWeight_mul_conditionalWeight
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (g : SuperSector) (s : Sector) (x : State s) :
    layeredJointWeight State super energy particleNumber superNumber β μ ν g s x =
      outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s *
        conditionalWeight State energy β s x := by
  rfl

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
    calc
      ∑ x, outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberSectorWeight State super energy particleNumber β μ g s *
          conditionalWeight State energy β s x
          =
          ∑ x, conditionalWeight State energy β s x *
            (outerWeight State super energy particleNumber superNumber β μ ν g *
              fiberSectorWeight State super energy particleNumber β μ g s) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
      _ = (∑ x, conditionalWeight State energy β s x) *
          (outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s) := by
              rw [Finset.sum_mul]
      _ = outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s := by
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
          apply Finset.sum_congr rfl
          intro g hg
          rw [sum_fiberSectorWeight_eq_one State super energy particleNumber β μ
            fiber_nonempty g]
          ring
    _ = 1 := by
          exact sum_outerWeight_eq_one State super energy particleNumber superNumber β μ ν
            fiber_nonempty

/-- Entropy of the full three-level joint distribution. -/
noncomputable def jointEntropy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) : ℝ :=
  -∑ g, ∑ s, ∑ x, layeredJointWeight State super energy particleNumber superNumber β μ ν g s x *
    Real.log (layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)

/-- The full joint entropy splits into outer, fiber, and conditional contributions. -/
theorem jointEntropy_eq_outerEntropy_add_expectedFiberEntropy_add_expectedConditionalEntropy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    jointEntropy State super energy particleNumber superNumber β μ ν =
      outerEntropy State super energy particleNumber superNumber β μ ν +
        ∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberEntropy State super energy particleNumber β μ g +
        ∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          (∑ s, fiberSectorWeight State super energy particleNumber β μ g s *
            conditionalEntropy State energy β s) := by
  classical
  unfold jointEntropy outerEntropy fiberEntropy conditionalEntropy finiteEntropy
  have hinner :
      ∀ g s,
        ∑ x, layeredJointWeight State super energy particleNumber superNumber β μ ν g s x *
          Real.log (layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)
          =
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s *
            Real.log (outerWeight State super energy particleNumber superNumber β μ ν g) +
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s *
            Real.log (fiberSectorWeight State super energy particleNumber β μ g s) +
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s *
            (∑ x, conditionalWeight State energy β s x *
              Real.log (conditionalWeight State energy β s x)) := by
    intro g s
    have houter : 0 < outerWeight State super energy particleNumber superNumber β μ ν g :=
      outerWeight_pos State super energy particleNumber superNumber β μ ν fiber_nonempty g
    have hfiber : 0 < fiberSectorWeight State super energy particleNumber β μ g s :=
      fiberSectorWeight_pos State super energy particleNumber β μ fiber_nonempty g s
    have hcond : ∀ x, 0 < conditionalWeight State energy β s x :=
      fun x => conditionalWeight_pos State energy β s x
    calc
      ∑ x, layeredJointWeight State super energy particleNumber superNumber β μ ν g s x *
          Real.log (layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)
          =
          ∑ x,
            (outerWeight State super energy particleNumber superNumber β μ ν g *
              fiberSectorWeight State super energy particleNumber β μ g s *
              conditionalWeight State energy β s x) *
              Real.log (outerWeight State super energy particleNumber superNumber β μ ν g *
                fiberSectorWeight State energy particleNumber β μ g s *
                conditionalWeight State energy β s x) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [layeredJointWeight_eq_outerWeight_mul_fiberSectorWeight_mul_conditionalWeight]
      _ =
          ∑ x,
            outerWeight State super energy particleNumber superNumber β μ ν g *
              fiberSectorWeight State super energy particleNumber β μ g s *
              conditionalWeight State energy β s x *
              (Real.log (outerWeight State super energy particleNumber superNumber β μ ν g) +
                Real.log (fiberSectorWeight State energy particleNumber β μ g s) +
                Real.log (conditionalWeight State energy β s x)) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [Real.log_mul (mul_pos houter hfiber) (hcond x)]
                  rw [Real.log_mul houter hfiber]
                  ring
      _ =
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s *
            Real.log (outerWeight State super energy particleNumber superNumber β μ ν g) *
              (∑ x, conditionalWeight State energy β s x) +
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State energy particleNumber β μ g s *
            Real.log (fiberSectorWeight State energy particleNumber β μ g s) *
              (∑ x, conditionalWeight State energy β s x) +
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State energy particleNumber β μ g s *
              (∑ x, conditionalWeight State energy β s x *
                Real.log (conditionalWeight State energy β s x)) := by
                  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                  congr
                  · rw [Finset.mul_sum]
                  · congr
                    · rw [Finset.mul_sum]
                    · rw [Finset.mul_sum]
  calc
    jointEntropy State super energy particleNumber superNumber β μ ν
        =
        -∑ g, ∑ s,
          (outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s *
            Real.log (outerWeight State super energy particleNumber superNumber β μ ν g) +
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State energy particleNumber β μ g s *
            Real.log (fiberSectorWeight State energy particleNumber β μ g s) +
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State energy particleNumber β μ g s *
              (∑ x, conditionalWeight State energy β s x *
                Real.log (conditionalWeight State energy β s x))) := by
            simp [jointEntropy, hinner]
    _ =
        -∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          Real.log (outerWeight State super energy particleNumber superNumber β μ ν g) +
        -∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          (∑ s, fiberSectorWeight State energy particleNumber β μ g s *
            Real.log (fiberSectorWeight State energy particleNumber β μ g s)) +
        -∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          (∑ s, fiberSectorWeight State energy particleNumber β μ g s *
            (∑ x, conditionalWeight State energy β s x *
              Real.log (conditionalWeight State energy β s x))) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            congr
            · rw [Finset.sum_mul]
              simp
            · congr
              · rw [Finset.sum_mul]
              · rw [Finset.sum_mul]
    _ = outerEntropy State super energy particleNumber superNumber β μ ν +
        ∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberEntropy State super energy particleNumber β μ g +
        ∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          (∑ s, fiberSectorWeight State super energy particleNumber β μ g s *
            conditionalEntropy State energy β s) := by
            simp [outerEntropy, fiberEntropy, conditionalEntropy, finiteEntropy]

end ThreeLevelFiniteGibbs

end InfoGeometry.Canonical
