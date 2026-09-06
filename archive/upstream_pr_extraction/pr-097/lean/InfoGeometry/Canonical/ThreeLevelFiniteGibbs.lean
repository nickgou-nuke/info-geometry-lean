import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators

namespace InfoGeometry.Canonical

/-!
# Three-level finite Gibbs tower

This is the next coarse-graining layer above the two-level hierarchy.  Fine
states are grouped into sectors, sectors are grouped into super-sectors, and
each level contributes its own finite Gibbs partition factor.  The results
are purely finite identities and make no thermodynamic-limit claim.
-/

namespace ThreeLevelFiniteGibbs

variable {SuperSector Sector : Type*}
  [Fintype SuperSector] [Nonempty SuperSector]
  [Fintype Sector] [Nonempty Sector] [DecidableEq SuperSector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- The finite fiber of sectors retained by a super-sector. -/
def superFiber (super : Sector → SuperSector) (g : SuperSector) : Finset Sector :=
  Finset.univ.filter (fun s => super s = g)

/-- Fine-state Boltzmann weight inside a sector. -/
noncomputable def canonicalWeight
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (x : State s) : ℝ :=
  Real.exp (-β * energy s x)

/-- Canonical partition of one sector. -/
noncomputable def canonicalPartition
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) : ℝ :=
  ∑ x, canonicalWeight State energy β s x

/-- Middle-level numerator of one sector. -/
noncomputable def middleNumerator
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) : ℝ :=
  Real.exp (β * μ * particleNumber s) * canonicalPartition State energy β s

/-- Partition of a super-sector after summing its sector fibers. -/
noncomputable def superPartition
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (g : SuperSector) : ℝ :=
  (superFiber super g).sum (fun s => middleNumerator State energy particleNumber β μ s)

/-- Outer grand numerator of one super-sector. -/
noncomputable def outerNumerator
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) (g : SuperSector) : ℝ :=
  Real.exp (β * ν * superNumber g) *
    superPartition State super energy particleNumber β μ g

/-- Total three-level grand partition. -/
noncomputable def grandPartition
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) : ℝ :=
  ∑ g, outerNumerator State super energy particleNumber superNumber β μ ν g

/-- Joint unnormalized weight of a super-sector, sector, and fine state. -/
noncomputable def jointNumerator
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (g : SuperSector) (s : Sector) (x : State s) : ℝ :=
  Real.exp (β * ν * superNumber g) *
    (Real.exp (β * μ * particleNumber s) * canonicalWeight State energy β s x)

noncomputable def jointWeight
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (g : SuperSector) (s : Sector) (x : State s) : ℝ :=
  jointNumerator State super energy particleNumber superNumber β μ ν g s x /
    grandPartition State super energy particleNumber superNumber β μ ν

theorem canonicalPartition_pos
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) :
    0 < canonicalPartition State energy β s := by
  classical
  unfold canonicalPartition canonicalWeight
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

theorem middleNumerator_pos
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) :
    0 < middleNumerator State energy particleNumber β μ s := by
  unfold middleNumerator
  exact mul_pos (Real.exp_pos _) (canonicalPartition_pos State energy β s)

theorem superPartition_pos
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) :
    0 < superPartition State super energy particleNumber β μ g := by
  unfold superPartition
  exact Finset.sum_pos
    (fun s hs => middleNumerator_pos State energy particleNumber β μ s)
    (fiber_nonempty g)

theorem outerNumerator_pos
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) (g : SuperSector) :
    0 < outerNumerator State super energy particleNumber superNumber β μ ν g := by
  unfold outerNumerator
  exact mul_pos (Real.exp_pos _)
    (superPartition_pos State super energy particleNumber β μ fiber_nonempty g)

theorem grandPartition_pos
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    0 < grandPartition State super energy particleNumber superNumber β μ ν := by
  unfold grandPartition
  exact Finset.sum_pos
    (fun g hg => outerNumerator_pos State super energy particleNumber superNumber
      β μ ν fiber_nonempty g)
    Finset.univ_nonempty

theorem sum_jointNumerator_over_state
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (g : SuperSector) (s : Sector) :
    (∑ x, jointNumerator State super energy particleNumber superNumber β μ ν g s x) =
      Real.exp (β * ν * superNumber g) * middleNumerator State energy particleNumber β μ s := by
  unfold jointNumerator middleNumerator canonicalPartition canonicalWeight
  rw [Finset.mul_sum, Finset.mul_sum]

theorem sum_jointNumerator_over_sector
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) (g : SuperSector) :
    ((superFiber super g).sum (fun s => ∑ x,
      jointNumerator State super energy particleNumber superNumber β μ ν g s x)) =
      outerNumerator State super energy particleNumber superNumber β μ ν g := by
  unfold outerNumerator superPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [sum_jointNumerator_over_state State super energy particleNumber superNumber
    β μ ν g s]

theorem sum_jointWeight_eq_one
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    (∑ g, (superFiber super g).sum (fun s => ∑ x,
      jointWeight State super energy particleNumber superNumber β μ ν g s x)) = 1 := by
  classical
  have hZ : grandPartition State super energy particleNumber superNumber β μ ν ≠ 0 :=
    ne_of_gt (grandPartition_pos State super energy particleNumber superNumber
      β μ ν fiber_nonempty)
  unfold jointWeight
  rw [show (∑ g, (superFiber super g).sum (fun s => ∑ x,
      jointNumerator State super energy particleNumber superNumber β μ ν g s x /
        grandPartition State super energy particleNumber superNumber β μ ν)) =
      (∑ g, (superFiber super g).sum (fun s => ∑ x,
        jointNumerator State super energy particleNumber superNumber β μ ν g s x)) /
        grandPartition State super energy particleNumber superNumber β μ ν by
          simp_rw [Finset.sum_div]]
  rw [show (∑ g, (superFiber super g).sum (fun s => ∑ x,
      jointNumerator State super energy particleNumber superNumber β μ ν g s x)) =
      grandPartition State super energy particleNumber superNumber β μ ν by
        unfold grandPartition
        apply Finset.sum_congr rfl
        intro g hg
        exact sum_jointNumerator_over_sector State super energy particleNumber superNumber
          β μ ν fiber_nonempty g]
  exact div_self hZ

end ThreeLevelFiniteGibbs

end InfoGeometry.Canonical
