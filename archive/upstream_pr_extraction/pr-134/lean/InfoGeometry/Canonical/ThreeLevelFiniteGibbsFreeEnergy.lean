import InfoGeometry.Canonical.ThreeLevelFiniteGibbs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace InfoGeometry.Canonical

namespace ThreeLevelFiniteGibbs

variable {SuperSector Sector : Type*}
  [Fintype SuperSector] [Nonempty SuperSector]
  [Fintype Sector] [Nonempty Sector] [DecidableEq SuperSector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- Canonical free energy of one finite sector. -/
noncomputable def canonicalFreeEnergy
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) : ℝ :=
  -(1 / β) * Real.log (canonicalPartition State energy β s)

/-- Effective grand potential of a sector in the three-level tower. -/
noncomputable def effectiveSectorPotential
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) : ℝ :=
  canonicalFreeEnergy State energy β s - μ * particleNumber s

/-- Free energy of a retained super-sector. -/
noncomputable def superFreeEnergy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (g : SuperSector) : ℝ :=
  -(1 / β) * Real.log (superPartition State super energy particleNumber β μ g)

/-- Effective outer potential of a super-sector. -/
noncomputable def effectiveSuperPotential
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) (g : SuperSector) : ℝ :=
  superFreeEnergy State super energy particleNumber β μ g - ν * superNumber g

/-- Grand free energy of the full finite three-level tower. -/
noncomputable def grandFreeEnergy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) : ℝ :=
  -(1 / β) * Real.log (grandPartition State super energy particleNumber superNumber β μ ν)

/-- Exponentiating minus β times a sector free energy recovers its partition. -/
theorem exp_neg_beta_mul_canonicalFreeEnergy_eq_canonicalPartition
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (hβ : β ≠ 0) :
    Real.exp (-β * canonicalFreeEnergy State energy β s) =
      canonicalPartition State energy β s := by
  unfold canonicalFreeEnergy
  have hcancel :
      -β * (-(1 / β) * Real.log (canonicalPartition State energy β s)) =
        Real.log (canonicalPartition State energy β s) := by
    field_simp [hβ]
  rw [hcancel]
  exact Real.exp_log (canonicalPartition_pos State energy β s)

/-- Exponentiating minus β times the super-sector free energy recovers its
    partition. -/
theorem exp_neg_beta_mul_superFreeEnergy_eq_superPartition
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (hβ : β ≠ 0) (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) :
    Real.exp (-β * superFreeEnergy State super energy particleNumber β μ g) =
      superPartition State super energy particleNumber β μ g := by
  unfold superFreeEnergy
  have hcancel :
      -β * (-(1 / β) * Real.log (superPartition State super energy particleNumber β μ g)) =
        Real.log (superPartition State super energy particleNumber β μ g) := by
    field_simp [hβ]
  rw [hcancel]
  exact Real.exp_log (superPartition_pos State super energy particleNumber β μ fiber_nonempty g)

/-- Exponentiating minus β times the effective super potential recovers the
    outer numerator. -/
theorem exp_neg_beta_mul_effectiveSuperPotential_eq_outerNumerator
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) (hβ : β ≠ 0)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) (g : SuperSector) :
    Real.exp (-β * effectiveSuperPotential State super energy particleNumber superNumber β μ ν g) =
      outerNumerator State super energy particleNumber superNumber β μ ν g := by
  unfold effectiveSuperPotential outerNumerator
  have hsuper :=
    exp_neg_beta_mul_superFreeEnergy_eq_superPartition State super energy particleNumber β μ
      hβ fiber_nonempty g
  rw [show -β * (superFreeEnergy State super energy particleNumber β μ g -
      ν * superNumber g) =
      -β * superFreeEnergy State super energy particleNumber β μ g +
        β * ν * superNumber g by ring]
  rw [Real.exp_add, hsuper]
  ring

/-- The grand free energy exponentiates back to the total partition. -/
theorem exp_neg_beta_mul_grandFreeEnergy_eq_grandPartition
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) (hβ : β ≠ 0)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    Real.exp (-β * grandFreeEnergy State super energy particleNumber superNumber β μ ν) =
      grandPartition State super energy particleNumber superNumber β μ ν := by
  unfold grandFreeEnergy
  have hcancel :
      -β * (-(1 / β) * Real.log (grandPartition State super energy particleNumber superNumber β μ ν)) =
        Real.log (grandPartition State super energy particleNumber superNumber β μ ν) := by
    field_simp [hβ]
  rw [hcancel]
  exact Real.exp_log (grandPartition_pos State super energy particleNumber superNumber
    β μ ν fiber_nonempty)

/-- The grand partition is the finite Gibbs partition of the effective
    super-sector potentials. -/
theorem grandPartition_eq_sum_exp_neg_beta_effectiveSuperPotential
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) (hβ : β ≠ 0)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    grandPartition State super energy particleNumber superNumber β μ ν =
      ∑ g, Real.exp (-β * effectiveSuperPotential State super energy particleNumber
        superNumber β μ ν g) := by
  classical
  unfold grandPartition
  apply Finset.sum_congr rfl
  intro g hg
  exact (exp_neg_beta_mul_effectiveSuperPotential_eq_outerNumerator State super energy
    particleNumber superNumber β μ ν hβ fiber_nonempty g).symm

end ThreeLevelFiniteGibbs

end InfoGeometry.Canonical
