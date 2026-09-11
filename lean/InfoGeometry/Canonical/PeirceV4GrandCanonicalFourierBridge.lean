import InfoGeometry.Canonical.PartitionHierarchy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.V4GroupFourierTransform

/-!
# Grand-canonical Gibbs sectors and the native V₄ Fourier transform

For a finite state space equipped with an explicit `V4Group` grading, this
owner defines the four sector-resolved grand-canonical partition functions and
the character-twisted sums.  The latter are exactly the Fourier evaluations of
the former.  No semantic identification of a particular grading with a
Peirce or fermion parity is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge

open scoped BigOperators
open InfoGeometry.Canonical.PartitionHierarchy
open InfoGeometry.Canonical.V4GroupFourierTransform
open InfoGeometry.GrandCanonical
open InfoGeometry.Topology.V4RootSystem

variable {α : Type*} [Fintype α] [Nonempty α]

/-- The grand-canonical partition carried by one `V₄`-graded sector. -/
def v4SectorPartition
    (params : GrandCanonicalTwoParam α)
    (grade : α → V4Group) (β μ : ℝ) (g : V4Group) : ℝ :=
  fiberPartition grade (fun x => shiftedEnergy params μ x) β g

/-- Character-twisted grand-canonical partition function. -/
def v4TwistedPartition
    (params : GrandCanonicalTwoParam α)
    (grade : α → V4Group) (β μ : ℝ) (k : Fin 4) : ℝ :=
  v4Fourier k (v4SectorPartition params grade β μ)

theorem v4SectorPartition_total (params : GrandCanonicalTwoParam α)
    (grade : α → V4Group) (β μ : ℝ) :
    partitionGC params β μ =
      ∑ g : V4Group, v4SectorPartition params grade β μ g := by
  simpa [v4SectorPartition, GrandCanonical.partitionGC,
    fiberPartition, FiniteCoarseGraining.fiberWeight, boltzmannWeight] using
    (Fintype.sum_fiberwise grade
      (fun x => Real.exp (-β * shiftedEnergy params μ x))).symm

theorem v4TwistedPartition_eq_state_sum
    (params : GrandCanonicalTwoParam α)
    (grade : α → V4Group) (β μ : ℝ) (k : Fin 4) :
    v4TwistedPartition params grade β μ k =
      ∑ x : α,
        v4Character k (grade x) *
          Real.exp (-β * shiftedEnergy params μ x) := by
  classical
  unfold v4TwistedPartition v4Fourier v4SectorPartition fiberPartition
  unfold FiniteCoarseGraining.fiberWeight
  change
    (∑ g : V4Group,
      v4Character k g *
        ∑ x : {x // grade x = g},
          Real.exp (-β * shiftedEnergy params μ x)) =
      ∑ x : α,
        v4Character k (grade x) *
          Real.exp (-β * shiftedEnergy params μ x)
  calc
    (∑ g : V4Group,
        v4Character k g *
          ∑ x : {x // grade x = g},
            Real.exp (-β * shiftedEnergy params μ x)) =
        ∑ g : V4Group,
          ∑ x : {x // grade x = g},
            v4Character k (grade x) *
              Real.exp (-β * shiftedEnergy params μ x) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [x.property]
    _ = ∑ x : α,
        v4Character k (grade x) *
          Real.exp (-β * shiftedEnergy params μ x) := by
      exact Fintype.sum_fiberwise grade
        (fun x => v4Character k (grade x) *
          Real.exp (-β * shiftedEnergy params μ x))

theorem v4Fourier_sector_inversion
    (params : GrandCanonicalTwoParam α)
    (grade : α → V4Group) (β μ : ℝ) (g : V4Group) :
    (1 / 4 : ℝ) *
        ∑ k : Fin 4, v4Character k g *
          v4TwistedPartition params grade β μ k =
      v4SectorPartition params grade β μ g := by
  exact v4Fourier_inversion
    (v4SectorPartition params grade β μ) g

end InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge
