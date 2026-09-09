import InfoGeometry.Routing.FiniteSoftmax
import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

noncomputable section
namespace InfoGeometry.Streaming.G2GradedRouter

open scoped BigOperators
open InfoGeometry.Routing.FiniteSoftmax
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Combinatorics

def rootDegree (r : ℤ × ℤ) : ℤ := r.2

theorem rootDegree_add (r s : ℤ × ℤ) : rootDegree (r + s) = rootDegree r + rootDegree s := rfl

def degreeCount (k : ℤ) : ℕ := (phi.filter (fun r => rootDegree r = k)).card

theorem contact_root_counts :
    degreeCount (-2) = 1 ∧ degreeCount (-1) = 4 ∧ degreeCount 0 = 2 ∧
      degreeCount 1 = 4 ∧ degreeCount 2 = 1 := by decide

def rootLengthSq (r : ℤ × ℤ) : ℤ := 2 * r.1 ^ 2 - 6 * r.1 * r.2 + 6 * r.2 ^ 2

theorem long_root_in_degree_one :
    (0, 1) ∈ phi ∧ rootLengthSq (0, 1) = 6 ∧ rootDegree (0, 1) = 1 := by decide

theorem short_root_in_degree_zero :
    (1, 0) ∈ phi ∧ rootLengthSq (1, 0) = 2 ∧ rootDegree (1, 0) = 0 := by decide

theorem root_count : phi.card = 12 := by decide

section Permutation
variable {ι : Type*} [Fintype ι]

theorem partition_reindex (score : ι → ℝ) (τ : ℝ) (p : Equiv.Perm ι) :
    partitionZ (fun i => score (p i)) τ = partitionZ score τ := by
  unfold partitionZ
  exact p.sum_comp Finset.univ (fun i => Real.exp (score i / τ)) (by
    intro i hi
    simp)

theorem weight_reindex (score : ι → ℝ) (τ : ℝ) (p : Equiv.Perm ι) (i : ι) :
    weight (fun j => score (p j)) τ i = weight score τ (p i) := by
  simp only [weight, partition_reindex]

theorem aggregation_reindex {V : Type*} [AddCommGroup V] [Module ℝ V]
    (score : ι → ℝ) (τ : ℝ) (p : Equiv.Perm ι) (expert : ι → V) :
    (∑ i, weight (fun j => score (p j)) τ i • expert (p i)) =
      ∑ i, weight score τ i • expert i := by
  simp only [weight_reindex]
  exact p.sum_comp Finset.univ (fun i => weight score τ i • expert i) (by
    intro i hi
    simp)
end Permutation

local instance : Fintype G2CoordinateRoot := Fintype.ofFinset phi (by intro r; rfl)
local instance : Nonempty G2CoordinateRoot := ⟨⟨(1, 0), by decide⟩⟩

def rootWeight (score : G2CoordinateRoot → ℝ) (τ : ℝ) : G2CoordinateRoot → ℝ :=
  weight score τ

theorem rootWeight_normalized (score : G2CoordinateRoot → ℝ) (τ : ℝ) :
    ∑ r, rootWeight score τ r = 1 := weight_sum_one score τ

theorem rootWeight_positive (score : G2CoordinateRoot → ℝ) (τ : ℝ) (r : G2CoordinateRoot) :
    0 < rootWeight score τ r := weight_pos score τ r

theorem rootWeight_simple_reflection (score : G2CoordinateRoot → ℝ)
    (τ : ℝ) (r : G2CoordinateRoot) :
    rootWeight (fun s => score (s1Root s)) τ r = rootWeight score τ (s1Root r) :=
  weight_reindex score τ s1Root r

theorem rootWeight_second_reflection (score : G2CoordinateRoot → ℝ)
    (τ : ℝ) (r : G2CoordinateRoot) :
    rootWeight (fun s => score (s2Root s)) τ r = rootWeight score τ (s2Root r) :=
  weight_reindex score τ s2Root r

end InfoGeometry.Streaming.G2GradedRouter
