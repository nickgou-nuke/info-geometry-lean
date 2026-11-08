import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.FiniteGibbsZeroTemperature

/-! Finite softmax weights.

This owner proves positivity and normalization only.  It does not assert
equivariance, uniqueness of an annealing limit, or expert-balance properties.
-/

namespace InfoGeometry.Routing.FiniteSoftmax

open Topology
open scoped BigOperators

noncomputable def partitionZ {G : Type*} [Fintype G]
    (score : G → ℝ) (tau : ℝ) : ℝ :=
  ∑ g, Real.exp (score g / tau)

noncomputable def weight {G : Type*} [Fintype G]
    (score : G → ℝ) (tau : ℝ) (g : G) : ℝ :=
  Real.exp (score g / tau) / partitionZ score tau

theorem partitionZ_pos {G : Type*} [Fintype G] [Nonempty G]
    (score : G → ℝ) (tau : ℝ) :
    0 < partitionZ score tau := by
  unfold partitionZ
  apply Finset.sum_pos'
  · intro g hg
    exact le_of_lt (Real.exp_pos _)
  · obtain ⟨g⟩ := ‹Nonempty G›
    exact ⟨g, Finset.mem_univ _, Real.exp_pos _⟩

theorem weight_pos {G : Type*} [Fintype G] [Nonempty G]
    (score : G → ℝ) (tau : ℝ) (g : G) :
    0 < weight score tau g := by
  unfold weight
  exact div_pos (Real.exp_pos _) (partitionZ_pos score tau)

theorem weight_sum_one {G : Type*} [Fintype G] [Nonempty G]
    (score : G → ℝ) (tau : ℝ) :
    ∑ g, weight score tau g = 1 := by
  unfold weight
  rw [← Finset.sum_div]
  change partitionZ score tau / partitionZ score tau = 1
  exact div_self (ne_of_gt (partitionZ_pos score tau))

/-- A finite softmax is a finite Gibbs responsibility with energy `-score`,
unit prior, and one datum. This identifies the attention carrier with the
existing general finite-Gibbs owner. -/
noncomputable def softmaxModelFamily {G : Type*} [Fintype G] [Nonempty G]
    (score : G → ℝ) :
    InfoGeometry.Inference.FiniteGibbs.ModelFamily (ModelId := G) (Data := Unit) :=
  { energy := fun g _ => -score g
    prior := fun _ => 1
    prior_pos := fun _ => one_pos }

/-- Exact identification of finite softmax weights with the responsibility
of the corresponding unit-prior Gibbs model. -/
theorem weight_eq_gibbsResponsibility {G : Type*} [Fintype G] [Nonempty G]
    (score : G → ℝ) (tau : ℝ) (g : G) :
    weight score tau g =
      InfoGeometry.Inference.FiniteGibbs.responsibility
        (softmaxModelFamily score) tau g () := by
  simp [weight, partitionZ, softmaxModelFamily,
    InfoGeometry.Inference.FiniteGibbs.responsibility,
    InfoGeometry.Inference.FiniteGibbs.modelPartition]

/-- Under a uniform positive gap below a unique maximum, the finite softmax
converges pointwise to the deterministic routing indicator as inverse
temperature tends to infinity. The convergence step is inherited from the
general finite-Gibbs concentration theorem through the exact identification
above. -/
theorem weight_tendsto_indicator_of_unique_max_gap
    {G : Type*} [Fintype G] [Nonempty G] [DecidableEq G]
    (score : G → ℝ) (gMax : G) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ g : G, g ≠ gMax → score g + δ ≤ score gMax)
    (g : G) :
    Filter.Tendsto (fun β : ℝ => weight score (1 / β) g)
      Filter.atTop (𝓝 (if g = gMax then 1 else 0)) := by
  classical
  let F := softmaxModelFamily score
  have hweight : (fun β : ℝ => weight score (1 / β) g) =
      (fun β : ℝ =>
        InfoGeometry.Inference.FiniteGibbs.responsibility F (1 / β) g ()) := by
    funext β
    exact weight_eq_gibbsResponsibility score (1 / β) g
  rw [hweight]
  by_cases h : g = gMax
  · subst g
    have hlimit :=
      InfoGeometry.Inference.FiniteGibbs.tendsto_responsibility_one_of_unique_energy_gap
        F hδ gMax () (fun m hm => by
          change -score gMax + δ ≤ -score m
          have hscore := hgap m hm
          linarith)
    simpa using hlimit
  · have hlimit :=
      InfoGeometry.Inference.FiniteGibbs.tendsto_responsibility_zero_of_energy_gap
        F hδ g gMax () (by
          change -score gMax + δ ≤ -score g
          have hscore := hgap g h
          linarith)
    simpa [h] using hlimit

/-- A strict maximum of a function on a finite type has a uniform positive
gap from every competitor. The empty-competitor case covers a singleton type. -/
theorem exists_pos_uniform_gap_of_unique_max
    {G : Type*} [Fintype G] [Nonempty G] [DecidableEq G]
    (score : G → ℝ) (gMax : G)
    (hmax : ∀ g : G, g ≠ gMax → score g < score gMax) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : G, g ≠ gMax → score g + δ ≤ score gMax := by
  classical
  let competitors : Finset G := Finset.univ.erase gMax
  by_cases hcomp : competitors.Nonempty
  · let gaps : Finset ℝ := competitors.image (fun g => score gMax - score g)
    have hgaps : gaps.Nonempty := by
      obtain ⟨g, hg⟩ := hcomp
      exact ⟨score gMax - score g, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩
    let δ : ℝ := gaps.min' hgaps
    have hδmem : δ ∈ gaps := by
      exact Finset.min'_mem gaps hgaps
    obtain ⟨g₀, hg₀, hδeq⟩ := Finset.mem_image.mp hδmem
    have hδpos : 0 < δ := by
      calc
        0 < score gMax - score g₀ :=
          sub_pos.mpr (hmax g₀ (Finset.ne_of_mem_erase hg₀))
        _ = δ := hδeq
    refine ⟨δ, hδpos, ?_⟩
    intro g hgne
    have hg : g ∈ competitors :=
      Finset.mem_erase.mpr ⟨hgne, Finset.mem_univ g⟩
    have hgapmem : score gMax - score g ∈ gaps :=
      Finset.mem_image.mpr ⟨g, hg, rfl⟩
    have hle : δ ≤ score gMax - score g := by
      simpa [δ] using Finset.min'_le gaps (score gMax - score g) hgapmem
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro g hgne
    have hg : g ∈ competitors :=
      Finset.mem_erase.mpr ⟨hgne, Finset.mem_univ g⟩
    exact (hcomp ⟨g, hg⟩).elim

/-- For a finite score function with a unique strict maximum, the softmax
converges to the Kronecker routing vector as inverse temperature tends to
infinity. -/
theorem weight_tendsto_indicator_of_unique_max
    {G : Type*} [Fintype G] [Nonempty G] [DecidableEq G]
    (score : G → ℝ) (gMax : G)
    (hmax : ∀ g : G, g ≠ gMax → score g < score gMax) (g : G) :
    Filter.Tendsto (fun β : ℝ => weight score (1 / β) g)
      Filter.atTop (𝓝 (if g = gMax then 1 else 0)) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_uniform_gap_of_unique_max score gMax hmax
  exact weight_tendsto_indicator_of_unique_max_gap score gMax hδ hgap g

end InfoGeometry.Routing.FiniteSoftmax
