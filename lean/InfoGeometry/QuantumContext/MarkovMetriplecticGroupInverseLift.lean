/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Bilinear
import InfoGeometry.QuantumContext.MarkovAttentionGroupInverse
import InfoGeometry.QuantumContext.MarkovMetriplecticFlowBridge

/-!
# Group inverse transport to the full matrix carrier

Convert the finite stochastic Laplacian group inverse on column observables
to a matrix, then lift it through left multiplication to an endomorphism of
the full matrix space. The final range theorem recovers every matrix force in
the image of the lifted Laplacian. No convergence, stationary distribution,
or detailed-balance claim is part of this module.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nontrivial finite matrix carrier contains explicit noncommuting matrix
units, so the full-matrix application below is not a commutative surrogate. -/
theorem matrix_noncommutative_witness [Nontrivial ι] :
    ∃ X Y : Matrix ι ι ℝ, X * Y ≠ Y * X := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  refine ⟨Matrix.single i j 1, Matrix.single j i 1, ?_⟩
  intro h
  have hdiag := congrArg (fun M : Matrix ι ι ℝ => M i i) h
  have hleft : Matrix.single i j (1 : ℝ) * Matrix.single j i 1 =
      Matrix.single i i 1 := by simp
  have hright : Matrix.single j i (1 : ℝ) * Matrix.single i j 1 =
      Matrix.single j j 1 := by simp
  rw [hleft, hright] at hdiag
  have hnot : ¬ (j = i ∧ j = i) := by
    rintro ⟨hji, _⟩
    exact hij hji.symm
  have hdiag' : (1 : ℝ) = 0 := by
    rw [Matrix.single_apply_of_ne (i := j) (j := j) (c := (1 : ℝ))
      (i' := i) (j' := i) hnot] at hdiag
    rw [Matrix.single_apply_same] at hdiag
    exact hdiag
  norm_num at hdiag'

/-- A group inverse on column observables, represented as a matrix. -/
theorem matrix_groupInverse_of_linear_groupInverse
    (A : Matrix ι ι ℝ) (D : Module.End ℝ (ι → ℝ))
    (hD : IsGroupInverse (Matrix.toLin' A) D) :
    ∃ G : Matrix ι ι ℝ, IsGroupInverse A G := by
  let G : Matrix ι ι ℝ := LinearMap.toMatrix' D
  refine ⟨G, ?_⟩
  constructor
  · apply Matrix.toLin'.injective
    simpa [G, Matrix.toLin'_mul, Module.End.mul_eq_comp] using hD.1
  constructor
  · apply Matrix.toLin'.injective
    simpa [G, Matrix.toLin'_mul, Module.End.mul_eq_comp] using hD.2.1
  · apply Matrix.toLin'.injective
    simpa [G, Matrix.toLin'_mul, Module.End.mul_eq_comp] using hD.2.2

/-- Left multiplication transports a matrix group inverse to the group
inverse of the induced endomorphisms on the full square-matrix carrier. -/
theorem mulLeftLinearMap_groupInverse
    (A G : Matrix ι ι ℝ) (hG : IsGroupInverse A G) :
    IsGroupInverse (mulLeftLinearMap ι ℝ A) (mulLeftLinearMap ι ℝ G) := by
  constructor
  · have h := congrArg (fun X : Matrix ι ι ℝ => mulLeftLinearMap ι ℝ X) hG.1
    simpa only [mulLeftLinearMap_mul, Module.End.mul_eq_comp] using h
  constructor
  · have h := congrArg (fun X : Matrix ι ι ℝ => mulLeftLinearMap ι ℝ X) hG.2.1
    simpa only [mulLeftLinearMap_mul, Module.End.mul_eq_comp] using h
  · have h := congrArg (fun X : Matrix ι ι ℝ => mulLeftLinearMap ι ℝ X) hG.2.2
    simpa only [mulLeftLinearMap_mul, Module.End.mul_eq_comp] using h

/-- Every finite row-stochastic Markov Laplacian has a group inverse on
column observables, and its left-multiplication lift is a group inverse on
the full matrix carrier. -/
theorem exists_stochastic_markovLeft_groupInverse
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ G : Matrix ι ι ℝ,
      IsGroupInverse (1 - P) G ∧
      IsGroupInverse (markovLeftOnsager P) (mulLeftLinearMap ι ℝ G) := by
  obtain ⟨D, hD⟩ := exists_stochastic_laplacian_groupInverse P hP
  obtain ⟨G, hG⟩ := matrix_groupInverse_of_linear_groupInverse (1 - P) D (by
    simpa using hD)
  refine ⟨G, hG, ?_⟩
  simpa [markovLeftOnsager] using mulLeftLinearMap_groupInverse (1 - P) G hG

/-- The lifted group inverse recovers a matrix force from its image whenever
the force lies in the range of the lifted Markov Laplacian. -/
theorem mulLeft_groupInverse_recovers_on_range
    (A G : Matrix ι ι ℝ) (hG : IsGroupInverse A G)
    (X : Matrix ι ι ℝ)
    (hX : X ∈ (mulLeftLinearMap ι ℝ A).range) :
    mulLeftLinearMap ι ℝ G (mulLeftLinearMap ι ℝ A X) = X := by
  obtain ⟨Z, hZ⟩ := LinearMap.mem_range.mp hX
  rw [← hZ]
  let a : Module.End ℝ (Matrix ι ι ℝ) := mulLeftLinearMap ι ℝ A
  let g : Module.End ℝ (Matrix ι ι ℝ) := mulLeftLinearMap ι ℝ G
  have hLift : IsGroupInverse a g := by
    simpa [a, g] using mulLeftLinearMap_groupInverse A G hG
  calc
    g (a (a Z)) = (g * a) (a Z) := by simp [Module.End.mul_eq_comp]
    _ = (a * g) (a Z) := by rw [hLift.2.2.symm]
    _ = ((a * g) * a) Z := by simp [Module.End.mul_eq_comp]
    _ = a Z := congrArg (fun F : Module.End ℝ (Matrix ι ι ℝ) => F Z) hLift.1

/-- For every finite row-stochastic `P`, the lifted group inverse solves the
left-multiplication Poisson equation on the actual range of the full-matrix
Markov Laplacian. -/
theorem exists_stochastic_markovLeft_green_recovers_range
    [Nontrivial ι]
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ G : Matrix ι ι ℝ,
      IsGroupInverse (1 - P) G ∧
      ∀ X : Matrix ι ι ℝ, X ∈ (markovLeftOnsager P).range →
        mulLeftLinearMap ι ℝ G (markovLeftOnsager P X) = X := by
  obtain ⟨G, hG, _⟩ := exists_stochastic_markovLeft_groupInverse P hP
  refine ⟨G, hG, ?_⟩
  intro X hX
  exact mulLeft_groupInverse_recovers_on_range (1 - P) G hG X (by
    simpa [markovLeftOnsager] using hX)

end InfoGeometry.QuantumContext.MarkovDrazin
