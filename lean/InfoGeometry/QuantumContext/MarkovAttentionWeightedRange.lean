/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import InfoGeometry.QuantumContext.MarkovAttentionGroupInverse

/-!
# Weighted solvability criterion for a positive finite Markov Laplacian

Given a normalized stationary row weight for a strictly positive finite
row-stochastic matrix, the range of `I - P` is exactly the kernel of the
weighted-mean functional. This converts the range hypothesis in the existing
group-inverse Poisson solver into an explicit finite balance condition.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A nonnegative normalized stationary row weight is strictly positive when
every transition entry is strictly positive. -/
theorem stationaryRowProbability_pos_of_pos_entries
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j) :
    ∀ j, 0 < π j := by
  have hsome : ∃ i, 0 < π i := by
    by_contra h
    push Not at h
    have hsum_nonpos : ∑ i, π i ≤ 0 :=
      Finset.sum_nonpos fun i _ => h i
    rw [hπsum] at hsum_nonpos
    norm_num at hsum_nonpos
  intro j
  rw [← hstat j]
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (hπnonneg i) (le_of_lt (hPpos i j))
  · obtain ⟨i, hi⟩ := hsome
    exact ⟨i, Finset.mem_univ _, mul_pos hi (hPpos i j)⟩

/-- Every finite strictly positive row-stochastic matrix has a strictly
positive normalized stationary row distribution. The construction is purely
finite-dimensional: singularity of `1 - P` gives a left fixed vector; its
coordinatewise absolute value is stationary by the triangle inequality and
row-sum identity, then normalization gives total mass one. -/
theorem exists_positive_normalized_stationary_row
    [Nonempty ι]
    (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) :
    ∃ π : ι → ℝ,
      (∀ i, 0 < π i) ∧
      (∑ i, π i = 1) ∧
      (∀ j, ∑ i, π i * P i j = π j) := by
  classical
  have hone_ne : (1 : ι → ℝ) ≠ 0 := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun h i
    norm_num at this
  have hone_fix : P *ᵥ (1 : ι → ℝ) = 1 :=
    (Matrix.mem_rowStochastic.mp hP).2
  have hLone : (1 - P) *ᵥ (1 : ι → ℝ) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hone_fix, sub_self]
  have hdet : (1 - P).det = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff).mp ⟨1, hone_ne, hLone⟩
  obtain ⟨v, hvne, hvL⟩ := (Matrix.exists_vecMul_eq_zero_iff).mpr hdet
  have hvstat : v ᵥ* P = v := by
    have hsub := Matrix.vecMul_sub 1 P v
    rw [Matrix.vecMul_one] at hsub
    rw [hsub] at hvL
    have : v - v ᵥ* P = 0 := hvL
    exact (sub_eq_zero.mp this).symm
  let w : ι → ℝ := fun i => |v i|
  have hdom (j : ι) : |v j| ≤ ∑ i, |v i| * P i j := by
    have hj : v j = ∑ i, v i * P i j := by
      have := congrFun hvstat j
      simpa [Matrix.vecMul, dotProduct] using this.symm
    rw [hj]
    calc
      |∑ i, v i * P i j| ≤ ∑ i, |v i * P i j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |v i| * P i j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_pos (hPpos i j)]
  have hRhs : (∑ j, ∑ i, |v i| * P i j) = ∑ i, |v i| := by
    rw [Finset.sum_comm]
    calc
      (∑ i, ∑ j, |v i| * P i j) = ∑ i, |v i| * (∑ j, P i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ i, |v i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Matrix.sum_row_of_mem_rowStochastic hP i, mul_one]
  have hdomSum : (∑ j, |v j|) = ∑ j, ∑ i, |v i| * P i j := by
    apply le_antisymm
    · exact Finset.sum_le_sum fun j hj => hdom j
    · rw [hRhs]
  have hdomEq : ∀ j, |v j| = ∑ i, |v i| * P i j := by
    intro j
    have hnonneg (k : ι) : 0 ≤ (∑ i, |v i| * P i k) - |v k| := sub_nonneg.mpr (hdom k)
    have hsumzero : ∑ k, ((∑ i, |v i| * P i k) - |v k|) = 0 := by
      rw [Finset.sum_sub_distrib, ← hdomSum]
      simp
    have hterm : (∑ i, |v i| * P i j) - |v j| = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => hnonneg k)).mp hsumzero j
      simp
    linarith
  have hwstat (j : ι) : ∑ i, w i * P i j = w j := by
    exact (hdomEq j).symm
  have hwnonneg (i : ι) : 0 ≤ w i := abs_nonneg _
  have hwsum_pos : 0 < ∑ i, w i := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hvne (funext h)
    have hiabs : 0 < w i := abs_pos.mpr hi
    have hsum : w i ≤ ∑ k, w k := Finset.single_le_sum
      (fun k hk => hwnonneg k) (Finset.mem_univ i)
    exact lt_of_lt_of_le hiabs hsum
  let c : ℝ := (∑ i, w i)⁻¹
  let π : ι → ℝ := fun i => c * w i
  have hπnonneg (i : ι) : 0 ≤ π i := by
    exact mul_nonneg (le_of_lt (inv_pos.mpr hwsum_pos)) (hwnonneg i)
  have hπsum : ∑ i, π i = 1 := by
    dsimp [π, c]
    calc
      (∑ i, (∑ k, w k)⁻¹ * w i) = (∑ k, w k)⁻¹ * (∑ i, w i) := by
        rw [Finset.mul_sum]
      _ = 1 := inv_mul_cancel₀ hwsum_pos.ne'
  have hπstat (j : ι) : ∑ i, π i * P i j = π j := by
    dsimp [π]
    calc
      (∑ i, c * w i * P i j) = c * (∑ i, w i * P i j) := by
        simp_rw [mul_assoc]
        rw [Finset.mul_sum]
      _ = c * w j := by rw [hwstat j]
  have hπpos : ∀ i, 0 < π i :=
    stationaryRowProbability_pos_of_pos_entries P π hPpos hπnonneg hπsum hπstat
  exact ⟨π, hπpos, hπsum, hπstat⟩

/-- The finite weighted-mean functional associated with a row weight `π`. -/
def weightedMeanMap (π : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, π i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, π i * (c * x i)) = ∑ i, c * (π i * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          π i * (c * x i) = (π i * c) * x i := (mul_assoc ..).symm
          _ = (c * π i) * x i := by rw [mul_comm (π i) c]
          _ = c * (π i * x i) := mul_assoc ..
      _ = c * (∑ i, π i * x i) := (Finset.mul_sum ..).symm

/-- A stationary row weight annihilates every vector in the range of `I-P`.
The stationarity convention is `∑ i, π i * P i j = π j`. -/
theorem weightedMeanMap_laplacian_eq_zero
    (P : Matrix ι ι ℝ) (π x : ι → ℝ)
    (hstat : ∀ j, ∑ i, π i * P i j = π j) :
    weightedMeanMap π ((1 - P).mulVec x) = 0 := by
  have htransition :
      ∑ i, π i * (P.mulVec x) i = ∑ j, π j * x j := by
    simp only [Matrix.mulVec, dotProduct]
    calc
      (∑ i, π i * ∑ j, P i j * x j) =
          ∑ i, ∑ j, (π i * P i j) * x j := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            exact (mul_assoc (π i) (P i j) (x j)).symm
      _ = ∑ j, ∑ i, (π i * P i j) * x j := by
            rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, π i * P i j) * x j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_mul]
      _ = ∑ j, π j * x j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hstat j]
  change (∑ i, π i * ((1 - P).mulVec x i)) = 0
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [htransition]
  exact sub_self _

private theorem weightedMeanMap_laplacian_apply
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (x : ι → ℝ) :
    weightedMeanMap π ((Matrix.toLin' (1 - P)) x) = 0 := by
  simpa only [Matrix.toLin'_apply] using
    weightedMeanMap_laplacian_eq_zero P π x hstat

/-- The range of the finite positive Markov Laplacian consists exactly of
the sources with zero stationary weighted mean. No detailed-balance
assumption is needed. -/
theorem range_laplacian_eq_weightedMean_ker
    [Nonempty ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j) :
    LinearMap.range (Matrix.toLin' (1 - P)) = LinearMap.ker (weightedMeanMap π) := by
  let A : Module.End ℝ (ι → ℝ) := Matrix.toLin' (1 - P)
  obtain ⟨D, hD⟩ := exists_stochastic_laplacian_groupInverse P hP
  have hmeanA (x : ι → ℝ) : weightedMeanMap π (A x) = 0 := by
    exact weightedMeanMap_laplacian_apply P π hstat x
  have hmeanE (x : ι → ℝ) :
      weightedMeanMap π (principalIdempotent A D x) = weightedMeanMap π x := by
    have hproj : principalIdempotent A D x = x - A (D x) := by
      simp [principalIdempotent, regularIdempotent, Module.End.mul_apply]
    rw [hproj, map_sub, hmeanA]
    simp
  have hEker (x : ι → ℝ) : A (principalIdempotent A D x) = 0 := by
    have h := congrArg (fun f : Module.End ℝ (ι → ℝ) => f x)
      (mul_principalIdempotent_eq_zero hD)
    change (A * principalIdempotent A D) x = 0 at h
    simpa only [Module.End.mul_apply] using h
  have hconst (x : ι → ℝ) (hx : A x = 0) : ∃ c : ℝ, ∀ i, x i = c := by
    have hfixed : P *ᵥ x = x := by
      have hA' : (1 - P) *ᵥ x = 0 := by
        simpa only [A, Matrix.toLin'_apply] using hx
      have hsub : x - P *ᵥ x = 0 := by
        simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hA'
      exact (sub_eq_zero.mp hsub).symm
    exact (positive_rowStochastic_mulVec_fixed_iff_const P hP hPpos x).mp hfixed
  apply le_antisymm
  · rintro b ⟨x, rfl⟩
    exact hmeanA x
  · intro b hb
    have hmeanEb : weightedMeanMap π (principalIdempotent A D b) = 0 := by
      rw [hmeanE, hb]
    obtain ⟨c, hc⟩ := hconst (principalIdempotent A D b) (hEker b)
    have hmean_const : weightedMeanMap π (fun _ : ι => c) = c := by
      simp only [weightedMeanMap]
      calc
        (∑ i, π i * c) = (∑ i, π i) * c := (Finset.sum_mul ..).symm
        _ = c := by rw [hπsum]; simp
    have hc0 : c = 0 := by
      calc
        c = weightedMeanMap π (principalIdempotent A D b) := by
          rw [show principalIdempotent A D b = (fun _ : ι => c) from funext hc]
          exact hmean_const.symm
        _ = 0 := hmeanEb
    have hEb : principalIdempotent A D b = 0 := by
      funext i
      rw [hc i, hc0]
      simp
    refine ⟨D b, ?_⟩
    have hdecomp : principalIdempotent A D b = b - A (D b) := by
      simp [principalIdempotent, regularIdempotent, Module.End.mul_apply,
        Module.End.one_apply]
    rw [hdecomp] at hEb
    have hbEq : b = A (D b) := sub_eq_zero.mp hEb
    exact hbEq.symm

/-- For a normalized stationary row weight of a strictly positive transition
matrix, the complementary group-inverse projector is the constant-valued
weighted-mean projection. -/
theorem principalIdempotent_eq_stationaryMean_projection
    [Nonempty ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (D : Module.End ℝ (ι → ℝ))
    (hD : IsGroupInverse (Matrix.toLin' (1 - P)) D)
    (x : ι → ℝ) :
    principalIdempotent (Matrix.toLin' (1 - P)) D x =
      fun _ => weightedMeanMap π x := by
  let A : Module.End ℝ (ι → ℝ) := Matrix.toLin' (1 - P)
  have hmeanA (y : ι → ℝ) : weightedMeanMap π (A y) = 0 := by
    exact weightedMeanMap_laplacian_apply P π hstat y
  have hmeanE (y : ι → ℝ) :
      weightedMeanMap π (principalIdempotent A D y) = weightedMeanMap π y := by
    have hproj : principalIdempotent A D y = y - A (D y) := by
      simp [principalIdempotent, regularIdempotent, Module.End.mul_apply]
    rw [hproj, map_sub, hmeanA]
    simp
  have hEker (y : ι → ℝ) : A (principalIdempotent A D y) = 0 := by
    have h := congrArg (fun f : Module.End ℝ (ι → ℝ) => f y)
      (mul_principalIdempotent_eq_zero hD)
    change (A * principalIdempotent A D) y = 0 at h
    simpa only [Module.End.mul_apply] using h
  have hconst (y : ι → ℝ) (hy : A y = 0) : ∃ c : ℝ, ∀ i, y i = c := by
    have hfixed : P *ᵥ y = y := by
      have hA' : (1 - P) *ᵥ y = 0 := by
        simpa only [A, Matrix.toLin'_apply] using hy
      have hsub : y - P *ᵥ y = 0 := by
        simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hA'
      exact (sub_eq_zero.mp hsub).symm
    exact (positive_rowStochastic_mulVec_fixed_iff_const P hP hPpos y).mp hfixed
  obtain ⟨c, hc⟩ := hconst (principalIdempotent A D x) (hEker x)
  have hmeanConst : weightedMeanMap π (fun _ : ι => c) = c := by
    simp only [weightedMeanMap]
    calc
      (∑ i, π i * c) = (∑ i, π i) * c := (Finset.sum_mul ..).symm
      _ = c := by rw [hπsum]; simp
  have hc_mean : c = weightedMeanMap π x := by
    calc
      c = weightedMeanMap π (principalIdempotent A D x) := by
        rw [show principalIdempotent A D x = (fun _ : ι => c) from funext hc]
        exact hmeanConst.symm
      _ = weightedMeanMap π x := hmeanE x
  funext i
  rw [hc i, hc_mean]

/-- The strictly positive normalized stationary row distribution of a finite
strictly positive row-stochastic matrix is unique. The proof identifies the
group-inverse kernel projector with the constant weighted-mean map and reads
the weights on the coordinate vectors. -/
theorem existsUnique_positive_normalized_stationary_row
    [Nonempty ι]
    (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j) :
    ∃! π : ι → ℝ,
      (∀ i, 0 < π i) ∧
      (∑ i, π i = 1) ∧
      (∀ j, ∑ i, π i * P i j = π j) := by
  obtain ⟨π, hπpos, hπsum, hπstat⟩ :=
    exists_positive_normalized_stationary_row P hP hPpos
  refine ⟨π, ⟨hπpos, hπsum, hπstat⟩, ?_⟩
  intro μ hμ
  rcases hμ with ⟨hμpos, hμsum, hμstat⟩
  obtain ⟨D, hD⟩ := exists_stochastic_laplacian_groupInverse P hP
  have hπproj := principalIdempotent_eq_stationaryMean_projection
    P π hP hPpos hπsum hπstat D hD
  have hμproj := principalIdempotent_eq_stationaryMean_projection
    P μ hP hPpos hμsum hμstat D hD
  have hmean_eq (x : ι → ℝ) : weightedMeanMap π x = weightedMeanMap μ x := by
    have hπx := hπproj x
    have hμx := hμproj x
    have hpoint (i : ι) : weightedMeanMap π x = weightedMeanMap μ x := by
      calc
        weightedMeanMap π x = principalIdempotent (Matrix.toLin' (1 - P)) D x i :=
          (congrFun hπx i).symm
        _ = weightedMeanMap μ x := congrFun hμx i
    exact hpoint (Classical.choice ‹Nonempty ι›)
  funext i
  have hcoord := hmean_eq (Pi.single i (1 : ℝ))
  have hπi : weightedMeanMap π (Pi.single i (1 : ℝ)) = π i := by
    simp [weightedMeanMap, Pi.single_apply]
  have hμi : weightedMeanMap μ (Pi.single i (1 : ℝ)) = μ i := by
    simp [weightedMeanMap, Pi.single_apply]
  calc
    μ i = weightedMeanMap μ (Pi.single i (1 : ℝ)) := hμi.symm
    _ = weightedMeanMap π (Pi.single i (1 : ℝ)) := hcoord.symm
    _ = π i := hπi

/-- A zero stationary weighted mean is the exact solvability condition for the
finite Markov Poisson equation. The group inverse gives the canonical solution
in `range (I - P)`, where it is unique. -/
theorem stochastic_laplacian_poisson_solution_of_weightedMean_zero
    [Nonempty ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (b : ι → ℝ) (hb : weightedMeanMap π b = 0) :
    ∃ D : Module.End ℝ (ι → ℝ),
      IsGroupInverse (Matrix.toLin' (1 - P)) D ∧
      Matrix.toLin' (1 - P) (D b) = b ∧
      D b ∈ (Matrix.toLin' (1 - P)).range ∧
      ∀ x : ι → ℝ, x ∈ (Matrix.toLin' (1 - P)).range →
        Matrix.toLin' (1 - P) x = b → x = D b := by
  have hbker : b ∈ LinearMap.ker (weightedMeanMap π) :=
    LinearMap.mem_ker.mpr hb
  have hbrange : b ∈ LinearMap.range (Matrix.toLin' (1 - P)) := by
    rw [range_laplacian_eq_weightedMean_ker P π hP hPpos hπsum hstat]
    exact hbker
  exact stochastic_laplacian_poisson_solution_exists_unique P hP b hbrange

end InfoGeometry.QuantumContext.MarkovDrazin
