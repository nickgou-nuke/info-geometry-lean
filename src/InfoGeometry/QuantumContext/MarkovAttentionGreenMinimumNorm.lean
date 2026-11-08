/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import InfoGeometry.QuantumContext.MarkovAttentionFiniteDirichlet
import InfoGeometry.QuantumContext.MarkovAttentionWeightedRange

/-!
# Weighted quadratic minimizer for the finite Markov Poisson equation

For a strictly positive finite row-stochastic transition matrix and a
normalized stationary row distribution, the group-inverse solution of a
solvable Poisson equation minimizes the stationary-weighted quadratic
functional `weightedMarkovPairing π x x` among all solutions. Equality forces
the solution to be the group-inverse solution. This uses the constant-kernel
characterization and weighted-mean range characterization; it does not
require detailed balance.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- Translate a zero weighted-mean vector by a constant. With normalized
weights, its weighted quadratic functional increases by exactly the square
of that constant. -/
theorem weightedMarkovPairing_translate_const
    (π x : ι → ℝ) (c : ℝ)
    (hmean : weightedMeanMap π x = 0)
    (hsum : ∑ i, π i = 1) :
    weightedMarkovPairing π (x + fun _ => c) (x + fun _ => c) =
      weightedMarkovPairing π x x + c ^ 2 := by
  unfold weightedMarkovPairing weightedMeanMap at *
  change (∑ i, π i * x i) = 0 at hmean
  calc
    (∑ i, π i * (x i + c) * (x i + c)) =
        ∑ i, (π i * x i * x i + (2 * c) * (π i * x i) + c ^ 2 * π i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, π i * x i * x i) +
        (2 * c) * (∑ i, π i * x i) + c ^ 2 * (∑ i, π i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (∑ i, π i * x i * x i) + c ^ 2 := by
          rw [hmean, hsum]
          ring

/-- Among all solutions of a finite strictly positive Markov Poisson equation,
the group-inverse solution minimizes the stationary-weighted quadratic
functional. The claim is valid for directed chains as stated; no reversibility
assumption is needed. -/
theorem groupInverse_poisson_solution_minimizes_weightedQuadratic
    (P G : Matrix ι ι ℝ) (π b x : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G)
    (hb : weightedMeanMap π b = 0)
    (hx : (1 - P).mulVec x = b) :
    weightedMarkovPairing π (G.mulVec b) (G.mulVec b) ≤
      weightedMarkovPairing π x x := by
  let A : Module.End ℝ (ι → ℝ) := Matrix.toLin' (1 - P)
  let D : Module.End ℝ (ι → ℝ) := Matrix.toLin' G
  have hD : IsGroupInverse A D := by
    constructor
    · have h := congrArg Matrix.toLin' hG.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    constructor
    · have h := congrArg Matrix.toLin' hG.2.1
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' hG.2.2
      simpa [A, D, Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  have hbRange : b ∈ LinearMap.range A := by
    rw [range_laplacian_eq_weightedMean_ker P π hP hPpos hπsum hstat]
    exact LinearMap.mem_ker.mpr hb
  have hsolveEnd : A (D b) = b :=
    apply_groupInverse_eq_of_mem_range A D hD b hbRange
  have hsolve : (1 - P).mulVec (G.mulVec b) = b := by
    simpa only [A, D, Matrix.toLin'_apply] using hsolveEnd
  have hsame : (1 - P).mulVec x = (1 - P).mulVec (G.mulVec b) :=
    hx.trans hsolve.symm
  obtain ⟨c, hc⟩ := positive_rowStochastic_laplacian_solutions_differ_by_const
    P hP hPpos x (G.mulVec b) hsame
  have htranslate : ∀ i, x i = (G.mulVec b) i + c := by
    intro i
    linarith [hc i]
  have hGRange : D b ∈ LinearMap.range A :=
    groupInverse_apply_mem_range A D hD b
  have hmeanG : weightedMeanMap π (G.mulVec b) = 0 := by
    rcases hGRange with ⟨y, hy⟩
    have hy' : (1 - P).mulVec y = G.mulVec b := by
      change Matrix.toLin' (1 - P) y = Matrix.toLin' G b at hy
      simpa only [Matrix.toLin'_apply] using hy
    have hmean := weightedMeanMap_laplacian_eq_zero P π y hstat
    rw [hy'] at hmean
    exact hmean
  have htranslateVec : x = G.mulVec b + fun _ => c := by
    funext i
    exact htranslate i
  rw [htranslateVec, weightedMarkovPairing_translate_const π (G.mulVec b) c
    hmeanG hπsum]
  exact le_add_of_nonneg_right (sq_nonneg c)

/-- Equality in the quadratic minimization forces the additive constant to
vanish, so the minimizing solution is unique. -/
theorem groupInverse_poisson_solution_unique_minimizer
    (P G : Matrix ι ι ℝ) (π b x : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G)
    (hb : weightedMeanMap π b = 0)
    (hx : (1 - P).mulVec x = b)
    (heq : weightedMarkovPairing π (G.mulVec b) (G.mulVec b) =
      weightedMarkovPairing π x x) :
    x = G.mulVec b := by
  have hD : IsGroupInverse
      (Matrix.toLin' (1 - P)) (Matrix.toLin' G) := by
    constructor
    · have h := congrArg Matrix.toLin' hG.1
      simpa [Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    constructor
    · have h := congrArg Matrix.toLin' hG.2.1
      simpa [Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
    · have h := congrArg Matrix.toLin' hG.2.2
      simpa [Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  have hsolve : (1 - P).mulVec (G.mulVec b) = b := by
    have hbRange : b ∈ LinearMap.range (Matrix.toLin' (1 - P)) := by
      rw [range_laplacian_eq_weightedMean_ker P π hP hPpos hπsum hstat]
      exact LinearMap.mem_ker.mpr hb
    have hs := apply_groupInverse_eq_of_mem_range
      (Matrix.toLin' (1 - P)) (Matrix.toLin' G) hD b hbRange
    simpa only [Matrix.toLin'_apply] using hs
  obtain ⟨c, hc⟩ := positive_rowStochastic_laplacian_solutions_differ_by_const
    P hP hPpos x (G.mulVec b) (hx.trans hsolve.symm)
  have htranslate : ∀ i, x i = (G.mulVec b) i + c := by
    intro i
    linarith [hc i]
  have hGmean : weightedMeanMap π (G.mulVec b) = 0 := by
    have hrange := groupInverse_apply_mem_range
      (Matrix.toLin' (1 - P)) (Matrix.toLin' G) hD b
    rcases hrange with ⟨y, hy⟩
    have hy' : (1 - P).mulVec y = G.mulVec b := by
      change Matrix.toLin' (1 - P) y = Matrix.toLin' G b at hy
      simpa only [Matrix.toLin'_apply] using hy
    have hmean := weightedMeanMap_laplacian_eq_zero P π y hstat
    rw [hy'] at hmean
    exact hmean
  have htranslateVec : x = G.mulVec b + fun _ => c := by
    funext i
    exact htranslate i
  rw [htranslateVec, weightedMarkovPairing_translate_const π (G.mulVec b) c
    hGmean hπsum] at heq
  have hc0 : c ^ 2 = 0 := by linarith
  have : c = 0 := sq_eq_zero_iff.mp hc0
  subst c
  have hzero : G.mulVec b + (fun _ : ι => (0 : ℝ)) = G.mulVec b := by
    funext i
    simp
  exact htranslateVec.trans hzero

end InfoGeometry.QuantumContext.MarkovDrazin
