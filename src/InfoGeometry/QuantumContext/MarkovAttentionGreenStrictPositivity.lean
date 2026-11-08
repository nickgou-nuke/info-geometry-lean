/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovAttentionGreenPositivity

/-!
# Strict positivity of the reversible Markov Green form

For a finite strictly positive reversible transition matrix, the group
inverse of `I - P` has strictly positive stationary-weighted quadratic form
on every nonzero source of zero stationary mean. The theorem uses the
existing finite Poisson solvability and Dirichlet zero-energy
characterization; it makes no claim for general directed chains.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A nonzero zero-mean source has strictly positive reversible Green energy.

The group inverse solves the Poisson equation on the zero-mean range. If its
Dirichlet energy vanished, strict positivity of the stationary weights and
transition entries would force the potential to be constant, and its
Laplacian would then force the source to vanish. -/
theorem weightedMarkovPairing_groupInverse_pos_of_ne
    (P G : Matrix ι ι ℝ) (π b : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπpos : ∀ i, 0 < π i)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hG : IsGroupInverse (1 - P) G)
    (hb : weightedMeanMap π b = 0)
    (hbne : b ≠ 0) :
    0 < weightedMarkovPairing π b (Matrix.mulVec G b) := by
  let A : Module.End ℝ (ι → ℝ) := Matrix.toLin' (1 - P)
  let D : Module.End ℝ (ι → ℝ) := Matrix.toLin' G
  let x : ι → ℝ := G.mulVec b
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
  have hsolve : (1 - P).mulVec x = b := by
    simpa only [A, D, x, Matrix.toLin'_apply] using hsolveEnd
  have henergy_nonneg :
      0 ≤ weightedMarkovPairing π x (x - P.mulVec x) :=
    weightedMarkovPairing_laplacian_nonneg P π x hP hDB
      (fun i => le_of_lt (hπpos i))
  have henergy_eq :
      weightedMarkovPairing π x (x - P.mulVec x) =
        weightedMarkovPairing π b x := by
    calc
      weightedMarkovPairing π x (x - P.mulVec x) =
          weightedMarkovPairing π (x - P.mulVec x) x :=
            weightedMarkovPairing_laplacian_symmetric P π x x hDB
      _ = weightedMarkovPairing π ((1 - P).mulVec x) x := by
            rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = weightedMarkovPairing π b x := by rw [hsolve]
  have henergy_pos :
      0 < weightedMarkovPairing π x (x - P.mulVec x) := by
    by_contra hnot
    have heq : weightedMarkovPairing π x (x - P.mulVec x) = 0 :=
      le_antisymm (le_of_not_gt hnot) henergy_nonneg
    obtain ⟨c, hc⟩ :=
      (weightedMarkovPairing_laplacian_eq_zero_iff_const P π x hP hDB
        hπpos hPpos).mp heq
    have hPx : P.mulVec x = x := by
      have hxConst : x = fun _ => c := funext hc
      rw [hxConst]
      ext i
      simp only [Matrix.mulVec, dotProduct]
      calc
        (∑ j, P i j * c) = (∑ j, P i j) * c := by
          rw [← Finset.sum_mul]
        _ = c := by
          rw [Matrix.sum_row_of_mem_rowStochastic hP i]
          ring
    have hLx : (1 - P).mulVec x = 0 := by
      calc
        (1 - P).mulVec x = x - P.mulVec x := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        _ = 0 := by rw [hPx, sub_self]
    exact hbne (hsolve.symm.trans hLx)
  rw [← henergy_eq]
  exact henergy_pos

end InfoGeometry.QuantumContext.MarkovDrazin
