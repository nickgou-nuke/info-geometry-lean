/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import InfoGeometry.QuantumContext.MarkovAttentionFiniteDirichlet
import InfoGeometry.QuantumContext.MarkovAttentionWeightedRange

/-!
# Positivity of the reversible Markov Green form

For a strictly positive finite reversible transition matrix, the group inverse
of `I - P` has a nonnegative stationary-weighted quadratic form on
mean-zero sources. The statement is conditional on detailed balance; it makes
no positivity claim for a general directed transition matrix.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A reversible Markov group inverse has nonnegative Green energy on every
source of zero stationary mean. Strict positivity identifies those sources
with the range of `I - P`; detailed balance supplies the nonnegative
Dirichlet form. -/
theorem weightedMarkovPairing_groupInverse_nonneg
    (P G : Matrix ι ι ℝ) (π b : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπpos : ∀ i, 0 < π i)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * P i j = π j)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hG : IsGroupInverse (1 - P) G)
    (hb : weightedMeanMap π b = 0) :
    0 ≤ weightedMarkovPairing π b (Matrix.mulVec G b) := by
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
  have hsolve : Matrix.mulVec (1 - P) (Matrix.mulVec G b) = b := by
    have h := apply_groupInverse_eq_of_mem_range A D hD b hbRange
    change Matrix.toLin' (1 - P) (Matrix.toLin' G b) = b at h
    simpa only [Matrix.toLin'_apply] using h
  have henergy := weightedMarkovPairing_laplacian_nonneg
    P π (Matrix.mulVec G b) hP hDB
    (fun i => le_of_lt (hπpos i))
  have hsymm := weightedMarkovPairing_laplacian_symmetric
    P π (Matrix.mulVec G b) (Matrix.mulVec G b) hDB
  calc
    0 ≤ weightedMarkovPairing π (Matrix.mulVec G b)
        (Matrix.mulVec G b - Matrix.mulVec P (Matrix.mulVec G b)) := henergy
    _ = weightedMarkovPairing π
        (Matrix.mulVec (1 - P) (Matrix.mulVec G b)) (Matrix.mulVec G b) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]
          exact hsymm
    _ = weightedMarkovPairing π b (Matrix.mulVec G b) := by rw [hsolve]

end InfoGeometry.QuantumContext.MarkovDrazin
