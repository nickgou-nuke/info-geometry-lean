/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovGroupInverseIntertwining
import InfoGeometry.QuantumContext.GroupInverseIntertwinerAlgebra

/-!
# Functoriality of the Markov group inverse under rectangular intertwiners

This module derives the consumer-facing corollaries of rectangular Markov
intertwining from the canonical owners

* `InfoGeometry.QuantumContext.IntertwinerAlgebra` for the purely algebraic
  intertwining step, and
* `InfoGeometry.QuantumContext.MarkovDrazin.groupInverse_intertwines_of_stochastic_compatible`
  for the finite stochastic group-inverse transport.

Four results are obtained.

1. `stationaryMeanMatrix_intertwines`: the rank-one stationary projector
   `stationaryMeanMatrix π` intertwines a rectangular intertwiner whenever the
   intertwiner has unit row sums and transports the stationary row.
2. `poissonGreen_transports_of_stationary_compatible`: the lifted coarse-space
   group-inverse solution operator satisfies the fine-space intertwining on
   transported right-hand sides.
3. `regularizedShift_intertwines_of_stationary_compatible`: the regularized
   Markov operators `G + stationaryMeanMatrix π` and `H + stationaryMeanMatrix μ`
   intertwine. `MarkovAttentionKemenySnell` separately proves that each has a
   two-sided inverse; this theorem does not claim that those inverses intertwine.
4. `liftedSolution_mean_zero_of_stationary_compatible`: the lifted solution has
   zero stationary weighted mean, so it lies in the solvable range of the fine
   Markov Laplacian.

## Scope

All statements are finite algebraic identities over `ℝ`. Nothing here asserts
convergence of stochastic iterates, a mean first passage time interpretation, or
an identification with lumping, Stiefel compression, RG coarse-graining or
attention pooling. The rectangular intertwiners quantified here are arbitrary
matrices of the stated size; they are not assumed to be projections, embeddings
or attention pooling operators, and no such interpretation is proved.

The hypothesis lists are inherited verbatim from the canonical owner
`groupInverse_intertwines_of_stochastic_compatible`, including the nonnegativity
of `π` and `μ`; this module adds no hypothesis of its own beyond the observable
that the corollary consumes.

## What is not covered

The rectangular intertwiners `C` quantified here are arbitrary matrices of the
stated size. They are not assumed to be projections, embeddings, lumping maps,
Stiefel embeddings or attention pooling operators, and no such interpretation
is proved. Coarse-graining and Stiefel owners do exist in the repository —
`InfoGeometry.Canonical.CoarseGraining` (`FiniteCoarseGraining X Y := X → Y`,
`encoderMarginal`) and `InfoGeometry.QuantumContext.CausalPetzStiefelConservation`
(`blockIntertwiner : Matrix (Fin 2) (Fin 2) R`, `gram_isometry_iff_stiefel`) —
but neither mentions `Markov`, `Laplacian` or `IsGroupInverse`, and
`blockIntertwiner` is square rather than rectangular. Specializing this module
to either would be new formalization work.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

omit [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- Rank-one stationary projector intertwining, in the row convention used
throughout the Markov layer: `C` has unit row sums and transports the
normalized stationary row `π` to the normalized stationary row `μ`.

This is the reusable form of the stationary compatibility condition that the
group-inverse intertwining theorem consumes. -/
theorem stationaryMeanMatrix_intertwines
    (π : ι → ℝ) (μ : κ → ℝ) (C : Matrix ι κ ℝ)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hCmean : ∀ j, ∑ i, π i * C i j = μ j) :
    stationaryMeanMatrix π * C = C * stationaryMeanMatrix μ := by
  ext i j
  simp only [Matrix.mul_apply, stationaryMeanMatrix]
  calc (∑ k, π k * C k j) = μ j := hCmean j
    _ = (∑ k, C i k) * μ j := by rw [hCrows i]; simp
    _ = ∑ k, C i k * μ j := by rw [← Finset.sum_mul]

omit [Nonempty ι] [DecidableEq κ] in
/-- **SHARPNESS CERTIFICATE.** Unit row sums alone do *not* intertwine the
stationary projector.

This refutes, by explicit counterexample, any claim that the stationary row
transport `∀ j, ∑ i, π i * C i j = μ j` is dispensable: the intertwiner
`!![1 / 2, 1 / 2; 0, 1]` has all row sums equal to `1`, yet
`stationaryMeanMatrix π * C` and `C * stationaryMeanMatrix π` for the uniform
weight `π` differ at entry `(0, 0)`, being `1 / 4` and `1 / 2` respectively.

It certifies that the stationary compatibility hypothesis of this module is
neither vacuous nor a consequence of unit row sums alone. -/
theorem unitRowSums_alone_do_not_intertwine_stationaryMeanMatrix :
    ¬ (∀ C : Matrix (Fin 2) (Fin 2) ℝ, (∀ i, ∑ j, C i j = 1) →
        stationaryMeanMatrix (fun _ => (1 : ℝ) / 2) * C
          = C * stationaryMeanMatrix (fun _ => (1 : ℝ) / 2)) := by
  intro hall
  have hall' := hall (C := !![(1 : ℝ) / 2, (1 : ℝ) / 2; 0, 1]) (by
    intro i
    fin_cases i <;> simp <;> norm_num)
  rw [show (stationaryMeanMatrix (fun _ => (1 : ℝ) / 2) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(1 : ℝ) / 2, (1 : ℝ) / 2; (1 : ℝ) / 2, (1 : ℝ) / 2] by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl] at hall'
  have hne : !![(1 : ℝ) / 2, (1 : ℝ) / 2; (1 : ℝ) / 2, (1 : ℝ) / 2]
      * !![(1 : ℝ) / 2, (1 : ℝ) / 2; 0, 1]
      ≠ !![(1 : ℝ) / 2, (1 : ℝ) / 2; 0, 1]
        * !![(1 : ℝ) / 2, (1 : ℝ) / 2; (1 : ℝ) / 2, (1 : ℝ) / 2] := by
    intro he
    have hzero := congrFun (congrFun he (0 : Fin 2)) (0 : Fin 2)
    rw [mul_fin_two, mul_fin_two] at hzero
    norm_num at hzero
  exact hne hall'

/-- Lifting a matrix-level group inverse of `1 - P` to the canonical endomorphism
interface `Module.End ℝ (ι → ℝ)`. This is the carrier bridge used by every lane
that reasons about ranges, kernels or unique solutions. -/
theorem isGroupInverse_toLin'
    {P G : Matrix ι ι ℝ} (hG : IsGroupInverse (1 - P) G) :
    IsGroupInverse (Matrix.toLin' (1 - P)) (Matrix.toLin' G) := by
  constructor
  · have h := congrArg Matrix.toLin' hG.1
    simpa [Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  constructor
  · have h := congrArg Matrix.toLin' hG.2.1
    simpa [Matrix.toLin'_mul, Module.End.mul_eq_comp] using h
  · have h := congrArg Matrix.toLin' hG.2.2
    simpa [Matrix.toLin'_mul, Module.End.mul_eq_comp] using h

/-- **POISSON GREEN TRANSPORT.**

For strictly positive finite row-stochastic `P` and `Q`, a nonnegative unit-row
rectangular intertwiner `C` with `P * C = C * Q`, and group inverses `G`, `H` of
`1 - P` and `1 - Q`, the group-inverse solution operators transport:

`G * (C * b) = C * (H * b)` for every matrix-valued right-hand side
`b : Matrix κ η ℝ`.

This is an identity of matrix products. Solvability and uniqueness of the
corresponding Poisson equations require the range hypotheses established in
`MarkovAttentionGroupInverse` and are not restated here. -/
theorem poissonGreen_transports_of_stationary_compatible {η : Type*}
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hQ : Q ∈ Matrix.rowStochastic ℝ κ)
    (hPpos : ∀ i j, 0 < P i j) (hQpos : ∀ i j, 0 < Q i j)
    (hπnonneg : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hμnonneg : ∀ j, 0 ≤ μ j) (hμsum : ∑ j, μ j = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hμstat : ∀ j, ∑ j', μ j' * Q j' j = μ j)
    (hCnonneg : ∀ i j, 0 ≤ C i j)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hintertwines : P * C = C * Q)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G)
    (H : Matrix κ κ ℝ) (hH : IsGroupInverse (1 - Q) H)
    (b : Matrix κ η ℝ) :
    G * (C * b) = C * (H * b) := by
  exact IntertwinerAlgebra.poisson_green_intertwines G H C b
    (groupInverse_intertwines_of_stochastic_compatible
      P Q C π μ hP hQ hPpos hQpos hπnonneg hπsum hμnonneg hμsum hπstat hμstat
      hCnonneg hCrows hintertwines G hG H hH)

/-- **REGULARIZED OPERATOR INTERTWINING (Kemeny-type).**

Under the same hypotheses, the regularized operators intertwine:

`(G + stationaryMeanMatrix π) * C = C * (H + stationaryMeanMatrix μ)`.

`MarkovAttentionKemenySnell.stationaryMean_shift_mul_inverse` proves that each
regularized operator has a right inverse, and its companion theorem proves the
reverse product is also the identity. The result here is the intertwining of
the regularized operators themselves; no intertwining theorem for their
inverses, and no mean first passage time interpretation, is asserted. -/
theorem regularizedShift_intertwines_of_stationary_compatible
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hQ : Q ∈ Matrix.rowStochastic ℝ κ)
    (hPpos : ∀ i j, 0 < P i j) (hQpos : ∀ i j, 0 < Q i j)
    (hπnonneg : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hμnonneg : ∀ j, 0 ≤ μ j) (hμsum : ∑ j, μ j = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hμstat : ∀ j, ∑ j', μ j' * Q j' j = μ j)
    (hCnonneg : ∀ i j, 0 ≤ C i j)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hintertwines : P * C = C * Q)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G)
    (H : Matrix κ κ ℝ) (hH : IsGroupInverse (1 - Q) H) :
    (G + stationaryMeanMatrix π) * C = C * (H + stationaryMeanMatrix μ) := by
  have hCmean : ∀ j, ∑ i, π i * C i j = μ j :=
    stationaryMean_transport_of_stochastic_intertwiner
      P Q C π μ hQ hQpos hπnonneg hπsum hπstat hμnonneg hμsum hμstat
      hCnonneg hCrows hintertwines
  have hsharp := groupInverse_intertwines_of_stochastic_compatible
    P Q C π μ hP hQ hPpos hQpos hπnonneg hπsum hμnonneg hμsum hπstat hμstat
    hCnonneg hCrows hintertwines G hG H hH
  exact IntertwinerAlgebra.regularized_groupInverse_intertwines
    G (stationaryMeanMatrix π) H (stationaryMeanMatrix μ) C hsharp
    (stationaryMeanMatrix_intertwines π μ C hCrows hCmean)

/-- **THE LIFTED SOLUTION HAS ZERO STATIONARY MEAN.**

Under the same hypotheses, the lifted coarse-space group-inverse solution
`C *ᵥ (H *ᵥ x)` has zero stationary weighted mean for `π`. By
`range_laplacian_eq_weightedMean_ker` it therefore lies in the range of
`1 - P`, which is the solvability condition for the fine-space Poisson
equation. Matrices act on column observables by `mulVec`. -/
theorem liftedSolution_mean_zero_of_stationary_compatible
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hQ : Q ∈ Matrix.rowStochastic ℝ κ)
    (hPpos : ∀ i j, 0 < P i j) (hQpos : ∀ i j, 0 < Q i j)
    (hπnonneg : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hμnonneg : ∀ j, 0 ≤ μ j) (hμsum : ∑ j, μ j = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hμstat : ∀ j, ∑ j', μ j' * Q j' j = μ j)
    (hCnonneg : ∀ i j, 0 ≤ C i j)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hintertwines : P * C = C * Q)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G)
    (H : Matrix κ κ ℝ) (hH : IsGroupInverse (1 - Q) H)
    (x : κ → ℝ) :
    weightedMeanMap π (C *ᵥ (H *ᵥ x)) = 0 := by
  have hsharp := groupInverse_intertwines_of_stochastic_compatible
    P Q C π μ hP hQ hPpos hQpos hπnonneg hπsum hμnonneg hμsum hπstat hμstat
    hCnonneg hCrows hintertwines G hG H hH
  have hLift : C *ᵥ (H *ᵥ x) = G *ᵥ (C *ᵥ x) :=
    calc C *ᵥ (H *ᵥ x) = (C * H) *ᵥ x := Matrix.mulVec_mulVec _ _ _
      _ = (G * C) *ᵥ x := by rw [hsharp]
      _ = G *ᵥ (C *ᵥ x) := (Matrix.mulVec_mulVec _ _ _).symm
  have hmem : Matrix.toLin' G (C *ᵥ x) ∈ (Matrix.toLin' (1 - P)).range :=
    groupInverse_apply_mem_range _ _ (isGroupInverse_toLin' hG) (C *ᵥ x)
  have hzero : weightedMeanMap π (Matrix.toLin' G (C *ᵥ x)) = 0 := by
    have hker : Matrix.toLin' G (C *ᵥ x) ∈ LinearMap.ker (weightedMeanMap π) := by
      rw [← range_laplacian_eq_weightedMean_ker P π hP hPpos hπsum hπstat]
      exact hmem
    rw [LinearMap.mem_ker] at hker
    exact hker
  calc weightedMeanMap π (C *ᵥ (H *ᵥ x))
      = weightedMeanMap π (G *ᵥ (C *ᵥ x)) := by rw [hLift]
    _ = weightedMeanMap π (Matrix.toLin' G (C *ᵥ x)) := by
      rw [show (G : Matrix ι ι ℝ) *ᵥ (C *ᵥ x) = Matrix.toLin' G (C *ᵥ x) from rfl]
    _ = 0 := hzero

end InfoGeometry.QuantumContext.MarkovDrazin

end
