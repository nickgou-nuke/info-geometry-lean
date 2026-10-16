/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovGroupInverseIntertwinerFunctoriality
import InfoGeometry.QuantumContext.MarkovGroupInverseIntertwining
import InfoGeometry.QuantumContext.MarkovGroupInverseStationaryReadout

/-!
# Selected cross-owner consequences for rectangular Markov intertwiners

The repository already has owners for the group inverse, stationary projector,
weighted range, Poisson solution and Kemeny--Snell inverse. This module does
not replace those owners or claim that their underlying results were absent.
It packages a small number of cross-owner consequences that are not stated by
those owners:

| lane | owner |
| --- | --- |
| A: canonical group inverse laws | `InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse` |
| B: rectangular intertwining algebra | `IntertwinerAlgebra.groupInverse_intertwines_of_laws` |
| C: stochastic group-inverse transport | `MarkovDrazin.groupInverse_intertwines_of_stochastic_compatible` |
| D: Poisson solvability and uniqueness | `MarkovAttentionGroupInverse` |
| E: Kemeny--Snell regularized shift | `MarkovAttentionKemenySnell.stationaryMean_shift_mul_inverse` |
| F: weighted range versus zero mean | `MarkovAttentionWeightedRange.range_laplacian_eq_weightedMean_ker` |

The results below connect selected interfaces: a conditional equivalence
between regular-idempotent and stationary-projector intertwining, observable
Laplacian transport, range-aware Poisson transport, and a composite identity
using the regularized-operator transport and Kemeny--Snell inverse owners.

## Scope

All statements are finite algebraic identities over `ℝ`. In particular,
`covariantPoisson_coarse_solution` needs `b` in the range of `1 - Q`. For a
group inverse `G` of `L = 1 - Q`, the general identity is
`L *ᵥ (G *ᵥ x) = (L * G) *ᵥ x`; `L * G` is the regular idempotent and is not
the identity on every vector. Nothing here asserts convergence of stochastic
iterates, a mean first passage time interpretation, or an identification with
lumping, Stiefel compression, RG coarse-graining or attention pooling.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

omit [Nonempty ι] [Nonempty κ] in
/-- **BRIDGE B--C (conditional equivalence).** Given the displayed
regular-idempotent readouts, intertwining those idempotents is equivalent to
intertwining the stationary projectors:

`(1 - P) * G * C = C * (1 - Q) * H`
if and only if
`stationaryMeanMatrix π * C = C * stationaryMeanMatrix μ`.

This equivalence is conditional on `hGproj` and `hHproj`; those readouts are
provided in the stochastic Markov setting by
`markovStationaryProjector_eq_stationaryMeanMatrix`. -/
theorem groupInverse_rangeIntertwining_iff_stationaryProjector
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ)
    (G : Matrix ι ι ℝ) (H : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hGproj : (1 - P) * G = 1 - stationaryMeanMatrix π)
    (hHproj : (1 - Q) * H = 1 - stationaryMeanMatrix μ) :
    (1 - P) * G * C = C * (1 - Q) * H
      ↔ stationaryMeanMatrix π * C = C * stationaryMeanMatrix μ := by
  have key : (1 - stationaryMeanMatrix π) * C = C * (1 - stationaryMeanMatrix μ)
      ↔ stationaryMeanMatrix π * C = C * stationaryMeanMatrix μ := by
    constructor
    · intro h
      calc stationaryMeanMatrix π * C = C - (1 - stationaryMeanMatrix π) * C := by
            rw [Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel]
        _ = C - C * (1 - stationaryMeanMatrix μ) := by rw [h]
        _ = C * stationaryMeanMatrix μ := by
            rw [Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]
    · intro h
      calc (1 - stationaryMeanMatrix π) * C = C - stationaryMeanMatrix π * C := by
            rw [Matrix.sub_mul, Matrix.one_mul]
        _ = C - C * stationaryMeanMatrix μ := by
            exact congrArg (fun M : Matrix ι κ ℝ => C - M) h
        _ = C * (1 - stationaryMeanMatrix μ) := by
            rw [Matrix.mul_sub, Matrix.mul_one]
  constructor
  · intro hr
    apply key.mp
    calc (1 - stationaryMeanMatrix π) * C = ((1 - P) * G) * C := by rw [hGproj]
      _ = (1 - P) * G * C := by rw [Matrix.mul_assoc]
      _ = C * (1 - Q) * H := hr
      _ = C * ((1 - Q) * H) := by rw [Matrix.mul_assoc]
      _ = C * (1 - stationaryMeanMatrix μ) := by rw [hHproj]
  · intro hs
    have hs' : (1 - stationaryMeanMatrix π) * C = C * (1 - stationaryMeanMatrix μ) :=
      key.mpr hs
    calc (1 - P) * G * C = ((1 - P) * G) * C := by rw [Matrix.mul_assoc]
      _ = (1 - stationaryMeanMatrix π) * C := by rw [hGproj]
      _ = C * (1 - stationaryMeanMatrix μ) := hs'
      _ = C * ((1 - Q) * H) := by rw [← hHproj]
      _ = C * (1 - Q) * H := by rw [Matrix.mul_assoc]

/-- **BRIDGE A--E--C.** The regular idempotent of the Markov Laplacian `1 - P`
is `1 - stationaryMeanMatrix π`.

This is *not* an independent proof: it is the matrix-level orientation of the
canonical owner `InfoGeometry.QuantumContext.markovStationaryProjector_eq_stationaryMeanMatrix`
in `MarkovGroupInverseStationaryReadout`, which reads the same fact on the
`markovStationaryProjector = 1 - markovRangeIdempotent` carrier. Re-proving it
here would have been a duplicate carrier, so this corollary only unfolds the
definitions and cancels. The upstream owner consumes the reflexive law and the
commutativity law of the group inverse, but not its absorption law. -/
theorem groupInverse_regularIdempotent_eq_one_sub_stationaryMeanMatrix
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    (1 - P) * G = 1 - stationaryMeanMatrix π := by
  have hsp : 1 - ((1 - P) * G) = stationaryMeanMatrix π := by
    simpa [markovStationaryProjector, markovRangeIdempotent] using
      (InfoGeometry.QuantumContext.markovStationaryProjector_eq_stationaryMeanMatrix
        P π hP hPpos hπsum hπstat G hG)
  calc (1 - P) * G = 1 - (1 - ((1 - P) * G)) := by rw [sub_sub_cancel]
    _ = 1 - stationaryMeanMatrix π := by rw [hsp]

/-- **BRIDGE B--C (regular projectors).** Under normalized stationary rows,
row-sum preservation, and stationary-mean compatibility, the regular
idempotents of the two Markov Laplacians intertwine.

This exposes the projector-level bridge used by the group-inverse transport
theorem. It does not restate that transport theorem or claim that either group
inverse is constructed here. The hypotheses on `C` do not include
nonnegativity, so `C` is called a row-sum-preserving map rather than a
stochastic kernel. -/
theorem regularIdempotents_intertwine_of_stationary_compatible
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hQ : Q ∈ Matrix.rowStochastic ℝ κ)
    (hPpos : ∀ i j, 0 < P i j) (hQpos : ∀ i j, 0 < Q i j)
    (hπsum : ∑ i, π i = 1) (hμsum : ∑ j, μ j = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hμstat : ∀ j, ∑ i, μ i * Q i j = μ j)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hCmean : ∀ j, ∑ i, π i * C i j = μ j)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G)
    (H : Matrix κ κ ℝ) (hH : IsGroupInverse (1 - Q) H) :
    (1 - P) * G * C = C * ((1 - Q) * H) := by
  have hGproj := groupInverse_regularIdempotent_eq_one_sub_stationaryMeanMatrix
    P π hP hPpos hπsum hπstat G hG
  have hHproj := groupInverse_regularIdempotent_eq_one_sub_stationaryMeanMatrix
    Q μ hQ hQpos hμsum hμstat H hH
  simpa [Matrix.mul_assoc] using
    (groupInverse_rangeIntertwining_iff_stationaryProjector
      P Q G H C π μ hGproj hHproj).2
      (stationaryMeanMatrix_intertwines π μ C hCrows hCmean)

/-- **BRIDGE C--D.** If `b` lies in the range of the coarse Markov Laplacian
`1 - Q`, then the group inverse *recovers* `b` on the left:
`(1 - Q) *ᵥ (H *ᵥ b) = b`.

Only the left identity is claimed. It is not asserted here that `H *ᵥ b` is the
*unique* solution of `(1 - Q) *ᵥ x = b`, nor that `H` also inverts `1 - Q` on
the left; both would need a further hypothesis. Uniqueness over the full space is
impossible anyway, since `H` is the inverse only modulo the kernel of `1 - Q`.

The range hypothesis is not optional. In general the group-inverse law gives
`(1 - Q) *ᵥ (H *ᵥ b) = ((1 - Q) * H) *ᵥ b`; this equals `b` for `b` in the
range of `1 - Q`. -/
theorem covariantPoisson_coarse_solution
    (Q : Matrix κ κ ℝ) (H : Matrix κ κ ℝ) (b : κ → ℝ)
    (hH : IsGroupInverse (1 - Q) H)
    (hb : b ∈ LinearMap.range (Matrix.toLin' (1 - Q))) :
    (1 - Q) *ᵥ (H *ᵥ b) = b := by
  have happly := apply_groupInverse_eq_of_mem_range
    (Matrix.toLin' (1 - Q)) (Matrix.toLin' H) (isGroupInverse_toLin' hH) b hb
  calc (1 - Q) *ᵥ (H *ᵥ b) = ((1 - Q) * H) *ᵥ b := Matrix.mulVec_mulVec _ _ _
    _ = Matrix.toLin' ((1 - Q) * H) b := rfl
    _ = Matrix.toLin' (1 - Q) (Matrix.toLin' H b) := by
      rw [Matrix.toLin'_mul]
      rfl
    _ = b := happly

omit [Nonempty ι] [Nonempty κ] in
/-- **BRIDGE C--D (arbitrary right-hand side).** The Markov Laplacian intertwines
the rectangular intertwiner on *every* column observable, with no range
hypothesis:

`(1 - P) *ᵥ (C *ᵥ y) = C *ᵥ ((1 - Q) *ᵥ y)`.

This is the observable-action form of the Laplacian conversion
`(1 - P) * C = C * (1 - Q)`. It is proved here directly by its own `calc`; this
module does **not** import or call
`GroupInverseIntertwinerLadder.stationary_laplacians_intertwine`, which proves
the matrix-level statement independently in that module.
`covariantPoisson_fine_solution` specializes this to `y = H *ᵥ b`. It consumes
only the transition intertwining, so it holds for any rectangular intertwiner. -/
theorem covariantLaplacian_intertwines_on_observables
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (hintertwines : P * C = C * Q)
    (y : κ → ℝ) :
    (1 - P) *ᵥ (C *ᵥ y) = C *ᵥ ((1 - Q) *ᵥ y) := by
  have hLC : (1 - P) * C = C * (1 - Q) := by
    calc (1 - P) * C = C - P * C := by simp only [Matrix.sub_mul, Matrix.one_mul]
      _ = C - C * Q := by rw [hintertwines]
      _ = C * (1 - Q) := by rw [Matrix.mul_sub, Matrix.mul_one]
  calc (1 - P) *ᵥ (C *ᵥ y) = ((1 - P) * C) *ᵥ y := Matrix.mulVec_mulVec _ _ _
    _ = (C * (1 - Q)) *ᵥ y := by rw [hLC]
    _ = C *ᵥ ((1 - Q) *ᵥ y) := (Matrix.mulVec_mulVec _ _ _).symm

omit [Nonempty ι] [Nonempty κ] in
/-- **BRIDGE C--D--F.** The lift of the coarse solution solves the transported
fine-space Poisson equation: `(1 - P) *ᵥ (C *ᵥ (H *ᵥ b)) = C *ᵥ b`.

This is the covariant Poisson transport law. It consumes the kernel
intertwining of the transition operators and the coarse solvability hypothesis
of `covariantPoisson_coarse_solution`; it does not consume any stochasticity,
positivity or normalization assumption beyond what those carry. -/
theorem covariantPoisson_fine_solution
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (H : Matrix κ κ ℝ) (b : κ → ℝ)
    (hintertwines : P * C = C * Q)
    (hcoarse : (1 - Q) *ᵥ (H *ᵥ b) = b) :
    (1 - P) *ᵥ (C *ᵥ (H *ᵥ b)) = C *ᵥ b :=
  (covariantLaplacian_intertwines_on_observables P Q C hintertwines (H *ᵥ b)).trans
    (by rw [hcoarse])

/-- **BRIDGE F.** The lifted solution lies in the range of the fine Markov
Laplacian `1 - P`, hence it satisfies the solvable-range condition of the
fine-space Poisson equation.

This is `liftedSolution_mean_zero_of_stationary_compatible` transported through
the owner identity `range (1 - P) = ker (weightedMeanMap π)`. -/
theorem covariantPoisson_fine_solution_in_range
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
    (b : κ → ℝ) :
    C *ᵥ (H *ᵥ b) ∈ LinearMap.range (Matrix.toLin' (1 - P)) := by
  have hzero := liftedSolution_mean_zero_of_stationary_compatible
    P Q C π μ hP hQ hPpos hQpos hπnonneg hπsum hμnonneg hμsum hπstat hμstat
    hCnonneg hCrows hintertwines G hG H hH b
  have hker : C *ᵥ (H *ᵥ b) ∈ LinearMap.ker (weightedMeanMap π) :=
    LinearMap.mem_ker.mpr hzero
  rw [range_laplacian_eq_weightedMean_ker P π hP hPpos hπsum hπstat]
  exact hker

/-- **BRIDGE C--D.** Uniqueness of the transported Poisson solution on the fine
solvable range: if `y` lies in `range (1 - P)` and solves the transported
equation `(1 - P) *ᵥ y = C *ᵥ b`, then `y` is the group-inverse image of the
transport `C *ᵥ b`.

This joins the rectangular intertwining lane to the range-constrained
uniqueness theorem `groupInverse_solution_unique_on_range`. Note that the
stronger-looking claim `G *ᵥ y = y` is **false** in general: for
`Q = Matrix.swap`, `L = 1 - Q`, `G = L / 4` and `b = (1, -1)` one has
`b ∈ im L` but `G *ᵥ b = b / 2`. The group inverse `G` is not itself a
projector; the associated idempotent is `L * G = G * L`. -/
theorem solvable_range_solution_eq_groupInverse_image
    (P : Matrix ι ι ℝ) (G : Matrix ι ι ℝ) (t : ι → ℝ) (y : ι → ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (ht_range : t ∈ LinearMap.range (Matrix.toLin' (1 - P)))
    (hy_range : y ∈ LinearMap.range (Matrix.toLin' (1 - P)))
    (hy_solve : (1 - P) *ᵥ y = t) :
    y = G *ᵥ t := by
  have hGend := isGroupInverse_toLin' hG
  have happly := apply_groupInverse_eq_of_mem_range
    (Matrix.toLin' (1 - P)) (Matrix.toLin' G) hGend t ht_range
  have hGrange : G *ᵥ t ∈ LinearMap.range (Matrix.toLin' (1 - P)) :=
    groupInverse_apply_mem_range _ _ hGend t
  have hGsolve : Matrix.toLin' (1 - P) (Matrix.toLin' G t)
      = Matrix.toLin' (1 - P) y := by
    calc Matrix.toLin' (1 - P) (Matrix.toLin' G t) = t := by
          simpa only [Matrix.toLin'_apply] using happly
      _ = Matrix.toLin' (1 - P) y := by
          symm
          simpa only [Matrix.toLin'_apply] using hy_solve
  have hEq := groupInverse_solution_unique_on_range _ _ hGend
    (Matrix.toLin' G t) y hGrange hy_range hGsolve
  change y = Matrix.toLin' G t
  exact hEq.symm

/-- **BRIDGE B--C--E.** The fine regularized shift inverts the transported coarse
regularized Laplacian:

`(G + stationaryMeanMatrix π) * (C * ((1 - Q) + stationaryMeanMatrix μ)) = C`.

This joins the rectangular intertwining law of the regularized operators to the
two-sided inverse identities of `MarkovAttentionKemenySnell`. The left inverse
identity is consumed; the right inverse identity is available in
`MarkovAttentionKemenySnell.stationaryMean_inverse_mul_shift` and is not needed
here. -/
theorem regularizedShift_inverts_transported_regularizedLaplacian
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hQ : Q ∈ Matrix.rowStochastic ℝ κ)
    (hPpos : ∀ i j, 0 < P i j) (hQpos : ∀ i j, 0 < Q i j)
    (hπnonneg : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hμnonneg : ∀ j, 0 ≤ μ j) (hμsum : ∑ j, μ j = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hμstat : ∀ j, ∑ i, μ i * Q i j = μ j)
    (hCnonneg : ∀ i j, 0 ≤ C i j)
    (hCrows : ∀ i, ∑ j, C i j = 1)
    (hintertwines : P * C = C * Q)
    (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G)
    (H : Matrix κ κ ℝ) (hH : IsGroupInverse (1 - Q) H) :
    (G + stationaryMeanMatrix π) * (C * ((1 - Q) + stationaryMeanMatrix μ)) = C := by
  have hshift := stationaryMean_shift_mul_inverse
    Q μ hQ hQpos hμsum hμstat H hH
  have hreg := regularizedShift_intertwines_of_stationary_compatible
    P Q C π μ hP hQ hPpos hQpos hπnonneg hπsum hμnonneg hμsum hπstat hμstat
    hCnonneg hCrows hintertwines G hG H hH
  calc (G + stationaryMeanMatrix π) * (C * ((1 - Q) + stationaryMeanMatrix μ))
      = ((G + stationaryMeanMatrix π) * C) * ((1 - Q) + stationaryMeanMatrix μ) := by
        rw [Matrix.mul_assoc]
    _ = (C * (H + stationaryMeanMatrix μ)) * ((1 - Q) + stationaryMeanMatrix μ) := by
        rw [hreg]
    _ = C * ((H + stationaryMeanMatrix μ) * ((1 - Q) + stationaryMeanMatrix μ)) := by
        rw [Matrix.mul_assoc]
    _ = C := by rw [hshift, Matrix.mul_one]

end InfoGeometry.QuantumContext.MarkovDrazin

end
