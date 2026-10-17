/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovGroupInverseIntertwinerFunctoriality
import InfoGeometry.QuantumContext.MarkovGroupInverseIntertwining
import InfoGeometry.QuantumContext.MarkovGroupInverseStationaryReadout
import InfoGeometry.QuantumContext.GroupInverseIntertwinerLadder
import InfoGeometry.QuantumContext.MarkovPartitionLumping

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
| C: stochastic group-inverse transport | `MarkovDrazin.groupInverse_intertwines_of_stationary_compatible` |
| D: Poisson solvability, uniqueness, and the range carrier | `MarkovAttentionGroupInverse.groupInverse_apply_mem_range`, and `MarkovDrazin.range_groupInverse_eq` in `MarkovGroupInverseIntertwinerFunctoriality` |
| E: Kemeny--Snell regularized shift | `MarkovAttentionKemenySnell.stationaryMean_shift_mul_inverse` |
| L: partition lumping | `MarkovPartitionLumping.partitionIncidence`, `…_of_partitionLumping` |

The results below connect selected interfaces: a conditional equivalence
between regular-idempotent and stationary-projector intertwining, the range
carrier for a group inverse, observable Laplacian transport, range-aware Poisson
transport, the composite regularized identity using the Kemeny--Snell inverse
owner, and the bridge between the lumping carrier and the abstract algebra.

Each theorem's docstring names the lanes it actually consumes. Earlier revisions
of this module carried `BRIDGE X--Y` labels that overstated the dependencies —
several theorems were labelled as consuming lane C when they consumed only lane
D — and those labels have been corrected against the proof terms.

## Scope

All statements are finite algebraic identities over `ℝ`. In particular,
`covariantPoisson_coarse_solution` needs `b` in the range of `1 - Q`. For a
group inverse `G` of `L = 1 - Q`, the general identity is
`L *ᵥ (G *ᵥ x) = (L * G) *ᵥ x`; `L * G` is the regular idempotent and is not
the identity on every vector. Nothing here asserts convergence of stochastic
iterates, a mean first passage time interpretation, or an identification with
Stiefel compression, RG coarse-graining or attention pooling. The one
identification that *is* stated is the lumping one of
`partitionIncidence_intertwines_regularIdempotents`, and it is stated about the
regular idempotents rather than about any physical coarse-graining operator.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.QuantumContext.MarkovPartitionLumping
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

/-- **BRIDGE A--E.** The regular idempotent of the Markov Laplacian `1 - P`
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

/-- **BRIDGE D (range solvability).** If `b` lies in the range of the coarse Markov Laplacian
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
/-- **BRIDGE B (observable Laplacian conversion).** The Markov Laplacian intertwines
the rectangular intertwiner on *every* column observable, with no range
hypothesis:

`(1 - P) *ᵥ (C *ᵥ y) = C *ᵥ ((1 - Q) *ᵥ y)`.

This is the observable-action form of the Laplacian conversion
`(1 - P) * C = C * (1 - Q)`. It calls
`GroupInverseIntertwinerLadder.stationary_laplacians_intertwine`, which this
module imports for that purpose; the conversion itself is no longer re-proved
inline.
`covariantPoisson_fine_solution` specializes this to `y = H *ᵥ b`. It consumes
only the transition intertwining, so it holds for any rectangular intertwiner. -/
theorem covariantLaplacian_intertwines_on_observables
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (hintertwines : P * C = C * Q)
    (y : κ → ℝ) :
    (1 - P) *ᵥ (C *ᵥ y) = C *ᵥ ((1 - Q) *ᵥ y) := by
  have hLC : (1 - P) * C = C * (1 - Q) :=
    GroupInverseIntertwinerLadder.stationary_laplacians_intertwine P Q C hintertwines
  calc (1 - P) *ᵥ (C *ᵥ y) = ((1 - P) * C) *ᵥ y := Matrix.mulVec_mulVec _ _ _
    _ = (C * (1 - Q)) *ᵥ y := by rw [hLC]
    _ = C *ᵥ ((1 - Q) *ᵥ y) := (Matrix.mulVec_mulVec _ _ _).symm

omit [Nonempty ι] [Nonempty κ] in
/-- **BRIDGE B--D.** The lift of the coarse solution solves the transported
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

/-- **BRIDGE D (range carrier).** The lifted solution lies in the range of the fine Markov
Laplacian `1 - P`, hence it satisfies the solvable-range condition of the
fine-space Poisson equation.

This is now proved from the existing owner
`MarkovAttentionGroupInverse.groupInverse_apply_mem_range`, lifted through
`isGroupInverse_toLin'`, rather than through
`liftedSolution_mean_zero_of_stationary_compatible`. The old route stated the
same conclusion behind 23 binders (15 propositions and 8 data arguments); this
one states it behind 7. The *conclusion is character-identical* — what changed is
the hypotheses, not the result.

The new form is a genuine generalisation: the old instance derives it via
`stationaryMean_transport_of_stochastic_intertwiner` followed by
`groupInverse_intertwines_of_stationary_compatible`, which is what supplies
`hsharp` here. It was not a binder-for-binder weakening.

Two facts suffice: the intertwining `G * C = C * H` rewrites the transported
solution as `G *ᵥ (C *ᵥ b)`, and the existing owner puts a group-inverse image
into the range of its argument. Note that `Q` does not appear in *this*
statement; in the full instance below it is constrained by `hH`. -/
theorem covariantPoisson_fine_solution_in_range
    (P : Matrix ι ι ℝ) (G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G)
    (C : Matrix ι κ ℝ) (H : Matrix κ κ ℝ) (hsharp : G * C = C * H)
    (b : κ → ℝ) :
    C *ᵥ (H *ᵥ b) ∈ LinearMap.range (Matrix.toLin' (1 - P)) := by
  have hsc : C *ᵥ (H *ᵥ b) = G *ᵥ (C *ᵥ b) := by
    symm
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hsharp]
  rw [hsc]
  exact groupInverse_apply_mem_range _ _ (isGroupInverse_toLin' hG) (C *ᵥ b)

/-- **BRIDGE D (uniqueness on the range).** Uniqueness
of the transported Poisson solution on the fine
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

/-- **BRIDGE C--E (core identity).** If the regularized fine operator intertwines
the regularized coarse one, and the regularized coarse operator inverts the
transported coarse regularized Laplacian, then the fine regularized shift inverts
the transport:

`(G + stationaryMeanMatrix π) * (C * ((1 - Q) + stationaryMeanMatrix μ)) = C`.

This is the whole content of the composite identity, stated with the two
hypotheses it actually consumes. Nothing about stochasticity, positivity or
stationarity enters here; those live in
`regularizedShift_inverts_of_stationary_compatible` below, which supplies them
from the transport owners. -/
theorem regularizedShift_inverts_transported_regularizedLaplacian
    (G : Matrix ι ι ℝ) (π : ι → ℝ) (C : Matrix ι κ ℝ)
    (H : Matrix κ κ ℝ) (Q : Matrix κ κ ℝ) (μ : κ → ℝ)
    (hreg : (G + stationaryMeanMatrix π) * C
      = C * (H + stationaryMeanMatrix μ))
    (hshift : (H + stationaryMeanMatrix μ) * ((1 - Q) + stationaryMeanMatrix μ) = 1) :
    (G + stationaryMeanMatrix π) * (C * ((1 - Q) + stationaryMeanMatrix μ)) = C := by
  calc (G + stationaryMeanMatrix π) * (C * ((1 - Q) + stationaryMeanMatrix μ))
      = ((G + stationaryMeanMatrix π) * C) * ((1 - Q) + stationaryMeanMatrix μ) := by
        rw [Matrix.mul_assoc]
    _ = (C * (H + stationaryMeanMatrix μ)) * ((1 - Q) + stationaryMeanMatrix μ) := by
        rw [hreg]
    _ = C * ((H + stationaryMeanMatrix μ) * ((1 - Q) + stationaryMeanMatrix μ)) := by
        rw [Matrix.mul_assoc]
    _ = C := by rw [hshift, Matrix.mul_one]

/-- **BRIDGE C--E (full instance).** The composite identity of
`regularizedShift_inverts_transported_regularizedLaplacian`, with the transport
and Kemeny--Snell inverse identities supplied from their owners.

The left inverse identity is consumed; the right inverse identity is available in
`MarkovAttentionKemenySnell.stationaryMean_inverse_mul_shift` and is not needed
here. -/
theorem regularizedShift_inverts_of_stationary_compatible
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
    (G + stationaryMeanMatrix π) * (C * ((1 - Q) + stationaryMeanMatrix μ)) = C :=
  regularizedShift_inverts_transported_regularizedLaplacian
    G π C H Q μ
    (regularizedShift_intertwines_of_stationary_compatible
      P Q C π μ hP hQ hPpos hQpos hπnonneg hπsum hμnonneg hμsum hπstat hμstat
      hCnonneg hCrows hintertwines G hG H hH)
    (stationaryMean_shift_mul_inverse Q μ hQ hQpos hμsum hμstat H hH)

/-- **BRIDGE B <-> LUMPING.** The lumping intertwiner satisfies the *abstract*
range-intertwining hypothesis of lane B, not only the stochastic one.

`MarkovPartitionLumping.groupInverse_intertwines_of_partitionLumping` reaches
`Gsharp * partitionIncidence Γ = partitionIncidence Γ * Qsharp` through the
stochastic route, via the transport owners. This theorem shows the regular
idempotents intertwine as well, which is what makes
`IntertwinerAlgebra.groupInverse_intertwines_of_rangeProjector` applicable to
lumping data. Once the transported group inverses intertwine, the rest is the
algebraic core plus the Laplacian conversion.

No stationary measure, no positivity, no row sums and no stochasticity appear
here; the bridge is between the lumping carrier and the abstract algebra, not
between two statements of the same fact. -/
theorem partitionIncidence_intertwines_regularIdempotents
    (Γ : InfoGeometry.Canonical.FiniteCoarseGraining ι κ)
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ)
    (Gsharp : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) Gsharp)
    (Qsharp : Matrix κ κ ℝ) (hQ : IsGroupInverse (1 - Q) Qsharp)
    (hintertwines : P * partitionIncidence Γ = partitionIncidence Γ * Q)
    (hlump : Gsharp * partitionIncidence Γ = partitionIncidence Γ * Qsharp) :
    (1 - P) * Gsharp * partitionIncidence Γ
      = partitionIncidence Γ * ((1 - Q) * Qsharp) := by
  calc (1 - P) * Gsharp * partitionIncidence Γ
      = ((1 - P) * Gsharp) * partitionIncidence Γ := rfl
    _ = (Gsharp * (1 - P)) * partitionIncidence Γ := by rw [hG.2.2]
    _ = Gsharp * ((1 - P) * partitionIncidence Γ) := by rw [Matrix.mul_assoc]
    _ = Gsharp * (partitionIncidence Γ * (1 - Q)) := by
      rw [GroupInverseIntertwinerLadder.stationary_laplacians_intertwine
        P Q (partitionIncidence Γ) hintertwines]
    _ = (Gsharp * partitionIncidence Γ) * (1 - Q) := by rw [Matrix.mul_assoc]
    _ = (partitionIncidence Γ * Qsharp) * (1 - Q) := by rw [hlump]
    _ = partitionIncidence Γ * (Qsharp * (1 - Q)) := by rw [Matrix.mul_assoc]
    _ = partitionIncidence Γ * ((1 - Q) * Qsharp) := by rw [hQ.2.2]

/-- **BRIDGE B <-> LUMPING (route agreement).** The lumping conclusion is exactly
what the abstract core concludes when its range hypothesis is supplied by the
previous theorem. The two routes — stochastic transport and abstract algebra —
are therefore not competing claims about lumping: on this carrier they have the
same conclusion, and the previous lemma is the shared hypothesis. -/
theorem partitionLumping_from_rangeIntertwining
    (Γ : InfoGeometry.Canonical.FiniteCoarseGraining ι κ)
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ)
    (Gsharp : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) Gsharp)
    (Qsharp : Matrix κ κ ℝ) (hQ : IsGroupInverse (1 - Q) Qsharp)
    (hintertwines : P * partitionIncidence Γ = partitionIncidence Γ * Q)
    (hrange : (1 - P) * Gsharp * partitionIncidence Γ
      = partitionIncidence Γ * ((1 - Q) * Qsharp)) :
    Gsharp * partitionIncidence Γ = partitionIncidence Γ * Qsharp :=
  IntertwinerAlgebra.groupInverse_intertwines_of_rangeProjector
    (1 - P) Gsharp (1 - Q) Qsharp (partitionIncidence Γ) hG hQ
    (GroupInverseIntertwinerLadder.stationary_laplacians_intertwine
      P Q (partitionIncidence Γ) hintertwines)
    hrange

/-- **BRIDGE B <-> LUMPING (route agreement, proved).** The stochastic conclusion
and the abstract hypothesis are *equivalent* on the lumping carrier.

The forward direction is the abstract core applied to `hrange`; the reverse is
`partitionIncidence_intertwines_regularIdempotents`. This is the content of the
claim that the two routes are not competing: on this carrier the stochastic
transport statement and the algebraic range-intertwining hypothesis determine
each other, and the preceding lemma is the single shared input. -/
theorem partitionIncidence_groupInverse_iff_regularIdempotentIntertwining
    (Γ : InfoGeometry.Canonical.FiniteCoarseGraining ι κ)
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ)
    (Gsharp : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) Gsharp)
    (Qsharp : Matrix κ κ ℝ) (hQ : IsGroupInverse (1 - Q) Qsharp)
    (hintertwines : P * partitionIncidence Γ = partitionIncidence Γ * Q) :
    (Gsharp * partitionIncidence Γ = partitionIncidence Γ * Qsharp)
      ↔ ((1 - P) * Gsharp * partitionIncidence Γ
        = partitionIncidence Γ * ((1 - Q) * Qsharp)) :=
  ⟨fun hlump => partitionIncidence_intertwines_regularIdempotents
      Γ P Q Gsharp hG Qsharp hQ hintertwines hlump,
    fun hrange => partitionLumping_from_rangeIntertwining
      Γ P Q Gsharp hG Qsharp hQ hintertwines hrange⟩

end InfoGeometry.QuantumContext.MarkovDrazin

end
