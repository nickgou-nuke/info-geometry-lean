/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.KMSSinkhornSeedState
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Peirce.PeirceLadderOperators
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Source-specific gap regressions

DIAGNOSTIC CANDIDATE. Its focused file elaboration has passed; owner-closure axiom
and package-publication gates remain incomplete. Prepared by source inspection against
`nickgou-nuke/info-geometry-lean` at
`fe24e350b08fdea04f74c0748ef9fd9417c47529`.
The intended environment is Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

This file imports the existing owners. It does not replace their carriers or
definitions. The first regression distinguishes the owner's phase-aligned
residual inequality from descent of one fixed column residual. It does not
refute the existing phase-aligned theorem or Sinkhorn convergence.

The second regression proves that the legacy scalar `NilpotentLadder` type
is empty. It does not apply to the separate Clifford/operator ladder owners.
The third regression tests the all-bounded-operators quantifier in the KMS
seed's commutator-orthogonality premise. It uses rank-one operators on the
existing real doubled Hilbert space and its real `clockAxis`.
These regressions establish no physical interpretation.
-/

noncomputable section

namespace InfoGeometry.GapRegression

open InfoGeometry.Canonical.MoE

/-! ## A row-normalization step can increase the column residual. -/

/-- A strictly positive matrix with both column sums equal to one. -/
def columnBalancedExample : SinkhornMatrix 2 :=
  !![(3 / 4 : ℝ), 1 / 2; 1 / 4, 1 / 2]

theorem columnBalancedExample_entry_pos (i j : Fin 2) :
    0 < columnBalancedExample i j := by
  fin_cases i <;> fin_cases j <;> norm_num [columnBalancedExample]

/-- The two positive row masses are `5/4` and `3/4`. -/
theorem columnBalancedExample_hasPositiveRowSums :
    HasPositiveRowSums 2 columnBalancedExample := by
  intro i
  fin_cases i <;>
    norm_num [rowSum, columnBalancedExample, Fin.sum_univ_two]

theorem columnBalancedExample_colSum (j : Fin 2) :
    colSum 2 columnBalancedExample j = 1 := by
  fin_cases j <;>
    norm_num [colSum, columnBalancedExample, Fin.sum_univ_two]

theorem columnBalancedExample_colLyapunov :
    colLyapunov 2 columnBalancedExample = 0 := by
  norm_num [colLyapunov, colSum, columnBalancedExample, Fin.sum_univ_two]

/-- The owner-defined row step produces rows `(3/5, 2/5)` and `(1/3, 2/3)`. -/
theorem columnBalancedExample_rowNormalize :
    rowNormalize 2 columnBalancedExample
        columnBalancedExample_hasPositiveRowSums =
      !![(3 / 5 : ℝ), 2 / 5; 1 / 3, 2 / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rowNormalize, rowSum, columnBalancedExample, Fin.sum_univ_two]

theorem columnBalancedExample_normalized_colSums :
    colSum 2
        (rowNormalize 2 columnBalancedExample
          columnBalancedExample_hasPositiveRowSums) 0 = 14 / 15 ∧
      colSum 2
        (rowNormalize 2 columnBalancedExample
          columnBalancedExample_hasPositiveRowSums) 1 = 16 / 15 := by
  rw [columnBalancedExample_rowNormalize]
  constructor <;> norm_num [colSum, Fin.sum_univ_two]

/-- The same column residual changes from zero to `2/15`. -/
theorem columnBalancedExample_normalized_colLyapunov :
    colLyapunov 2
        (rowNormalize 2 columnBalancedExample
          columnBalancedExample_hasPositiveRowSums) = 2 / 15 := by
  rw [columnBalancedExample_rowNormalize]
  norm_num [colLyapunov, colSum, Fin.sum_univ_two]

theorem columnBalancedExample_colLyapunov_increases :
    colLyapunov 2 columnBalancedExample <
      colLyapunov 2
        (rowNormalize 2 columnBalancedExample
          columnBalancedExample_hasPositiveRowSums) := by
  rw [columnBalancedExample_colLyapunov,
    columnBalancedExample_normalized_colLyapunov]
  norm_num

/-- Positivity of row sums alone does not make the fixed column residual descend. -/
theorem not_fixedColumnResidual_descent :
    ¬ (∀ (M : SinkhornMatrix 2) (hrow : HasPositiveRowSums 2 M),
      colLyapunov 2 (rowNormalize 2 M hrow) ≤ colLyapunov 2 M) := by
  intro h
  have hbound := h columnBalancedExample columnBalancedExample_hasPositiveRowSums
  rw [columnBalancedExample_normalized_colLyapunov,
    columnBalancedExample_colLyapunov] at hbound
  norm_num at hbound

/-- The existing phase-aligned theorem remains valid: its two sides are zero. -/
theorem columnBalancedExample_phase_residuals :
    phaseLyapunovBefore 2 SinkhornPhase.row columnBalancedExample = 0 ∧
      phaseLyapunovAfter 2 SinkhornPhase.row
        (rowNormalize 2 columnBalancedExample
          columnBalancedExample_hasPositiveRowSums) = 0 := by
  constructor
  · exact columnBalancedExample_colLyapunov
  · exact rowLyapunov_rowNormalize_eq_zero (n := 2)
      columnBalancedExample columnBalancedExample_hasPositiveRowSums

/-! ## The legacy scalar ladder carrier has no witness. -/

/-- In the legacy real-scalar carrier, `u² = 0` already forces `u = 0`,
which contradicts the required anticommutator. The `d² = 0` field is not needed. -/
theorem scalarNilpotentLadder_false
    (L : _root_.PeirceLadder.NilpotentLadder) : False := by
  have hu : L.u = 0 := (mul_eq_zero.mp L.u_nilpotent).elim id id
  have hzero : (0 : ℝ) = 1 := by
    simpa [hu] using L.anticommutator
  exact zero_ne_one hzero

/-- This names emptiness explicitly instead of proving downstream claims
conditionally from an impossible scalar ladder. It is not registered as an instance. -/
theorem scalarNilpotentLadder_isEmpty :
    IsEmpty _root_.PeirceLadder.NilpotentLadder :=
  ⟨scalarNilpotentLadder_false⟩

/-! ## A nonzero vector state cannot annihilate all operator commutators. -/

section RankOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- For two nonzero orthogonal real Hilbert vectors, the two ordered
rank-one products have a strictly positive commutator expectation at `u`.
There is no finite-dimensional or completeness hypothesis. -/
theorem rankOne_commutator_expectation_pos (u v : H)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : inner ℝ u v = 0) :
    0 < inner ℝ
      (((InnerProductSpace.rankOne ℝ u v * InnerProductSpace.rankOne ℝ v u -
          InnerProductSpace.rankOne ℝ v u * InnerProductSpace.rankOne ℝ u v) u)) u := by
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  have hcalc :
      inner ℝ
        (((InnerProductSpace.rankOne ℝ u v * InnerProductSpace.rankOne ℝ v u -
            InnerProductSpace.rankOne ℝ v u * InnerProductSpace.rankOne ℝ u v) u)) u =
        (inner ℝ u u * inner ℝ v v) * inner ℝ u u := by
    simp only [sub_apply, mul_apply_eq_comp,
      InnerProductSpace.rankOne_apply, inner_smul_right, real_inner_smul_left,
      hvu, inner_zero_right, zero_smul, sub_zero]
  rw [hcalc]
  exact mul_pos (mul_pos (real_inner_self_pos.mpr hu) (real_inner_self_pos.mpr hv))
    (real_inner_self_pos.mpr hu)

end RankOne

section KMSSeed

open InfoGeometry.Krein
open InfoGeometry.Canonical.KMSSinkhornBridge

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The owner predicate quantifies over the full real bounded operator algebra.
Its only vector witness is zero. This is not a statement about commutators
restricted to an observable subalgebra or the full analytic KMS condition. -/
theorem kms_commutatorOrthogonal_iff_zero (Ω : DoubledSpace F) :
    CommutatorOrthogonalOnOmega (F := F) Ω ↔ Ω = 0 := by
  constructor
  · intro h
    by_contra hΩ
    have hphase : clockAxis (E := F) Ω ≠ 0 := by
      intro hzero
      have hnorm := clockAxis_norm (E := F) Ω
      rw [hzero, norm_zero] at hnorm
      exact hΩ (norm_eq_zero.mp hnorm.symm)
    have horth : inner ℝ Ω (clockAxis (E := F) Ω) = 0 := by
      have hskew :=
        InfoGeometry.Canonical.TomitaTakesaki.clockAxis_inner_skew (E := F) Ω Ω
      change inner ℝ (clockAxis (E := F) Ω) Ω = -inner ℝ Ω (clockAxis (E := F) Ω) at hskew
      rw [real_inner_comm Ω (clockAxis (E := F) Ω)] at hskew
      linarith
    have hpos := rankOne_commutator_expectation_pos
      Ω (clockAxis (E := F) Ω) hΩ hphase horth
    have hzero := h
      (InnerProductSpace.rankOne ℝ Ω (clockAxis (E := F) Ω))
      (InnerProductSpace.rankOne ℝ (clockAxis (E := F) Ω) Ω)
    exact (ne_of_gt hpos) hzero
  · intro hΩ
    subst Ω
    intro A B
    simp

/-- Nonzero `Ω` and the owner's all-operator commutator condition are
incompatible, independently of the supplied joint-kernel condition. -/
theorem kmsStructuralWitness_isEmpty (K : AlgebraEnd F) (β : ℝ) :
    IsEmpty (ExpectationSeedStructuralWitness (F := F) K β) :=
  ⟨fun W => W.hΩ ((kms_commutatorOrthogonal_iff_zero W.Ω).mp W.commutatorOrthogonal)⟩

end KMSSeed

end InfoGeometry.GapRegression
