/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.QuantumContext.MarkovGroupInverseIntertwinerFunctoriality
import InfoGeometry.QuantumContext.GroupInverseIntertwinerAlgebra

/-!
# Composition lemmas for the rectangular group-inverse intertwining

This module records the two composition steps of the ladder, each of which is a
compiled implication over the actual matrix carriers rather than a label on a
diagram.

| step | statement |
| --- | --- |
| Laplacian conversion | `P * C = C * Q → (1 - P) * C = C * (1 - Q)` |
| Kemeny-type step | `(G + stationaryMeanMatrix π) * C = C * (H + stationaryMeanMatrix μ)` given `G * C = C * H` and `stationaryMeanMatrix π * C = C * stationaryMeanMatrix μ` |

The second step genuinely consumes **two** proof inputs. A rank or ordering
alone does not record that conjunction or the proof dependencies.

## What this module records, and what it does not

Several stages below are not declared in this module; their witness lemmas live
in the modules named in the table. That is deliberate: a second copy of a public
theorem is a duplicate carrier, not a dependency edge.

| stage | owning declaration | witness lemma in this module |
| --- | --- | --- |
| `core` | `IntertwinerAlgebra.groupInverse_intertwines_of_laws` | — (the root) |
| `poissonGreen` | `IntertwinerAlgebra.poisson_green_intertwines` | — (the owner is itself the witness) |
| `regularized` | `IntertwinerAlgebra.regularized_groupInverse_intertwines` | — (the owner is itself the witness) |
| `stochastic` | `MarkovDrazin.groupInverse_intertwines_of_stationary_compatible` | — (converted by `stationary_laplacians_intertwine`) |
| `stationaryProjector` | `MarkovDrazin.stationaryMeanMatrix_intertwines` | — |
| `markovPoisson` | `MarkovDrazin.poissonGreen_transports_of_stationary_compatible` | — (literal application of `poissonGreen`) |
| `markovRegularized` | `MarkovDrazin.regularizedShift_intertwines_of_stationary_compatible` | `stochastic_conclusion_and_stationaryProjector_imply_markovRegularized` |
| `markovMeanZero` | `MarkovDrazin.liftedSolution_mean_zero_of_stationary_compatible` | — |

## Removed: two certified duplicate re-exports

Earlier revisions carried `core_conclusion_implies_poissonGreen` and
`core_conclusion_implies_regularized` in this module. A repository-wide skeleton
search over all 156,321 statements in the authoritative surfaces found them to be
structure-identical to `IntertwinerAlgebra.poisson_green_intertwines` and
`IntertwinerAlgebra.regularized_groupInverse_intertwines` respectively, and both
directions of the derivation were accepted by the kernel
(`scratch/opengauss/DuplicateAdjudication.lean`). They were therefore genuine
duplicates with no external references, and were removed rather than kept as
"witnesses". The two edge rows now name the owners directly.

## Honest scope of the `decide` certificates

`Stage.edge` and `Stage.rank` are literals written in the same file as the
theorems that "certify" them. The `by decide` results below are therefore
**transcription guards, not mathematical certificates**: deleting every real
theorem in the repository would leave all of them true. They are retained because
they do catch an inconsistent hand-edit to the edge table, and because the edge
table is what a reader consults.

What is *not* claimed: that the edge set is the true dependency graph of the
cluster. It is a hand-maintained summary. The mathematical content is in the
witness lemmas, each of which has a real proof term over real matrix carriers.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.GroupInverseIntertwinerLadder

open Matrix

/-! ## The dependency relation -/

/-- The formalized declarations of the rectangular intertwining ladder. -/
inductive Stage where
  | core
  | poissonGreen
  | regularized
  | stochastic
  | stationaryProjector
  | markovPoisson
  | markovRegularized
  | markovMeanZero
  deriving DecidableEq

instance : Fintype Stage where
  elems := { .core, .poissonGreen, .regularized, .stochastic,
    .stationaryProjector, .markovPoisson, .markovRegularized, .markovMeanZero }
  complete := by
    intro x
    cases x <;> simp

/-- `b` depends on `a`. This relation carries no causal meaning.

The edge set was corrected after independent review found it incomplete: the
literal applications of `poisson_green_intertwines` and of
`regularized_groupInverse_intertwines` inside
`MarkovGroupInverseIntertwinerFunctoriality` were not represented, so
`markovPoisson` and `markovRegularized` appeared to have no predecessor upstream
of `stochastic`. Those edges are now present. The `stochastic → markovMeanZero`
edge was *not* missing — it was already there — but it had no witness lemma in this
module, which is why no local lemma was named for it.

The `stochastic → core` conversion is deliberately **not** an edge. It is a
hypothesis conversion rather than a rung of the ladder — `P * C = C * Q` becomes
`(1 - P) * C = C * (1 - Q)` — and adding it would reverse the rank order, since
the stochastic layer sits *above* the algebraic root. The same two-input
obstruction is why `markovRegularized` is recorded with three predecessors
(`regularized`, `stochastic`, `stationaryProjector`) instead of being given a
single position. -/
def Stage.edge : Stage → Stage → Prop
  | .core, .poissonGreen => True
  | .core, .regularized => True
  | .poissonGreen, .markovPoisson => True
  | .regularized, .markovRegularized => True
  | .stochastic, .markovPoisson => True
  | .stochastic, .markovRegularized => True
  | .stationaryProjector, .markovRegularized => True
  | .stochastic, .markovMeanZero => True
  | _, _ => False

instance (a b : Stage) : Decidable (Stage.edge a b) := by
  cases a <;> cases b <;> simp [Stage.edge] <;> infer_instance

/-- A rank function on the dependency relation: every edge strictly raises the
rank, so the relation is acyclic. Unrelated stages are not asserted comparable. -/
def Stage.rank : Stage → ℕ
  | .core => 0
  | .poissonGreen => 1
  | .regularized => 1
  | .stochastic => 2
  | .stationaryProjector => 2
  | .markovPoisson => 3
  | .markovRegularized => 3
  | .markovMeanZero => 3

/-- The dependency relation is irreflexive: no stage consumes itself. -/
theorem Stage.edge_irreflexive : ∀ a : Stage, ¬ Stage.edge a a := by decide

/-- Every dependency edge strictly increases `Stage.rank`, so the relation is
acyclic and the rank is a topological order of the ladder. -/
theorem Stage.rank_lt_of_edge : ∀ a b : Stage,
    Stage.edge a b → Stage.rank a < Stage.rank b := by decide

/-- `core` is a root of the ladder: nothing in the ladder feeds into it. -/
theorem core_has_no_prerequisite : ∀ a : Stage, ¬ Stage.edge a Stage.core := by
  decide

/-! ## The edges are real implications -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {R : Type*} [Ring R]

/-- **Laplacian conversion.** Whenever the transition operators intertwine, the
Markov Laplacians `1 - P` and `1 - Q` intertwine. This is the conversion from the
stochastic layer of the ladder down to the algebraic `core` layer, and it is the
step that lets `IntertwinerAlgebra` be applied to Markov data at all.

Proved directly by a `calc` on `Matrix.sub_mul` / `Matrix.mul_sub`; it is the one
edge witness in this file that is not a re-export. -/
theorem stationary_laplacians_intertwine
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (hintertwines : P * C = C * Q) :
    (1 - P) * C = C * (1 - Q) := by
  calc (1 - P) * C = C - P * C := by simp only [Matrix.sub_mul, Matrix.one_mul]
    _ = C - C * Q := by rw [hintertwines]
    _ = C * (1 - Q) := by rw [Matrix.mul_sub, Matrix.mul_one]

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The Kemeny-type step.** The regularized group inverse `G + P_stationary`
intertwines when the group inverse itself intertwines *and* the stationary
projectors intertwine. This lemma's contract explicitly supplies both
intertwining equalities.

This is the two-input node of the ladder: it consumes both the `G * C = C * H`
conclusion and the stationary-projector conclusion. -/
theorem stochastic_conclusion_and_stationaryProjector_imply_markovRegularized
    (G : Matrix ι ι ℝ) (H : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (π : ι → ℝ) (μ : κ → ℝ)
    (hsharp : G * C = C * H)
    (hstat : MarkovDrazin.stationaryMeanMatrix π * C
      = C * MarkovDrazin.stationaryMeanMatrix μ) :
    (G + MarkovDrazin.stationaryMeanMatrix π) * C
      = C * (H + MarkovDrazin.stationaryMeanMatrix μ) :=
  IntertwinerAlgebra.regularized_groupInverse_intertwines
    G (MarkovDrazin.stationaryMeanMatrix π) H (MarkovDrazin.stationaryMeanMatrix μ)
    C hsharp hstat

end InfoGeometry.QuantumContext.GroupInverseIntertwinerLadder

end
