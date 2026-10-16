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

## Withdrawn: the `Stage.edge` certificate apparatus

An earlier revision of this file encoded the development order as an inductive
`Stage` of formalized declaration names, with a hand-written `Stage.edge`
relation (a `True`/`False` pattern match), a hand-written `Stage.rank` table, and
three `by decide` theorems asserting irreflexivity, rank monotonicity along
edges, and that `core` is a root.

**That apparatus was withdrawn because it certifies nothing.** `Stage.edge` and
`Stage.rank` are literals written in the same file as the theorems that "certify"
them. Deleting every real theorem in the repository would leave all three
`decide` theorems still true. A kernel check of a hand-written relation is a
check of the author's transcription, not of the mathematics.

Only the two composition implications above are kept, because each has a real
proof term over real matrix carriers: `stationary_laplacians_intertwine` is
proved directly by a `calc` on `Matrix.sub_mul` / `Matrix.mul_sub`, and the
Kemeny-type step is a genuine instantiation of the `regularized` step at the
Markov stationary projector.

The `core → poissonGreen` and `core → regularized` steps are deliberately
**absent**: they were verbatim re-exports of the already-public
`IntertwinerAlgebra.poisson_green_intertwines` and
`IntertwinerAlgebra.regularized_groupInverse_intertwines`, and a second copy of a
public theorem is a duplicate carrier, not a dependency edge.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.GroupInverseIntertwinerLadder

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **Laplacian conversion.** Whenever the transition operators intertwine, the
Markov Laplacians `1 - P` and `1 - Q` intertwine. This is the conversion from the
stochastic layer of the ladder down to the algebraic `core` layer, and it is the
step that lets `IntertwinerAlgebra` be applied to Markov data at all. -/
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
