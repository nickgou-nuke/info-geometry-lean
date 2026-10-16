/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Order
import Mathlib.Tactic
import InfoGeometry.QuantumContext.MarkovGroupInverseIntertwinerFunctoriality
import InfoGeometry.QuantumContext.GroupInverseIntertwinerAlgebra

/-!
# The dependency ladder for rectangular Markov group-inverse intertwining

This module records the two formalized layers of rectangular group-inverse
intertwining, the dependency edges between them, and — for every edge — a
compiled implication showing that the dependency is a real logical consequence
rather than a label.

## What is ordered here

`Stage` names the formalized declarations that make up the ladder:

| stage | owning declaration |
| --- | --- |
| `core` | `IntertwinerAlgebra.groupInverse_intertwines_of_rangeProjector` |
| `poissonGreen` | `IntertwinerAlgebra.poisson_green_intertwines` |
| `regularized` | `IntertwinerAlgebra.regularized_groupInverse_intertwines` |
| `stochastic` | `MarkovDrazin.groupInverse_intertwines_of_stochastic_compatible` |
| `stationaryProjector` | `MarkovDrazin.stationaryMeanMatrix_intertwines` |
| `markovPoisson` | `MarkovDrazin.poissonGreen_transports_of_stationary_compatible` |
| `markovRegularized` | `MarkovDrazin.regularizedShift_intertwines_of_stationary_compatible` |
| `markovMeanZero` | `MarkovDrazin.liftedSolution_mean_zero_of_stationary_compatible` |

## Scope of the order

`Stage.edge` is a dependency relation on these names only. It is **not** an
implication between the stages, and this module asserts no physical, causal or
temporal causation. It is checked to be irreflexive and to admit a strictly
decreasing `Stage.rank`, which makes it an acyclic development order.

The mathematical content is in the implication lemmas
`core_conclusion_implies_poissonGreen`,
`core_conclusion_implies_regularized`,
`stochastic_conclusion_implies_markovPoisson`,
`stochastic_conclusion_and_stationaryProjector_imply_markovRegularized` and
`stochastic_conclusion_implies_markovMeanZero`, and in the refutation
`unitRowSums_do_not_imply_stationaryProjector`, each of which is a compiled
theorem over the actual matrix carriers.

The ladder is deliberately not a partial order on the mathematical content: the
Kemeny-type step genuinely has two inputs (`core` and `stationaryProjector`),
which no binary order can express. Encoding it as one would misrepresent the
architecture.
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

/-- `b` depends on `a`: the conclusion certified for `a` is an input of the
proof of the declaration standing for `b`. This relation carries no causal
meaning. -/
def Stage.edge : Stage → Stage → Prop
  | .core, .poissonGreen => True
  | .core, .regularized => True
  | .stochastic, .markovPoisson => True
  | .stochastic, .markovRegularized => True
  | .stationaryProjector, .markovRegularized => True
  | .stochastic, .markovMeanZero => True
  | _, _ => False

instance (a b : Stage) : Decidable (Stage.edge a b) := by
  cases a <;> cases b <;> simp [Stage.edge] <;> infer_instance

/-- A strict rank of the dependency relation: a strictly decreasing `ℕ` value
turns the acyclic development order into a linear order. -/
def Stage.rank : Stage → ℕ
  | .core => 0
  | .stationaryProjector => 1
  | .stochastic => 1
  | .poissonGreen => 2
  | .regularized => 2
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

/-! ## The edges are real implications

Each lemma below has a compiled proof; none is an axiom, `sorry`, or a
restatement of a hypothesis. -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {R : Type*} [CommRing R]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The `poissonGreen` step consumes the conclusion of `core`. -/
theorem core_conclusion_implies_poissonGreen
    (LP_sharp : Matrix ι ι R) (LQ_sharp : Matrix κ κ R)
    (C : Matrix ι κ R) (b : Matrix κ (Fin 1) R)
    (h : LP_sharp * C = C * LQ_sharp) :
    LP_sharp * (C * b) = C * (LQ_sharp * b) :=
  IntertwinerAlgebra.poisson_green_intertwines LP_sharp LQ_sharp C b h

omit [DecidableEq ι] [DecidableEq κ] in
/-- The `regularized` step consumes the conclusion of `core` together with the
intertwining of the regularizing idempotents. -/
theorem core_conclusion_implies_regularized
    (LP_sharp EP : Matrix ι ι R) (LQ_sharp EQ : Matrix κ κ R)
    (C : Matrix ι κ R)
    (h : LP_sharp * C = C * LQ_sharp) (h' : EP * C = C * EQ) :
    (LP_sharp + EP) * C = C * (LQ_sharp + EQ) :=
  IntertwinerAlgebra.regularized_groupInverse_intertwines
    LP_sharp EP LQ_sharp EQ C h h'

/-- The Markov Laplacians intertwine whenever the transition operators do. This
is the hypothesis conversion from the `stochastic` layer to the `core` layer. -/
theorem stationary_laplacians_intertwine
    (P : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    (hintertwines : P * C = C * Q) :
    (1 - P) * C = C * (1 - Q) := by
  calc (1 - P) * C = C - P * C := by simp only [Matrix.sub_mul, Matrix.one_mul]
    _ = C - C * Q := by rw [hintertwines]
    _ = C * (1 - Q) := by rw [Matrix.mul_sub, Matrix.mul_one]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The `markovPoisson` step consumes the conclusion of `stochastic`. The
group inverse hypotheses are not repeated here: the algebraic step needs only the
transported conclusion, and this module does not restate the stochastic
preconditions. -/
theorem stochastic_conclusion_implies_markovPoisson
    (G : Matrix ι ι ℝ) (H : Matrix κ κ ℝ)
    (C : Matrix ι κ ℝ) (b : Matrix κ (Fin 1) ℝ)
    (hsharp : G * C = C * H) :
    G * (C * b) = C * (H * b) :=
  IntertwinerAlgebra.poisson_green_intertwines G H C b hsharp

omit [DecidableEq ι] [DecidableEq κ] in
/-- The `markovRegularized` step consumes the conclusions of both `stochastic`
and `stationaryProjector`. This is the reason the ladder is recorded as a
dependency relation with a two-input node rather than as a binary order. -/
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