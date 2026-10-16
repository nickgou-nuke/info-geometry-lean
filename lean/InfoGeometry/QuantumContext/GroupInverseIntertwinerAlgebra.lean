/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-!
# Algebraic core of rectangular intertwining for group inverses

This module isolates the purely algebraic content behind rectangular transport
of Markov group inverses, independently of any stochastic hypothesis.

Let `LP` and `LQ` be square matrices over a (possibly noncommutative) ring, let `LP_sharp`
and `LQ_sharp` be group inverses of them in the sense of the canonical
`InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse` interface
applied to the square matrix ring, and let `C` be a rectangular intertwiner.
Two intertwining equations suffice:

* `LP * C = C * LQ`, so the kernels intertwine, and
* `LP * LP_sharp * C = C * (LQ * LQ_sharp)`, so the regular idempotents
  intertwine.

Then `LP_sharp * C = C * LQ_sharp`: the group inverses intertwine strictly.

## Scope of this module

The proof uses associativity of matrix multiplication together with four of the
group inverse equations: `LP_sharp * LP * LP_sharp = LP_sharp`,
`LQ_sharp * LQ * LQ_sharp = LQ_sharp`, `LP * LP_sharp = LP_sharp * LP` and
`LQ * LQ_sharp = LQ_sharp * LQ`. The reflexive law `LP * LP_sharp * LP = LP`
is available in the hypotheses but is not consumed by the proof, and no
commutativity of the coefficient ring is used.

This module proves no Poisson solvability statement, no mean first passage time
identity, and no coarse-graining, Stiefel compression or attention-pooling
interpretation.

## Adjacent owners (checked, not connected)

A search over every `lean_lib` root declared in `lakefile.lean`
(`lean/InfoGeometry/**`, `proofs/**` declared at `lakefile.lean:885`,
`lib/InfoGeometryCore/**`, `tests/**`, `lean/Experimental/**`, `lean/DAG/**`,
`lean/Agent/**`, `lean/Omega/**`) shows that coarse-graining and Stiefel
owners already exist:

* `InfoGeometry.Canonical.CoarseGraining` defines `FiniteCoarseGraining X Y`
  as `X → Y`, with `fiberWeight` and `encoderMarginal`;
* `InfoGeometry.Canonical.PartitionHierarchy` and
  `InfoGeometry.Canonical.RefinementGaloisConnection` refine and coarsen
  partition and sector structures;
* `InfoGeometry.QuantumContext.CausalPetzStiefelConservation` defines
  `blockIntertwiner : Matrix (Fin 2) (Fin 2) R`, a *square* two-by-two block
  operator, with `gram_isometry_iff_stiefel` and `petz_trace_preservation`.

None of these mentions `Markov`, `Laplacian`, `stationaryMeanMatrix` or
`IsGroupInverse`, and `blockIntertwiner` is square rather than rectangular. So
the structures are formalized while their coupling to rectangular Markov
intertwining is not. Attaching this module to them would be new formalization
work, not a corollary of anything proved here.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.IntertwinerAlgebra

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {R : Type*} [Ring R]

omit [DecidableEq ι] [DecidableEq κ] in
/-- THE ALGEBRAIC CORE, AT THE LEVEL OF THE INDIVIDUAL GROUP INVERSE LAWS.

A rectangular intertwiner `C` transports group inverses whenever it also
intertwines the two regular idempotents `LP * LP_sharp` and `LQ * LQ_sharp`.
No stochastic hypothesis is used.

Only the two absorption laws and the two commutativity laws are consumed. The
reflexive law `LP * LP_sharp * LP = LP` is **not** assumed and is **not** used,
which is why this statement is stated over the individual laws rather than over
the `IsGroupInverse` bundle: see `groupInverse_intertwines_of_rangeProjector`
for the bundle-level consumer entry point.

The proof runs the absorption law of `LP_sharp` from the left and the
absorption law of `LQ_sharp` from the right, meeting at the common regular
idempotent. -/
theorem groupInverse_intertwines_of_laws
    (LP LP_sharp : Matrix ι ι R) (LQ LQ_sharp : Matrix κ κ R)
    (C : Matrix ι κ R)
    (hP_abs : LP_sharp * LP * LP_sharp = LP_sharp)
    (hQ_abs : LQ_sharp * LQ * LQ_sharp = LQ_sharp)
    (hP_comm : LP * LP_sharp = LP_sharp * LP)
    (hQ_comm : LQ * LQ_sharp = LQ_sharp * LQ)
    (h_lap : LP * C = C * LQ)
    (h_range : LP * LP_sharp * C = C * (LQ * LQ_sharp)) :
    LP_sharp * C = C * LQ_sharp := by
  calc LP_sharp * C = (LP_sharp * LP * LP_sharp) * C := by rw [hP_abs]
    _ = LP_sharp * ((LP * LP_sharp) * C) := by simp only [Matrix.mul_assoc]
    _ = LP_sharp * (C * (LQ * LQ_sharp)) := by rw [h_range]
    _ = LP_sharp * ((C * LQ) * LQ_sharp) := by simp only [Matrix.mul_assoc]
    _ = LP_sharp * ((LP * C) * LQ_sharp) := by rw [h_lap]
    _ = (LP_sharp * (LP * C)) * LQ_sharp := by simp only [Matrix.mul_assoc]
    _ = (LP_sharp * LP * C) * LQ_sharp := by rw [← Matrix.mul_assoc]
    _ = (LP * LP_sharp * C) * LQ_sharp := by rw [hP_comm]
    _ = (C * (LQ * LQ_sharp)) * LQ_sharp := by rw [h_range]
    _ = (C * (LQ_sharp * LQ)) * LQ_sharp := by rw [hQ_comm]
    _ = C * ((LQ_sharp * LQ) * LQ_sharp) := by simp only [Matrix.mul_assoc]
    _ = C * LQ_sharp := by rw [hQ_abs]

/-- THE ALGEBRAIC CORE (`LP_sharp * C = C * LQ_sharp`), at the canonical
`IsGroupInverse` interface.

A rectangular intertwiner `C` transports group inverses whenever it also
intertwines the two regular idempotents `LP * LP_sharp` and `LQ * LQ_sharp`.
No stochastic hypothesis is used.

This is a thin corollary of `groupInverse_intertwines_of_laws`; the reflexive
group inverse law is available here but is not needed for the conclusion. -/
theorem groupInverse_intertwines_of_rangeProjector
    (LP LP_sharp : Matrix ι ι R) (LQ LQ_sharp : Matrix κ κ R)
    (C : Matrix ι κ R)
    (hP : IsGroupInverse LP LP_sharp)
    (hQ : IsGroupInverse LQ LQ_sharp)
    (h_lap : LP * C = C * LQ)
    (h_range : LP * LP_sharp * C = C * (LQ * LQ_sharp)) :
    LP_sharp * C = C * LQ_sharp :=
  groupInverse_intertwines_of_laws LP LP_sharp LQ LQ_sharp C
    hP.2.1 hQ.2.1 hP.2.2 hQ.2.2 h_lap h_range

omit [DecidableEq ι] [DecidableEq κ] in
/-- Poisson Green transport for an arbitrary family of right-hand sides: if the
group inverses intertwine, then pushing any matrix-valued right-hand side
through the intertwiner leaves the group-inverse solution operator unchanged.
This is an identity of matrix products; it asserts no existence or uniqueness
of Poisson solutions. -/
theorem poisson_green_intertwines {η : Type*}
    (LP_sharp : Matrix ι ι R) (LQ_sharp : Matrix κ κ R)
    (C : Matrix ι κ R) (b : Matrix κ η R)
    (h_inter : LP_sharp * C = C * LQ_sharp) :
    LP_sharp * (C * b) = C * (LQ_sharp * b) :=
  calc LP_sharp * (C * b) = (LP_sharp * C) * b := (Matrix.mul_assoc _ _ _).symm
    _ = (C * LQ_sharp) * b := by rw [h_inter]
    _ = C * (LQ_sharp * b) := Matrix.mul_assoc _ _ _

omit [DecidableEq ι] [DecidableEq κ] in
/-- Regularized (Kemeny-type) intertwining: if the group inverses intertwine
and the regularizing idempotents intertwine, then the regularized operators
`LP_sharp + EP` and `LQ_sharp + EQ` intertwine. This is an identity of finite
algebraic objects; no mean first passage time interpretation is asserted. -/
theorem regularized_groupInverse_intertwines
    (LP_sharp EP : Matrix ι ι R) (LQ_sharp EQ : Matrix κ κ R)
    (C : Matrix ι κ R)
    (h_sharp : LP_sharp * C = C * LQ_sharp)
    (h_stat : EP * C = C * EQ) :
    (LP_sharp + EP) * C = C * (LQ_sharp + EQ) :=
  calc (LP_sharp + EP) * C = LP_sharp * C + EP * C := Matrix.add_mul _ _ _
    _ = (C * LQ_sharp) + (C * EQ) := by rw [h_sharp, h_stat]
    _ = C * (LQ_sharp + EQ) := (Matrix.mul_add _ _ _).symm

end InfoGeometry.QuantumContext.IntertwinerAlgebra

end
