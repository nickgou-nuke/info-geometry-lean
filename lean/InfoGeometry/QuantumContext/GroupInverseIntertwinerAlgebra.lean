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
For full group inverses, `groupInverse_intertwines` derives inverse transport
from `LP * C = C * LQ` alone. The regular projectors then intertwine by
`groupInverse_rangeProjector_intertwines`.

For the weaker absorption-and-commutation interface, two equations suffice:

* `LP * C = C * LQ`, so the kernels intertwine, and
* `LP * LP_sharp * C = C * (LQ * LQ_sharp)`, so the regular idempotents
  intertwine.

Then `LP_sharp * C = C * LQ_sharp`: the group inverses intertwine strictly.

## Scope of this module

The proof of `groupInverse_intertwines_of_laws` uses associativity of matrix
multiplication together with four of the group inverse equations:
`LP_sharp * LP * LP_sharp = LP_sharp`,
`LQ_sharp * LQ * LQ_sharp = LQ_sharp`, `LP * LP_sharp = LP_sharp * LP` and
`LQ * LQ_sharp = LQ_sharp * LQ`. The reflexive law `LP * LP_sharp * LP = LP`
is available in the `IsGroupInverse` entry point but is not consumed by the
proof.

The stronger `groupInverse_intertwines` uses both reflexive laws to derive
support compatibility, eliminating the independent range-projector premise.

`regularized_groupInverse_intertwines` additionally uses left and right
distributivity of matrix addition over multiplication, because its conclusion is
a sum `LP_sharp + EP`. Associativity alone does not discharge it.

The coefficient hypothesis remains `[Ring R]`: the bundled `IsGroupInverse`
interface is defined over rings, and the additive distributivity used by the
`regularized` step needs only an additive commutative group. The coefficient
ring may be noncommutative; no commutativity of `R` is assumed.

This module proves no *solvability* statement — no claim that some vector lies
in the range of a Laplacian, and no mean first passage time identity. It does
export `poisson_green_intertwines`, which is a *transport* identity: it carries
an already-given intertwining `LP_sharp * C = C * LQ_sharp` through a further
matrix `b`. No module here proves that coarse-grained Laplacian is solvable or
that any `b` is attained; and none gives a coarse-graining, Stiefel compression
or attention-pooling interpretation.

## Adjacent owners (checked, and one of them is already connected)

A search over every `lean_lib` root declared in `lakefile.lean`
(`lean/InfoGeometry/**`, `proofs/**` declared at `lakefile.lean:885`, plus
`lean/Experimental/**`, `lean/DAG/**`, `lean/Agent/**`, `lean/Omega/**`,
`lean/InfoGeometry/LLM/**`, `lean/VirasoroProject/**`) — and, separately, over
the `require`d package `lib/InfoGeometryCore`, which has its own lakefile and is
therefore *not* a `lean_lib` root of this repository — shows that
coarse-graining and Stiefel owners already exist:

* `InfoGeometry.Canonical.CoarseGraining` defines `FiniteCoarseGraining X Y`
  as `X → Y`, with `fiberWeight` and `encoderMarginal`. It carries no
  Markov content of its own;
* `InfoGeometry.Canonical.PartitionHierarchy` is a finite coarse-grained
  Boltzmann/Gibbs partition calculus. It contains no reference to `sector` and
  does not refine or coarsen anything; it carries no Markov content;
* `InfoGeometry.Canonical.RefinementGaloisConnection` relates refinements and
  likewise carries no Markov content;
* `InfoGeometry.QuantumContext.CausalPetzStiefelConservation` defines
  `blockIntertwiner : Matrix (Fin 2) (Fin 2) R`, a *square* two-by-two block
  operator, with `gram_isometry_iff_stiefel` and `petz_trace_preservation`;
  it does not mention `Markov`, `Laplacian` or `IsGroupInverse`;
* `InfoGeometry.QuantumContext.MarkovPartitionLumping` **does** carry the
  lumping specialization: `partitionIncidence`, the block-sum criterion
  `partitionIntertwining_iff_blockSum`, the stationary pushforward
  `pushforwardStationaryRow`, and `groupInverse_intertwines_of_partitionLumping`
  concluding `Gsharp * partitionIncidence G = partitionIncidence G * Qsharp`.

That last owner reaches its conclusion through the *stochastic* route
`groupInverse_intertwines_of_stationary_compatible`. This module supplies the
*abstract* route; the two are related, not competing. The Stiefel owner above
remains unconnected to rectangular Markov intertwining.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.IntertwinerAlgebra

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {R : Type*} [Ring R]

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The generic three-factor identity.** For a group inverse pair, `a * x * x = x`.

This is a purely ring-theoretic consequence of the absorption law `x * a * x = x`
together with commutativity `x * a = a * x`, and it is stated here over `[Ring R]`
because that is the layer it belongs to — not in any Markov consumer module.

The canonical owner `InfoGeometry.Canonical.HartwigSouriauFrameDrazin` derives
the same identity inline, privately, at the point of use inside
`principalIdempotent_mul_groupInverse_eq_zero`. It is recorded here as a public
lemma so that downstream range arguments have a named owner to cite rather than
re-deriving it. -/
theorem groupInverse_mul_mul {a x : R} (h : IsGroupInverse a x) : a * x * x = x := by
  rw [h.2.2]
  exact h.2.1

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

/-- Full group inverses are natural under rectangular intertwiners. Reflexivity
derives the support compatibility that the weaker outer-inverse theorem needs
as an additional hypothesis. -/
theorem groupInverse_intertwines
    (P P' : Matrix ι ι R) (Q Q' : Matrix κ κ R) (C : Matrix ι κ R)
    (hP : IsGroupInverse P P') (hQ : IsGroupInverse Q Q')
    (hC : P * C = C * Q) : P' * C = C * Q' := by
  have hp : P' * P' * P = P' := by
    rw [mul_assoc, ← hP.2.2, ← mul_assoc, hP.2.1]
  have hq : Q * Q * Q' = Q := by
    rw [mul_assoc, hQ.2.2, ← mul_assoc, hQ.1]
  have hq' : Q * Q' * Q' = Q' := groupInverse_mul_mul hQ
  calc
    P' * C = (P' * P' * P) * C := by rw [hp]
    _ = (P' * P') * (C * Q) := by rw [Matrix.mul_assoc, hC]
    _ = (P' * P') * (C * (Q * Q * Q')) := by rw [hq]
    _ = (P' * P' * P) * C * Q * Q' := by
      simp only [Matrix.mul_assoc, hC]
    _ = P' * C * Q * Q' := by rw [hp]
    _ = (P * P') * C * Q' := by
      rw [Matrix.mul_assoc P' C Q, ← hC, ← Matrix.mul_assoc P' P C, ← hP.2.2]
    _ = (P * P') * C * (Q * Q' * Q') := by rw [hq']
    _ = (P * P' * P) * C * Q' * Q' := by
      simp only [Matrix.mul_assoc, hC]
    _ = C * (Q * Q' * Q') := by rw [hP.1, hC]; simp only [Matrix.mul_assoc]
    _ = C * Q' := by rw [hq']

/-- Regular support transport follows from the full inverse laws and the
operator intertwiner; it does not need to be supplied independently. -/
theorem groupInverse_rangeProjector_intertwines
    (P P' : Matrix ι ι R) (Q Q' : Matrix κ κ R) (C : Matrix ι κ R)
    (hP : IsGroupInverse P P') (hQ : IsGroupInverse Q Q')
    (hC : P * C = C * Q) : P * P' * C = C * (Q * Q') := by
  rw [Matrix.mul_assoc, groupInverse_intertwines P P' Q Q' C hP hQ hC,
    ← Matrix.mul_assoc, hC, Matrix.mul_assoc]

/-- For Laplacians `1-P` and `1-Q`, intertwining of the transition operators
already transports any given group inverses. Positivity, stochasticity, and
stationary-row compatibility are unnecessary for this algebraic conclusion. -/
theorem laplacian_groupInverse_intertwines
    (P : Matrix ι ι R) (Q : Matrix κ κ R) (C : Matrix ι κ R)
    (G : Matrix ι ι R) (H : Matrix κ κ R)
    (hG : IsGroupInverse (1 - P) G) (hH : IsGroupInverse (1 - Q) H)
    (hC : P * C = C * Q) : G * C = C * H := by
  apply groupInverse_intertwines (1 - P) G (1 - Q) H C hG hH
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hC]

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

/-- The nilpotent exchange matrix `-E₀₁` used as the counterexample carrier in
`groupInverse_intertwines_of_laws_needs_hQ_comm`. -/
def nilpotentExchangeUp : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 0, 0]

/-- Its transpose-like partner `-E₁₀`, which satisfies the absorption law
`M * L * M = M` but does not commute with `nilpotentExchangeUp`. -/
def nilpotentExchangeDown : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; -1, 0]

/-- **Non-commutativity witness (T16).** `nilpotentExchangeUp` and
`nilpotentExchangeDown` genuinely fail to commute:

`nilpotentExchangeUp * nilpotentExchangeDown ≠ nilpotentExchangeDown * nilpotentExchangeUp`.

The products differ at entry `(0, 0)`, being `1` and `0`. This shows that the
matrix algebra in play is genuinely non-commutative, so no commutativity of `R`
may be assumed in `groupInverse_intertwines_of_laws`.

This witness is a *non-commutativity* certificate, not a *necessity*
certificate. It does not by itself show that the commutativity law
`LQ * LQ_sharp = LQ_sharp * LQ` is required. That is a separate claim, proved
separately by `groupInverse_intertwines_of_laws_needs_hQ_comm` below, with an
explicit counterexample. -/
theorem nilpotentExchange_noncommutes :
    nilpotentExchangeUp * nilpotentExchangeDown
      ≠ nilpotentExchangeDown * nilpotentExchangeUp := by
  intro h
  have h0 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  simp only [nilpotentExchangeUp, nilpotentExchangeDown, Matrix.mul_apply,
    Matrix.zero_apply] at h0
  norm_num at h0

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Counterexample when `hQ_comm` is omitted.**

The other five displayed hypotheses of `groupInverse_intertwines_of_laws` do
not, by themselves, imply its conclusion. This explicit matrix witness shows
why the commutativity law is needed by that proof contract.

The witness is the nilpotent exchange pair `LQ = -E₀₁`, `LQ_sharp = -E₁₀` with
`LP = LP_sharp = 0` and `C = LQ`. All five remaining binders hold, yet
`LP_sharp * C = 0` while `C * LQ_sharp = E₀₀ ≠ 0`.

This counterexample concerns only the displayed individual laws. It does not
claim anything about the `IsGroupInverse` bundle statement: the witness
exploits the individual laws being weaker than that bundle. -/
theorem groupInverse_intertwines_of_laws_needs_hQ_comm :
    ¬ (∀ (LP LP_sharp : Matrix (Fin 2) (Fin 2) ℝ) (LQ LQ_sharp : Matrix (Fin 2) (Fin 2) ℝ)
        (C : Matrix (Fin 2) (Fin 2) ℝ),
        LP_sharp * LP * LP_sharp = LP_sharp →
        LQ_sharp * LQ * LQ_sharp = LQ_sharp →
        LP * LP_sharp = LP_sharp * LP →
        LP * C = C * LQ →
        LP * LP_sharp * C = C * (LQ * LQ_sharp) →
        LP_sharp * C = C * LQ_sharp) := by
  intro hall
  set L : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 0, 0] with hL
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; -1, 0] with hM
  have h1 : (0 : Matrix (Fin 2) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 2) ℝ)
      * (0 : Matrix (Fin 2) (Fin 2) ℝ) = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
        simp
  have h2 : M * L * M = M := by
    rw [hM, hL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply] <;> norm_num
  have h3 : (0 : Matrix (Fin 2) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 2) ℝ)
      = (0 : Matrix (Fin 2) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
        simp
  have h4 : (0 : Matrix (Fin 2) (Fin 2) ℝ) * L = L * L := by
    rw [hL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply] <;> norm_num
  have h5 : (0 : Matrix (Fin 2) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 2) ℝ) * L
      = L * (L * M) := by
    rw [hL, hM]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply] <;> norm_num
  have hbad := hall (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ)
    L M L h1 h2 h3 h4 h5
  rw [hL, hM] at hbad
  have hbad0 := congrFun (congrFun hbad (0 : Fin 2)) (0 : Fin 2)
  simp only [Matrix.mul_apply, Matrix.zero_apply] at hbad0
  exact absurd hbad0 (by norm_num)

end InfoGeometry.QuantumContext.IntertwinerAlgebra

end
