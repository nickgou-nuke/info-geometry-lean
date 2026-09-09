import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic

/-!
# Generalized Nilpotent / Tripotent Operators and the Hodge–Krein Split

This module formalizes the operator-algebraic generalization sketched in
`GeneralizedNilpotentTripotent`: moving from binary / tripotent systems to
arbitrary `$N$`-nilpotent operators `$X^N = 0$` and `$N$`-ary Cuntz-type
fractals.

All statements are native Lean 4 derivations checked by the kernel with **zero
`sorry` debt**.  The two sections of the blueprint are implemented exactly:

* **§1 — Tripotent operators** (`$O^3 = O$`): the three Hodge–Krein projectors
  `$P_+, P_-, P_0$` are constructed from `$O$` and proven to be mutually
  orthogonal idempotents summing to the identity, with `$O = P_+ - P_-$`.
* **§2 — Generalized `$N$`-nilpotence** (`$X^N = 0$`): the universal unipotent
  inverse `$(1+X)^{-1} = \sum_{j<N} (-1)^j X^j$` is proven for an arbitrary
  nilpotent element of any ring; the matrix instance is recovered directly.

The tripotent decomposition is carried out over `Matrix (Fin n) (Fin n) ℂ`, the
finite-dimensional operator algebra of the original blueprint.  The unipotent
inverse is proven once and for all over a general `[Ring R]`, which then covers
the matrix case (and every other ring) by specialization.

For the `$N$-ary Cuntz fractal algebra `$\mathcal O_N$`, see the existing live
owner files `InfoGeometry.Topology.CuntzCantorSpectralTriple` (`CuntzO2Carrier`)
and `InfoGeometry.External.Auto.FractalKleinSUSYFramework` (`CuntzAlgebraRelations`);
this module is the algebraic engine they build upon, not a replacement.
-/

open Matrix Finset

namespace InfoGeometry.OperatorAlgebra.GeneralizedNilpotentTripotent

variable {n : ℕ}

/-!
## §1  Tripotent operators and the Hodge–Krein decomposition  (`$O^3 = O$`)

A tripotent operator has spectrum inside `$\{-1, 0, +1\}$`.  The three
orthogonal projectors

* `$P_+ = \tfrac12 (O^2 + O)$`  (positive / physical sector),
* `$P_- = \tfrac12 (O^2 - O)$`  (negative / ghost sector),
* `$P_0 = 1 - O^2$`            (null / topological boundary),

split the space into three mutually orthogonal sectors.
-/

/-- A tripotent matrix operator of dimension `n`: `$O^3 = O$`. -/
structure TripotentOperator (n : ℕ) where
  O : Matrix (Fin n) (Fin n) ℂ
  h_tripotent : O * O * O = O

/-- Positive / physical Hodge–Krein projector `$P_+ = \tfrac12 (O^2 + O)$`. -/
noncomputable def projectPlus (t : TripotentOperator n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (t.O ^ 2 + t.O)

/-- Negative / ghost Hodge–Krein projector `$P_- = \tfrac12 (O^2 - O)$`. -/
noncomputable def projectMinus (t : TripotentOperator n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (t.O ^ 2 - t.O)

/-- Null / boundary Hodge–Krein projector `$P_0 = 1 - O^2$`. -/
noncomputable def projectNull (t : TripotentOperator n) : Matrix (Fin n) (Fin n) ℂ :=
  1 - t.O ^ 2

/-- Auxiliary: from `$O^3 = O$` we get `$O^4 = O^2$`. -/
lemma tripotent_pow_four (t : TripotentOperator n) : t.O ^ 4 = t.O ^ 2 := by
  calc
    t.O ^ 4 = t.O ^ 3 * t.O := by rw [pow_succ]
    _ = (t.O * t.O * t.O) * t.O := by
      congr 1
      noncomm_ring
    _ = t.O * t.O := by rw [t.h_tripotent]
    _ = t.O ^ 2 := by rw [pow_two]

lemma tripotent_pow_three (t : TripotentOperator n) : t.O ^ 3 = t.O := by
  simpa [pow_succ, pow_two, mul_assoc] using t.h_tripotent

/-- The square of `$O^2 + O$` collapses to twice itself: `$(O^2+O)^2 = 2 (O^2+O)$`. -/
lemma plus_square (t : TripotentOperator n) :
    (t.O ^ 2 + t.O) * (t.O ^ 2 + t.O) = (2 : ℂ) • (t.O ^ 2 + t.O) := by
  calc (t.O ^ 2 + t.O) * (t.O ^ 2 + t.O)
    _ = t.O ^ 4 + t.O ^ 3 + t.O ^ 3 + t.O ^ 2 := by noncomm_ring
    _ = t.O ^ 2 + t.O + t.O + t.O ^ 2 := by
      rw [tripotent_pow_four t, tripotent_pow_three t]
    _ = (2 : ℂ) • (t.O ^ 2 + t.O) := by
      ext i j
      simp
      ring

/-- The square of `$O^2 - O$` collapses to twice itself: `$(O^2-O)^2 = 2 (O^2-O)$`. -/
lemma minus_square (t : TripotentOperator n) :
    (t.O ^ 2 - t.O) * (t.O ^ 2 - t.O) = (2 : ℂ) • (t.O ^ 2 - t.O) := by
  calc (t.O ^ 2 - t.O) * (t.O ^ 2 - t.O)
    _ = t.O ^ 4 - t.O ^ 3 - t.O ^ 3 + t.O ^ 2 := by noncomm_ring
    _ = t.O ^ 2 - t.O - t.O + t.O ^ 2 := by
      rw [tripotent_pow_four t, tripotent_pow_three t]
    _ = (2 : ℂ) • (t.O ^ 2 - t.O) := by
      ext i j
      simp
      ring

/-- **Theorem 1 (blueprint).** The null / boundary projector is idempotent:
`$P_0^2 = P_0$`. -/
theorem null_projector_idempotent (t : TripotentOperator n) :
    projectNull t * projectNull t = projectNull t := by
  simp only [projectNull]
  calc (1 - t.O ^ 2) * (1 - t.O ^ 2)
    _ = 1 - t.O ^ 2 - t.O ^ 2 + t.O ^ 2 * t.O ^ 2 := by noncomm_ring
    _ = 1 - t.O ^ 2 - t.O ^ 2 + t.O ^ 4 := by
      simp [pow_succ, pow_two, mul_assoc]
    _ = 1 - t.O ^ 2 - t.O ^ 2 + t.O ^ 2 := by rw [tripotent_pow_four t]
    _ = 1 - t.O ^ 2 := by abel

/-- The positive projector is idempotent: `$P_+^2 = P_+$`. -/
theorem plus_projector_idempotent (t : TripotentOperator n) :
    projectPlus t * projectPlus t = projectPlus t := by
  simp only [projectPlus]
  rw [show
      ((1 / 2 : ℂ) • (t.O ^ 2 + t.O)) *
          ((1 / 2 : ℂ) • (t.O ^ 2 + t.O)) =
        ((1 / 2 : ℂ) * (1 / 2 : ℂ)) •
          ((t.O ^ 2 + t.O) * (t.O ^ 2 + t.O)) by
    exact (Algebra.smul_mul_assoc _ _ _).trans
      (congrArg (fun z => (1 / 2 : ℂ) • z) (Algebra.mul_smul_comm _ _ _)) |>.trans
        (smul_smul _ _ _)]
  rw [plus_square t]
  simp [smul_smul]

/-- The negative projector is idempotent: `$P_-^2 = P_-$`. -/
theorem minus_projector_idempotent (t : TripotentOperator n) :
    projectMinus t * projectMinus t = projectMinus t := by
  simp only [projectMinus]
  rw [show
      ((1 / 2 : ℂ) • (t.O ^ 2 - t.O)) *
          ((1 / 2 : ℂ) • (t.O ^ 2 - t.O)) =
        ((1 / 2 : ℂ) * (1 / 2 : ℂ)) •
          ((t.O ^ 2 - t.O) * (t.O ^ 2 - t.O)) by
    exact (Algebra.smul_mul_assoc _ _ _).trans
      (congrArg (fun z => (1 / 2 : ℂ) • z) (Algebra.mul_smul_comm _ _ _)) |>.trans
        (smul_smul _ _ _)]
  rw [minus_square t]
  simp [smul_smul]

/-- `$P_+$ and `$P_-$` are mutually orthogonal. -/
theorem plus_minus_orthogonal (t : TripotentOperator n) :
    projectPlus t * projectMinus t = 0 := by
  simp only [projectPlus, projectMinus]
  have h : (t.O ^ 2 + t.O) * (t.O ^ 2 - t.O) = 0 := by
    calc
      (t.O ^ 2 + t.O) * (t.O ^ 2 - t.O) = t.O ^ 4 - t.O ^ 2 := by
        noncomm_ring
      _ = 0 := by rw [tripotent_pow_four t]; abel
  rw [show
      ((1 / 2 : ℂ) • (t.O ^ 2 + t.O)) *
          ((1 / 2 : ℂ) • (t.O ^ 2 - t.O)) =
        ((1 / 2 : ℂ) * (1 / 2 : ℂ)) •
          ((t.O ^ 2 + t.O) * (t.O ^ 2 - t.O)) by
    exact (Algebra.smul_mul_assoc _ _ _).trans
      (congrArg (fun z => (1 / 2 : ℂ) • z) (Algebra.mul_smul_comm _ _ _)) |>.trans
        (smul_smul _ _ _)]
  rw [h]
  simp

/-- `$P_+$ and `$P_0$` are mutually orthogonal. -/
theorem plus_null_orthogonal (t : TripotentOperator n) :
    projectPlus t * projectNull t = 0 := by
  simp only [projectPlus, projectNull]
  have h : (t.O ^ 2 + t.O) * (1 - t.O ^ 2) = 0 := by
    calc
      (t.O ^ 2 + t.O) * (1 - t.O ^ 2) =
          t.O ^ 2 + t.O - (t.O ^ 4 + t.O ^ 3) := by
        noncomm_ring
      _ = 0 := by rw [tripotent_pow_four t, tripotent_pow_three t]; abel
  rw [show
      ((1 / 2 : ℂ) • (t.O ^ 2 + t.O)) * (1 - t.O ^ 2) =
        (1 / 2 : ℂ) • ((t.O ^ 2 + t.O) * (1 - t.O ^ 2)) by
    exact Algebra.smul_mul_assoc _ _ _]
  rw [h]
  simp

/-- `$P_-$ and `$P_0$` are mutually orthogonal. -/
theorem minus_null_orthogonal (t : TripotentOperator n) :
    projectMinus t * projectNull t = 0 := by
  simp only [projectMinus, projectNull]
  have h : (t.O ^ 2 - t.O) * (1 - t.O ^ 2) = 0 := by
    calc
      (t.O ^ 2 - t.O) * (1 - t.O ^ 2) =
          t.O ^ 2 - t.O - (t.O ^ 4 - t.O ^ 3) := by
        noncomm_ring
      _ = 0 := by rw [tripotent_pow_four t, tripotent_pow_three t]; abel
  rw [show
      ((1 / 2 : ℂ) • (t.O ^ 2 - t.O)) * (1 - t.O ^ 2) =
        (1 / 2 : ℂ) • ((t.O ^ 2 - t.O) * (1 - t.O ^ 2)) by
    exact Algebra.smul_mul_assoc _ _ _]
  rw [h]
  simp

/-- The three Hodge–Krein projectors sum to the identity: `$P_+ + P_- + P_0 = 1$`. -/
theorem projector_sum_is_one (t : TripotentOperator n) :
    projectPlus t + projectMinus t + projectNull t = 1 := by
  simp only [projectPlus, projectMinus, projectNull]
  ext i j
  simp [smul_add, sub_eq_add_neg]
  ring

/-- Reconstruction of the operator from its sectors: `$O = P_+ - P_-$`. -/
theorem operator_reconstruction (t : TripotentOperator n) :
    t.O = projectPlus t - projectMinus t := by
  simp only [projectPlus, projectMinus]
  ext i j
  simp [smul_add, smul_sub, sub_eq_add_neg]
  ring

/-!
## §2  Generalized `$N$`-nilpotence  (`$X^N = 0$`)

An element `$X$` with `$X^{\deg}=0$` yields a unipotent `$1+X$` whose inverse is
the finite telescoping sum `$\sum_{j<\deg} (-1)^j X^j$`.  Because the proof only
uses the ring structure of `$X$`, it is given once for an arbitrary `[Ring R]`.
-/

/-- **Theorem 2 (blueprint).** Universal unipotent inverse for any nilpotent
element of any ring:
`$(1+X)\bigl(\sum_{j<\deg} (-1)^j X^j\bigr) = 1$`. -/
theorem generalized_unipotent_inverse {R : Type*} [Ring R] {degree : ℕ}
    (X : R) (h : X ^ degree = 0) :
    (1 + X) * (∑ j ∈ Finset.range degree, (-1 : R) ^ j * X ^ j) = 1 := by
  have : (∑ j ∈ Finset.range degree, (-1 : R) ^ j * X ^ j) = ∑ j ∈ Finset.range degree, (-X) ^ j := by
    simp [← neg_pow X]
  rw [this, ← sub_neg_eq_add, mul_neg_geom_sum (-X) degree]
  simp [h, neg_pow X]

/-- A finite-dimensional `$N$`-nilpotent matrix operator of dimension `n`. -/
structure NilpotentOperator (n degree : ℕ) where
  X : Matrix (Fin n) (Fin n) ℂ
  h_nilpotent : X ^ degree = 0

/-- The blueprint's matrix-level unipotent inverse, written with the alternating
summand `$(-op.X)^j$`.  By `neg_pow` this is exactly the blueprint's
`$\sum_{j<\deg} (-1 : \mathbb C)^j \bullet X^j$`, i.e. `generalized_unipotent_inverse`
specialized to the operator algebra `Matrix (Fin n) (Fin n) ℂ`. -/
theorem generalized_unipotent_inverse_matrix {degree : ℕ}
    (op : NilpotentOperator n degree) :
    (1 + op.X) * (∑ j ∈ Finset.range degree, (-op.X) ^ j) = 1 := by
  simp only [neg_pow op.X]
  exact generalized_unipotent_inverse op.X op.h_nilpotent

end InfoGeometry.OperatorAlgebra.GeneralizedNilpotentTripotent
