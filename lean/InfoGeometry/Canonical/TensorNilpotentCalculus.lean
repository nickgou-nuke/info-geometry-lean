/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11ConditionalExpectation
import InfoGeometry.Canonical.TensorPolynomialTrace
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.OperatorAlgebra.SquareZeroPolynomial

/-!
# Nontrivial nilpotent calculus in the existing algebraic matrix colimit

Polynomial evaluation commutes with the actual finite-stage maps. Nonzero
square-zero matrix units survive those maps, while a coherent idempotent
family seeded at the scalar stage is necessarily trivial. The latter theorem
explains why nontrivial Peirce data must be seeded at a positive matrix stage.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorNilpotentCalculus

open Polynomial
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Canonical.Cl11ConditionalExpectation
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.SquareZeroPolynomial

/-- Native polynomial evaluation is natural for the existing canonical
map from a full matrix stage into the real algebraic direct limit. -/
theorem ofStage_aeval (n : ℕ) (X : Stage n) (F : ℝ[X]) :
    ofStage n (aeval X F) = aeval (ofStage n X) F := by
  let f : Stage n →ₐ[ℝ] Limit :=
    { toRingHom := ofStage n
      commutes' := fun r => (realAlgebraMap_stage n r).symm }
  exact (Polynomial.aeval_algHom_apply f X F).symm

/-- Every last-factor matrix unit gives a nonzero nilpotent in the actual
direct limit, since the canonical stage maps are injective. -/
theorem fineCreation_limit_ne_zero (n : ℕ) :
    ofStage (n + 1) (fineCreation n) ≠ 0 := by
  exact (ofStage_eq_zero_iff (n + 1) (fineCreation n)).not.mpr (fineCreation_ne_zero n)

/-- Exact polynomial calculus at a scalar base holds on the explicit
nonzero square-zero operators in the full matrix direct limit. -/
theorem fineCreation_limit_polynomial (n : ℕ) (r : ℝ) (F : ℝ[X]) :
    aeval (algebraMap ℝ Limit r + ofStage (n + 1) (fineCreation n)) F =
      algebraMap ℝ Limit (F.eval r) +
        F.derivative.eval r • ofStage (n + 1) (fineCreation n) := by
  exact aeval_scalar_add_sq_zero F r (limit_square_zero (fineCreation_sq n))

/-- A coherent nontrivial tail, seeded at the first matrix stage rather than
the scalar stage. The source mode is transported by the existing bonding maps. -/
def creationTail (n : ℕ) : Stage (n + 1) :=
  bondMap stageBond 1 (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (fineCreation 0)

/-- The positive-stage seed is compatible with every one-step refinement. -/
theorem creationTail_coherent (n : ℕ) :
    stageEmbed (n + 1) (creationTail n) = creationTail (n + 1) := by
  change stageBond (n + 1)
      (bondMap stageBond 1 (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (fineCreation 0)) =
    bondMap stageBond 1 (n + 1 + 1)
      (Nat.succ_le_succ (Nat.zero_le (n + 1))) (fineCreation 0)
  rw [bondMap_succ stageBond 1 (n + 1) (Nat.succ_le_succ (Nat.zero_le n))]
  rfl

/-- All representatives of the coherent tail define the same limit element. -/
theorem creationTail_ofStage (n : ℕ) :
    ofStage (n + 1) (creationTail n) = ofStage 1 (fineCreation 0) := by
  exact directLimitOf_bondMap stageBond 1 (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (fineCreation 0)

/-- Refinement preserves nonzeroness of the explicit coherent nilpotent. -/
theorem creationTail_ne_zero (n : ℕ) : creationTail n ≠ 0 := by
  intro h
  have he := congrArg (ofStage (n + 1)) h
  rw [creationTail_ofStage, map_zero] at he
  exact fineCreation_limit_ne_zero 0 he

/-- The same coherent tail remains square-zero at every positive stage. -/
theorem creationTail_sq (n : ℕ) : creationTail n * creationTail n = 0 := by
  unfold creationTail
  rw [← map_mul, fineCreation_sq, map_zero]

/-- Polynomial evaluation of a scalar-shifted coherent nilpotent is
independent of the representative stage in the actual direct limit. -/
theorem creationTail_polynomial_compatible (n : ℕ) (r : ℝ) (F : ℝ[X]) :
    ofStage (n + 1) (aeval (algebraMap ℝ (Stage (n + 1)) r + creationTail n) F) =
      ofStage 1 (aeval (algebraMap ℝ (Stage 1) r + fineCreation 0) F) := by
  simp only [ofStage_aeval, map_add]
  rw [← realAlgebraMap_stage, ← realAlgebraMap_stage, creationTail_ofStage]

/-- The one-dimensional real matrix stage has only the two scalar
idempotents. -/
theorem stageZero_idempotent_eq_zero_or_one {P : Stage 0}
    (hP : P * P = P) : P = 0 ∨ P = 1 := by
  have he := congrArg (fun M : Stage 0 => M default default) hP
  have hr : P default default * P default default = P default default := by
    change (∑ k : Idx 0, P default k * P k default) = P default default at he
    have hsum : (∑ k : Idx 0, P default k * P k default) =
        P default default * P default default :=
      Fintype.sum_subsingleton
        (fun k : Idx 0 => P default k * P k default) (default : Idx 0)
    exact hsum.symm.trans he
  have hz : P default default * (P default default - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h0 | h1
  · left
    ext i j
    have hi : i = default := Subsingleton.elim _ _
    have hj : j = default := Subsingleton.elim _ _
    subst i
    subst j
    exact h0
  · right
    have h1' : P default default = 1 := by linarith
    ext i j
    have hi : i = default := Subsingleton.elim _ _
    have hj : j = default := Subsingleton.elim _ _
    subst i
    subst j
    simpa only [Matrix.one_apply_eq] using h1'

/-- Coherence from the scalar stage forces the entire idempotent family
to be the zero family or the unit family. -/
theorem coherent_idempotent_family_trivial (P : ∀ n, Stage n)
    (h0 : P 0 * P 0 = P 0)
    (hcoh : ∀ n, stageEmbed n (P n) = P (n + 1)) :
    (∀ n, P n = 0) ∨ (∀ n, P n = 1) := by
  rcases stageZero_idempotent_eq_zero_or_one h0 with hz | ho
  · left
    intro n
    induction n with
    | zero => exact hz
    | succ n ih => rw [← hcoh n, ih, map_zero]
  · right
    intro n
    induction n with
    | zero => exact ho
    | succ n ih => rw [← hcoh n, ih, map_one]

/-- In particular, the proposed coherent stage-zero seed cannot support
a nonzero off-diagonal Peirce block at any later stage. -/
theorem coherent_stageZero_corners_vanish (P : ∀ n, Stage n)
    (h0 : P 0 * P 0 = P 0)
    (hcoh : ∀ n, stageEmbed n (P n) = P (n + 1))
    (n : ℕ) (X : Stage n) :
    conePlus (P n) X = 0 ∧ coneMinus (P n) X = 0 := by
  rcases coherent_idempotent_family_trivial P h0 hcoh with hz | ho
  · simp [hz n, conePlus, coneMinus]
  · simp [ho n, conePlus, coneMinus]

/-- The cubic noncommuting correction is nonzero on the actual two-by-two
creation/annihilation pair. -/
theorem witt_cubic_residual_ne_zero :
    wittCreationBase * wittAnnihilationBase * wittCreationBase ≠ 0 := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [wittCreationBase, wittAnnihilationBase, Matrix.mul_apply,
    Fin.sum_univ_two] at he

end InfoGeometry.Canonical.TensorNilpotentCalculus
