/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Preservation of a split form and growth with iteration depth

The carrier is the native product `E × E`, and powers are composition powers
in `Module.End ℝ (E × E)`. For any real bilinear form `B`, the difference of
its pullbacks along the two projections gives the split form `B ⊕ -B`.
The operator `c I + s swap` preserves that form when `c² - s² = 1`.

At `c = 5/4`, `s = 3/4`, every nonzero diagonal vector doubles in each step.
The norm statements use Mathlib's native product sup norm, not the Hilbert
direct-sum norm. They require neither finite dimension nor completeness.
The form-preservation calculation requires no symmetry or nondegeneracy of
`B`; an indefinite metric interpretation requires those separate hypotheses.
-/

noncomputable section

namespace InfoGeometry.Krein.HyperbolicDepth

variable {E : Type*}

section Algebraic

variable [AddCommGroup E] [Module ℝ E]

/-- The split form, constructed by native bilinear pullbacks. -/
def splitForm (B : LinearMap.BilinForm ℝ E) : LinearMap.BilinForm ℝ (E × E) :=
  B.comp (LinearMap.fst ℝ E E) (LinearMap.fst ℝ E E) -
    B.comp (LinearMap.snd ℝ E E) (LinearMap.snd ℝ E E)

@[simp] theorem splitForm_apply (B : LinearMap.BilinForm ℝ E) (u v : E × E) :
    splitForm B u v = B u.1 v.1 - B u.2 v.2 := rfl

/-- The diagonal is totally isotropic for the split bilinear form. -/
@[simp] theorem splitForm_diagonal (B : LinearMap.BilinForm ℝ E) (v w : E) :
    splitForm B (v, v) (w, w) = 0 := by
  simp

/-- A concrete linear operator on the entire product module; the exchange
operator is Mathlib's native product commutation equivalence. -/
def boost (c s : ℝ) : Module.End ℝ (E × E) :=
  c • (1 : Module.End ℝ (E × E)) +
    s • (LinearEquiv.prodComm ℝ E E).toLinearMap

@[simp] theorem boost_apply (c s : ℝ) (u : E × E) :
    boost c s u = (c • u.1 + s • u.2, s • u.1 + c • u.2) := by
  ext <;> simp [boost, add_comm]

/-- Exact form transport before imposing the hyperbola relation. -/
theorem splitForm_boost (B : LinearMap.BilinForm ℝ E) (c s : ℝ) (u v : E × E) :
    splitForm B (boost c s u) (boost c s v) =
      (c ^ 2 - s ^ 2) * splitForm B u v := by
  simp only [splitForm_apply, boost_apply, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  simp only [pow_two, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  rw [mul_comm s c]
  abel

/-- The hyperbola condition preserves the whole bilinear form, not only a
particular quadratic value or a selected invariant vector. -/
theorem boost_preserves_splitForm (B : LinearMap.BilinForm ℝ E) (c s : ℝ)
    (hcs : c ^ 2 - s ^ 2 = 1) (u v : E × E) :
    splitForm B (boost c s u) (boost c s v) = splitForm B u v := by
  rw [splitForm_boost, hcs, one_mul]

/-- Form preservation persists under actual operator composition powers. -/
theorem boost_pow_preserves_splitForm (B : LinearMap.BilinForm ℝ E) (c s : ℝ)
    (hcs : c ^ 2 - s ^ 2 = 1) (n : ℕ) (u v : E × E) :
    splitForm B ((boost c s ^ n) u) ((boost c s ^ n) v) = splitForm B u v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply,
        boost_preserves_splitForm B c s hcs]
      exact ih

/-- The diagonal subspace has multiplier `c + s`. -/
theorem boost_diagonal (c s : ℝ) (v : E) :
    boost c s (v, v) = (c + s) • (v, v) := by
  ext <;> simp [boost_apply, add_smul, add_comm]

/-- Native endomorphism powers give the exact finite-depth action. -/
theorem boost_pow_diagonal (c s : ℝ) (n : ℕ) (v : E) :
    (boost c s ^ n) (v, v) = (c + s) ^ n • (v, v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, boost_diagonal, map_smul, ih, smul_smul]
      rw [pow_succ']

/-- The normalized boost with coupling `s/c = 3/5`. -/
def doublingBoost : Module.End ℝ (E × E) := boost (5 / 4) (3 / 4)

/-- This fixed, finite one-step boost preserves the form at every depth. -/
theorem doublingBoost_pow_preserves_splitForm (B : LinearMap.BilinForm ℝ E)
    (n : ℕ) (u v : E × E) :
    splitForm B ((doublingBoost ^ n) u) ((doublingBoost ^ n) v) = splitForm B u v := by
  exact boost_pow_preserves_splitForm B (5 / 4) (3 / 4) (by norm_num) n u v

/-- The same form-preserving powers amplify a whole null subspace. -/
theorem doublingBoost_pow_diagonal (n : ℕ) (v : E) :
    (doublingBoost ^ n) (v, v) = (2 : ℝ) ^ n • (v, v) := by
  have hc : (5 / 4 : ℝ) + 3 / 4 = 2 := by norm_num
  simpa only [doublingBoost, hc] using boost_pow_diagonal (5 / 4) (3 / 4) n v

end Algebraic

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact orbit norm in the native product sup norm. -/
theorem norm_doublingBoost_pow_diagonal (n : ℕ) (v : E) :
    ‖(doublingBoost ^ n) (v, v)‖ = (2 : ℝ) ^ n * ‖v‖ := by
  rw [doublingBoost_pow_diagonal, norm_smul]
  simp

/-- Every proposed depth-independent bound is exceeded after finitely many
iterations, although the same operator preserves the split form. -/
theorem exists_norm_doublingBoost_pow_gt (v : E) (hv : v ≠ 0) (C : ℝ) :
    ∃ n : ℕ, C < ‖(doublingBoost ^ n) (v, v)‖ := by
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖v‖) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n, ?_⟩
  rw [norm_doublingBoost_pow_diagonal]
  exact (div_lt_iff₀ hnorm).mp hn

end Normed

end InfoGeometry.Krein.HyperbolicDepth
