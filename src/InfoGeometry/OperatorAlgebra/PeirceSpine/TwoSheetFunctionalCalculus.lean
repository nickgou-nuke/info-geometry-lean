/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Tactic.Module

/-!
# Two-sheet functional calculus in the ambient noncommutative algebra

The existing Peirce corners remain the directed operator inputs. A two-sheet
coefficient has a finite spectrum, but neither the algebra nor its arbitrary
off-diagonal inputs are assumed commutative. Functional calculus is evaluated
on a self-adjoint projection, rather than postulated as a logarithm formula.
The algebraic identities do not require a star, positivity, or a trace.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

section Algebra

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- A coefficient with independently weighted complementary Peirce sheets. -/
def twoSheet (P : B) (a b : ℝ) : B := a • P + b • (1 - P)

theorem twoSheet_affine (P : B) (a b : ℝ) :
    twoSheet P a b = b • (1 : B) + (a - b) • P := by
  simp only [twoSheet, smul_sub, sub_smul]
  abel

/-- The central mean and the oriented sheet difference in the original grading. -/
theorem twoSheet_chiral (P : B) (a b : ℝ) :
    twoSheet P a b = ((a + b) / 2) • (1 : B) + ((a - b) / 2) • invS P := by
  simp only [twoSheet, invS, smul_sub]
  module

@[simp] theorem twoSheet_equal (P : B) (a : ℝ) :
    twoSheet P a a = a • (1 : B) := by
  rw [twoSheet_affine, sub_self, zero_smul, add_zero]

theorem twoSheet_mul (P : B) (hP : P * P = P) (a b c d : ℝ) :
    twoSheet P a b * twoSheet P c d = twoSheet P (a * c) (b * d) := by
  simp only [twoSheet, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    mul_sub, sub_mul, mul_one, one_mul, hP]
  module

/-- Central scalar parts disappear from the commutator. -/
theorem comm_twoSheet (P X : B) (a b : ℝ) :
    comm (twoSheet P a b) X = (a - b) • comm P X := by
  simp only [twoSheet, comm, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, smul_sub, sub_smul]
  abel

theorem comm_twoSheet_phi (P : B) (hP : P * P = P) (A C : B) (a b : ℝ) :
    comm (twoSheet P a b) (genPhi P A C) = (a - b) • genJ P A C := by
  rw [comm_twoSheet]
  congr 1
  peirce_nf hP

theorem comm_twoSheet_current (P : B) (hP : P * P = P) (A C : B) (a b : ℝ) :
    comm (twoSheet P a b) (genJ P A C) = (a - b) • genPhi P A C := by
  rw [comm_twoSheet]
  congr 1
  peirce_nf hP

/-- The same two-sheet coefficient on both sides scales every odd input. -/
theorem twoSheet_sandwich_phi (P : B) (hP : P * P = P)
    (A C : B) (a b : ℝ) :
    twoSheet P a b * genPhi P A C * twoSheet P a b =
      (a * b) • genPhi P A C := by
  simp only [twoSheet, genPhi, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm]
  simp only [mul_sub, sub_mul, one_mul, mul_one,
    P_mul_conePlus hP, P_mul_coneMinus hP, conePlus_mul_P hP,
    coneMinus_mul_P hP, zero_mul, smul_zero,
    smul_sub, smul_add, smul_smul]
  module

end Algebra

section FunctionalCalculus

variable {B : Type*} [CStarAlgebra B] {P : B}

/-- Every scalar function on a projection is its exact two-point interpolant. -/
theorem cfc_projection_twoSheet (hP : IsStarProjection P) (f : ℝ → ℝ) :
    cfc f P = twoSheet P (f 1) (f 0) := by
  have heq : (spectrum ℝ P).EqOn f (fun x => f 0 + (f 1 - f 0) * x) := by
    intro x hx
    have hx' := hP.isIdempotentElem.spectrum_subset ℝ hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl <;> simp
  rw [cfc_congr heq,
    cfc_const_add (f 0) (fun x => (f 1 - f 0) * x) P (by fun_prop) hP.isSelfAdjoint,
    cfc_const_mul_id (f 1 - f 0) P hP.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one, twoSheet_affine]

/-- Genuine continuous functional calculus of a two-sheet operator, valid
also at coincident sheet weights. Finite spectra make every restricted
scalar function continuous. -/
theorem cfc_twoSheet (hP : IsStarProjection P) (a b : ℝ) (f : ℝ → ℝ) :
    cfc f (twoSheet P a b) = twoSheet P (f a) (f b) := by
  let g : ℝ → ℝ := fun x => b + (a - b) * x
  have hg : cfc g P = twoSheet P a b := by
    rw [cfc_projection_twoSheet hP]
    simp [g]
  have hf : ContinuousOn f (g '' spectrum ℝ P) :=
    ((hP.isIdempotentElem.finite_spectrum ℝ).image g).continuousOn f
  rw [← hg, ← cfc_comp f g P hP.isSelfAdjoint hf,
    cfc_projection_twoSheet hP]
  simp [g]

/-- Positive sheet weights give a strictly positive operator, proved by
spectral mapping rather than assumed as a structure field. -/
theorem twoSheet_isStrictlyPositive [PartialOrder B] [StarOrderedRing B]
    (hP : IsStarProjection P) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IsStrictlyPositive (twoSheet P p q) := by
  let g : ℝ → ℝ := fun x => q + (p - q) * x
  have hg : cfc g P = twoSheet P p q := by
    rw [cfc_projection_twoSheet hP]
    simp [g]
  rw [← hg]
  apply (cfc_isStrictlyPositive_iff g P (by fun_prop) hP.isSelfAdjoint).2
  intro x hx
  have hx' := hP.isIdempotentElem.spectrum_subset ℝ hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
  rcases hx' with rfl | rfl
  · simpa [g] using hq
  · simpa [g] using hp

/-- The two-sheet expression is the native negative CFC logarithm.
This total identity uses `Real.log` at all weights. The usual positive
operator-logarithm interpretation requires positive sheet weights. -/
theorem neg_log_twoSheet (hP : IsStarProjection P) (p q : ℝ) :
    -CFC.log (twoSheet P p q) = twoSheet P (-Real.log p) (-Real.log q) := by
  rw [CFC.log, cfc_twoSheet hP]
  simp only [twoSheet, neg_smul, neg_add_rev]
  abel

/-- Canonical central/chiral normal form of the actual sheet logarithm. -/
theorem neg_log_twoSheet_chiral (hP : IsStarProjection P) (p q : ℝ) :
    -CFC.log (twoSheet P p q) =
      (-((Real.log p + Real.log q) / 2)) • (1 : B) -
        ((Real.log p - Real.log q) / 2) • invS P := by
  rw [neg_log_twoSheet hP, twoSheet_chiral]
  module

/-- The volume logarithm cannot generate a commutator with the deformation
whose square defines it. The theorem uses total CFC: outside its self-adjoint
domain it may return zero. For self-adjoint `Φ` and nonnegative `β`, the
argument is strictly positive and the same identity concerns its genuine log. -/
theorem volume_log_commutes (Φ : B) (β : ℝ) :
    Commute (CFC.log (1 + β • (Φ * Φ))) Φ := by
  apply Commute.cfc_real
  exact (Commute.one_left Φ).add_left ((Commute.refl Φ).mul_left
    (Commute.refl Φ) |>.smul_left β)

end FunctionalCalculus

end InfoGeometry.OperatorAlgebra.PeirceSpine
