/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ElementaryMatrixOperators
import InfoGeometry.Core.PeirceDefect
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The ordered roundtrip of two elementary shears

The input word is `V⁻¹ U⁻¹ V U`, where `U` and `V` are the existing native
elementary matrix units. Its coordinate formula retains arbitrary associative
coefficient rings and every multiplication order. Trace and determinant
readouts specialize to commutative coefficients; nonnilpotency specializes to
real coefficients.

In particular, two unipotent shears can have a roundtrip whose difference from
identity is not nilpotent. This finite matrix statement supplies neither a
connection nor a topological monodromy representation. Separate explicit
countermodels distinguish square-zero perturbations from idempotency defects.
-/

namespace InfoGeometry.Algebra.ElementaryShearRoundtrip

open Matrix ElementaryMatrixOperators
open InfoGeometry.Core.IdempotencyDefect InfoGeometry.Core.PeirceDefect

section Ring

variable {R : Type*} [Ring R]

/-- The precise order in the intake, built from actual units with certified inverses. -/
def roundtrip (a b : R) : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  (elementaryUnit 1 0 (by decide) b)⁻¹ *
    (elementaryUnit 0 1 (by decide) a)⁻¹ *
    elementaryUnit 1 0 (by decide) b * elementaryUnit 0 1 (by decide) a

/-- Complete ordered formula over a possibly noncommutative coefficient ring. -/
theorem coe_roundtrip (a b : R) :
    (roundtrip a b : Matrix (Fin 2) (Fin 2) R) =
      !![1 - a * b, -(a * b * a); b * a * b, 1 + b * a + b * a * b * a] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [roundtrip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single] <;>
    noncomm_ring

/-- In a noncommutative coefficient ring both ordered products must vanish. -/
theorem roundtrip_eq_one_iff (a b : R) :
    roundtrip a b = 1 ↔ a * b = 0 ∧ b * a = 0 := by
  constructor
  · intro h
    have hm : (roundtrip a b : Matrix (Fin 2) (Fin 2) R) = 1 :=
      congrArg Units.val h
    rw [coe_roundtrip] at hm
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) hm
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 1) hm
    have hab : a * b = 0 := by
      simpa using h00
    have hquartic : b * a * b * a = 0 := by
      rw [mul_assoc b a b, hab, mul_zero, zero_mul]
    have hba : b * a = 0 := by
      simpa [hquartic] using h11
    exact ⟨hab, hba⟩
  · rintro ⟨hab, hba⟩
    apply Units.ext
    rw [coe_roundtrip]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hab, hba]

/-- Opposite elementary units remain noncommuting over every nontrivial ring. -/
theorem opposite_elementaryUnits_not_commute [Nontrivial R] :
    (elementaryUnit (n := Fin 2) 0 1 (by decide) (1 : R) :
        Matrix (Fin 2) (Fin 2) R) *
      (elementaryUnit (n := Fin 2) 1 0 (by decide) (1 : R) :
        Matrix (Fin 2) (Fin 2) R) ≠
      (elementaryUnit (n := Fin 2) 1 0 (by decide) (1 : R) :
        Matrix (Fin 2) (Fin 2) R) *
      (elementaryUnit (n := Fin 2) 0 1 (by decide) (1 : R) :
        Matrix (Fin 2) (Fin 2) R) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single] at h00

/-- Actual elementary units give noncommuting unipotents without any
commutativity assumption on the coefficient ring. -/
theorem exists_noncommuting_unipotents [Nontrivial R] :
    ∃ U V : Matrix (Fin 2) (Fin 2) R,
      U * V ≠ V * U ∧ (U - 1) * (U - 1) = 0 ∧ (V - 1) * (V - 1) = 0 := by
  refine ⟨(elementaryUnit (n := Fin 2) 0 1 (by decide) (1 : R) :
      Matrix (Fin 2) (Fin 2) R),
    (elementaryUnit (n := Fin 2) 1 0 (by decide) (1 : R) :
      Matrix (Fin 2) (Fin 2) R),
    opposite_elementaryUnits_not_commute, ?_, ?_⟩
  · simp
  · simp

/-- The product of the two native roots is an idempotent. -/
theorem upperRoot_mul_lowerRoot_idempotent :
    IsIdempotentElem
      ((upperRoot : Matrix (Fin 2) (Fin 2) R) * lowerRoot) := by
  change (_ : Matrix (Fin 2) (Fin 2) R) * _ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperRoot, lowerRoot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

/-- A one-sided square-zero direction preserves this native projector. -/
theorem projector_add_upperRoot_idempotent :
    IsIdempotentElem
      ((upperRoot : Matrix (Fin 2) (Fin 2) R) * lowerRoot + upperRoot) := by
  change (_ : Matrix (Fin 2) (Fin 2) R) * _ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperRoot, lowerRoot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

/-- The perturbation in the preceding theorem is nonzero in every nontrivial ring. -/
theorem upperRoot_ne_zero [Nontrivial R] :
    (upperRoot : Matrix (Fin 2) (Fin 2) R) ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) h
  simp [upperRoot, Matrix.single] at h01

/-- The same perturbation is square-zero, not merely singular. -/
theorem upperRoot_mul_self :
    (upperRoot : Matrix (Fin 2) (Fin 2) R) * upperRoot = 0 :=
  single_mul_self_eq_zero 0 1 (by decide) 1

/-- A complete counterexample to obligatory loss of idempotency, in every
nontrivial coefficient ring. -/
theorem exists_nonzero_square_zero_preserving_idempotence [Nontrivial R] :
    ∃ p n : Matrix (Fin 2) (Fin 2) R,
      IsIdempotentElem p ∧ n ≠ 0 ∧ n * n = 0 ∧ IsIdempotentElem (p + n) := by
  exact ⟨upperRoot * lowerRoot, upperRoot, upperRoot_mul_lowerRoot_idempotent,
    upperRoot_ne_zero, upperRoot_mul_self, projector_add_upperRoot_idempotent⟩

/-- An explicit square-zero perturbation with identity defect, over any ring.
In a nontrivial coefficient ring the identity is not nilpotent. -/
theorem exists_square_zero_with_identity_defect :
    ∃ p n : Matrix (Fin 2) (Fin 2) R,
      IsIdempotentElem p ∧ n * n = 0 ∧ defect (p + n) = 1 := by
  refine ⟨upperRoot * lowerRoot, !![1, 1; -1, -1], ?_, ?_, ?_⟩
  all_goals
    first | change (_ : Matrix (Fin 2) (Fin 2) R) * _ = _ | skip
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [defect, upperRoot, lowerRoot, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.single] <;> noncomm_ring

/-- The identity-defect example refutes nilpotency of the defect in every
nontrivial coefficient ring. -/
theorem exists_square_zero_with_nonnilpotent_defect [Nontrivial R] :
    ∃ p n : Matrix (Fin 2) (Fin 2) R,
      IsIdempotentElem p ∧ n * n = 0 ∧ ¬ IsNilpotent (defect (p + n)) := by
  obtain ⟨p, n, hp, hn, hd⟩ := exists_square_zero_with_identity_defect (R := R)
  refine ⟨p, n, hp, hn, ?_⟩
  rintro ⟨k, hk⟩
  simp [hd] at hk

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-- The group roundtrip remains a determinant-one matrix. -/
theorem det_roundtrip (a b : R) :
    Matrix.det (roundtrip a b : Matrix (Fin 2) (Fin 2) R) = 1 := by
  rw [coe_roundtrip, Matrix.det_fin_two]
  change (1 - a * b) * (1 + b * a + b * a * b * a) -
    (-(a * b * a)) * (b * a * b) = 1
  ring

/-- The trace detects the fourth-order term missing from the proposed linear loop. -/
theorem trace_roundtrip (a b : R) :
    Matrix.trace (roundtrip a b : Matrix (Fin 2) (Fin 2) R) = 2 + (a * b) ^ 2 := by
  rw [coe_roundtrip]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

theorem det_roundtrip_sub_one (a b : R) :
    Matrix.det ((roundtrip a b : Matrix (Fin 2) (Fin 2) R) - 1) = -(a * b) ^ 2 := by
  rw [coe_roundtrip, Matrix.det_fin_two]
  simp
  ring

end CommRing

section Real

/-- A concrete real pair is simultaneously unipotent and noncommuting. -/
theorem exists_real_noncommuting_unipotents :
    ∃ U V : Matrix (Fin 2) (Fin 2) ℝ,
      U * V ≠ V * U ∧ (U - 1) * (U - 1) = 0 ∧ (V - 1) * (V - 1) = 0 := by
  exact exists_noncommuting_unipotents

/-- With nonzero parameter product, the roundtrip is not a unipotent operator. -/
theorem roundtrip_sub_one_not_nilpotent {a b : ℝ} (hab : a * b ≠ 0) :
    ¬ IsNilpotent ((roundtrip a b : Matrix (Fin 2) (Fin 2) ℝ) - 1) := by
  intro hn
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hn).eq_zero
  rw [Matrix.trace_sub, trace_roundtrip] at ht
  have htrace : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
    simp [Matrix.trace]
  rw [htrace, add_sub_cancel_left] at ht
  exact hab (eq_zero_of_pow_eq_zero ht)

/-- The real unit-parameter loop is an explicit non-unipotent example. -/
theorem roundtrip_one_one :
    (roundtrip (1 : ℝ) 1 : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 3] := by
  rw [coe_roundtrip]
  norm_num

end Real

end InfoGeometry.Algebra.ElementaryShearRoundtrip
