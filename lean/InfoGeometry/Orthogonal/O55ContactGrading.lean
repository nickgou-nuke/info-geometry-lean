/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Orthogonal.O55ContactLie
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Native contact grading of the split orthogonal endomorphism lane. -/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

def endCommutator (A B : End55) : End55 := A * B - B * A

@[simp] theorem endCommutator_apply (A B : End55) (x : Vector55) :
    endCommutator A B x = A (B x) - B (A x) := rfl

def IsContactGrade (k : ℤ) (A : O55Lie) : Prop :=
  endCommutator contactEulerEnd (A : End55) =
    (k : ℝ) • (A : End55)

def realContactGradeSpace (k : ℤ) : Submodule ℝ O55Lie where
  carrier := {A | IsContactGrade k A}
  zero_mem' := by simp [IsContactGrade, endCommutator]
  add_mem' := by
    intro A B hA hB
    change IsContactGrade k A at hA
    change IsContactGrade k B at hB
    unfold IsContactGrade at hA hB ⊢
    change endCommutator contactEulerEnd
        ((A : End55) + (B : End55)) =
      (k : ℝ) • ((A : End55) + (B : End55))
    have hadd : endCommutator contactEulerEnd
        ((A : End55) + (B : End55)) =
        endCommutator contactEulerEnd (A : End55) +
          endCommutator contactEulerEnd (B : End55) := by
      unfold endCommutator
      noncomm_ring
    rw [hadd, hA, hB]
    module
  smul_mem' := by
    intro c A hA
    change IsContactGrade k A at hA
    unfold IsContactGrade at hA ⊢
    change endCommutator contactEulerEnd
        (c • (A : End55)) =
      (k : ℝ) • (c • (A : End55))
    have hsmul : endCommutator contactEulerEnd (c • (A : End55)) =
        c • endCommutator contactEulerEnd (A : End55) := by
      unfold endCommutator
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
        smul_sub]
    rw [hsmul, hA]
    module

@[simp] theorem mem_realContactGradeSpace_iff (k : ℤ) (A : O55Lie) :
    A ∈ realContactGradeSpace k ↔ IsContactGrade k A := Iff.rfl

theorem endCommutator_derivation (A B : End55) :
    endCommutator contactEulerEnd (endCommutator A B) =
      endCommutator (endCommutator contactEulerEnd A) B +
        endCommutator A (endCommutator contactEulerEnd B) := by
  unfold endCommutator
  simp only [mul_sub, sub_mul]
  noncomm_ring

theorem contactGrade_bracket
    {k l : ℤ} {A B : O55Lie}
    (hA : A ∈ realContactGradeSpace k) (hB : B ∈ realContactGradeSpace l) :
    ⁅A, B⁆ ∈ realContactGradeSpace (k + l) := by
  change IsContactGrade (k + l) ⁅A, B⁆
  change IsContactGrade k A at hA
  change IsContactGrade l B at hB
  unfold IsContactGrade at hA hB ⊢
  change endCommutator contactEulerEnd
      (⁅(A : End55), (B : End55)⁆) =
    ((k + l : ℤ) : ℝ) • ⁅(A : End55), (B : End55)⁆
  change endCommutator contactEulerEnd
      (endCommutator (A : End55) (B : End55)) =
    ((k + l : ℤ) : ℝ) • endCommutator (A : End55) (B : End55)
  rw [endCommutator_derivation]
  change endCommutator contactEulerEnd (A : End55) =
      (k : ℝ) • (A : End55) at hA
  change endCommutator contactEulerEnd (B : End55) =
      (l : ℝ) • (B : End55) at hB
  rw [hA, hB]
  simp only [endCommutator, smul_sub, smul_mul_assoc, mul_smul_comm]
  module



/-- Crosscap conjugation reverses the represented contact grade. -/
theorem crosscap_reverses_grade {k : ℤ} {A : O55Lie}
    (hA : A ∈ realContactGradeSpace k) :
    crosscapConjugation A ∈ realContactGradeSpace (-k) := by
  change IsContactGrade (-k) (crosscapConjugation A)
  change endCommutator contactEulerEnd
      (crosscapEnd * (A : End55) * crosscapEnd) =
    ((-k : ℤ) : ℝ) • (crosscapEnd * (A : End55) * crosscapEnd)
  apply LinearMap.ext
  intro v
  simp only [endCommutator_apply, Module.End.mul_apply, Pi.smul_apply]
  change contactEulerEnd (crosscapEnd ((A : End55) (crosscapEnd v))) -
      crosscapEnd ((A : End55) (crosscapEnd (contactEulerEnd v))) =
    ((-k : ℤ) : ℝ) • crosscapEnd ((A : End55) (crosscapEnd v))
  have hce (w : Vector55) :
      contactEulerEnd (crosscapEnd w) = -crosscapEnd (contactEulerEnd w) := by
    simpa only [Module.End.mul_apply, Pi.neg_apply, LinearMap.neg_apply] using
      LinearMap.congr_fun crosscap_anticommutes_euler w
  have hg (w : Vector55) :
      contactEulerEnd ((A : End55) w) - (A : End55) (contactEulerEnd w) =
        (k : ℝ) • (A : End55) w := by
    change endCommutator contactEulerEnd (A : End55) w = ((k : ℝ) • (A : End55)) w
    have h := LinearMap.congr_fun hA w
    simpa [IsContactGrade, endCommutator_apply] using h
  rw [hce ((A : End55) (crosscapEnd v))]
  have hgv0 := hg (crosscapEnd v)
  rw [hce v] at hgv0
  rw [LinearMap.map_neg] at hgv0
  have hgv :
      contactEulerEnd ((A : End55) (crosscapEnd v)) +
          (A : End55) (crosscapEnd (contactEulerEnd v)) =
        (k : ℝ) • (A : End55) (crosscapEnd v) := by
    simpa only [sub_neg_eq_add] using hgv0
  have hsum :
      -crosscapEnd (contactEulerEnd ((A : End55) (crosscapEnd v))) -
          crosscapEnd ((A : End55) (crosscapEnd (contactEulerEnd v))) =
        -(crosscapEnd (contactEulerEnd ((A : End55) (crosscapEnd v))) +
          crosscapEnd ((A : End55) (crosscapEnd (contactEulerEnd v)))) := by
    abel
  rw [hsum, ← map_add, hgv]
  simp

end InfoGeometry.Orthogonal.O55Contact
