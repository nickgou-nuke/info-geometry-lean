/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.AlbertJordanThreeGenerationFreudenthal

/-!
# Audit: Раздел 137 — 27-Мерна Изключителна Албертова Алгебра 𝔍₃(𝕆_s) и Детерминант на Фройдентал
Concrete `ℤ` checks for `InfoGeometry.Superalgebra.AlbertJordanFreudenthal`.
-/

namespace InfoGeometry.Superalgebra.AlbertJordanFreudenthalAudit

open InfoGeometry.Superalgebra.AlbertJordanFreudenthal

def sampleX : SplitOctonion ℤ := ⟨1, ⟨1, 2, 0⟩, ⟨0, 1, -1⟩, 2⟩
def sampleY : SplitOctonion ℤ := ⟨-1, ⟨0, 1, 3⟩, ⟨2, 0, 1⟩, 1⟩
def sampleZ : SplitOctonion ℤ := ⟨2, ⟨-1, 0, 2⟩, ⟨1, -2, 0⟩, -1⟩

theorem audit_octonion_nonassociative_but_trace_associative_int :
    SplitOctonion.associator sampleX sampleY sampleZ ≠ SplitOctonion.zero ∧
    SplitOctonion.trace (SplitOctonion.associator sampleX sampleY sampleZ) = 0 := by decide

theorem audit_trace_mul_assoc_int :
    SplitOctonion.trace (SplitOctonion.mul (SplitOctonion.mul sampleX sampleY) sampleZ) =
      SplitOctonion.trace (SplitOctonion.mul sampleX (SplitOctonion.mul sampleY sampleZ)) ∧
    SplitOctonion.trace (SplitOctonion.mul (SplitOctonion.mul sampleX sampleY) sampleZ) = -10 := by
  decide

theorem audit_freudenthal_det_parenthesis_invariant_int :
    let M : AlbertMatrix27 ℤ := ⟨2, 3, 5, sampleX, sampleY, sampleZ⟩
    AlbertMatrix27.freudenthalDetLeft M = AlbertMatrix27.freudenthalDetRight M ∧
    AlbertMatrix27.freudenthalDetLeft M = 37 := by decide

theorem audit_three_generation_baryon_unification_int :
    let u1 : ColorVec3 ℤ := ⟨1, 0, 0⟩
    let u2 : ColorVec3 ℤ := ⟨0, 2, 0⟩
    let u3 : ColorVec3 ℤ := ⟨0, 0, 3⟩
    AlbertMatrix27.freudenthalDetLeft
      (AlbertMatrix27.threeGenerationQuarkMatrix (2 : ℤ) 3 5 u1 u2 u3) =
      2 * 3 * 5 + ColorVec3.det3 u1 u2 u3 ∧
    AlbertMatrix27.freudenthalDetLeft
      (AlbertMatrix27.threeGenerationQuarkMatrix (2 : ℤ) 3 5 u1 u2 u3) = 36 := by decide

end InfoGeometry.Superalgebra.AlbertJordanFreudenthalAudit
