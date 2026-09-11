import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

/-!
# Block form of the Witt-skew endomorphisms

For a doubled carrier `V ⊕ V*` with neutral pairing
`η_W = [[0, I], [I, 0]]`, this owner records the exact block constraint on
an infinitesimal orthogonal endomorphism.  It is deliberately independent of
the exceptional derivation subalgebra: the latter is a further multiplication-
preserving constraint inside this 28-dimensional orthogonal space.
-/

namespace InfoGeometry.Canonical.ZornWittEndomorphismBlockBridge

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

structure Block (n : ℕ) where
  A : Square n
  B : Square n
  C : Square n
  D : Square n

def blockNeg {n : ℕ} (T : Block n) : Block n :=
  ⟨-T.A, -T.B, -T.C, -T.D⟩

def wittAdjoint {n : ℕ} (T : Block n) : Block n :=
  ⟨T.D.transpose, T.B.transpose, T.C.transpose, T.A.transpose⟩

theorem block_ext {n : ℕ} {T U : Block n}
    (hA : T.A = U.A) (hB : T.B = U.B)
    (hC : T.C = U.C) (hD : T.D = U.D) : T = U := by
  cases T
  cases U
  simp_all

theorem wittSkew_iff {n : ℕ} (T : Block n) :
    wittAdjoint T = blockNeg T ↔
      T.D = -T.A.transpose ∧
        T.B.transpose = -T.B ∧
        T.C.transpose = -T.C := by
  constructor
  · intro h
    have hA := congrArg Block.A h
    have hB := congrArg Block.B h
    have hC := congrArg Block.C h
    have hD := congrArg Block.D h
    have hD' : T.A.transpose = -T.D := by
      simpa [wittAdjoint, blockNeg] using hD
    exact ⟨by
        calc
          T.D = -(-T.D) := by simp
          _ = -(T.A.transpose) := by rw [← hD'],
      by simpa [wittAdjoint, blockNeg] using hB,
      by simpa [wittAdjoint, blockNeg] using hC⟩
  · rintro ⟨hD, hB, hC⟩
    apply block_ext
    · have hDt := congrArg Matrix.transpose hD
      simpa using hDt
    · simpa [wittAdjoint, blockNeg] using hB
    · simpa [wittAdjoint, blockNeg] using hC
    · have hD' : T.A.transpose = -T.D := by
        calc
          T.A.transpose = -(-T.A.transpose) := by simp
          _ = -T.D := by rw [← hD]
      simpa [wittAdjoint, blockNeg] using hD'

theorem wittSkew_iff_block_form {n : ℕ} (T : Block n) :
    wittAdjoint T = blockNeg T ↔
      ∃ A B C : Square n,
        T = ⟨A, B, C, -A.transpose⟩ ∧
          B.transpose = -B ∧ C.transpose = -C := by
  rw [wittSkew_iff]
  constructor
  · rintro ⟨hD, hB, hC⟩
    refine ⟨T.A, T.B, T.C, ?_, hB, hC⟩
    cases T
    simp_all
  · rintro ⟨A, B, C, hT, hB, hC⟩
    subst hT
    exact ⟨rfl, hB, hC⟩

end InfoGeometry.Canonical.ZornWittEndomorphismBlockBridge
