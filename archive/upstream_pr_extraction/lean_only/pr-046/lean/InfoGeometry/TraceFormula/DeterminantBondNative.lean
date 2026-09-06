import InfoGeometry.Algebra.PrimonColimitAlgebra

/-!
# Native determinant law for the Primon matrix bond

The `BitWord (n + 1)` presentation of the bond is a reindexed Kronecker
product.  This file records that identification and discharges the resulting
determinant law with Mathlib's native `det_reindex` and `det_kronecker`.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.DeterminantBondNative

open Matrix
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.PrimonColimitAlgebra

def bitWordSuccEquiv (n : ℕ) : BitWord (n + 1) ≃ BitWord n × Bool := by
  exact {
    toFun := fun w => (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩)
    invFun := fun p => extendSucc n p.1 p.2
    left_inv := by
      intro w
      ext i
      by_cases h : (i : ℕ) < n
      · simp [prefixSucc, extendSucc, h]
      · have hi : i = Fin.last n := Fin.eq_last_of_not_lt h
        subst i
        dsimp [prefixSucc, extendSucc]
        rw [dif_neg (lt_irrefl n)]
        rfl
    right_inv := by
      rintro ⟨w, b⟩
      apply Prod.ext
      · exact prefixSucc_extendSucc n w b
      · simp [extendSucc]
  }

lemma matrixBondFun_eq_reindex_kronecker (n : ℕ) (M : MatrixStage n) :
    matrixBondFun n M =
      Matrix.reindex (bitWordSuccEquiv n).symm (bitWordSuccEquiv n).symm
        (Matrix.kronecker M (1 : Matrix Bool Bool ℝ)) := by
  ext v w
  dsimp [matrixBondFun]
  by_cases h : v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩
  · rw [if_pos h]
    simp [Matrix.one_apply, bitWordSuccEquiv, h]
  · rw [if_neg h]
    have hbits : (bitWordSuccEquiv n v).2 ≠ (bitWordSuccEquiv n w).2 := by
      simpa [bitWordSuccEquiv] using h
    have hp : (prefixSucc n v, v ⟨n, Nat.lt_succ_self n⟩) ≠
        (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩) := by
      intro heq
      exact h (congrArg Prod.snd heq)
    simp [Matrix.one_apply, bitWordSuccEquiv, hbits, hp]
    intro h'
    exact (h h').elim

theorem matrixBond_det_native (n : ℕ) (M : MatrixStage n) :
    Matrix.det (matrixBond n M) = (Matrix.det M) ^ 2 := by
  rw [show matrixBond n M = matrixBondFun n M by rfl,
    matrixBondFun_eq_reindex_kronecker]
  rw [Matrix.det_reindex]
  simp [Matrix.det_kronecker]

theorem determinant_mul_native (n : ℕ) (A B : MatrixStage n) :
    Matrix.det (A * B) = Matrix.det A * Matrix.det B :=
  Matrix.det_mul A B

theorem determinant_group_hom_native (n : ℕ) (A B : MatrixStage n) :
    Matrix.detMonoidHom (A * B) =
      Matrix.detMonoidHom A * Matrix.detMonoidHom B := by
  exact Matrix.det_mul A B

theorem trace_mul_comm_native (n : ℕ) (A B : MatrixStage n) :
    Matrix.trace (A * B) = Matrix.trace (B * A) :=
  Matrix.trace_mul_comm A B

theorem kronecker_identity_det_native (n : ℕ) (M : MatrixStage n) :
    Matrix.det (Matrix.kronecker M (1 : Matrix Bool Bool ℝ)) =
      (Matrix.det M) ^ 2 := by
  change Matrix.det
      (Matrix.kroneckerMap (fun x y : ℝ => x * y) M
        (1 : Matrix Bool Bool ℝ)) = (Matrix.det M) ^ 2
  rw [Matrix.det_kronecker]
  simp

end InfoGeometry.TraceFormula.DeterminantBondNative
