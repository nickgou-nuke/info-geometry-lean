import InfoGeometry.Projective.HadjiivanovLogConnectionBridge

/-!
# Native rank-two realization of the algebraic logarithmic residue

The generic fiber is specialized to the existing LCFT carrier
`LogCftModule ℂ = Fin 2 → ℂ`.  The nilpotent endomorphism is matrix action by
the native upper Jordan generator, so its square-zero law is inherited from
`Clifford.LogCftMonodromy` rather than postulated again.
-/

namespace InfoGeometry.Projective.HadjiivanovLogConnectionRankTwoBridge

open scoped TensorProduct
open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Projective.PuncturedAffineLogDifferential

noncomputable section

abbrev RankTwoFiber := LogCftModule ℂ

/-- Native Jordan nilpotent acting on the rank-two LCFT fiber. -/
def nativeNilpotentEnd : RankTwoFiber →ₗ[ℂ] RankTwoFiber :=
  Matrix.mulVecLin jordanNilpotent

theorem nativeNilpotentEnd_sq :
    nativeNilpotentEnd.comp nativeNilpotentEnd = 0 := by
  apply LinearMap.ext
  intro v
  change (jordanNilpotent : Matrix (Fin 2) (Fin 2) ℂ).mulVec
      (jordanNilpotent.mulVec v) = 0
  rw [Matrix.mulVec_mulVec, jordanNilpotent_sq]
  simp

/-- Concrete residue `h I + N` on the native LCFT module. -/
def rankTwoLogResidue (h : ℂ) : LogResidue RankTwoFiber where
  weight := h
  nilpotent := nativeNilpotentEnd
  nilpotent_sq := nativeNilpotentEnd_sq

@[simp] theorem rankTwoLogResidue_weight (h : ℂ) :
    (rankTwoLogResidue h).weight = h := rfl

@[simp] theorem rankTwoLogResidue_nilpotent (h : ℂ) :
    (rankTwoLogResidue h).nilpotent = nativeNilpotentEnd := rfl

/-- The generic residue operator is exactly action by the native `L₀` cell. -/
theorem rankTwo_residueOperator_eq_mulVecLin (h : ℂ) :
    residueOperator (rankTwoLogResidue h) =
      Matrix.mulVecLin (virasoroL0Cell h) := by
  apply LinearMap.ext
  intro v
  rw [l0_cell_decomposition]
  simp [residueOperator, rankTwoLogResidue, nativeNilpotentEnd]

/-- Explicit connection formula on a native rank-two pure section. -/
theorem rankTwo_logarithmicConnection_tmul
    (h : ℂ) (f : HadjiivanovLogConnectionBridge.LaurentRing)
    (v : RankTwoFiber) :
    logarithmicConnection (rankTwoLogResidue h) (f ⊗ₜ[ℂ] v) =
      logarithmicDifferential f ⊗ₜ[ℂ] v +
        f ⊗ₜ[ℂ] (virasoroL0Cell h).mulVec v := by
  rw [logarithmicConnection_tmul]
  congr 2
  change residueOperator (rankTwoLogResidue h) v = _
  rw [rankTwo_residueOperator_eq_mulVecLin, Matrix.mulVecLin_apply]

theorem rankTwo_logarithmicConnection_T_tmul
    (h : ℂ) (n : ℤ) (v : RankTwoFiber) :
    logarithmicConnection (rankTwoLogResidue h)
        (LaurentPolynomial.T n ⊗ₜ[ℂ] v) =
      (n : ℂ) • (LaurentPolynomial.T n ⊗ₜ[ℂ] v) +
        LaurentPolynomial.T n ⊗ₜ[ℂ]
          (virasoroL0Cell h).mulVec v := by
  rw [logarithmicConnection_tmul,
    logarithmicDifferential_T]
  congr 1
  congr 1
  change residueOperator (rankTwoLogResidue h) v = _
  rw [rankTwo_residueOperator_eq_mulVecLin, Matrix.mulVecLin_apply]

theorem rankTwo_logarithmicConnection_C_mul_T_tmul
    (h c : ℂ) (n : ℤ) (v : RankTwoFiber) :
    logarithmicConnection (rankTwoLogResidue h)
        ((LaurentPolynomial.C c * LaurentPolynomial.T n) ⊗ₜ[ℂ] v) =
      (n : ℂ) •
          ((LaurentPolynomial.C c * LaurentPolynomial.T n) ⊗ₜ[ℂ] v) +
        (LaurentPolynomial.C c * LaurentPolynomial.T n) ⊗ₜ[ℂ]
          (virasoroL0Cell h).mulVec v := by
  rw [logarithmicConnection_tmul,
    logarithmicDifferential_C_mul_T]
  congr 1
  congr 1
  change residueOperator (rankTwoLogResidue h) v = _
  rw [rankTwo_residueOperator_eq_mulVecLin, Matrix.mulVecLin_apply]

end

end InfoGeometry.Projective.HadjiivanovLogConnectionRankTwoBridge
