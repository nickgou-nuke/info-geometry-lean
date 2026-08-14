import InfoGeometry.Projective.MobiusLoxodromicSpectralParameter

/-!
# Trace/discriminant readout for the diagonal Möbius flow

The determinant fixes the product of eigenvalues, while the trace and its
discriminant control the spectral separation.  This owner records that exact
finite matrix data for the existing reciprocal exponential flow; it does not
classify arbitrary Möbius transformations.
-/

namespace InfoGeometry.Projective.MobiusMatrixSpectralClassification

open InfoGeometry.Projective.MobiusLoxodromicSpectralParameter

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℂ

noncomputable section

def characteristicPolynomialEval (A : Matrix2) (z : ℂ) : ℂ :=
  z ^ 2 - Matrix.trace A * z + A.det

def traceDiscriminant (A : Matrix2) : ℂ :=
  (Matrix.trace A) ^ 2 - 4 * A.det

theorem flow_characteristicPolynomialEval (κ z : ℂ) :
    characteristicPolynomialEval (flow κ) z =
      (z - Complex.exp κ) * (z - Complex.exp (-κ)) := by
  rw [characteristicPolynomialEval, flow_trace, flow_det]
  have hexp : Complex.exp κ * Complex.exp (-κ) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hfactor : (z - Complex.exp κ) * (z - Complex.exp (-κ)) =
      z ^ 2 - (Complex.exp κ + Complex.exp (-κ)) * z + 1 := by
    calc
      (z - Complex.exp κ) * (z - Complex.exp (-κ)) =
          z ^ 2 - (Complex.exp κ + Complex.exp (-κ)) * z +
            Complex.exp κ * Complex.exp (-κ) := by ring
      _ = z ^ 2 - (Complex.exp κ + Complex.exp (-κ)) * z + 1 := by
        rw [hexp]
  rw [hfactor]

theorem flow_characteristicPolynomial (κ : ℂ) :
    characteristicPolynomialEval (flow κ) =
      fun z => (z - Complex.exp κ) * (z - Complex.exp (-κ)) := by
  funext z
  exact flow_characteristicPolynomialEval κ z

theorem flow_eigenvalues (κ : ℂ) :
    (flow κ).mulVec plusVector = (Complex.exp κ) • plusVector ∧
      (flow κ).mulVec minusVector = (Complex.exp (-κ)) • minusVector :=
  ⟨flow_apply_plus κ, flow_apply_minus κ⟩

theorem flow_traceDiscriminant (κ : ℂ) :
    traceDiscriminant (flow κ) =
      (Complex.exp κ - Complex.exp (-κ)) ^ 2 := by
  rw [traceDiscriminant, flow_trace, flow_det]
  have hexp : Complex.exp κ * Complex.exp (-κ) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    (Complex.exp κ + Complex.exp (-κ)) ^ 2 - 4 * 1 =
        Complex.exp κ ^ 2 + 2 * (Complex.exp κ * Complex.exp (-κ)) +
          Complex.exp (-κ) ^ 2 - 4 := by ring
    _ = Complex.exp κ ^ 2 - 2 * (Complex.exp κ * Complex.exp (-κ)) +
          Complex.exp (-κ) ^ 2 := by rw [hexp]; ring
    _ = (Complex.exp κ - Complex.exp (-κ)) ^ 2 := by ring

theorem flow_eigenvalue_ratio (κ : ℂ) :
    Complex.exp κ / Complex.exp (-κ) = Complex.exp (2 * κ) := by
  rw [div_eq_mul_inv, ← Complex.exp_neg]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem flow_det_one (κ : ℂ) :
    (flow κ).det = 1 :=
  flow_det κ

/-! The diagonal matrix is semisimple whenever its two spectral values are
distinct; this is packaged through a square-free annihilating polynomial. -/

abbrev FlowSpace := Fin 2 → ℂ

noncomputable def flowEnd (κ : ℂ) : Module.End ℂ FlowSpace :=
  Matrix.toLin (Pi.basisFun ℂ (Fin 2)) (Pi.basisFun ℂ (Fin 2)) (flow κ)

theorem flowEnd_apply_basis (κ : ℂ) (i : Fin 2) :
    flowEnd κ ((Pi.basisFun ℂ (Fin 2)) i) =
      (flow κ).mulVec ((Pi.basisFun ℂ (Fin 2)) i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [flowEnd, Matrix.toLin_apply, Matrix.mulVec, dotProduct,
      Pi.basisFun, flow, Fin.sum_univ_two]

theorem flowEnd_isSemisimple_of_distinct {κ : ℂ}
    (hκ : Complex.exp κ ≠ Complex.exp (-κ)) :
    (flowEnd κ).IsSemisimple := by
  let p : Polynomial ℂ :=
    (Polynomial.X - Polynomial.C (Complex.exp κ)) *
      (Polynomial.X - Polynomial.C (Complex.exp (-κ)))
  have hsep₁ : (Polynomial.X - Polynomial.C (Complex.exp κ)).Separable :=
    Polynomial.separable_X_sub_C
  have hsep₂ : (Polynomial.X - Polynomial.C (Complex.exp (-κ))).Separable :=
    Polynomial.separable_X_sub_C
  have hcop : IsCoprime
      (Polynomial.X - Polynomial.C (Complex.exp κ))
      (Polynomial.X - Polynomial.C (Complex.exp (-κ))) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      ((isUnit_iff_ne_zero).2 (sub_ne_zero.mpr hκ))
  have hp : p.Separable := by
    exact hsep₁.mul hsep₂ hcop
  have hpa : Polynomial.aeval (flowEnd κ) p = 0 := by
    have hbi0 : (Pi.basisFun ℂ (Fin 2)) 0 = plusVector := by
      ext j
      fin_cases j <;> simp [Pi.basisFun, plusVector]
    have hbi1 : (Pi.basisFun ℂ (Fin 2)) 1 = minusVector := by
      ext j
      fin_cases j <;> simp [Pi.basisFun, minusVector]
    apply Module.Basis.ext (Pi.basisFun ℂ (Fin 2))
    intro i
    fin_cases i
    · have he : flowEnd κ ((Pi.basisFun ℂ (Fin 2)) 0) =
          Complex.exp κ • (Pi.basisFun ℂ (Fin 2)) 0 := by
        rw [flowEnd_apply_basis, hbi0, flow_apply_plus]
      change ((Polynomial.aeval (flowEnd κ)) p) ((Pi.basisFun ℂ (Fin 2)) 0) = 0
      rw [Module.End.aeval_apply_of_hasEigenvector
        (f := flowEnd κ) (p := p) (μ := Complex.exp κ)
        ⟨Module.End.mem_eigenspace_iff.mpr he, by simp [hbi0, plusVector]⟩]
      simp [p]
    · have he : flowEnd κ ((Pi.basisFun ℂ (Fin 2)) 1) =
          Complex.exp (-κ) • (Pi.basisFun ℂ (Fin 2)) 1 := by
        rw [flowEnd_apply_basis, hbi1, flow_apply_minus]
      change ((Polynomial.aeval (flowEnd κ)) p) ((Pi.basisFun ℂ (Fin 2)) 1) = 0
      rw [Module.End.aeval_apply_of_hasEigenvector
        (f := flowEnd κ) (p := p) (μ := Complex.exp (-κ))
        ⟨Module.End.mem_eigenspace_iff.mpr he, by simp [hbi1, minusVector]⟩]
      simp [p]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.squarefree hpa

theorem flow_semisimple_of_ne_exp_two_kappa {κ : ℂ}
    (hκ : Complex.exp (2 * κ) ≠ 1) :
    (flowEnd κ).IsSemisimple := by
  apply flowEnd_isSemisimple_of_distinct
  intro heq
  apply hκ
  rw [← flow_eigenvalue_ratio κ, heq]
  exact div_self (Complex.exp_ne_zero _)

end

end InfoGeometry.Projective.MobiusMatrixSpectralClassification
