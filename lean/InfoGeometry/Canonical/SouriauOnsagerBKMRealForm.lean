import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Thermo.SusceptibilityOnsagerStress

noncomputable section

namespace SouriauOnsagerBKM

open InfoGeometry.Thermo.SusceptibilityOnsagerStress

variable {n : ℕ}

theorem FaithfulDensityOperator.kuboMoriPairing_add_right
    (D : FaithfulDensityOperator n) (A B C : FiniteOperatorAlgebra n)
    (h : Continuous D.rpow) :
    D.kuboMoriPairing A (B + C) =
      D.kuboMoriPairing A B + D.kuboMoriPairing A C := by
  rw [D.kuboMoriPairing_eq_trace_kuboMoriTransform A (B + C) h,
    D.kuboMoriPairing_eq_trace_kuboMoriTransform A B h,
    D.kuboMoriPairing_eq_trace_kuboMoriTransform A C h]
  simp only [mul_add]
  simpa only [finiteOperatorTraceLinear_apply] using
    (finiteOperatorTraceLinear n).map_add
      (D.kuboMoriTransform (star A) * B)
      (D.kuboMoriTransform (star A) * C)

theorem FaithfulDensityOperator.kuboMoriPairing_real_smul_right
    (D : FaithfulDensityOperator n) (r : ℝ) (A B : FiniteOperatorAlgebra n)
    (h : Continuous D.rpow) :
    D.kuboMoriPairing A (r • B) = r • D.kuboMoriPairing A B := by
  rw [D.kuboMoriPairing_eq_trace_kuboMoriTransform A (r • B) h,
    D.kuboMoriPairing_eq_trace_kuboMoriTransform A B h]
  change finiteOperatorTrace
      (D.kuboMoriTransform (star A) * ((r : ℂ) • B)) =
    (r : ℂ) • finiteOperatorTrace (D.kuboMoriTransform (star A) * B)
  rw [mul_smul_comm]
  simpa only [finiteOperatorTraceLinear_apply] using
    (finiteOperatorTraceLinear n).map_smul (r : ℂ)
      (D.kuboMoriTransform (star A) * B)

theorem FaithfulDensityOperator.kuboMoriPairing_add_left
    (D : FaithfulDensityOperator n) (A C B : FiniteOperatorAlgebra n)
    (h : Continuous D.rpow) :
    D.kuboMoriPairing (A + C) B =
      D.kuboMoriPairing A B + D.kuboMoriPairing C B := by
  rw [← D.kuboMoriPairing_conj_symm_of_continuous_rpow B (A + C) h,
    D.kuboMoriPairing_add_right B A C h, star_add,
    D.kuboMoriPairing_conj_symm_of_continuous_rpow B A h,
    D.kuboMoriPairing_conj_symm_of_continuous_rpow B C h]

theorem FaithfulDensityOperator.kuboMoriPairing_real_smul_left
    (D : FaithfulDensityOperator n) (r : ℝ) (A B : FiniteOperatorAlgebra n)
    (h : Continuous D.rpow) :
    D.kuboMoriPairing (r • A) B = r • D.kuboMoriPairing A B := by
  rw [← D.kuboMoriPairing_conj_symm_of_continuous_rpow B (r • A) h,
    D.kuboMoriPairing_real_smul_right r B A h]
  change star ((r : ℂ) • D.kuboMoriPairing B A) = _
  rw [star_smul]
  rw [show star (r : ℂ) = (r : ℂ) by exact Complex.conj_ofReal r,
    D.kuboMoriPairing_conj_symm_of_continuous_rpow B A h]
  rfl

theorem FaithfulDensityOperator.kuboMoriPairing_self_real_of_continuous_rpow
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h : Continuous D.rpow) :
    (D.kuboMoriPairing A A).im = 0 := by
  have hs := D.kuboMoriPairing_conj_symm_of_continuous_rpow A A h
  have him := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

/-- The real part of the Hermitian BKM pairing as a native real bilinear
response form on the full finite operator algebra. -/
noncomputable def FaithfulDensityOperator.bkmRealBilinForm
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow) :
    LinearMap.BilinForm ℝ (FiniteOperatorAlgebra n) :=
  LinearMap.mk₂ ℝ (fun A B => (D.kuboMoriPairing A B).re)
    (fun A C B => by
      dsimp
      rw [D.kuboMoriPairing_add_left A C B h, Complex.add_re])
    (fun r A B => by
      dsimp
      rw [D.kuboMoriPairing_real_smul_left r A B h]
      simp)
    (fun A B C => by
      dsimp
      rw [D.kuboMoriPairing_add_right A B C h, Complex.add_re])
    (fun r A B => by
      dsimp
      rw [D.kuboMoriPairing_real_smul_right r A B h]
      simp)

@[simp] theorem FaithfulDensityOperator.bkmRealBilinForm_apply
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) :
    D.bkmRealBilinForm h A B = (D.kuboMoriPairing A B).re :=
  rfl

/-- Hermitian symmetry of the complex BKM pairing descends to Onsager
reciprocity of its real bilinear response form. -/
theorem FaithfulDensityOperator.bkmRealBilinForm_symm
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow) :
    (D.bkmRealBilinForm h).IsSymm := by
  refine ⟨?_⟩
  intro A B
  have hs := D.kuboMoriPairing_conj_symm_of_continuous_rpow A B h
  simpa [FaithfulDensityOperator.bkmRealBilinForm] using
    congrArg Complex.re hs

/-- Install the real BKM response as the repository's positive Onsager form
once the remaining diagonal-positivity theorem is available for the model. -/
noncomputable def FaithfulDensityOperator.bkmOnsagerForm
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (h_nonneg : ∀ A : FiniteOperatorAlgebra n,
      0 ≤ (D.kuboMoriPairing A A).re) :
    OnsagerTwoOperatorForm (FiniteOperatorAlgebra n) where
  form := D.bkmRealBilinForm h
  symmetric := fun A B => (D.bkmRealBilinForm_symm h).eq A B
  diagonal_nonnegative := by
    intro A
    simpa using h_nonneg A

@[simp] theorem FaithfulDensityOperator.bkmOnsagerForm_apply
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (h_nonneg : ∀ A : FiniteOperatorAlgebra n,
      0 ≤ (D.kuboMoriPairing A A).re)
    (A B : FiniteOperatorAlgebra n) :
    (D.bkmOnsagerForm h h_nonneg).form A B =
      (D.kuboMoriPairing A B).re :=
  rfl

end SouriauOnsagerBKM
