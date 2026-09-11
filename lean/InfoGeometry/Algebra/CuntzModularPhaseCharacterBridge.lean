import InfoGeometry.Algebra.CuntzModularAutomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Unit-valued character readout of the Cuntz modular phase

The modular automorphism owner already proves the scalar phase law.  This
owner packages that law as a genuine character into the unit group of `ℂ`.
It does not add analytic, topological, or KMS assertions.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzModularPhaseCharacterBridge

open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable def modularPhaseUnit (p : ℕ) (t : ℝ) : ℂˣ :=
  Units.mk0 (modularPhase p t) (Complex.exp_ne_zero _)

@[simp] theorem modularPhaseUnit_coe (p : ℕ) (t : ℝ) :
    (modularPhaseUnit p t : ℂ) = modularPhase p t :=
  rfl

/-- The phase character is unitary on real modular time. -/
theorem modularPhase_normSq_eq_one (p : ℕ) (t : ℝ) :
    Complex.normSq (modularPhase p t) = 1 := by
  dsimp [modularPhase]
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have h_re : (Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
  rw [h_re, Real.exp_zero]
  norm_num

/-- Negative modular time gives the inverse unit character. -/
theorem modularPhaseUnit_neg_eq_inv (p : ℕ) (t : ℝ) :
    modularPhaseUnit p (-t) = (modularPhaseUnit p t)⁻¹ := by
  apply Units.ext
  change modularPhase p (-t) = (modularPhase p t)⁻¹
  dsimp [modularPhase]
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- Arithmetic multiplicativity of the phase label. -/
theorem modularPhase_mul_label
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) :
    modularPhase (m * n) t = modularPhase m t * modularPhase n t := by
  dsimp [modularPhase]
  have hlog : Real.log ((m * n : ℕ) : ℝ) =
      Real.log (m : ℝ) + Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
  rw [hlog]
  convert Complex.exp_add
      (Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ))
      (Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) using 1 <;>
    push_cast <;> ring

theorem modularPhaseUnit_mul_label
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) :
    modularPhaseUnit (m * n) t =
      modularPhaseUnit m t * modularPhaseUnit n t := by
  apply Units.ext
  simp only [modularPhaseUnit_coe, Units.val_mul]
  exact modularPhase_mul_label m n hm hn t

theorem modularPhaseUnit_add (p : ℕ) (s t : ℝ) :
    modularPhaseUnit p (s + t) =
      modularPhaseUnit p s * modularPhaseUnit p t := by
  apply Units.ext
  simp [modularPhaseUnit, modularPhase_add]

noncomputable def modularPhaseCharacter (p : ℕ) :
    Multiplicative ℝ →* ℂˣ where
  toFun t := modularPhaseUnit p (Multiplicative.toAdd t)
  map_one' := by
    simp [modularPhaseUnit]
  map_mul' := by
    intro s t
    change modularPhaseUnit p
        (Multiplicative.toAdd s + Multiplicative.toAdd t) =
      modularPhaseUnit p (Multiplicative.toAdd s) *
        modularPhaseUnit p (Multiplicative.toAdd t)
    exact modularPhaseUnit_add p _ _

@[simp] theorem modularPhaseCharacter_coe (p : ℕ) (t : Multiplicative ℝ) :
    (modularPhaseCharacter p t : ℂ) =
      modularPhase p (Multiplicative.toAdd t) := by
  rfl

theorem modularPhaseCharacter_neg (p : ℕ) (t : ℝ) :
    modularPhaseCharacter p (Multiplicative.ofAdd (-t)) =
      (modularPhaseCharacter p (Multiplicative.ofAdd t))⁻¹ := by
  change modularPhaseUnit p (-t) = (modularPhaseUnit p t)⁻¹
  exact modularPhaseUnit_neg_eq_inv p t

theorem modularPhaseCharacter_add (p : ℕ) (s t : ℝ) :
    modularPhaseCharacter p (Multiplicative.ofAdd (s + t)) =
      modularPhaseCharacter p (Multiplicative.ofAdd s) *
        modularPhaseCharacter p (Multiplicative.ofAdd t) := by
  exact map_mul (modularPhaseCharacter p)
    (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

theorem sigma_cuntzS_eq_modularPhaseCharacter_smul
    (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (i : Fin n) :
    sigma n primes t (cuntzS n i) =
      (modularPhaseCharacter (primes i) (Multiplicative.ofAdd t) : ℂ) •
        cuntzS n i := by
  rw [sigma_cuntzS]
  rfl

end InfoGeometry.Algebra.CuntzModularPhaseCharacterBridge
