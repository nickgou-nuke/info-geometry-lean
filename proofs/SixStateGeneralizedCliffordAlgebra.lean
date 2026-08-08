import Mathlib
import proofs.TwoSheetThreeColorWeyl
import proofs.CRTGeneralizedPauliSix
import proofs.TwelveFoldArithmetic

noncomputable section
namespace SixStateGeneralizedCliffordAlgebra

open TwoSheetThreeColorWeyl
open CRTGeneralizedPauliSix
open TwelveFoldArithmetic

/-- Sheet generators lifted to six states. -/
def sheetGamma6 : M6C := tensor sheetGamma (1 : M3C)
def sheetFlip6 : M6C := tensor sheetFlip (1 : M3C)

def colorShift6 : M6C := tensor (1 : M2C) colorShift
def colorClock6 : M6C := tensor (1 : M2C) (colorClock ω3)

def X6 : M6C := tensor sheetFlip colorShift
def Z6 : M6C := tensor sheetGamma (colorClock ω3 ^ 2)

theorem sheetGamma_sq : sheetGamma6 * sheetGamma6 = (1 : M6C) := by
  simp [sheetGamma6, tensor_mul, sheet_parity.1, tensor_one]

theorem sheetFlip_sq : sheetFlip6 * sheetFlip6 = (1 : M6C) := by
  simp [sheetFlip6, tensor_mul, sheet_parity.2.1, tensor_one]

theorem sheetGamma_sheetFlip_anticommute :
    sheetGamma6 * sheetFlip6 = -(sheetFlip6 * sheetGamma6) := by
  have h : (sheetGamma : M2C) * sheetFlip = -(sheetFlip * sheetGamma) := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sheetGamma, sheetFlip, Matrix.mul_apply, Fin.sum_univ_two]
  simpa [sheetGamma6, sheetFlip6, tensor_mul] using congrArg (fun A : M2C => tensor A (1 : M3C)) h

theorem sheetGamma_colorShift_comm :
    sheetGamma6 * colorShift6 = colorShift6 * sheetGamma6 := by
  simpa [sheetGamma6, colorShift6] using
    (tensor_factor_commute (A := sheetGamma) (B := colorShift))

/-- `[\Gamma ⊗ 1, 1 ⊗ X] = 0` (sheet and color sectors commute). -/
theorem sheetGamma_colorShift_commutator :
    sheetGamma6 * colorShift6 - colorShift6 * sheetGamma6 = 0 := by
  exact sub_eq_zero.mpr sheetGamma_colorShift_comm

theorem sheetGamma_colorClock6_comm :
    sheetGamma6 * colorClock6 = colorClock6 * sheetGamma6 := by
  simpa [sheetGamma6, colorClock6] using
    (tensor_factor_commute (A := sheetGamma) (B := colorClock ω3))

/-- `[\Gamma ⊗ 1, 1 ⊗ Z] = 0` (sheet and color sectors commute). -/
theorem sheetGamma_colorClock6_commutator :
    sheetGamma6 * colorClock6 - colorClock6 * sheetGamma6 = 0 := by
  exact sub_eq_zero.mpr sheetGamma_colorClock6_comm

theorem sheetFlip_colorShift_comm :
    sheetFlip6 * colorShift6 = colorShift6 * sheetFlip6 := by
  simpa [sheetFlip6, colorShift6] using
    (tensor_factor_commute (A := sheetFlip) (B := colorShift))

/-- `[J ⊗ 1, 1 ⊗ X] = 0` (sheet and color sectors commute). -/
theorem sheetFlip_colorShift_commutator :
    sheetFlip6 * colorShift6 - colorShift6 * sheetFlip6 = 0 := by
  exact sub_eq_zero.mpr sheetFlip_colorShift_comm

theorem sheetFlip_colorClock6_comm :
    sheetFlip6 * colorClock6 = colorClock6 * sheetFlip6 := by
  simpa [sheetFlip6, colorClock6] using
    (tensor_factor_commute (A := sheetFlip) (B := colorClock ω3))

/-- `[J ⊗ 1, 1 ⊗ Z] = 0` (sheet and color sectors commute). -/
theorem sheetFlip_colorClock6_commutator :
    sheetFlip6 * colorClock6 - colorClock6 * sheetFlip6 = 0 := by
  exact sub_eq_zero.mpr sheetFlip_colorClock6_comm

theorem X6_pow_six : X6 ^ 6 = (1 : M6C) := by
  calc
    X6 ^ 6 = tensor ((sheetFlip : M2C) ^ 6) (colorShift ^ 6) := by
      simpa [X6] using (TwelveFoldSheetColorOmega.tensor_pow (A := (sheetFlip : M2C)) (B := colorShift) 6)
    _ = tensor (1 : M2C) (1 : M3C) := by
      rw [pow_eq_pow_mod (a := (sheetFlip : M2C)) (n := 2) (m := 6) sheet_parity.2.1,
        pow_eq_pow_mod (a := (colorShift : M3C)) (n := 3) (m := 6) (color_weyl ω3 omega3_root).1]
    _ = (1 : M6C) := by simp [tensor_one]

theorem Z6_pow_six : Z6 ^ 6 = (1 : M6C) := by
  have hclock2pow6 : (colorClock ω3 ^ 2 : M3C) ^ 6 = (1 : M3C) := by
    have hclock2pow3 : (colorClock ω3 ^ 2 : M3C) ^ 3 = (1 : M3C) := by
      calc
        (colorClock ω3 ^ 2 : M3C) ^ 3 = (colorClock ω3 : M3C) ^ (2 * 3) := by
          simpa [pow_mul]
        _ = (colorClock ω3 : M3C) ^ (3 * 2) := by ring
        _ = ((colorClock ω3 : M3C) ^ 3) ^ 2 := by
          rw [pow_mul]
        _ = (1 : M3C) ^ 2 := by rw [(color_weyl ω3 omega3_root).2.1]
        _ = (1 : M3C) := by simp
    calc
      (colorClock ω3 ^ 2 : M3C) ^ 6 = ((colorClock ω3 ^ 2 : M3C) ^ 3) ^ 2 := by
        simpa [pow_mul]
      _ = (1 : M3C) ^ 2 := by rw [hclock2pow3]
      _ = (1 : M3C) := by simp
  have hgamma6 : (sheetGamma : M2C) ^ 6 = (1 : M2C) := by
    exact pow_eq_pow_mod (a := (sheetGamma : M2C)) (n := 2) (m := 6) sheet_parity.1
  calc
    Z6 ^ 6 = tensor (sheetGamma ^ 6) ((colorClock ω3 ^ 2 : M3C) ^ 6) := by
      simpa [Z6] using
        (TwelveFoldSheetColorOmega.tensor_pow (A := (sheetGamma : M2C)) (B := colorClock ω3 ^ 2) 6)
    _ = tensor (1 : M2C) (1 : M3C) := by
      rw [hgamma6]
      rw [hclock2pow6]
    _ = (1 : M6C) := by simp [tensor_one]

theorem colorClock_sq_comm_colorShift :
    (colorClock ω3 ^ 2) * colorShift = (ω3 ^ 2 : ℂ) • (colorShift * (colorClock ω3 ^ 2)) := by
  have hcol : colorClock ω3 * colorShift = (ω3 : ℂ) • (colorShift * colorClock ω3) := (color_weyl ω3 omega3_root).2.2
  calc
    (colorClock ω3 ^ 2) * colorShift = colorClock ω3 * (colorClock ω3 * colorShift) := by
      simp [pow_two, mul_assoc]
    _ = colorClock ω3 * ((ω3 : ℂ) • (colorShift * colorClock ω3)) := by
      rw [hcol]
    _ = (ω3 : ℂ) • (colorClock ω3 * (colorShift * colorClock ω3)) := by
      simp [Matrix.mul_smul]
    _ = (ω3 : ℂ) • ((ω3 : ℂ) • (colorShift * (colorClock ω3 * colorClock ω3))) := by
      rw [hcol, mul_assoc]
    _ = (ω3 ^ 2 : ℂ) • (colorShift * (colorClock ω3 ^ 2)) := by
      simp [pow_two, smul_smul, mul_assoc]

theorem X6_Z6_comm :
    Z6 * X6 = (-(ω3 ^ 2 : ℂ)) • (X6 * Z6) := by
  have hflip : (sheetGamma : M2C) * sheetFlip = -(sheetFlip * sheetGamma) := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sheetGamma, sheetFlip, Matrix.mul_apply, Fin.sum_univ_two]
  calc
    Z6 * X6 = tensor (sheetGamma * sheetFlip) ((colorClock ω3 ^ 2) * colorShift) := by
      simp [Z6, X6, tensor_mul]
    _ = tensor (sheetGamma * sheetFlip) ((ω3 ^ 2 : ℂ) • (colorShift * (colorClock ω3 ^ 2))) := by
      rw [colorClock_sq_comm_colorShift]
    _ = (ω3 ^ 2 : ℂ) • tensor (sheetGamma * sheetFlip) (colorShift * (colorClock ω3 ^ 2)) := by
      ext ⟨i, a⟩ ⟨j, b⟩ <;> simp [tensor, Matrix.kroneckerMap_apply, Matrix.mul_assoc]
    _ = (-(ω3 ^ 2 : ℂ)) • tensor (sheetFlip * sheetGamma) (colorShift * (colorClock ω3 ^ 2)) := by
      rw [hflip]
      simp
    _ = (-(ω3 ^ 2 : ℂ)) • (X6 * Z6) := by
      simp [X6, Z6, tensor_mul, mul_assoc]

theorem neg_omega3_sq_eq_zeta6 : (-(ω3 ^ (2 : ℕ) : ℂ)) = ζ6 := by
  unfold ω3 ζ6
  have hpow : Complex.exp (2 * Real.pi * Complex.I / 3 : ℂ) ^ (2 : ℕ) =
      Complex.exp ((2 : ℂ) * (2 * Real.pi * Complex.I / 3 : ℂ)) := by
    simpa [pow_succ] using
      (Complex.exp_nat_mul (2 * Real.pi * Complex.I / 3 : ℂ) 2).symm
  calc
    -((Complex.exp (2 * Real.pi * Complex.I / 3 : ℂ)) ^ (2 : ℕ))
        = -(Complex.exp (4 * Real.pi * Complex.I / 3 : ℂ)) := by
      rw [hpow]
      ring_nf
    _ = -(Complex.exp (Real.pi * Complex.I / 3 + Real.pi * Complex.I : ℂ)) := by
      congr
      ring
    _ = -(Complex.exp (Real.pi * Complex.I / 3 : ℂ) * Complex.exp (Real.pi * Complex.I : ℂ)) := by
      rw [Complex.exp_add]
    _ = Complex.exp (Real.pi * Complex.I / 3 : ℂ) := by
      simp [Complex.exp_pi_mul_I]
    _ = Complex.exp (2 * Real.pi * Complex.I / 6 : ℂ) := by
      ring

theorem X6_Z6_comm_zeta6 :
    Z6 * X6 = ζ6 • (X6 * Z6) := by
  rw [X6_Z6_comm, neg_omega3_sq_eq_zeta6]

theorem X6_pow_four : X6 ^ 4 = tensor (1 : M2C) colorShift := by
  have hflip4 : (sheetFlip : M2C) ^ 4 = (1 : M2C) := by
    calc
      (sheetFlip : M2C) ^ 4 = (sheetFlip : M2C) ^ (2 * 2) := by
        norm_num
      _ = ((sheetFlip : M2C) ^ 2) ^ 2 := by simpa [pow_mul]
      _ = (1 : M2C) ^ 2 := by simpa [pow_two] using sheet_parity.2.1
      _ = (1 : M2C) := by simp
  have hshift4 : (colorShift : M3C) ^ 4 = colorShift := by
    calc
      (colorShift : M3C) ^ 4 = (colorShift : M3C) ^ (3 + 1) := by
        norm_num
      _ = (colorShift : M3C) ^ 3 * colorShift := by simp [pow_succ]
      _ = (1 : M3C) * colorShift := by
        rw [(color_weyl ω3 omega3_root).1]
      _ = colorShift := by simp
  calc
    X6 ^ 4 = tensor ((sheetFlip : M2C) ^ 4) (colorShift ^ 4) := by
      simpa [X6] using (TwelveFoldSheetColorOmega.tensor_pow (A := (sheetFlip : M2C)) (B := colorShift) 4)
    _ = tensor (1 : M2C) colorShift := by rw [hflip4, hshift4]

theorem Z6_pow_three : Z6 ^ 3 = tensor sheetGamma (1 : M3C) := by
  have hclock3 : (colorClock ω3 ^ 2 : M3C) ^ 3 = (1 : M3C) := by
    calc
      (colorClock ω3 ^ 2 : M3C) ^ 3 = (colorClock ω3) ^ (2 * 3) := by simp [pow_mul]
      _ = (colorClock ω3) ^ (3 * 2) := by ring
      _ = ((colorClock ω3) ^ 3) ^ 2 := by rw [pow_mul]
      _ = (1 : M3C) ^ 2 := by rw [(color_weyl ω3 omega3_root).2.1]
      _ = (1 : M3C) := by simp
  have hgamma3 : (sheetGamma : M2C) ^ 3 = sheetGamma := by
    calc
      (sheetGamma : M2C) ^ 3 = (sheetGamma : M2C) ^ 2 * sheetGamma := by simp [pow_succ]
      _ = (1 : M2C) * sheetGamma := by
        simpa [pow_two] using sheet_parity.1
      _ = sheetGamma := by simp
  calc
    Z6 ^ 3 = tensor (sheetGamma ^ 3) (colorClock ω3 ^ 2) ^ 3 := by rfl
    _ = tensor (sheetGamma ^ 3) ((colorClock ω3 ^ 2) ^ 3) := by
      symm
      exact (TwelveFoldSheetColorOmega.tensor_pow (A := (sheetGamma : M2C)) (B := (colorClock ω3 ^ 2)) 3)
    _ = tensor sheetGamma (1 : M3C) := by rw [hgamma3, hclock3]

theorem sixfoldTriality_eq_X6_pow_four_mul_Z6_pow_three :
    sixfoldTriality = X6 ^ 4 * Z6 ^ 3 := by
  calc
    X6 ^ 4 * Z6 ^ 3 = tensor (1 : M2C) colorShift * tensor sheetGamma (1 : M3C) := by
      rw [X6_pow_four, Z6_pow_three]
    _ = tensor (sheetGamma : M2C) colorShift := by
      simpa [tensor_mul]
    _ = sixfoldTriality := rfl

/-- Sheet-color reflection in involution `Θ := J ⊗ R`. -/
def pinTheta : M6C := tensor sheetFlip colorReflection

/-- `Θ` conjugates triality by inversion up to a central sign. -/
theorem pinTheta_conj_sixfoldTriality (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    pinTheta * sixfoldTriality * pinTheta = -(sixfoldTriality ^ (5 : ℕ) : M6C) := by
  have hR : colorReflection * colorShift * colorReflection = colorShift ^ 2 :=
    (color_reflection_relations (ω := ω) hω).2.1
  have hT2 : sixfoldTriality ^ (2 : ℕ) = tensor (1 : M2C) (colorShift ^ 2) := by
    calc
      sixfoldTriality ^ (2 : ℕ) = (tensor sheetGamma colorShift) ^ (2 : ℕ) := by rfl
      _ = tensor (sheetGamma ^ (2 : ℕ)) (colorShift ^ (2 : ℕ)) := by
        simp [pow_two, tensor_mul]
      _ = tensor (1 : M2C) (colorShift ^ (2 : ℕ)) := by simp [sheet_parity.1]
  have hT5 : sixfoldTriality ^ (5 : ℕ) = tensor (sheetGamma : M2C) (colorShift ^ 2) := by
    calc
      sixfoldTriality ^ (5 : ℕ) = sixfoldTriality ^ ((2 : ℕ) + 3) := by norm_num
      _ = sixfoldTriality ^ 2 * sixfoldTriality ^ 3 := by rw [pow_add]
      _ = (tensor (1 : M2C) (colorShift ^ 2)) * tensor sheetGamma (1 : M3C) := by
        rw [hT2, sixfoldTriality_cube (ω := ω3) omega3_root]
      _ = tensor (sheetGamma : M2C) (colorShift ^ 2) := by
        simp [tensor_mul, mul_assoc]
  calc
    pinTheta * sixfoldTriality * pinTheta
        = tensor (sheetFlip * sheetGamma * sheetFlip) (colorReflection * colorShift * colorReflection) := by
      simp [pinTheta, sixfoldTriality, tensor_mul, mul_assoc]
    _ = tensor (-(sheetGamma : M2C)) (colorShift ^ 2) := by
      simp [sheet_parity.2.2, hR]
    _ = -(tensor (sheetGamma : M2C) (colorShift ^ 2)) := by
      simp [tensor]
    _ = -(sixfoldTriality ^ (5 : ℕ) : M6C) := by rw [hT5]

end SixStateGeneralizedCliffordAlgebra

end noncomputable section
