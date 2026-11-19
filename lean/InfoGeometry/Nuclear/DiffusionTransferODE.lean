/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Nuclear.DiffusionTransfer
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Analytic concentration–flux evolution for diffusion transfer

The entrywise derivatives of the explicit real transfer matrix satisfy
`T' = A * T` under the attenuation relation. Together with `transfer_zero`,
this constructs a fundamental matrix with initial value the identity.
For any initial concentration–flux vector, multiplication by this matrix
constructs a solution of the first-order system with that initial value.
These are existence statements for the specified constant-coefficient system;
they do not assert ODE uniqueness or identify a matrix exponential.

The zero-loss branch is the separate shear `lossFreeTransfer`. Substitution
of `k = 0` and `z = B * k = 0` in `transfer` gives the identity because division
is total in Lean; it does not recover a concentration gradient at nonzero
flux. The shear retains that gradient. Its identities hold algebraically for
all `B`, while the physical flux interpretation requires `B ≠ 0`.
-/

noncomputable section

open scoped Matrix

namespace InfoGeometry.Nuclear.DiffusionTransfer

private theorem hasDerivAt_transfer_entry_explicit
    (k z d : ℝ) (i j : Fin 2) :
    HasDerivAt (fun x => transfer k z x i j)
      ((!![Real.sinh (k * d) * k, -(Real.cosh (k * d) * k) / z;
           -z * (Real.cosh (k * d) * k), Real.sinh (k * d) * k] :
        Matrix (Fin 2) (Fin 2) ℝ) i j) d := by
  have hlin : HasDerivAt (fun x : ℝ => k * x) k d := by
    simpa only [mul_one] using (hasDerivAt_id' d).const_mul k
  have hc := hlin.cosh
  have hs := hlin.sinh
  fin_cases i <;> fin_cases j
  · simpa [transfer] using hc
  · simpa [transfer] using hs.neg.div_const z
  · simpa [transfer] using hs.const_mul (-z)
  · simpa [transfer] using hc

/-- The explicit transfer is an entrywise solution of `T' = A * T`.
The initial identity matrix is supplied by `transfer_zero`. -/
theorem hasDerivAt_transfer_entry (B storage rate k d : ℝ)
    (hB : B ≠ 0) (hk : k ≠ 0) (hrel : k ^ 2 = rate * storage / B)
    (i j : Fin 2) :
    HasDerivAt (fun x => transfer k (B * k) x i j)
      ((physicalGenerator B storage rate * transfer k (B * k) d) i j) d := by
  apply (hasDerivAt_transfer_entry_explicit k (B * k) d i j).congr_deriv
  have hrate : rate * storage = B * k ^ 2 := by
    calc
      rate * storage = k ^ 2 * B := ((eq_div_iff hB).mp hrel).symm
      _ = B * k ^ 2 := mul_comm _ _
  have hq : -rate * storage = -(B * k ^ 2) := by rw [neg_mul, hrate]
  fin_cases i <;> fin_cases j <;>
    simp [physicalGenerator, offDiag, transfer, hq, Matrix.mul_apply,
      Fin.sum_univ_two] <;> field_simp [hB, hk]

/-- Every initial concentration–flux vector evolves by the stated generator.
This proves the differential equation for the actual matrix-vector product. -/
theorem hasDerivAt_transfer_state_entry (B storage rate k d : ℝ)
    (hB : B ≠ 0) (hk : k ≠ 0) (hrel : k ^ 2 = rate * storage / B)
    (y₀ : Fin 2 → ℝ) (i : Fin 2) :
    HasDerivAt (fun x => (transfer k (B * k) x *ᵥ y₀) i)
      ((physicalGenerator B storage rate *ᵥ
        (transfer k (B * k) d *ᵥ y₀)) i) d := by
  have h₀ :=
    (hasDerivAt_transfer_entry B storage rate k d hB hk hrel i 0).mul_const (y₀ 0)
  have h₁ :=
    (hasDerivAt_transfer_entry B storage rate k d hB hk hrel i 1).mul_const (y₀ 1)
  convert h₀.add h₁ using 1
  · ext x
    simp only [Pi.add_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  · rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]

/-- The constructed state takes its prescribed value at thickness zero. -/
@[simp] theorem transfer_state_zero (k B : ℝ) (y₀ : Fin 2 → ℝ) :
    transfer k (B * k) 0 *ᵥ y₀ = y₀ := by
  rw [transfer_zero, Matrix.one_mulVec]

/-- Zero-loss evolution retains the concentration change caused by constant flux. -/
def lossFreeTransfer (B d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -d / B; 0, 1]

/-- The zero-loss generator is nilpotent, so the transfer is affine in thickness. -/
theorem lossFreeTransfer_eq_generator (B storage d : ℝ) :
    lossFreeTransfer B d = (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      d • physicalGenerator B storage 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lossFreeTransfer, physicalGenerator, offDiag, Matrix.add_apply,
      div_eq_mul_inv]

@[simp] theorem lossFreeTransfer_zero (B : ℝ) : lossFreeTransfer B 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lossFreeTransfer]

/-- Same-medium zero-loss layers compose in their order of action. -/
theorem lossFreeTransfer_add (B d₁ d₂ : ℝ) :
    lossFreeTransfer B (d₁ + d₂) =
      lossFreeTransfer B d₂ * lossFreeTransfer B d₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lossFreeTransfer, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
  ring

/-- The shear is a genuine entrywise solution of the zero-loss first-order system. -/
theorem hasDerivAt_lossFreeTransfer_entry (B storage d : ℝ) (i j : Fin 2) :
    HasDerivAt (fun x => lossFreeTransfer B x i j)
      ((physicalGenerator B storage 0 * lossFreeTransfer B d) i j) d := by
  fin_cases i <;> fin_cases j
  · simpa [lossFreeTransfer, physicalGenerator, offDiag, Matrix.mul_apply,
      Fin.sum_univ_two] using hasDerivAt_const d (1 : ℝ)
  · simpa [lossFreeTransfer, physicalGenerator, offDiag, Matrix.mul_apply,
      Fin.sum_univ_two] using (hasDerivAt_id' d).neg.div_const B
  · simpa [lossFreeTransfer, physicalGenerator, offDiag, Matrix.mul_apply,
      Fin.sum_univ_two] using hasDerivAt_const d (0 : ℝ)
  · simpa [lossFreeTransfer, physicalGenerator, offDiag, Matrix.mul_apply,
      Fin.sum_univ_two] using hasDerivAt_const d (1 : ℝ)

/-- At nonzero thickness and diffusivity, the zero-loss transfer is not the identity. -/
theorem lossFreeTransfer_ne_one (B d : ℝ) (hB : B ≠ 0) (hd : d ≠ 0) :
    lossFreeTransfer B d ≠ 1 := by
  intro h
  have he : -d / B = 0 := by
    simpa [lossFreeTransfer, Matrix.one_apply] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  exact (div_ne_zero (neg_ne_zero.mpr hd) hB) he

end InfoGeometry.Nuclear.DiffusionTransfer
