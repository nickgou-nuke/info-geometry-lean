import Mathlib
import InfoGeometry.Canonical.StokesQutritChannelBasis
import InfoGeometry.Canonical.QutritGellMannOperatorBasis

/-!
# The explicit Stokes--Gell--Mann basis of `M₆(ℂ)`

`StokesQutritChannelBasis` owns the discrete Weyl product basis.  This owner
uses the same four sheet channels with the continuous Gell--Mann family.  The
Gram weights are inherited exactly: the sheet contributes `2`, while the
identity and the unnormalised `gl8` contribute `3` and `6` respectively.
-/

noncomputable section

namespace InfoGeometry.Canonical.StokesGellMannChannelBasis

open Matrix
open InfoGeometry.Canonical.ChiralStokesPauliBasis
open InfoGeometry.Canonical.StokesQutritChannelBasis
open InfoGeometry.Canonical.QutritGellMannOperatorBasis

abbrev M6C := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

def stokesGellMannChannel (μ : Fin 4) (r : Fin 9) : M6C :=
  sheetTensor (sheetChannel μ) (gellMannFamily r)

theorem stokesGellMannChannel_conjTranspose (μ : Fin 4) (r : Fin 9) :
    (stokesGellMannChannel μ r)ᴴ =
      sheetTensor (sheetChannel μ) (gellMannFamily r) := by
  rw [stokesGellMannChannel, sheetTensor_conjTranspose,
    sheetChannel_conjTranspose, gellMannFamily_conjTranspose]

theorem stokesGellMannChannel_hs_orthogonal (μ ν : Fin 4) (r s : Fin 9) :
    Matrix.trace ((stokesGellMannChannel μ r)ᴴ * stokesGellMannChannel ν s) =
      if μ = ν ∧ r = s then 2 * gramWeight r else 0 := by
  rw [stokesGellMannChannel_conjTranspose, stokesGellMannChannel,
    sheetTensor_mul, sheetTensor_trace]
  rw [show (sheetChannel μ) * (sheetChannel ν) =
      (sheetChannel μ)ᴴ * sheetChannel ν by rw [sheetChannel_conjTranspose]]
  rw [show (gellMannFamily r) * (gellMannFamily s) =
      (gellMannFamily r)ᴴ * gellMannFamily s by
        rw [gellMannFamily_conjTranspose]]
  rw [sheetChannel_hs_orthogonal, gellMannFamily_hs_orthogonal]
  by_cases hμ : μ = ν
  · by_cases hrs : r = s
    · simp [hμ, hrs]
    · simp [hμ, hrs]
  · simp [hμ]

theorem stokesGellMannChannel_linearIndependent :
    LinearIndependent ℂ
      (fun x : Fin 4 × Fin 9 => stokesGellMannChannel x.1 x.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c h x
  have hx := congrArg
    (fun M : M6C => Matrix.trace ((stokesGellMannChannel x.1 x.2)ᴴ * M)) h
  change Matrix.trace
      ((stokesGellMannChannel x.1 x.2)ᴴ *
        (∑ y : Fin 4 × Fin 9, c y • stokesGellMannChannel y.1 y.2)) =
      Matrix.trace ((stokesGellMannChannel x.1 x.2)ᴴ * 0) at hx
  rw [Matrix.mul_sum, Matrix.trace_sum] at hx
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_zero, Matrix.trace_zero] at hx
  simp_rw [stokesGellMannChannel_hs_orthogonal] at hx
  have hcollapse :
      (∑ y : Fin 4 × Fin 9,
        c y * if x.1 = y.1 ∧ x.2 = y.2 then 2 * gramWeight x.2 else 0) =
        c x * (2 * gramWeight x.2) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hne
      have hcond : ¬ (x.1 = y.1 ∧ x.2 = y.2) := by
        intro hcond
        exact hne (Prod.ext hcond.1.symm hcond.2.symm)
      simp [hcond]
    · simp
  rw [hcollapse] at hx
  exact (mul_eq_zero.mp hx).resolve_right (by
    exact mul_ne_zero (by norm_num) (gramWeight_ne_zero x.2))

theorem stokesGellMannChannel_count :
    Fintype.card (Fin 4 × Fin 9) = 36 ∧
      Fintype.card (Fin 4 × Fin 9) = Module.finrank ℂ M6C := by
  refine ⟨by simp, ?_⟩
  simp [Module.finrank_matrix]

theorem stokesGellMannChannel_span_eq_top :
    Submodule.span ℂ
        (Set.range (fun x : Fin 4 × Fin 9 =>
          stokesGellMannChannel x.1 x.2)) = ⊤ := by
  apply stokesGellMannChannel_linearIndependent.span_eq_top_of_card_eq_finrank
  simp [Module.finrank_matrix]

def stokesGellMannBasis :
    Module.Basis (Fin 4 × Fin 9) ℂ M6C :=
  basisOfLinearIndependentOfCardEqFinrank stokesGellMannChannel_linearIndependent (by
    simp [Module.finrank_matrix])

@[simp] theorem stokesGellMannBasis_apply (x : Fin 4 × Fin 9) :
    stokesGellMannBasis x = stokesGellMannChannel x.1 x.2 := by
  simp [stokesGellMannBasis]

def stokesGellMannCoefficient (A : M6C) (x : Fin 4 × Fin 9) : ℂ :=
  (stokesGellMannBasis.repr A) x

theorem stokesGellMann_expansion (A : M6C) :
    ∑ x : Fin 4 × Fin 9,
        stokesGellMannCoefficient A x • stokesGellMannChannel x.1 x.2 = A := by
  simpa [stokesGellMannCoefficient] using Module.Basis.sum_repr stokesGellMannBasis A

theorem stokesGellMann_trace_readout (A : M6C) (x : Fin 4 × Fin 9) :
    Matrix.trace ((stokesGellMannChannel x.1 x.2)ᴴ * A) =
      (2 * gramWeight x.2) * stokesGellMannCoefficient A x := by
  classical
  have h := congrArg
    (fun M : M6C => Matrix.trace ((stokesGellMannChannel x.1 x.2)ᴴ * M))
    (stokesGellMann_expansion A)
  change Matrix.trace
      ((stokesGellMannChannel x.1 x.2)ᴴ *
        (∑ y : Fin 4 × Fin 9,
          stokesGellMannCoefficient A y • stokesGellMannChannel y.1 y.2)) =
      Matrix.trace ((stokesGellMannChannel x.1 x.2)ᴴ * A) at h
  rw [Matrix.mul_sum, Matrix.trace_sum] at h
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h
  simp_rw [stokesGellMannChannel_hs_orthogonal] at h
  have hcollapse :
      (∑ y : Fin 4 × Fin 9,
        stokesGellMannCoefficient A y *
          if x.1 = y.1 ∧ x.2 = y.2 then 2 * gramWeight x.2 else 0) =
        (2 * gramWeight x.2) * stokesGellMannCoefficient A x := by
    rw [Finset.sum_eq_single x]
    · simp [mul_comm]
    · intro y _ hne
      have hcond : ¬ (x.1 = y.1 ∧ x.2 = y.2) := by
        intro hcond
        exact hne (Prod.ext hcond.1.symm hcond.2.symm)
      simp [hcond]
    · simp
  rw [hcollapse] at h
  exact h.symm

theorem stokesGellMann_coefficient_eq_trace (A : M6C) (x : Fin 4 × Fin 9) :
    stokesGellMannCoefficient A x =
      (2 * gramWeight x.2)⁻¹ *
        Matrix.trace ((stokesGellMannChannel x.1 x.2)ᴴ * A) := by
  rw [stokesGellMann_trace_readout, ← mul_assoc,
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) (gramWeight_ne_zero x.2)),
    one_mul]

end InfoGeometry.Canonical.StokesGellMannChannelBasis
end noncomputable section
