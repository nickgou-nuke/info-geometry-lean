import Mathlib
import InfoGeometry.Canonical.QutritGellMannOperatorBasis
import InfoGeometry.Canonical.StokesQutritChannelBasis

/-!
# The 32-dimensional traceless-colour tensor sector

The eight chiral Zorn slots with `M₂(ℂ)` coefficients are soldered linearly
to `M₂(ℂ) ⊗ sl₃(ℂ)`, using the eight non-identity channels of the existing
Gell--Mann family.  This is a linear/operator readout only; it is not a
multiplicative embedding of the non-associative Zorn product.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralTracelessColorTensorLift

open Matrix
open InfoGeometry.Canonical.ChiralStokesPauliBasis
open InfoGeometry.Canonical.QutritGellMannOperatorBasis
open InfoGeometry.Canonical.StokesQutritChannelBasis

abbrev SheetOperator := Matrix (Fin 2) (Fin 2) ℂ
abbrev SixOperator := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ
abbrev ChiralEightSlots := Fin 8 → SheetOperator

def colorChannel (a : Fin 8) : QutritMatrix := gellMannFamily (Fin.succ a)

theorem colorChannel_linearIndependent :
    LinearIndependent ℂ colorChannel := by
  exact gellMannFamily_linearIndependent.comp Fin.succ (Fin.succ_injective 8)

def tracelessColorTensorLift (U : ChiralEightSlots) : SixOperator :=
  ∑ a : Fin 8, sheetTensor (U a) (colorChannel a)

@[simp] theorem tracelessColorTensorLift_apply
    (U : ChiralEightSlots) (s t : Fin 2) (i j : Fin 3) :
    tracelessColorTensorLift U (s, i) (t, j) =
      ∑ a : Fin 8, U a s t * colorChannel a i j := by
  simp [tracelessColorTensorLift, colorChannel, sheetTensor, Matrix.sum_apply]

theorem tracelessColorTensorLift_add (U V : ChiralEightSlots) :
    tracelessColorTensorLift (U + V) =
      tracelessColorTensorLift U + tracelessColorTensorLift V := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  simp [tracelessColorTensorLift_apply, add_mul, Finset.sum_add_distrib]

theorem tracelessColorTensorLift_smul (c : ℂ) (U : ChiralEightSlots) :
    tracelessColorTensorLift (c • U) =
      c • tracelessColorTensorLift U := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  simp [tracelessColorTensorLift_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

def tracelessColorTensorLiftLinear :
    ChiralEightSlots →ₗ[ℂ] SixOperator where
  toFun := tracelessColorTensorLift
  map_add' := tracelessColorTensorLift_add
  map_smul' := tracelessColorTensorLift_smul

@[simp] theorem tracelessColorTensorLiftLinear_apply (U : ChiralEightSlots) :
    tracelessColorTensorLiftLinear U = tracelessColorTensorLift U := rfl

def colorSlice (A : SixOperator) (s t : Fin 2) : QutritMatrix :=
  fun i j => A (s, i) (t, j)

theorem colorSlice_lift (U : ChiralEightSlots) (s t : Fin 2) :
    colorSlice (tracelessColorTensorLift U) s t =
      ∑ a : Fin 8, (U a s t) • colorChannel a := by
  ext i j
  simp [colorSlice, tracelessColorTensorLift_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]

theorem colorSlice_lift_trace_zero (U : ChiralEightSlots) (s t : Fin 2) :
    Matrix.trace (colorSlice (tracelessColorTensorLift U) s t) = 0 := by
  rw [colorSlice_lift]
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Matrix.trace_smul]
  simp [colorChannel, gellMannFamily_trace]

theorem tracelessColorTensorLift_injective :
    Function.Injective tracelessColorTensorLift := by
  intro U V hUV
  funext a
  ext s t
  have hslice :
      colorSlice (tracelessColorTensorLift U) s t =
        colorSlice (tracelessColorTensorLift V) s t := by
    rw [hUV]
  rw [colorSlice_lift, colorSlice_lift] at hslice
  have hli : LinearIndependent ℂ colorChannel := colorChannel_linearIndependent
  have hzero :
      ∑ a : Fin 8, ((U a s t) - (V a s t)) • colorChannel a = 0 := by
    calc
      ∑ a : Fin 8, ((U a s t) - (V a s t)) • colorChannel a =
          ∑ a : Fin 8, (((U a s t) • colorChannel a) -
            ((V a s t) • colorChannel a)) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [sub_smul]
      _ = (∑ a : Fin 8, (U a s t) • colorChannel a) -
            (∑ a : Fin 8, (V a s t) • colorChannel a) := by
              rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hslice
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) _ hzero a
  exact sub_eq_zero.mp hcoeff

theorem chiralEightSlots_finrank :
    Module.finrank ℂ ChiralEightSlots = 32 := by
  rw [Module.finrank_pi_fintype ℂ]
  simp [SheetOperator, Module.finrank_matrix]

theorem tracelessColorTensorLift_range_finrank :
    Module.finrank ℂ (LinearMap.range tracelessColorTensorLiftLinear) = 32 := by
  have hker : (tracelessColorTensorLiftLinear :
      ChiralEightSlots →ₗ[ℂ] SixOperator).ker = ⊥ :=
    (LinearMap.ker_eq_bot).2 tracelessColorTensorLift_injective
  have hdim := LinearMap.finrank_range_add_finrank_ker
    (tracelessColorTensorLiftLinear : ChiralEightSlots →ₗ[ℂ] SixOperator)
  rw [hker] at hdim
  have hdim' :
      Module.finrank ℂ (LinearMap.range tracelessColorTensorLiftLinear) =
        Module.finrank ℂ ChiralEightSlots := by
    simpa using hdim
  exact hdim'.trans chiralEightSlots_finrank

theorem colorCoefficient_lift
    (U : ChiralEightSlots) (s t : Fin 2) (a : Fin 8) :
    gellMannCoefficient (colorSlice (tracelessColorTensorLift U) s t)
        (Fin.succ a) = U a s t := by
  rw [gellMannCoefficient_eq_trace, colorSlice_lift]
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  simp_rw [colorChannel, gellMannFamily_hs_orthogonal]
  have hcollapse :
      (∑ b : Fin 8,
        U b s t * if Fin.succ a = Fin.succ b then
          gramWeight (Fin.succ a) else 0) =
        U a s t * gramWeight (Fin.succ a) := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      have hne : Fin.succ a ≠ Fin.succ b := by
        intro hab
        exact hba ((Fin.succ_injective 8) hab).symm
      simp [hne]
    · simp
  rw [hcollapse]
  field_simp [gramWeight_ne_zero]

theorem tracelessColorTensorLift_image_has_no_singlet
    (U : ChiralEightSlots) (s t : Fin 2) :
    Matrix.trace (colorSlice (tracelessColorTensorLift U) s t) = 0 :=
  colorSlice_lift_trace_zero U s t

end InfoGeometry.Canonical.ChiralTracelessColorTensorLift
