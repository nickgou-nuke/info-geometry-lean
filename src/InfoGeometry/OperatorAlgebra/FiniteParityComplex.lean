import InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Quotient.Basic

open Matrix

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParityComplex

open InfoGeometry.OperatorAlgebra.FiniteParitySupertrace

variable {n : Type*} [Fintype n] [DecidableEq n]

def positiveParitySpace (sign : n → ℝ) : Submodule ℝ (n → ℝ) :=
  LinearMap.range (Matrix.mulVecLin (positiveParityProjector sign))

def negativeParitySpace (sign : n → ℝ) : Submodule ℝ (n → ℝ) :=
  LinearMap.range (Matrix.mulVecLin (negativeParityProjector sign))

def positiveToNegativeLinear
    (sign : n → ℝ) (Q : Matrix n n ℝ) :
    positiveParitySpace sign →ₗ[ℝ] negativeParitySpace sign :=
  LinearMap.codRestrict (negativeParitySpace sign)
    ((Matrix.mulVecLin (positiveToNegativeDifferential sign Q)).comp
      (positiveParitySpace sign).subtype)
    (by
      rintro ⟨v, _⟩
      refine ⟨Matrix.mulVec (Q * positiveParityProjector sign) v, ?_⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply,
        Matrix.mulVecLin_apply, positiveToNegativeDifferential]
      rw [Matrix.mulVec_mulVec]
      simp [Matrix.mul_assoc])

def negativeToPositiveLinear
    (sign : n → ℝ) (Q : Matrix n n ℝ) :
    negativeParitySpace sign →ₗ[ℝ] positiveParitySpace sign :=
  LinearMap.codRestrict (positiveParitySpace sign)
    ((Matrix.mulVecLin (negativeToPositiveDifferential sign Q)).comp
      (negativeParitySpace sign).subtype)
    (by
      rintro ⟨v, _⟩
      refine ⟨Matrix.mulVec (Q * negativeParityProjector sign) v, ?_⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply,
        Matrix.mulVecLin_apply, negativeToPositiveDifferential]
      rw [Matrix.mulVec_mulVec]
      simp [Matrix.mul_assoc])

@[simp]
theorem positiveToNegativeLinear_apply
    (sign : n → ℝ) (Q : Matrix n n ℝ)
    (v : positiveParitySpace sign) :
    (positiveToNegativeLinear sign Q v : n → ℝ) =
      positiveToNegativeDifferential sign Q *ᵥ (v : n → ℝ) :=
  rfl

@[simp]
theorem negativeToPositiveLinear_apply
    (sign : n → ℝ) (Q : Matrix n n ℝ)
    (v : negativeParitySpace sign) :
    (negativeToPositiveLinear sign Q v : n → ℝ) =
      negativeToPositiveDifferential sign Q *ᵥ (v : n → ℝ) :=
  rfl

theorem restrictedLinearDifferentials_comp_zero
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1)
    (Q : Matrix n n ℝ)
    (hQodd : IsOdd sign Q)
    (hQsq : Q * Q = 0) :
    (negativeToPositiveLinear sign Q).comp
        (positiveToNegativeLinear sign Q) = 0 ∧
      (positiveToNegativeLinear sign Q).comp
        (negativeToPositiveLinear sign Q) = 0 := by
  obtain ⟨hminusPlus, hplusMinus⟩ :=
    restrictedDifferentials_comp_zero sign hsign Q hQodd hQsq
  constructor
  · ext v
    simp only [LinearMap.comp_apply, positiveToNegativeLinear_apply,
      negativeToPositiveLinear_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [Matrix.mulVec_mulVec, hminusPlus, zero_mulVec]
  · ext v
    simp only [LinearMap.comp_apply, negativeToPositiveLinear_apply,
      positiveToNegativeLinear_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [Matrix.mulVec_mulVec, hplusMinus, zero_mulVec]

theorem positiveRange_le_negativeKernel
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1)
    (Q : Matrix n n ℝ)
    (hQodd : IsOdd sign Q)
    (hQsq : Q * Q = 0) :
    LinearMap.range (positiveToNegativeLinear sign Q) ≤
      LinearMap.ker (negativeToPositiveLinear sign Q) := by
  rw [LinearMap.range_le_ker_iff]
  exact (restrictedLinearDifferentials_comp_zero sign hsign Q hQodd hQsq).1

theorem negativeRange_le_positiveKernel
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1)
    (Q : Matrix n n ℝ)
    (hQodd : IsOdd sign Q)
    (hQsq : Q * Q = 0) :
    LinearMap.range (negativeToPositiveLinear sign Q) ≤
      LinearMap.ker (positiveToNegativeLinear sign Q) := by
  rw [LinearMap.range_le_ker_iff]
  exact (restrictedLinearDifferentials_comp_zero sign hsign Q hQodd hQsq).2

structure TwoPeriodicComplex
    (Vplus Vminus : Type*)
    [AddCommGroup Vplus] [Module ℝ Vplus]
    [AddCommGroup Vminus] [Module ℝ Vminus] where
  dPlus : Vplus →ₗ[ℝ] Vminus
  dMinus : Vminus →ₗ[ℝ] Vplus
  dMinus_comp_dPlus : dMinus.comp dPlus = 0
  dPlus_comp_dMinus : dPlus.comp dMinus = 0

namespace TwoPeriodicComplex

variable {Vplus Vminus : Type*}
variable [AddCommGroup Vplus] [Module ℝ Vplus]
variable [AddCommGroup Vminus] [Module ℝ Vminus]

def positiveBoundaries (C : TwoPeriodicComplex Vplus Vminus) :
    Submodule ℝ (LinearMap.ker C.dPlus) :=
  (LinearMap.range C.dMinus).comap (LinearMap.ker C.dPlus).subtype

def negativeBoundaries (C : TwoPeriodicComplex Vplus Vminus) :
    Submodule ℝ (LinearMap.ker C.dMinus) :=
  (LinearMap.range C.dPlus).comap (LinearMap.ker C.dMinus).subtype

def PositiveCohomology (C : TwoPeriodicComplex Vplus Vminus) : Type _ :=
  LinearMap.ker C.dPlus ⧸ C.positiveBoundaries

def NegativeCohomology (C : TwoPeriodicComplex Vplus Vminus) : Type _ :=
  LinearMap.ker C.dMinus ⧸ C.negativeBoundaries

instance (C : TwoPeriodicComplex Vplus Vminus) :
    AddCommGroup C.PositiveCohomology :=
  Submodule.Quotient.addCommGroup _

instance (C : TwoPeriodicComplex Vplus Vminus) :
    Module ℝ C.PositiveCohomology :=
  Submodule.Quotient.module _

instance (C : TwoPeriodicComplex Vplus Vminus) :
    AddCommGroup C.NegativeCohomology :=
  Submodule.Quotient.addCommGroup _

instance (C : TwoPeriodicComplex Vplus Vminus) :
    Module ℝ C.NegativeCohomology :=
  Submodule.Quotient.module _

end TwoPeriodicComplex

def finiteParityComplex
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1)
    (Q : Matrix n n ℝ)
    (hQodd : IsOdd sign Q)
    (hQsq : Q * Q = 0) :
    TwoPeriodicComplex (positiveParitySpace sign) (negativeParitySpace sign) where
  dPlus := positiveToNegativeLinear sign Q
  dMinus := negativeToPositiveLinear sign Q
  dMinus_comp_dPlus :=
    (restrictedLinearDifferentials_comp_zero sign hsign Q hQodd hQsq).1
  dPlus_comp_dMinus :=
    (restrictedLinearDifferentials_comp_zero sign hsign Q hQodd hQsq).2

end InfoGeometry.OperatorAlgebra.FiniteParityComplex
