/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorPolynomialCCR
import InfoGeometry.Canonical.KahlerAtiyahCartanForms
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Real polynomial/exterior supertwistor operators

Bosonic wavefunctions and fermionic exterior generators live in the native
tensor product `MvPolynomial ι ℝ ⊗[ℝ] ExteriorAlgebra ℝ E`.  Tensor-product
algebra homomorphisms transport the polynomial CCR and the existing native
exterior CAR to this common carrier.  The two factors commute as operators.

This is an algebraic real supertwistor realization (four bosonic coordinates
when `ι = Fin 4`); it does not construct a projective supermanifold, a twistor
string, BRST cohomology, or a supersymmetry representation.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealSupertwistor

open scoped TensorProduct
open RealPolynomialCCR
open InfoGeometry.Canonical.KahlerAtiyahCartanForms

variable (ι E : Type*) [AddCommGroup E] [Module ℝ E]

abbrev SuperWave := WavePolynomial ι ⊗[ℝ] ExteriorAlgebra ℝ E
abbrev SuperOperator := Module.End ℝ (SuperWave ι E)

/-- Native algebra homomorphism acting on the bosonic tensor factor. -/
def bosonLift : Operator ι →ₐ[ℝ] SuperOperator ι E :=
  Module.End.rTensorAlgHom ℝ (WavePolynomial ι) (ExteriorAlgebra ℝ E)

/-- Native algebra homomorphism acting on the fermionic tensor factor. -/
def fermionLift : FormEnd E →ₐ[ℝ] SuperOperator ι E :=
  Module.End.lTensorAlgHom ℝ (ExteriorAlgebra ℝ E) (WavePolynomial ι)

@[simp] theorem bosonLift_tmul (A : Operator ι) (p : WavePolynomial ι)
    (ξ : ExteriorAlgebra ℝ E) :
    bosonLift ι E A (p ⊗ₜ[ℝ] ξ) = A p ⊗ₜ[ℝ] ξ := rfl

@[simp] theorem fermionLift_tmul (B : FormEnd E) (p : WavePolynomial ι)
    (ξ : ExteriorAlgebra ℝ E) :
    fermionLift ι E B (p ⊗ₜ[ℝ] ξ) = p ⊗ₜ[ℝ] B ξ := rfl

theorem boson_fermion_commute (A : Operator ι) (B : FormEnd E) :
    bosonLift ι E A * fermionLift ι E B =
      fermionLift ι E B * bosonLift ι E A := by
  change (A.rTensor (ExteriorAlgebra ℝ E)).comp (B.lTensor (WavePolynomial ι)) =
    (B.lTensor (WavePolynomial ι)).comp (A.rTensor (ExteriorAlgebra ℝ E))
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- CCR survive on the full polynomial/exterior tensor carrier. -/
theorem bosonic_CCR (h : ℝ) (A B : Coeff ι) :
    bosonLift ι E (quantize h A) * bosonLift ι E (quantize h B) -
        bosonLift ι E (quantize h B) * bosonLift ι E (quantize h A) =
      (h * omega A B) • (1 : SuperOperator ι E) := by
  have hCCR := congrArg (bosonLift ι E) (quantize_commutator h A B)
  simpa only [map_sub, map_mul, map_smul, map_one] using hCCR

/-- Tensor-lifted native exterior creation. -/
def fermionCreate (v : E) : SuperOperator ι E :=
  fermionLift ι E (wedgeOperator v)

/-- Tensor-lifted native contraction by an actual covector. -/
def fermionAnnihilate (φ : Module.Dual ℝ E) : SuperOperator ι E :=
  fermionLift ι E (contractionOperator φ)

omit [Fintype ι] [DecidableEq ι] in
/-- The fermionic relation is an anticommutator, kept separate from the CCR. -/
theorem fermionic_CAR (φ : Module.Dual ℝ E) (v : E) :
    fermionAnnihilate ι E φ * fermionCreate ι E v +
        fermionCreate ι E v * fermionAnnihilate ι E φ =
      (φ v) • (1 : SuperOperator ι E) := by
  have hCAR := congrArg (fermionLift ι E) (contraction_wedge_CAR φ v)
  simpa only [map_add, map_mul, map_smul, map_one,
    fermionAnnihilate, fermionCreate] using hCAR

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem fermionCreate_sq_zero (v : E) :
    fermionCreate ι E v * fermionCreate ι E v = 0 := by
  have h := congrArg (fermionLift ι E) (wedgeOperator_sq_zero v)
  simpa only [map_mul, map_zero, fermionCreate] using h

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem fermionAnnihilate_sq_zero (φ : Module.Dual ℝ E) :
    fermionAnnihilate ι E φ * fermionAnnihilate ι E φ = 0 := by
  have h := congrArg (fermionLift ι E) (contractionOperator_sq_zero φ)
  simpa only [map_mul, map_zero, fermionAnnihilate] using h

omit [Fintype ι] [DecidableEq ι] in
/-- The coordinate CAR has a nonzero unit coefficient on matching modes. -/
theorem coordinate_fermionic_CAR (n : ℕ) (i j : Fin n) :
    fermionAnnihilate ι (Fin n → ℝ) (LinearMap.proj i) *
        fermionCreate ι (Fin n → ℝ) (Pi.single j 1) +
      fermionCreate ι (Fin n → ℝ) (Pi.single j 1) *
        fermionAnnihilate ι (Fin n → ℝ) (LinearMap.proj i) =
      (if i = j then 1 else 0 : ℝ) • (1 : SuperOperator ι (Fin n → ℝ)) := by
  simpa [Pi.single_apply] using
    fermionic_CAR ι (Fin n → ℝ) (LinearMap.proj i) (Pi.single j 1)

end InfoGeometry.Twistor.RealSupertwistor
