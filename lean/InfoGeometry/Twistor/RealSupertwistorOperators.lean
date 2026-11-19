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
open scoped BigOperators
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

/-- The coordinate summand in the polynomial/exterior differential.  The
exterior carrier is the coordinate space itself, so `Pi.single i 1` is an
actual element of that carrier. -/
def polynomialExteriorDifferentialTerm (i : ι) : SuperOperator ι (ι → ℝ) :=
  bosonLift ι (ι → ℝ) (annihilate i) *
    fermionCreate ι (ι → ℝ) (Pi.single i (1 : ℝ))

/-- The polynomial de Rham operator on the polynomial/exterior tensor carrier.
Each polynomial annihilator is paired with exterior creation in the same
coordinate, so this operator raises exterior degree by one. -/
def polynomialExteriorDifferential : SuperOperator ι (ι → ℝ) :=
  ∑ i : ι, polynomialExteriorDifferentialTerm ι i

/-- On a simple tensor, the polynomial/exterior differential is the sum of
coordinate derivatives wedged on the left of the exterior coefficient. -/
theorem polynomialExteriorDifferential_tmul
    (p : WavePolynomial ι) (a : ExteriorAlgebra ℝ (ι → ℝ)) :
    polynomialExteriorDifferential ι (p ⊗ₜ[ℝ] a) =
      ∑ i : ι, (MvPolynomial.pderiv i p) ⊗ₜ[ℝ]
        (ExteriorAlgebra.ι ℝ (Pi.single i (1 : ℝ)) * a) := by
  simp [polynomialExteriorDifferential, fermionCreate, wedgeOperator_apply,
    polynomialExteriorDifferentialTerm, annihilate_apply]

/-- Distinct coordinate summands of the polynomial/exterior differential
anticommute: polynomial annihilators commute, while exterior creations
anticommute, and the two lifted actions commute with one another. -/
theorem polynomialExteriorDifferentialTerm_anticommutes (i j : ι) :
    polynomialExteriorDifferentialTerm ι i * polynomialExteriorDifferentialTerm ι j +
      polynomialExteriorDifferentialTerm ι j * polynomialExteriorDifferentialTerm ι i = 0 := by
  let Bᵢ : SuperOperator ι (ι → ℝ) := bosonLift ι (ι → ℝ) (annihilate i)
  let Bⱼ : SuperOperator ι (ι → ℝ) := bosonLift ι (ι → ℝ) (annihilate j)
  let Fᵢ : SuperOperator ι (ι → ℝ) := fermionCreate ι (ι → ℝ) (Pi.single i (1 : ℝ))
  let Fⱼ : SuperOperator ι (ι → ℝ) := fermionCreate ι (ι → ℝ) (Pi.single j (1 : ℝ))
  have hB : Bᵢ * Bⱼ = Bⱼ * Bᵢ := by
    dsimp [Bᵢ, Bⱼ]
    simpa only [map_mul] using congrArg (bosonLift ι (ι → ℝ)) (annihilate_commute i j)
  have hF : Fᵢ * Fⱼ + Fⱼ * Fᵢ = 0 := by
    dsimp [Fᵢ, Fⱼ, fermionCreate]
    simpa only [map_add, map_mul, map_zero] using congrArg (fermionLift ι (ι → ℝ))
      (wedgeOperator_anticommutator_zero (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)))
  have hFᵢBⱼ : Fᵢ * Bⱼ = Bⱼ * Fᵢ := by
    dsimp [Fᵢ, Bⱼ, fermionCreate]
    exact (boson_fermion_commute ι (ι → ℝ) (annihilate j)
      (wedgeOperator (Pi.single i (1 : ℝ)))).symm
  have hFⱼBᵢ : Fⱼ * Bᵢ = Bᵢ * Fⱼ := by
    dsimp [Fⱼ, Bᵢ, fermionCreate]
    exact (boson_fermion_commute ι (ι → ℝ) (annihilate i)
      (wedgeOperator (Pi.single j (1 : ℝ)))).symm
  change (Bᵢ * Fᵢ) * (Bⱼ * Fⱼ) + (Bⱼ * Fⱼ) * (Bᵢ * Fᵢ) = 0
  have h₁ : (Bᵢ * Fᵢ) * (Bⱼ * Fⱼ) = (Bᵢ * Bⱼ) * (Fᵢ * Fⱼ) := by
    calc (Bᵢ * Fᵢ) * (Bⱼ * Fⱼ)
      _ = Bᵢ * (Fᵢ * Bⱼ) * Fⱼ := by noncomm_ring
      _ = Bᵢ * (Bⱼ * Fᵢ) * Fⱼ := by rw [hFᵢBⱼ]
      _ = (Bᵢ * Bⱼ) * (Fᵢ * Fⱼ) := by noncomm_ring
  have h₂ : (Bⱼ * Fⱼ) * (Bᵢ * Fᵢ) = (Bⱼ * Bᵢ) * (Fⱼ * Fᵢ) := by
    calc (Bⱼ * Fⱼ) * (Bᵢ * Fᵢ)
      _ = Bⱼ * (Fⱼ * Bᵢ) * Fᵢ := by noncomm_ring
      _ = Bⱼ * (Bᵢ * Fⱼ) * Fᵢ := by rw [hFⱼBᵢ]
      _ = (Bⱼ * Bᵢ) * (Fⱼ * Fᵢ) := by noncomm_ring
  rw [h₁, h₂, hB.symm]
  calc (Bᵢ * Bⱼ) * (Fᵢ * Fⱼ) + (Bᵢ * Bⱼ) * (Fⱼ * Fᵢ)
    _ = (Bᵢ * Bⱼ) * (Fᵢ * Fⱼ + Fⱼ * Fᵢ) := by noncomm_ring
    _ = 0 := by rw [hF]; simp

/-- Each individual coordinate summand squares to zero by exterior creation
nilpotence and commutation of the two tensor-factor actions. -/
theorem polynomialExteriorDifferentialTerm_sq_zero (i : ι) :
    polynomialExteriorDifferentialTerm ι i * polynomialExteriorDifferentialTerm ι i = 0 := by
  let Bᵢ : SuperOperator ι (ι → ℝ) := bosonLift ι (ι → ℝ) (annihilate i)
  let Fᵢ : SuperOperator ι (ι → ℝ) := fermionCreate ι (ι → ℝ) (Pi.single i (1 : ℝ))
  have hcross : Fᵢ * Bᵢ = Bᵢ * Fᵢ := by
    dsimp [Fᵢ, Bᵢ, fermionCreate]
    exact (boson_fermion_commute ι (ι → ℝ) (annihilate i)
      (wedgeOperator (Pi.single i (1 : ℝ)))).symm
  have hF : Fᵢ * Fᵢ = 0 := by
    dsimp [Fᵢ, fermionCreate]
    simpa only [map_mul, map_zero] using congrArg (fermionLift ι (ι → ℝ))
      (wedgeOperator_sq_zero (Pi.single i (1 : ℝ)))
  change (Bᵢ * Fᵢ) * (Bᵢ * Fᵢ) = 0
  calc (Bᵢ * Fᵢ) * (Bᵢ * Fᵢ)
    _ = (Bᵢ * Bᵢ) * (Fᵢ * Fᵢ) := by
      calc (Bᵢ * Fᵢ) * (Bᵢ * Fᵢ)
        _ = Bᵢ * (Fᵢ * Bᵢ) * Fᵢ := by noncomm_ring
        _ = Bᵢ * (Bᵢ * Fᵢ) * Fᵢ := by rw [hcross]
        _ = (Bᵢ * Bᵢ) * (Fᵢ * Fᵢ) := by noncomm_ring
    _ = 0 := by rw [hF]; simp

/-- On two polynomial coordinates, the assembled differential is square-zero.
This is the finite carrier's de Rham complex law. -/
theorem polynomialExteriorDifferential_fin2_sq_zero :
    polynomialExteriorDifferential (Fin 2) *
      polynomialExteriorDifferential (Fin 2) = 0 := by
  have h₀ := polynomialExteriorDifferentialTerm_sq_zero (ι := Fin 2) 0
  have h₁ := polynomialExteriorDifferentialTerm_sq_zero (ι := Fin 2) 1
  have h₀₁ := polynomialExteriorDifferentialTerm_anticommutes (ι := Fin 2) 0 1
  simp only [polynomialExteriorDifferential, Fin.sum_univ_two]
  calc (polynomialExteriorDifferentialTerm (Fin 2) 0 +
        polynomialExteriorDifferentialTerm (Fin 2) 1) *
      (polynomialExteriorDifferentialTerm (Fin 2) 0 +
        polynomialExteriorDifferentialTerm (Fin 2) 1)
    _ = polynomialExteriorDifferentialTerm (Fin 2) 0 *
          polynomialExteriorDifferentialTerm (Fin 2) 0 +
        (polynomialExteriorDifferentialTerm (Fin 2) 0 *
            polynomialExteriorDifferentialTerm (Fin 2) 1 +
          polynomialExteriorDifferentialTerm (Fin 2) 1 *
            polynomialExteriorDifferentialTerm (Fin 2) 0) +
        polynomialExteriorDifferentialTerm (Fin 2) 1 *
          polynomialExteriorDifferentialTerm (Fin 2) 1 := by noncomm_ring
    _ = 0 := by rw [h₀₁, h₀, h₁]; simp

/-- The two distinct coordinate one-forms have nonzero wedge product.  Contracting
their product by the first coordinate covector recovers the second generator,
so this is a carrier-level nonvanishing result, not a formal exterior-degree
label. -/
theorem coordinateExteriorWedge_ne_zero :
    ExteriorAlgebra.ι ℝ (Pi.single (0 : Fin 2) (1 : ℝ)) *
      ExteriorAlgebra.ι ℝ ((Pi.single (1 : Fin 2) (1 : ℝ)) : Fin 2 → ℝ) ≠ 0 := by
  let φ : Module.Dual ℝ (Fin 2 → ℝ) := LinearMap.proj 0
  let e₀ : Fin 2 → ℝ := Pi.single 0 1
  let e₁ : Fin 2 → ℝ := Pi.single (1 : Fin 2) (1 : ℝ)
  have hφ₀ : φ e₀ = 1 := by simp [φ, e₀, Pi.single_apply]
  have hφ₁ : φ e₁ = 0 := by simp [φ, e₁, Pi.single_apply]
  have he₁ : e₁ ≠ 0 := by
    intro h
    have hval := congrFun h 1
    simp [e₁, Pi.single_apply] at hval
  have hι₁ : ExteriorAlgebra.ι ℝ e₁ ≠ 0 :=
    (ExteriorAlgebra.ι_eq_zero_iff e₁).not.mpr he₁
  have hcar := congrArg (fun T : FormEnd (Fin 2 → ℝ) =>
      T (ExteriorAlgebra.ι ℝ e₁))
    (contraction_wedge_CAR φ e₀)
  change contractionOperator φ (ExteriorAlgebra.ι ℝ e₀ * ExteriorAlgebra.ι ℝ e₁) +
      ExteriorAlgebra.ι ℝ e₀ * contractionOperator φ (ExteriorAlgebra.ι ℝ e₁) =
    (φ e₀) • ExteriorAlgebra.ι ℝ e₁ at hcar
  have hcontract₁ : contractionOperator φ (ExteriorAlgebra.ι ℝ e₁) = 0 := by
    simp [contractionOperator, CliffordAlgebra.contractLeft_ι, hφ₁]
  rw [hcontract₁, mul_zero, hφ₀, one_smul, add_zero] at hcar
  intro hzero
  have hzero' := congrArg (contractionOperator φ) hzero
  rw [hcar] at hzero'
  exact hι₁ (by simpa using hzero')

/-- The polynomial augmentation tensored with the identity on exterior forms.
This map detects nonzero pure exterior tensors in `SuperWave`. -/
def polynomialExteriorAugmentation :
    SuperWave ι E →ₐ[ℝ] ExteriorAlgebra ℝ E :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId ℝ (ExteriorAlgebra ℝ E)).comp
      (MvPolynomial.aeval (fun _ : ι => (0 : ℝ))))
    (AlgHom.id ℝ (ExteriorAlgebra ℝ E))
    (by
      intro p a
      change algebraMap ℝ (ExteriorAlgebra ℝ E) _ * a =
        a * algebraMap ℝ (ExteriorAlgebra ℝ E) _
      exact Algebra.commutes _ _)

/-- The coordinate one-form in the polynomial/exterior tensor carrier. -/
def coordinateOneForm (i : Fin 2) : SuperWave (Fin 2) (Fin 2 → ℝ) :=
  (1 : WavePolynomial (Fin 2)) ⊗ₜ[ℝ]
    ExteriorAlgebra.ι ℝ (Pi.single i (1 : ℝ))

@[simp] theorem polynomialExteriorAugmentation_coordinateOneForm (i : Fin 2) :
    polynomialExteriorAugmentation (ι := Fin 2) (E := Fin 2 → ℝ)
      (coordinateOneForm i) = ExteriorAlgebra.ι ℝ (Pi.single i (1 : ℝ)) := by
  simp [polynomialExteriorAugmentation, coordinateOneForm]

/-- The simple tensor of the coordinate two-form is nonzero in the actual
polynomial/exterior coefficient algebra. -/
theorem coordinateOneForm_mul_ne_zero :
    coordinateOneForm 0 * coordinateOneForm 1 ≠ 0 := by
  intro hzero
  have h := congrArg
    (polynomialExteriorAugmentation (ι := Fin 2) (E := Fin 2 → ℝ)) hzero
  rw [map_mul, polynomialExteriorAugmentation_coordinateOneForm,
    polynomialExteriorAugmentation_coordinateOneForm, map_zero] at h
  exact coordinateExteriorWedge_ne_zero h

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
