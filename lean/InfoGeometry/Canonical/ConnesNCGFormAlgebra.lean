/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConnesSpectralTripleBridge
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
import InfoGeometry.Canonical.CEOneFormNOperatorBridge
import InfoGeometry.OperatorAlgebra.SpectralTriple
import InfoGeometry.KK.RealSplitKreinUnboundedCycle
import InfoGeometry.KK.RealSplitKreinBoundedTransform
import InfoGeometry.KK.SpectralTripleKreinCycleBridge
import InfoGeometry.Canonical.SpectralTripleCommutatorData
import InfoGeometry.Algebra.NoncommutativePeierlsBerryKitaevSynthesis
import InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis

open ConnesSpectral
open ConnesSpectral.SpectralTriple

noncomputable section

namespace InfoGeometry.Canonical.ConnesNCGFormAlgebra

/-!
# Connes Non-Commutative Differential Form Algebra Ω¹(A)

This module formalizes the non-commutative 1-form differential algebra $\Omega^1(A)$
derived from Dirac commutators $d(a) = [D, a] = D a - a D$, proving:
1. Non-commutative Leibniz Rule: $d(a b) = (d a) b + a (d b)$
2. Additivity: $d(a + b) = d(a) + d(b)$
3. Constant Vanishing: $d(0) = 0$ and $d(1) = 0$
4. Self-Adjoint Star-Involution: $(d a)^* = - d(a^*)$ for $D^* = D$.
-/

variable {A : Type*} [Ring A]

/-- The non-commutative exterior derivative d(a) = [D, a] = D a - a D. -/
def ncDeriv (D a : A) : A := D * a - a * D

/-- **Theorem**: Non-commutative Leibniz Rule: d(a b) = (d a) b + a (d b). -/
theorem ncDeriv_leibniz (D a b : A) :
    ncDeriv D (a * b) = (ncDeriv D a) * b + a * (ncDeriv D b) := by
  dsimp [ncDeriv]
  noncomm_ring

/-- **Theorem**: Additivity of non-commutative derivative: d(a + b) = d(a) + d(b). -/
theorem ncDeriv_add (D a b : A) :
    ncDeriv D (a + b) = ncDeriv D a + ncDeriv D b := by
  dsimp [ncDeriv]
  noncomm_ring

/-- **Theorem**: Zero element derivative: d(0) = 0. -/
theorem ncDeriv_zero (D : A) : ncDeriv D 0 = 0 := by
  dsimp [ncDeriv]
  noncomm_ring

/-- **Theorem**: Identity element derivative: d(1) = 0. -/
theorem ncDeriv_one (D : A) : ncDeriv D 1 = 0 := by
  dsimp [ncDeriv]
  noncomm_ring

/-- **Theorem**: Star-involution property for self-adjoint Dirac operators D* = D.
    (d a)* = - d(a*). -/
theorem ncDeriv_star {R : Type*} [Ring R] [StarRing R] (D a : R)
    (hD_self : star D = D) :
    star (ncDeriv D a) = - ncDeriv D (star a) := by
  dsimp [ncDeriv]
  rw [star_sub, star_mul, star_mul, hD_self]
  noncomm_ring

/-! ## R1 Derivation Spine, `OneForms A`, `NOperatorForm`, & Spectral Triple 1-Forms (F2.4 / M3.5) -/

section ConnesR1DerivationBridge

open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Algebra.NoncommutativePeierlsBerryKitaevSynthesis
open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
open InfoGeometry.NCG
open InfoGeometry.NCG.Calculus

/-- Package `ncDeriv D` as an R1 `RingDeriv A` over any `[Ring A]`. -/
def ncDerivRingDeriv (D : A) : RingDeriv A where
  toFun := ncDeriv D
  map_mul := ncDeriv_leibniz D

@[simp] theorem ncDerivRingDeriv_apply (D a : A) :
    (ncDerivRingDeriv D).toFun a = ncDeriv D a :=
  rfl

/-- Package `ncDeriv D` as an R1 `NCG.Calculus.NCDerivation A` over any `[Ring A]`. -/
def ncDerivNCDerivation (D : A) : InfoGeometry.NCG.Calculus.NCDerivation A where
  toLinearMap :=
    { toFun := ncDeriv D
      map_add' := ncDeriv_add D
      map_smul' := fun n x => by
        change ncDeriv D (n • x) = n • ncDeriv D x
        dsimp [ncDeriv]
        rw [mul_smul_comm, smul_mul_assoc, smul_sub] }
  leibniz' := ncDeriv_leibniz D

@[simp] theorem ncDerivNCDerivation_apply (D a : A) :
    ncDerivNCDerivation D a = ncDeriv D a :=
  rfl

/-- Compatibility with `DerivationExteriorCalculus.innerLieActionLane A`. -/
theorem ncDeriv_eq_innerLieActionLane (D a : A) :
    ncDeriv D a = (innerLieActionLane A).operatorAction D a :=
  rfl

/-- Package `ncDeriv D` as an `R`-linear derivation in `NonAssocDerivation.derivations R A`
for any `[CommRing R] [Ring A] [Algebra R A]`. -/
def ncDerivDerivation {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (D : A) :
    InfoGeometry.Algebra.NonAssocDerivation.derivations R A :=
  ⟨{ toFun := ncDeriv D
     map_add' := ncDeriv_add D
     map_smul' := fun r x => by
       change ncDeriv D (r • x) = r • ncDeriv D x
       dsimp [ncDeriv]
       rw [mul_smul_comm, smul_mul_assoc, smul_sub] },
   ncDeriv_leibniz D⟩

@[simp] theorem ncDerivDerivation_apply
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (D a : A) :
    (ncDerivDerivation (R := R) D : A →ₗ[R] A) a = ncDeriv D a :=
  rfl

/-- `ncDerivDerivation` satisfies `IsProductDerivation` for the associative multiplication
`LinearMap.mul R A`. -/
theorem ncDeriv_isProductDerivation
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (D : A) :
    IsProductDerivation (LinearMap.mul R A) (ncDerivDerivation (R := R) D : A →ₗ[R] A) := by
  intro x y
  exact ncDeriv_leibniz D x y

end ConnesR1DerivationBridge

section ConnesUniversalOneFormsAndNOperatorBridge

open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.NCG

/-- Canonical representation of universal 1-forms `OneForms A` into Connes 1-forms
generated by `D : A`: sends `a · dᵤ b ↦ a * [D, b]` and `dᵤ a ↦ [D, a]`. -/
def connesUniversalOneFormMap (D : A) : OneForms A →+ A :=
  cyclicDerivationUniversalEval (innerAlgebraDerivation (R := ℤ) D)

@[simp] theorem connesUniversalOneFormMap_differential (D a : A) :
    connesUniversalOneFormMap D (differential A a) = ncDeriv D a :=
  cyclicDerivationUniversalEval_differential (innerAlgebraDerivation (R := ℤ) D) a

@[simp] theorem connesUniversalOneFormMap_leftDifferentialForm (D a b : A) :
    connesUniversalOneFormMap D (leftDifferentialForm A a b) = a * ncDeriv D b :=
  cyclicDerivationUniversalEval_leftDifferentialForm (innerAlgebraDerivation (R := ℤ) D) a b

@[simp] theorem connesUniversalOneFormMap_rightDifferentialForm (D a b : A) :
    connesUniversalOneFormMap D (rightDifferentialForm A a b) = ncDeriv D a * b :=
  cyclicDerivationUniversalEval_rightDifferentialForm (innerAlgebraDerivation (R := ℤ) D) a b

/-- `connesUniversalOneFormMap` agrees with `universalOneFormToActionForm` on
`innerLieActionLane A` evaluated at `![D]`. -/
theorem connesUniversalOneFormMap_eq_actionForm (D : A) (ω : OneForms A) :
    universalOneFormToActionForm (innerLieActionLane A) ω ![D] =
      connesUniversalOneFormMap D ω := by
  let f : OneForms A →+ A :=
    { toFun := fun η => universalOneFormToActionForm (innerLieActionLane A) η ![D]
      map_zero' := by simp
      map_add' := fun η₁ η₂ => by simp }
  have heq : f = connesUniversalOneFormMap D := by
    apply oneForms_addHom_ext A
    intro a b
    change universalOneFormToActionForm (innerLieActionLane A)
        (leftDifferentialForm A a b) ![D] =
      connesUniversalOneFormMap D (leftDifferentialForm A a b)
    rw [universalOneFormToActionForm_leftDifferentialForm_raw,
      connesUniversalOneFormMap_leftDifferentialForm]
    change a * (D * b - b * D) - (a * b) * (D * 1 - 1 * D) =
      a * (D * b - b * D)
    noncomm_ring
  exact DFunLike.congr_fun heq ω

/-- `connesUniversalOneFormMap` agrees with `universalOneFormToDerivationForm` on
`fullDerivationLieLane R A` evaluated at `![ncDerivDerivation (R := R) D]`. -/
theorem connesUniversalOneFormMap_eq_derivationForm
    {R : Type*} [CommRing R] [Algebra R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (D : A) (ω : OneForms A) :
    universalOneFormToDerivationForm (fullDerivationLieLane R A) ω
        ![ncDerivDerivation (R := R) D] =
      connesUniversalOneFormMap D ω := by
  let f : OneForms A →+ A :=
    { toFun := fun η =>
        universalOneFormToDerivationForm (fullDerivationLieLane R A) η
          ![ncDerivDerivation (R := R) D]
      map_zero' := by simp
      map_add' := fun η₁ η₂ => by simp }
  have heq : f = connesUniversalOneFormMap D := by
    apply oneForms_addHom_ext A
    intro a b
    change universalOneFormToDerivationForm (fullDerivationLieLane R A)
        (leftDifferentialForm A a b) ![ncDerivDerivation (R := R) D] =
      connesUniversalOneFormMap D (leftDifferentialForm A a b)
    rw [universalOneFormToDerivationForm_leftDifferentialForm,
      connesUniversalOneFormMap_leftDifferentialForm]
    rfl
  exact DFunLike.congr_fun heq ω

/-- Disambiguated `NOperatorForm 1` bridge: the 1-component `NOperatorForm` built via
`CEOneFormNOperatorBridge.ofCEFamily` from `ceExteriorDerivative` / `exteriorDerivativeZero`
evaluates at `ncDerivDerivation D` to `ncDeriv D a`. -/
theorem connesNOperatorForm_eq_ncDeriv
    [Algebra ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (D a : A) :
    let K := fullDerivationLieLane ℝ A
    let ω : NOperatorForm 1 (Point := Unit) (Tangent := K.L) (Value := A) :=
      ofCEFamily K 1 (fun _ => exteriorDerivativeZero K a)
    ω 0 () (ncDerivDerivation (R := ℝ) D) =
        component K 1 (fun _ => exteriorDerivativeZero K a) 0
          (ncDerivDerivation (R := ℝ) D) ∧
      component K 1 (fun _ => exteriorDerivativeZero K a) 0
          (ncDerivDerivation (R := ℝ) D) =
        ncDeriv D a := by
  exact ⟨rfl, rfl⟩

/-- `SpectralTripleCommutatorData.boundedCommutator` is definitionally `ncDeriv S.D (S.representation a)`. -/
theorem boundedCommutator_eq_ncDeriv
    {A₀ H₀ : Type*} [NormedRing A₀] [NormedAlgebra ℝ A₀]
    [NormedAddCommGroup H₀] [NormedSpace ℝ H₀] [CompleteSpace H₀]
    (S : SpectralTripleCommutatorData (A := A₀) (H := H₀)) (a : A₀) :
    boundedCommutator S a = ncDeriv S.D (S.representation a) :=
  rfl

end ConnesUniversalOneFormsAndNOperatorBridge

section SpectralTripleAndUnboundedCycleForms

open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open InfoGeometry.KK
open InfoGeometry.Krein
open InfoGeometry.NCG
open scoped TensorProduct

/-- Convert a ring homomorphism `φ : A₀ →+* B₀` into a `ℤ`-linear map. -/
def ringHomToIntLinear {A₀ B₀ : Type*} [Ring A₀] [Ring B₀] (φ : A₀ →+* B₀) :
    A₀ →ₗ[ℤ] B₀ where
  toFun := φ
  map_add' := φ.map_add
  map_smul' n x := by
    change φ (n • x) = n • φ x
    exact map_zsmul φ.toAddMonoidHom n x

private theorem multiplicationTensor_tensorMap_ringHom
    {A₀ B₀ : Type*} [Ring A₀] [Ring B₀] (φ : A₀ →+* B₀) (z : A₀ ⊗[ℤ] A₀) :
    multiplicationTensor B₀
        (TensorProduct.map (ringHomToIntLinear φ) (ringHomToIntLinear φ) z) =
      φ (multiplicationTensor A₀ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      change φ x * φ y = φ (x * y)
      exact (map_mul φ x y).symm
  | add x y hx hy => simp [map_add, hx, hy]

/-- Functorial pushforward of universal 1-forms `OneForms A₀ →+ OneForms B₀` along a ring
homomorphism `φ : A₀ →+* B₀`. -/
def ringHomMapOneForms {A₀ B₀ : Type*} [Ring A₀] [Ring B₀] (φ : A₀ →+* B₀) :
    OneForms A₀ →+ OneForms B₀ where
  toFun ω :=
    ⟨TensorProduct.map (ringHomToIntLinear φ) (ringHomToIntLinear φ) ω.1, by
      change multiplicationTensor B₀ _ = 0
      exact (multiplicationTensor_tensorMap_ringHom φ ω.1).trans
        (by rw [show multiplicationTensor A₀ ω.1 = 0 from ω.2, map_zero])⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' ω₁ ω₂ := by
    apply Subtype.ext
    simp [map_add]

@[simp] theorem ringHomMapOneForms_differential
    {A₀ B₀ : Type*} [Ring A₀] [Ring B₀] (φ : A₀ →+* B₀) (a : A₀) :
    ringHomMapOneForms φ (differential A₀ a) = differential B₀ (φ a) := by
  apply Subtype.ext
  change TensorProduct.map (ringHomToIntLinear φ) (ringHomToIntLinear φ)
      ((1 : A₀) ⊗ₜ[ℤ] a - a ⊗ₜ[ℤ] (1 : A₀)) =
    (1 : B₀) ⊗ₜ[ℤ] φ a - φ a ⊗ₜ[ℤ] (1 : B₀)
  simp [map_sub, ringHomToIntLinear]

@[simp] theorem ringHomMapOneForms_leftDifferentialForm
    {A₀ B₀ : Type*} [Ring A₀] [Ring B₀] (φ : A₀ →+* B₀) (a b : A₀) :
    ringHomMapOneForms φ (leftDifferentialForm A₀ a b) =
      leftDifferentialForm B₀ (φ a) (φ b) := by
  apply Subtype.ext
  change TensorProduct.map (ringHomToIntLinear φ) (ringHomToIntLinear φ)
      (a ⊗ₜ[ℤ] b - (a * b) ⊗ₜ[ℤ] (1 : A₀)) =
    φ a ⊗ₜ[ℤ] φ b - (φ a * φ b) ⊗ₜ[ℤ] (1 : B₀)
  simp [map_sub, ringHomToIntLinear, map_mul]

/-- The universal one-form pushforward preserves identity homomorphisms. -/
@[simp] theorem ringHomMapOneForms_id {A₀ : Type*} [Ring A₀] :
    ringHomMapOneForms (RingHom.id A₀) = AddMonoidHom.id (OneForms A₀) := by
  apply oneForms_addHom_ext A₀
  intro a b
  simp

/-- The universal one-form pushforward respects composition of ring homomorphisms. -/
@[simp] theorem ringHomMapOneForms_comp
    {A₀ B₀ C₀ : Type*} [Ring A₀] [Ring B₀] [Ring C₀]
    (ψ : B₀ →+* C₀) (φ : A₀ →+* B₀) :
    ringHomMapOneForms (ψ.comp φ) =
      (ringHomMapOneForms ψ).comp (ringHomMapOneForms φ) := by
  apply oneForms_addHom_ext A₀
  intro a b
  simp

/-- Universal Connes 1-form map `Ω¹(A₀) →+ EndR H₀` induced by a `PhaseRealSpectralTriple A₀ H₀`,
sending `a · dᵤ b ↦ π(a) ∘ [D, π(b)]` and `dᵤ a ↦ [D, π(a)]`. -/
def phaseRealSpectralTripleOneForm
    {A₀ H₀ : Type*} [Ring A₀] [Star A₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    (T : InfoGeometry.OperatorAlgebra.SpectralTriple.PhaseRealSpectralTriple A₀ H₀) :
    OneForms A₀ →+ InfoGeometry.OperatorAlgebra.SpectralTriple.EndR H₀ :=
  (cyclicDerivationUniversalEval
      (innerAlgebraDerivation (R := ℤ) T.spectralGenerator.D)).comp
    (ringHomMapOneForms T.representedAlgebra.rep)

@[simp] theorem phaseRealSpectralTripleOneForm_differential
    {A₀ H₀ : Type*} [Ring A₀] [Star A₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    (T : InfoGeometry.OperatorAlgebra.SpectralTriple.PhaseRealSpectralTriple A₀ H₀) (a : A₀) :
    phaseRealSpectralTripleOneForm T (differential A₀ a) =
      InfoGeometry.OperatorAlgebra.SpectralTriple.commutator
        T.spectralGenerator.D (T.representedAlgebra.rep a) := by
  simp [phaseRealSpectralTripleOneForm, InfoGeometry.OperatorAlgebra.SpectralTriple.commutator]
  rfl

@[simp] theorem phaseRealSpectralTripleOneForm_leftDifferentialForm
    {A₀ H₀ : Type*} [Ring A₀] [Star A₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    (T : InfoGeometry.OperatorAlgebra.SpectralTriple.PhaseRealSpectralTriple A₀ H₀) (a b : A₀) :
    phaseRealSpectralTripleOneForm T (leftDifferentialForm A₀ a b) =
      (T.representedAlgebra.rep a).comp
        (InfoGeometry.OperatorAlgebra.SpectralTriple.commutator
          T.spectralGenerator.D (T.representedAlgebra.rep b)) := by
  simp [phaseRealSpectralTripleOneForm, InfoGeometry.OperatorAlgebra.SpectralTriple.commutator,
    ContinuousLinearMap.mul_def]

/-- `OrderOneCondition` + `OrderZeroCondition` propagate to every Connes 1-form
`ω ∈ OneForms A₀`: `phaseRealSpectralTripleOneForm T ω` commutes with `oppositeRep`. -/
theorem phaseRealSpectralTripleOneForm_orderOne
    {A₀ H₀ : Type*} [Ring A₀] [Star A₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    (T : InfoGeometry.OperatorAlgebra.SpectralTriple.PhaseRealSpectralTriple A₀ H₀)
    (ω : OneForms A₀) (c : A₀) :
    (phaseRealSpectralTripleOneForm T ω).comp
        (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
          T.representedAlgebra T.realStructure c) =
      (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
          T.representedAlgebra T.realStructure c).comp
        (phaseRealSpectralTripleOneForm T ω) := by
  refine Submodule.span_induction
    (p := fun η _ =>
      (phaseRealSpectralTripleOneForm T η).comp
          (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
            T.representedAlgebra T.realStructure c) =
        (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
            T.representedAlgebra T.realStructure c).comp
          (phaseRealSpectralTripleOneForm T η))
    ?_ ?_ ?_ ?_ (oneForms_mem_span A₀ ω)
  · rintro η ⟨⟨a, b⟩, rfl⟩
    rw [phaseRealSpectralTripleOneForm_leftDifferentialForm]
    have h0 := T.orderZero a c
    have h1 := T.orderOne b c
    calc
      ((T.representedAlgebra.rep a).comp
          (InfoGeometry.OperatorAlgebra.SpectralTriple.commutator
            T.spectralGenerator.D (T.representedAlgebra.rep b))).comp
          (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
            T.representedAlgebra T.realStructure c)
          = (T.representedAlgebra.rep a).comp
              ((InfoGeometry.OperatorAlgebra.SpectralTriple.commutator
                  T.spectralGenerator.D (T.representedAlgebra.rep b)).comp
                (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
                  T.representedAlgebra T.realStructure c)) := by
            rfl
      _ = (T.representedAlgebra.rep a).comp
            ((InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
                T.representedAlgebra T.realStructure c).comp
              (InfoGeometry.OperatorAlgebra.SpectralTriple.commutator
                T.spectralGenerator.D (T.representedAlgebra.rep b))) := by
            rw [h1]
      _ = ((T.representedAlgebra.rep a).comp
            (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
              T.representedAlgebra T.realStructure c)).comp
            (InfoGeometry.OperatorAlgebra.SpectralTriple.commutator
              T.spectralGenerator.D (T.representedAlgebra.rep b)) := by
            rfl
      _ = ((InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
              T.representedAlgebra T.realStructure c).comp
            (T.representedAlgebra.rep a)).comp
            (InfoGeometry.OperatorAlgebra.SpectralTriple.commutator
              T.spectralGenerator.D (T.representedAlgebra.rep b)) := by
            rw [h0]
      _ = (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
              T.representedAlgebra T.realStructure c).comp
            ((T.representedAlgebra.rep a).comp
              (InfoGeometry.OperatorAlgebra.SpectralTriple.commutator
                T.spectralGenerator.D (T.representedAlgebra.rep b))) := by
            rfl
  · simp [map_zero]
  · intro η₁ η₂ _ _ h₁ h₂
    simp [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, h₁, h₂]
  · intro n η _ hη
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun f : InfoGeometry.OperatorAlgebra.SpectralTriple.EndR H₀ => f v) hη
    simp only [ContinuousLinearMap.comp_apply] at hv ⊢
    rw [map_zsmul]
    change (n • phaseRealSpectralTripleOneForm T η)
        (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
          T.representedAlgebra T.realStructure c v) =
      InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
        T.representedAlgebra T.realStructure c
        ((n • phaseRealSpectralTripleOneForm T η) v)
    rw [smul_apply, hv]
    exact (map_zsmul (InfoGeometry.OperatorAlgebra.SpectralTriple.oppositeRep
      T.representedAlgebra T.realStructure c) n _).symm

/-- Leibniz rule for the bounded commutator representative `X.commutator` of a
`RealSplitKreinUnboundedCycle`, proved on `X.domain` via `X.commutator_formula` and
extended to all of `H₀` by `X.dense_domain`. -/
theorem unboundedCycle_commutator_leibniz
    {A₀ B₀ H₀ : Type*} [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀]
    (X : RealSplitKreinUnboundedCycle A₀ B₀ H₀) (a b : A₀) :
    X.commutator (a * b) = X.commutator a * X.π b + X.π a * X.commutator b := by
  let Lhs : EndH H₀ := X.commutator (a * b)
  let Rhs : EndH H₀ := X.commutator a * X.π b + X.π a * X.commutator b
  have heqOn : Set.EqOn Lhs Rhs X.domain := by
    intro v hv
    let x : {u : H₀ // u ∈ X.domain} := ⟨v, hv⟩
    let bx : {u : H₀ // u ∈ X.domain} := ⟨(X.π b) v, X.π_preserves_domain b hv⟩
    have h1 := X.commutator_formula (a * b) x
    have h2 := X.commutator_formula a bx
    have h3 := X.commutator_formula b x
    have hpi : ∀ u : H₀, (X.π (a * b)) u = (X.π a) ((X.π b) u) := fun u => by
      rw [map_mul]
      rfl
    have hsub :
        (⟨(X.π (a * b)) v, X.π_preserves_domain (a * b) hv⟩ : {u : H₀ // u ∈ X.domain}) =
          ⟨(X.π a) bx.1, X.π_preserves_domain a bx.2⟩ := by
      apply Subtype.ext
      exact hpi v
    change X.commutator (a * b) x.1 =
      X.commutator a ((X.π b) x.1) + (X.π a) (X.commutator b x.1)
    rw [h1, hsub, h2, h3, map_sub]
    have hpi2 : (X.π a) ((X.π b) (X.D x)) = (X.π (a * b)) (X.D x) := (hpi (X.D x)).symm
    rw [hpi2]
    abel
  have hclosed : IsClosed {v : H₀ | Lhs v = Rhs v} :=
    isClosed_eq Lhs.continuous Rhs.continuous
  have hclosure : X.domain ⊆ {v : H₀ | Lhs v = Rhs v} := heqOn
  have hall : Set.univ ⊆ {v : H₀ | Lhs v = Rhs v} := by
    rw [← X.dense_domain.closure_eq]
    exact hclosed.closure_subset_iff.mpr hclosure
  apply ContinuousLinearMap.ext
  intro v
  exact hall (Set.mem_univ v)

/-- Unit vanishing `X.commutator 1 = 0` proved on `X.domain` and extended to `H₀` by
`X.dense_domain`. -/
theorem unboundedCycle_commutator_one
    {A₀ B₀ H₀ : Type*} [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀]
    (X : RealSplitKreinUnboundedCycle A₀ B₀ H₀) :
    X.commutator 1 = 0 := by
  have heqOn : X.domain ⊆ {v : H₀ | X.commutator 1 v = (0 : EndH H₀) v} := by
    intro v hv
    let x : {u : H₀ // u ∈ X.domain} := ⟨v, hv⟩
    have h1 := X.commutator_formula 1 x
    have hpi : X.π 1 = 1 := map_one X.π
    have hsub :
        (⟨(X.π 1) v, X.π_preserves_domain 1 hv⟩ : {u : H₀ // u ∈ X.domain}) = x := by
      apply Subtype.ext
      simp [x, hpi]
    change X.commutator 1 x.1 = 0
    rw [h1, hsub]
    simp [hpi]
  have hclosed : IsClosed {v : H₀ | X.commutator 1 v = (0 : EndH H₀) v} :=
    isClosed_eq (X.commutator 1).continuous continuous_const
  have hall : Set.univ ⊆ {v : H₀ | X.commutator 1 v = (0 : EndH H₀) v} := by
    rw [← X.dense_domain.closure_eq]
    exact hclosed.closure_subset_iff.mpr heqOn
  apply ContinuousLinearMap.ext
  intro v
  exact hall (Set.mem_univ v)

/-- Bounded-transform Connes 1-form map `Ω¹(A₀) →+ EndH H₀` on `RealSplitKreinUnboundedCycle`
via `T : RealSplitKreinBoundedTransform X` (`T.phase = X.resolvent`, `BUCKET 3` resolvent
representative). -/
def unboundedCycleResolventOneForm
    {A₀ B₀ H₀ : Type*} [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀]
    {X : RealSplitKreinUnboundedCycle A₀ B₀ H₀}
    (T : RealSplitKreinBoundedTransform X) :
    OneForms A₀ →+ EndH H₀ :=
  (cyclicDerivationUniversalEval (innerAlgebraDerivation (R := ℤ) T.phase)).comp
    (ringHomMapOneForms X.π.toRingHom)

@[simp] theorem unboundedCycleResolventOneForm_differential
    {A₀ B₀ H₀ : Type*} [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀]
    {X : RealSplitKreinUnboundedCycle A₀ B₀ H₀}
    (T : RealSplitKreinBoundedTransform X) (a : A₀) :
    unboundedCycleResolventOneForm T (differential A₀ a) =
      T.phase * X.π a - X.π a * T.phase := by
  simp [unboundedCycleResolventOneForm]

@[simp] theorem unboundedCycleResolventOneForm_leftDifferentialForm
    {A₀ B₀ H₀ : Type*} [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀]
    {X : RealSplitKreinUnboundedCycle A₀ B₀ H₀}
    (T : RealSplitKreinBoundedTransform X) (a b : A₀) :
    unboundedCycleResolventOneForm T (leftDifferentialForm A₀ a b) =
      X.π a * (T.phase * X.π b - X.π b * T.phase) := by
  simp [unboundedCycleResolventOneForm]

/-- Every Connes 1-form `ω ∈ Ω¹(A₀)` evaluated through `unboundedCycleResolventOneForm T`
(`T.phase = X.resolvent`) is compact (`IsCompactEnd H₀`). -/
theorem unboundedCycleResolventOneForm_compact
    {A₀ B₀ H₀ : Type*} [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀]
    {X : RealSplitKreinUnboundedCycle A₀ B₀ H₀}
    (T : RealSplitKreinBoundedTransform X) (ω : OneForms A₀) :
    IsCompactEnd H₀ (unboundedCycleResolventOneForm T ω) := by
  refine Submodule.span_induction
    (p := fun η _ => IsCompactEnd H₀ (unboundedCycleResolventOneForm T η))
    ?_ ?_ ?_ ?_ (oneForms_mem_span A₀ ω)
  · rintro η ⟨⟨a, b⟩, rfl⟩
    rw [unboundedCycleResolventOneForm_leftDifferentialForm]
    exact isCompactEnd_comp_left (S := X.π a) (T.phase_commutator_compact b)
  · rw [map_zero]
    exact isCompactEnd_zero
  · intro η₁ η₂ _ _ h₁ h₂
    rw [map_add]
    exact isCompactEnd_add h₁ h₂
  · intro n η _ hη
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ n (unboundedCycleResolventOneForm T η)]
    exact isCompactEnd_smul (n : ℝ) hη

/-- Bounded Kasparov-cycle Connes 1-form map `Ω¹(A₀) →+ EndH H₀` via `X.F` and `X.π`. -/
def kasparovCycleOneForm
    {A₀ B₀ H₀ : Type*} [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀]
    (X : RealSplitKreinKasparovCycle A₀ B₀ H₀) :
    OneForms A₀ →+ EndH H₀ :=
  (cyclicDerivationUniversalEval (innerAlgebraDerivation (R := ℤ) X.F)).comp
    (ringHomMapOneForms X.π.toRingHom)

/-- Every Connes 1-form `ω ∈ Ω¹(A₀)` evaluated through `kasparovCycleOneForm X` is compact
(`IsCompactEnd H₀`). -/
theorem kasparovCycleOneForm_compact
    {A₀ B₀ H₀ : Type*} [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀]
    (X : RealSplitKreinKasparovCycle A₀ B₀ H₀) (ω : OneForms A₀) :
    IsCompactEnd H₀ (kasparovCycleOneForm X ω) := by
  refine Submodule.span_induction
    (p := fun η _ => IsCompactEnd H₀ (kasparovCycleOneForm X η))
    ?_ ?_ ?_ ?_ (oneForms_mem_span A₀ ω)
  · rintro η ⟨⟨a, b⟩, rfl⟩
    have heq : kasparovCycleOneForm X (leftDifferentialForm A₀ a b) =
        X.π a * (X.F * X.π b - X.π b * X.F) := by
      simp [kasparovCycleOneForm]
    rw [heq]
    exact isCompactEnd_comp_left (S := X.π a) (X.comm_compact b)
  · rw [map_zero]
    exact isCompactEnd_zero
  · intro η₁ η₂ _ _ h₁ h₂
    rw [map_add]
    exact isCompactEnd_add h₁ h₂
  · intro n η _ hη
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ n (kasparovCycleOneForm X η)]
    exact isCompactEnd_smul (n : ℝ) hη

/-- Explicit contrast between `BUCKET 3` infinite-dimensional `X.resolvent` phase
(`unboundedCycleResolventOneForm`) and `BUCKET 2` finite-dimensional `CFC.sqrt` phase
(`finiteDimPhase`, `[FiniteDimensional ℝ H₀]`). -/
theorem finiteDimPhase_vs_resolvent_oneForm_contrast
    {A₀ B₀ H₀ : Type*} [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [KreinSpace H₀] [KreinGradedModule H₀] [FiniteDimensional ℝ H₀]
    {X : RealSplitKreinUnboundedCycle A₀ B₀ H₀}
    (T : RealSplitKreinBoundedTransform X)
    (D : EndH H₀) (hD_self : IsSelfAdjoint D) (a : A₀) (ω : OneForms A₀) :
    IsCompactEnd H₀ (unboundedCycleResolventOneForm T ω) ∧
      IsCompactEnd H₀ (finiteDimPhase D * X.π a - X.π a * finiteDimPhase D) ∧
      ((1 + D * D) * (1 - finiteDimPhase D * finiteDimPhase D) = 1) :=
  ⟨unboundedCycleResolventOneForm_compact T ω,
    isCompactEnd_of_finiteDimensional (H := H₀) _,
    (finiteDimPhase_sq_add_inv_one_add_sq hD_self).1⟩

end SpectralTripleAndUnboundedCycleForms

section NoncommutativeMatrixWitness

/-- Non-commuting `M₂(ℝ)` Connes 1-form witness (`T1-F2.4-5`, `T2-F2.4-1`): preserves `[Ring A]`
without `[CommRing A]`, exhibiting `D, a, b ∈ M₂(ℝ)` with `[D, a] ≠ 0`, `D * a ≠ a * D`,
and the Leibniz derivation rule `ncDeriv_leibniz`. -/
theorem ncDeriv_mat2_noncommutative_witness :
    let D : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
    let a : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let b : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    ncDeriv D a ≠ 0 ∧
      D * a ≠ a * D ∧
      ncDeriv D (a * b) = ncDeriv D a * b + a * ncDeriv D b := by
  intro D a b
  refine ⟨?_, ?_, ncDeriv_leibniz D a b⟩
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    simp [ncDeriv, D, a] at h01
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    simp [D, a, Matrix.mul_apply, Fin.sum_univ_two] at h01
    norm_num at h01

end NoncommutativeMatrixWitness

end InfoGeometry.Canonical.ConnesNCGFormAlgebra
