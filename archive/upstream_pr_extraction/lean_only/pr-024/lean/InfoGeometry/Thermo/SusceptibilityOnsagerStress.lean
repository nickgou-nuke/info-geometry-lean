import Mathlib
import InfoGeometry.Thermo.SusceptibilityHessian
import InfoGeometry.Meta.Architecture

/-!
# Susceptibility Onsager Stress

Two-operator Onsager forms, stress-tensor readouts, and derivations for
the susceptibility Hessian layer.

The module keeps the dependencies proof-carrying:

* the Hessian/susceptibility layer supplies material response;
* an Onsager two-operator form supplies reciprocal response coefficients;
* a stress-tensor operator reads material response as a bilinear carrier form;
* a mathlib-linear derivation records how stress changes under operator transport.

It does not assert a concrete constitutive law. Material models provide the
calibration fields.
-/

noncomputable section

namespace InfoGeometry.Thermo.SusceptibilityOnsagerStress

open InfoGeometry.Thermo.SusceptibilityHessian

/-! ## 1. Two-operator Onsager forms -/

/--
A scalar two-operator form.

This is the abstract response kernel `L(A,B)` used for Onsager coefficients,
susceptibility pairings, and stress-response contractions.
-/
abbrev TwoOperatorForm
    (Op : Type*)
    [AddCommMonoid Op] [Module ℝ Op] : Type _ :=
  LinearMap.BilinForm ℝ Op

/--
An Onsager two-operator form.

The symmetry field is the reciprocal-response law. Positivity is kept as a
a separate theorem-owner obligation because indefinite/Krein response channels
are not automatically positive.
-/
structure OnsagerTwoOperatorForm
    (Op : Type*)
    [AddCommMonoid Op] [Module ℝ Op] where
  /-- Scalar response coefficient for a pair of operator perturbations. -/
  form : TwoOperatorForm Op

  /-- Onsager reciprocity. -/
  symmetric :
    ∀ A B : Op, form A B = form B A

  /-- Optional second-law/PSD constraint for the diagonal sector. -/
  diagonal_nonnegative : Prop

namespace OnsagerTwoOperatorForm

variable
    {Op : Type*}
    [AddCommMonoid Op] [Module ℝ Op]

variable (L : OnsagerTwoOperatorForm Op)

/-- Re-export of Onsager reciprocity. -/
@[rep_depth thermo]
theorem swap
    (A B : Op) :
    L.form A B = L.form B A :=
  L.symmetric A B

end OnsagerTwoOperatorForm

/-! ## 2. Susceptibility-induced Onsager pairings -/

/--
An Onsager pairing installed around a constructive Hessian-to-susceptibility
calibration.

The field `pairing` is the two-field response form, while
`pairing_from_susceptibility` records the concrete constitutive relation
chosen by a material model. For example, a model may pair `E₁` with `χ_U E₂`,
or use a Kubo/symmetrized response kernel.
-/
structure SusceptibilityOnsagerPairing
    (Op Field Response : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    (C : ConstructiveHessianSusceptibilityCalibration Op Field Response) where
  /-- Two-field Onsager response form at a material state. -/
  pairing : Op → TwoOperatorForm Field

  /-- Reciprocity of the field response pairing. -/
  pairing_symmetric :
    ∀ U : Op, ∀ E₁ E₂ : Field, pairing U E₁ E₂ = pairing U E₂ E₁

  /-- Constitutive relation connecting the pairing to the susceptibility `χ_U`. -/
  pairing_from_susceptibility : Prop

namespace SusceptibilityOnsagerPairing

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    {C : ConstructiveHessianSusceptibilityCalibration Op Field Response}

variable (P : SusceptibilityOnsagerPairing Op Field Response C)

/-- The susceptibility Onsager pairing is reciprocal in its two field slots. -/
@[rep_depth thermo]
theorem pairing_swap
    (U : Op)
    (E₁ E₂ : Field) :
    P.pairing U E₁ E₂ = P.pairing U E₂ E₁ :=
  P.pairing_symmetric U E₁ E₂

end SusceptibilityOnsagerPairing

/-! ## 3. Stress-tensor operator readouts -/

/--
A stress-tensor operator readout.

For each material/operator state `U`, it returns a bilinear stress tensor on a
carrier space. Symmetry and constitutive origin are proof-carrying fields.
-/
structure StressTensorOperator
    (Op Carrier : Type*)
    [AddCommMonoid Carrier] [Module ℝ Carrier] where
  /-- Stress tensor at a material/operator state. -/
  stress : Op → LinearMap.BilinForm ℝ Carrier

  /-- Stress tensor symmetry. -/
  stress_symmetric :
    ∀ U : Op, ∀ X Y : Carrier, stress U X Y = stress U Y X

  /-- Constitutive relation linking stress to the chosen response geometry. -/
  constitutive : Prop

namespace StressTensorOperator

variable
    {Op Carrier : Type*}
    [AddCommMonoid Carrier] [Module ℝ Carrier]

variable (T : StressTensorOperator Op Carrier)

/-- Re-export of stress-tensor symmetry. -/
@[rep_depth thermo]
theorem stress_swap
    (U : Op)
    (X Y : Carrier) :
    T.stress U X Y = T.stress U Y X :=
  T.stress_symmetric U X Y

end StressTensorOperator

/-! ## 4. Operator derivations -/

/--
A noncommutative operator derivation on a real module with multiplication.

Linearity is represented by mathlib's `LinearMap`; the only extra datum is the
product rule for the chosen multiplication.
-/
structure ThermodynamicOperatorDerivation
    (Op : Type*)
    [AddCommMonoid Op] [Module ℝ Op] [Mul Op] where
  /-- Linear derivation/readout map. -/
  toLinearMap : Op →ₗ[ℝ] Op

  /-- Product rule for the derivation. -/
  map_mul_eq :
    ∀ A B : Op, toLinearMap (A * B) = toLinearMap A * B + A * toLinearMap B

namespace ThermodynamicOperatorDerivation

variable
    {Op : Type*}
    [AddCommMonoid Op] [Module ℝ Op] [Mul Op]

instance : CoeFun (ThermodynamicOperatorDerivation Op) (fun _ => Op → Op) where
  coe D := D.toLinearMap

variable (D : ThermodynamicOperatorDerivation Op)

/-- Additivity follows from the underlying mathlib linear map. -/
@[rep_depth thermo]
theorem map_add
    (A B : Op) :
    D (A + B) = D A + D B :=
  D.toLinearMap.map_add A B

/-- Real homogeneity follows from the underlying mathlib linear map. -/
@[rep_depth thermo]
theorem map_smul
    (c : ℝ)
    (A : Op) :
    D (c • A) = c • D A :=
  D.toLinearMap.map_smul c A

/-- Product rule for the derivation. -/
@[rep_depth thermo]
theorem map_mul
    (A B : Op) :
    D (A * B) = D A * B + A * D B :=
  D.map_mul_eq A B

end ThermodynamicOperatorDerivation

/-! ## 5. Stress derivation response -/

/--
Stress response under an operator derivation.

`derivedStress U` is the stress tensor after applying the thermodynamic
derivation to the material/operator state. The equality field makes the
transport law explicit rather than pretending it follows from abstract
susceptibility alone.
-/
structure DerivedStressTensorResponse
    (Op Carrier : Type*)
    [AddCommMonoid Op] [Module ℝ Op] [Mul Op]
    [AddCommMonoid Carrier] [Module ℝ Carrier]
    (D : ThermodynamicOperatorDerivation Op)
    (T : StressTensorOperator Op Carrier) where
  /-- Derived stress readout. -/
  derivedStress : Op → LinearMap.BilinForm ℝ Carrier

  /-- Transport law: derived stress is stress evaluated on the derived state. -/
  derivedStress_eq :
    ∀ U : Op, derivedStress U = T.stress (D U)

namespace DerivedStressTensorResponse

variable
    {Op Carrier : Type*}
    [AddCommMonoid Op] [Module ℝ Op] [Mul Op]
    [AddCommMonoid Carrier] [Module ℝ Carrier]
    {D : ThermodynamicOperatorDerivation Op}
    {T : StressTensorOperator Op Carrier}

variable (R : DerivedStressTensorResponse Op Carrier D T)

/-- Re-export of the derived-stress transport law. -/
@[rep_depth thermo]
theorem derivedStress_eq_stress_derivation
    (U : Op) :
    R.derivedStress U = T.stress (D U) :=
  R.derivedStress_eq U

/-- Pointwise form of derived-stress transport. -/
@[rep_depth thermo]
theorem derivedStress_apply
    (U : Op)
    (X Y : Carrier) :
    R.derivedStress U X Y = T.stress (D U) X Y := by
  rw [R.derivedStress_eq_stress_derivation U]

/-- Derived stress remains symmetric because the stress readout is symmetric. -/
@[rep_depth thermo]
theorem derivedStress_swap
    (U : Op)
    (X Y : Carrier) :
    R.derivedStress U X Y = R.derivedStress U Y X := by
  rw [R.derivedStress_apply U X Y, R.derivedStress_apply U Y X]
  exact T.stress_swap (D U) X Y

end DerivedStressTensorResponse

/-! ## 6. Full susceptibility/Onsager/stress packet -/

/--
Full proof-carrying packet connecting susceptibility, Onsager two-operator
forms, stress-tensor readouts, and thermodynamic derivations.
-/
structure SusceptibilityOnsagerStressPacket
    (Op Field Response Carrier : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op] [Mul Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [AddCommMonoid Carrier] [Module ℝ Carrier] where
  /-- Constructive Hessian-to-susceptibility descent. -/
  hessianCalibration :
    ConstructiveHessianSusceptibilityCalibration Op Field Response

  /-- Onsager pairing around the susceptibility. -/
  onsagerPairing :
    SusceptibilityOnsagerPairing Op Field Response hessianCalibration

  /-- Operator-level Onsager response form. -/
  operatorOnsager :
    OnsagerTwoOperatorForm Op

  /-- Stress-tensor operator readout. -/
  stressTensor :
    StressTensorOperator Op Carrier

  /-- Thermodynamic operator derivation. -/
  derivation :
    ThermodynamicOperatorDerivation Op

  /-- Derived stress response under the thermodynamic derivation. -/
  derivedStress :
    DerivedStressTensorResponse Op Carrier derivation stressTensor

  /-- Calibration connecting the operator Onsager form to stress response. -/
  onsager_controls_stress : Prop

namespace SusceptibilityOnsagerStressPacket

variable
    {Op Field Response Carrier : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op] [Mul Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [AddCommMonoid Carrier] [Module ℝ Carrier]

variable (P : SusceptibilityOnsagerStressPacket Op Field Response Carrier)

/-- The operator Onsager form in the packet is reciprocal. -/
@[rep_depth thermo]
theorem operatorOnsager_swap
    (A B : Op) :
    P.operatorOnsager.form A B = P.operatorOnsager.form B A :=
  P.operatorOnsager.swap A B

/-- The field Onsager pairing in the packet is reciprocal. -/
@[rep_depth thermo]
theorem fieldOnsager_swap
    (U : Op)
    (E₁ E₂ : Field) :
    P.onsagerPairing.pairing U E₁ E₂ = P.onsagerPairing.pairing U E₂ E₁ :=
  P.onsagerPairing.pairing_swap U E₁ E₂

/-- The packet stress tensor is symmetric. -/
@[rep_depth thermo]
theorem stressTensor_swap
    (U : Op)
    (X Y : Carrier) :
    P.stressTensor.stress U X Y = P.stressTensor.stress U Y X :=
  P.stressTensor.stress_swap U X Y

/-- The packet derived stress is stress evaluated on the derived operator. -/
@[rep_depth thermo]
theorem derivedStress_eq_stress_derivation
    (U : Op) :
    P.derivedStress.derivedStress U = P.stressTensor.stress (P.derivation U) :=
  P.derivedStress.derivedStress_eq_stress_derivation U

/-- Pointwise derived-stress identity. -/
@[rep_depth thermo]
theorem derivedStress_apply
    (U : Op)
    (X Y : Carrier) :
    P.derivedStress.derivedStress U X Y =
      P.stressTensor.stress (P.derivation U) X Y :=
  P.derivedStress.derivedStress_apply U X Y

/-- Derived stress remains symmetric. -/
@[rep_depth thermo]
theorem derivedStress_swap
    (U : Op)
    (X Y : Carrier) :
    P.derivedStress.derivedStress U X Y =
      P.derivedStress.derivedStress U Y X :=
  P.derivedStress.derivedStress_swap U X Y

end SusceptibilityOnsagerStressPacket

/-! ## 7. Owner target -/

/--
Owner target for installing a susceptibility/Onsager/stress/derivation packet.
-/
def SusceptibilityOnsagerStressOwnerTarget
    (Op Field Response Carrier : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op] [Mul Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [AddCommMonoid Carrier] [Module ℝ Carrier] : Prop :=
  ∀ (P : SusceptibilityOnsagerStressPacket Op Field Response Carrier),
    (∀ (A B : Op),
      P.operatorOnsager.form A B = P.operatorOnsager.form B A) ∧
    (∀ (U : Op) (E₁ E₂ : Field),
      P.onsagerPairing.pairing U E₁ E₂ = P.onsagerPairing.pairing U E₂ E₁) ∧
    (∀ (U : Op) (X Y : Carrier),
      P.stressTensor.stress U X Y = P.stressTensor.stress U Y X) ∧
    (∀ (U : Op),
      P.derivedStress.derivedStress U = P.stressTensor.stress (P.derivation U))

/--
Any installed susceptibility/Onsager/stress packet satisfies the owner-side
reciprocity, symmetry, and readback laws already proved in this file.
-/
theorem susceptibilityOnsagerStressOwnerTarget
    (Op Field Response Carrier : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op] [Mul Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [AddCommMonoid Carrier] [Module ℝ Carrier] :
    ∀ (P : SusceptibilityOnsagerStressPacket Op Field Response Carrier),
      (∀ (A B : Op),
        P.operatorOnsager.form A B = P.operatorOnsager.form B A) ∧
      (∀ (U : Op) (E₁ E₂ : Field),
        P.onsagerPairing.pairing U E₁ E₂ = P.onsagerPairing.pairing U E₂ E₁) ∧
      (∀ (U : Op) (X Y : Carrier),
        P.stressTensor.stress U X Y = P.stressTensor.stress U Y X) ∧
      (∀ (U : Op),
        P.derivedStress.derivedStress U = P.stressTensor.stress (P.derivation U)) := by
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B
    exact P.operatorOnsager_swap A B
  · intro U E₁ E₂
    exact P.fieldOnsager_swap U E₁ E₂
  · intro U X Y
    exact P.stressTensor_swap U X Y
  · intro U
    exact P.derivedStress_eq_stress_derivation U

end InfoGeometry.Thermo.SusceptibilityOnsagerStress
