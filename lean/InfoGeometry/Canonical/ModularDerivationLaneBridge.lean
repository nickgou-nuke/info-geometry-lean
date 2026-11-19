/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NonAssocDerivation
import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.Thermo.OnsagerDifferentialFormsBridge
import InfoGeometry.Modular.DerivationLieIdeal
import InfoGeometry.Modular.DualExponentialCommutatorBridge
import InfoGeometry.Modular.DualFlowLieAlgebraBridge
import InfoGeometry.Modular.NoncommutativeModularRadonSurprisalBridge
import InfoGeometry.Modular.NoncommutativeRadonNikodymDLog
import InfoGeometry.Modular.CommutantSemidirectProduct
import InfoGeometry.Modular.InnerDerivationLieIdeal
import InfoGeometry.Modular.ModularTimeSemigroupBridge
import InfoGeometry.Modular.SuperKMS
import InfoGeometry.Modular.KMSState
import InfoGeometry.Modular.TrifoldRadonNikodymBridge
import InfoGeometry.Modular.ModularSurprisalDerivationBridge
import InfoGeometry.Information.ModularSurprisalDerivationBridge
import InfoGeometry.Modular.SemidirectExteriorAlgebra
import InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge
import InfoGeometry.Algebra.DualAlgebraAutomorphismDerivationBridge
import InfoGeometry.Canonical.OperatorialFierzDerivationBridge
import InfoGeometry.EndToEnd
import InfoGeometry.EndToEnd.KMS
import InfoGeometry.QuantumGeometry.BerryKeatingDilationBridge
import InfoGeometry.Canonical.AlbertAlgebraGenerationsBridge
import InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra
import InfoGeometry.Modular.ColimitFlowDerivation
import InfoGeometry.Modular.ColimitKMSInfinitesimal
import InfoGeometry.Modular.ModularColimitDerivation
import InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
import InfoGeometry.Canonical.CoreHypothesisTheoremFoundations
import InfoGeometry.QuantumGeometry.DensityOperatorDLogHomomorphism
import InfoGeometry.Synthesis
import InfoGeometry.QuantumGeometry.DualExponentialArchitectureCertificate
import InfoGeometry.QuantumGeometry.NoncommutativePhaseSpace
import InfoGeometry.Topological.DonaldsonWittenNonassociativeBRST
import InfoGeometry.Algebra.CuntzDerivationTangent
import InfoGeometry.Algebra.CuntzSharpTangent
import InfoGeometry.OperatorAlgebra.KreinInnerDerivation
import InfoGeometry.Canonical.CoordinateFreeSouriau

/-!
# Additive Unification of Modular and Associative `*Derivation` Lanes (Gap D Part 1)

This module unifies the unconsolidated `InfoGeometry.Modular.*` derivation wrappers,
tower/colimit derivation lanes, and standalone `[Ring]` / `R`-linear `*Derivation`
wrappers into the canonical spine:

- `InfoGeometry.Algebra.NonAssocDerivation.derivations`
- `InfoGeometry.Algebra.DerivationLieLane` (`fullDerivationLieLane`, `lieSubalgebraLane`)
- `InfoGeometry.Thermo.OnsagerFormsBridge` (`inducedDerivationLaneOnsagerSystem`,
  `onsager_pairing_derivationForm_reciprocity`)

All bridges are purely additive (`≃`, `≃+`, `≃ₗ[R]`, `≃ₗ⁅R⁆`, or injective maps
onto subtypes/Lie subalgebras), introduce zero global typeclass instances, and
preserve all existing owner definitions and downstream consumers untouched.
-/

namespace InfoGeometry.Canonical.ModularDerivationLaneBridge

open InfoGeometry.Algebra (DerivationLieLane LieActionLane DerivationLaneEquiv)
open InfoGeometry.Algebra.NonAssocDerivation (IsLeibniz derivations)
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
  (fullDerivationLieLane lieSubalgebraLane DerivationOperatorForm ceExteriorDerivative ceCurvature
   zeroFormAlternatingEquiv modularInnerIdeal)
open InfoGeometry.Thermo.OnsagerClosure (OnsagerCasimirSystem)
open InfoGeometry.Thermo.OnsagerFormsBridge
  (OnsagerFormPairing ParityOnsagerFormPairing inducedDerivationLaneOnsagerSystem
   inducedDerivationLaneOnsagerSystem_totalGenerator onsager_pairing_derivationForm_reciprocity)

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private def intLinearEndOfAdd {A : Type*} [AddCommGroup A] (f : A → A)
    (hf : ∀ x y, f (x + y) = f x + f y) : Module.End ℤ A where
  toFun := f
  map_add' := hf
  map_smul' := fun n x => by
    change f (n • x) = n • f x
    exact (AddMonoidHom.mk' f hf).map_zsmul n x

/-! ## F7.1: Four `Modular.*.RingDerivation` Bridges & `FullLieAlgebra.Der` -/

section F7_1_RingDerivations

variable {A : Type*} [Ring A]

/-- Equivalence between `InfoGeometry.Modular.LieIdeal.RingDerivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def lieIdealRingDerivationEquivDerivations :
    InfoGeometry.Modular.LieIdeal.RingDerivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by
    apply InfoGeometry.Modular.LieIdeal.RingDerivation.extensionality
    intro x; rfl
  right_inv D := by
    apply Subtype.ext; ext x; rfl

theorem lieIdealRingDerivationEquivDerivations_zero :
    lieIdealRingDerivationEquivDerivations
        (InfoGeometry.Modular.LieIdeal.RingDerivation.zero :
          InfoGeometry.Modular.LieIdeal.RingDerivation A) = 0 := by
  apply Subtype.ext; ext x; rfl

theorem lieIdealRingDerivationEquivDerivations_add
    (D₁ D₂ : InfoGeometry.Modular.LieIdeal.RingDerivation A) :
    lieIdealRingDerivationEquivDerivations
        (InfoGeometry.Modular.LieIdeal.RingDerivation.add D₁ D₂) =
      lieIdealRingDerivationEquivDerivations D₁ +
        lieIdealRingDerivationEquivDerivations D₂ := by
  apply Subtype.ext; ext x; rfl

theorem lieIdealRingDerivationEquivDerivations_neg
    (D : InfoGeometry.Modular.LieIdeal.RingDerivation A) :
    lieIdealRingDerivationEquivDerivations
        (InfoGeometry.Modular.LieIdeal.RingDerivation.neg D) =
      -lieIdealRingDerivationEquivDerivations D := by
  apply Subtype.ext; ext x; rfl

theorem lieIdealRingDerivationEquivDerivations_commutator
    (D₁ D₂ : InfoGeometry.Modular.LieIdeal.RingDerivation A) :
    lieIdealRingDerivationEquivDerivations
        (InfoGeometry.Modular.LieIdeal.RingDerivation.commutator D₁ D₂) =
      ⁅lieIdealRingDerivationEquivDerivations D₁,
        lieIdealRingDerivationEquivDerivations D₂⁆ := by
  apply Subtype.ext; ext x; rfl

theorem lieIdealRingDerivation_isInner_iff
    (D : InfoGeometry.Modular.LieIdeal.RingDerivation A) :
    InfoGeometry.Modular.LieIdeal.isInner D ↔
      lieIdealRingDerivationEquivDerivations D ∈ modularInnerIdeal A := by
  constructor
  · rintro ⟨K, rfl⟩
    refine ⟨K, ?_⟩
    apply Subtype.ext; ext x; rfl
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    apply InfoGeometry.Modular.LieIdeal.RingDerivation.extensionality
    intro x
    have hx := congrArg (fun d : derivations ℤ A => (d : Module.End ℤ A) x) hK
    exact hx.symm

/-- Equivalence between `InfoGeometry.Modular.DualExponential.RingDerivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def dualExponentialRingDerivationEquivDerivations :
    InfoGeometry.Modular.DualExponential.RingDerivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by
    apply InfoGeometry.Modular.DualExponential.RingDerivation.extensionality
    intro x; rfl
  right_inv D := by
    apply Subtype.ext; ext x; rfl

theorem dualExponentialRingDerivationEquivDerivations_commutator
    (D₁ D₂ : InfoGeometry.Modular.DualExponential.RingDerivation A) :
    dualExponentialRingDerivationEquivDerivations
        (InfoGeometry.Modular.DualExponential.RingDerivation.commutator D₁ D₂) =
      ⁅dualExponentialRingDerivationEquivDerivations D₁,
        dualExponentialRingDerivationEquivDerivations D₂⁆ := by
  apply Subtype.ext; ext x; rfl

theorem dualExponentialRingDerivation_add_apply
    (D₁ D₂ : InfoGeometry.Modular.DualExponential.RingDerivation A) (x : A) :
    ((dualExponentialRingDerivationEquivDerivations D₁ +
        dualExponentialRingDerivationEquivDerivations D₂ : derivations ℤ A) :
      Module.End ℤ A) x = D₁ x + D₂ x := rfl

/-- Equivalence between `InfoGeometry.Modular.LieAlgebra.RingDerivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def lieAlgebraRingDerivationEquivDerivations :
    InfoGeometry.Modular.LieAlgebra.RingDerivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by
    cases D; rfl
  right_inv D := by
    apply Subtype.ext; ext x; rfl

theorem lieAlgebraRingDerivationEquivDerivations_commutator
    (D₁ D₂ : InfoGeometry.Modular.LieAlgebra.RingDerivation A) :
    lieAlgebraRingDerivationEquivDerivations
        (InfoGeometry.Modular.LieAlgebra.RingDerivation.derivationCommutator D₁ D₂) =
      ⁅lieAlgebraRingDerivationEquivDerivations D₁,
        lieAlgebraRingDerivationEquivDerivations D₂⁆ := by
  apply Subtype.ext; ext x; rfl

theorem lieAlgebraRingDerivation_add_apply
    (D₁ D₂ : InfoGeometry.Modular.LieAlgebra.RingDerivation A) (x : A) :
    ((lieAlgebraRingDerivationEquivDerivations D₁ +
        lieAlgebraRingDerivationEquivDerivations D₂ : derivations ℤ A) :
      Module.End ℤ A) x = D₁ x + D₂ x := rfl

/-- Equivalence between `InfoGeometry.Modular.Synthesis.RingDerivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def synthesisRingDerivationEquivDerivations :
    InfoGeometry.Modular.Synthesis.RingDerivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by
    cases D; rfl
  right_inv D := by
    apply Subtype.ext; ext x; rfl

theorem synthesisRingDerivation_add_apply
    (D₁ D₂ : InfoGeometry.Modular.Synthesis.RingDerivation A) (x : A) :
    ((synthesisRingDerivationEquivDerivations D₁ +
        synthesisRingDerivationEquivDerivations D₂ : derivations ℤ A) :
      Module.End ℤ A) x = D₁ x + D₂ x := rfl

theorem synthesisRingDerivation_bracket_apply
    (D₁ D₂ : InfoGeometry.Modular.Synthesis.RingDerivation A) (x : A) :
    (⁅synthesisRingDerivationEquivDerivations D₁,
        synthesisRingDerivationEquivDerivations D₂⁆ : Module.End ℤ A) x =
      D₁ (D₂ x) - D₂ (D₁ x) := rfl

/-- Lie algebra homomorphism from associative derivations `NonAssocDerivation.derivations R A`
into `InfoGeometry.Modular.FullLieAlgebra.Der R A` (`LieDerivation R A A`). -/
def derivationsToFullLieDerHom (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    derivations R A →ₗ⁅R⁆ InfoGeometry.Modular.FullLieAlgebra.Der R A where
  toFun D :=
    { toLinearMap := (D : Module.End R A)
      leibniz' := fun {a b} => by
        change (D : Module.End R A) (a * b - b * a) =
          (a * (D : Module.End R A) b - (D : Module.End R A) b * a) -
          (b * (D : Module.End R A) a - (D : Module.End R A) a * b)
        rw [LinearMap.map_sub, D.property a b, D.property b a]
        abel }
  map_add' D₁ D₂ := by
    ext a; rfl
  map_smul' r D := by
    ext a; rfl
  map_lie' {D₁ D₂} := by
    ext a
    change (D₁ : Module.End R A) ((D₂ : Module.End R A) a) -
        (D₂ : Module.End R A) ((D₁ : Module.End R A) a) =
      (D₁ : Module.End R A) ((D₂ : Module.End R A) a) -
        (D₂ : Module.End R A) ((D₁ : Module.End R A) a)
    rfl

/-- Canonical `LieActionLane R A` for `InfoGeometry.Modular.FullLieAlgebra.Der R A`
(`LieDerivation R A A` acting on `A` by evaluation). -/
def fullLieDerLieActionLane (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    LieActionLane R A where
  L := InfoGeometry.Modular.FullLieAlgebra.Der R A
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act :=
    { toFun := fun D => D.toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := fun {D₁ D₂} => by
        ext a
        rfl }

end F7_1_RingDerivations

/-! ## F7.2: Four Additive `Modular/*` Derivation Bridges -/

section F7_2_AdditiveDerivations

variable {A : Type*} [Ring A]

/-- Equivalence between `InfoGeometry.Modular.NoncommutativeRN.NoncommutativeDerivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def noncommutativeDerivationEquivDerivations :
    InfoGeometry.Modular.NoncommutativeRN.NoncommutativeDerivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by
    apply InfoGeometry.Modular.NoncommutativeRN.NoncommutativeDerivation.ext
    intro x; rfl
  right_inv D := by
    apply Subtype.ext; ext x; rfl

theorem noncommutativeDerivationEquivDerivations_commutator
    (D₁ D₂ : InfoGeometry.Modular.NoncommutativeRN.NoncommutativeDerivation A) :
    noncommutativeDerivationEquivDerivations
        (InfoGeometry.Modular.NoncommutativeRN.commutatorDerivation D₁ D₂) =
      ⁅noncommutativeDerivationEquivDerivations D₁,
        noncommutativeDerivationEquivDerivations D₂⁆ := by
  apply Subtype.ext; ext x; rfl

theorem noncommutativeDerivation_add_apply
    (D₁ D₂ : InfoGeometry.Modular.NoncommutativeRN.NoncommutativeDerivation A) (x : A) :
    ((noncommutativeDerivationEquivDerivations D₁ +
        noncommutativeDerivationEquivDerivations D₂ : derivations ℤ A) :
      Module.End ℤ A) x = D₁ x + D₂ x := rfl

/-- Equivalence between `InfoGeometry.Modular.Commutant.Derivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def commutantDerivationEquivDerivations :
    InfoGeometry.Modular.Commutant.Derivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by
    cases D; rfl
  right_inv D := by
    apply Subtype.ext; ext x; rfl

theorem commutantDerivationEquivDerivations_commutator
    (D₁ D₂ : InfoGeometry.Modular.Commutant.Derivation A) :
    commutantDerivationEquivDerivations
        (InfoGeometry.Modular.Commutant.Derivation.commutator D₁ D₂) =
      ⁅commutantDerivationEquivDerivations D₁,
        commutantDerivationEquivDerivations D₂⁆ := by
  apply Subtype.ext; ext x; rfl

theorem commutantSemidirect_der_bracket
    (E₁ E₂ : InfoGeometry.Modular.Commutant.SemidirectElement A) :
    commutantDerivationEquivDerivations
        (InfoGeometry.Modular.Commutant.semidirectBracket E₁ E₂).der =
      ⁅commutantDerivationEquivDerivations E₁.der,
        commutantDerivationEquivDerivations E₂.der⁆ := by
  apply Subtype.ext; ext x; rfl

theorem commutantDerivation_add_apply
    (D₁ D₂ : InfoGeometry.Modular.Commutant.Derivation A) (x : A) :
    ((commutantDerivationEquivDerivations D₁ +
        commutantDerivationEquivDerivations D₂ : derivations ℤ A) :
      Module.End ℤ A) x = D₁ x + D₂ x := rfl

/-- Additive equivalence (`≃+`) between `InfoGeometry.Modular.LieIdeal.Derivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def lieIdealDerivationAddEquivDerivations :
    InfoGeometry.Modular.LieIdeal.Derivation A ≃+ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by
    apply InfoGeometry.Modular.LieIdeal.Derivation.ext
    intro x; rfl
  right_inv D := by
    apply Subtype.ext; ext x; rfl
  map_add' D₁ D₂ := by
    apply Subtype.ext; ext x; rfl

theorem lieIdealDerivationAddEquivDerivations_commutator
    (D₁ D₂ : InfoGeometry.Modular.LieIdeal.Derivation A) :
    lieIdealDerivationAddEquivDerivations
        (InfoGeometry.Modular.LieIdeal.Derivation.commutator D₁ D₂) =
      ⁅lieIdealDerivationAddEquivDerivations D₁,
        lieIdealDerivationAddEquivDerivations D₂⁆ := by
  apply Subtype.ext; ext x; rfl

theorem lieIdealDerivation_isInner_iff
    (D : InfoGeometry.Modular.LieIdeal.Derivation A) :
    InfoGeometry.Modular.LieIdeal.isInnerDerivation D ↔
      lieIdealDerivationAddEquivDerivations D ∈ modularInnerIdeal A := by
  constructor
  · rintro ⟨K, rfl⟩
    refine ⟨K, ?_⟩
    apply Subtype.ext; ext x; rfl
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    apply InfoGeometry.Modular.LieIdeal.Derivation.ext
    intro x
    have hx := congrArg (fun d : derivations ℤ A => (d : Module.End ℤ A) x) hK
    exact hx.symm

/-- Equivalence between `InfoGeometry.Modular.TimeSemigroup.Derivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def timeSemigroupDerivationEquivDerivations :
    InfoGeometry.Modular.TimeSemigroup.Derivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by
    cases D; rfl
  right_inv D := by
    apply Subtype.ext; ext x; rfl

theorem timeSemigroupDerivation_opComm
    (D₁ D₂ : InfoGeometry.Modular.TimeSemigroup.Derivation A) (x : A) :
    (⁅timeSemigroupDerivationEquivDerivations D₁,
        timeSemigroupDerivationEquivDerivations D₂⁆ : Module.End ℤ A) x =
      InfoGeometry.Modular.TimeSemigroup.opComm D₁ D₂ x := rfl

theorem timeSemigroupDerivation_add_apply
    (D₁ D₂ : InfoGeometry.Modular.TimeSemigroup.Derivation A) (x : A) :
    ((timeSemigroupDerivationEquivDerivations D₁ +
        timeSemigroupDerivationEquivDerivations D₂ : derivations ℤ A) :
      Module.End ℤ A) x = D₁ x + D₂ x := rfl

end F7_2_AdditiveDerivations

/-! ## F7.3: `R`-Linear `Modular/*` & Associative `*Derivation` Bridges -/

section F7_3_LinearAndAssociativeDerivations

/-- Equivalence between `InfoGeometry.Modular.SuperKMS.LinearDerivation R A` and
`NonAssocDerivation.derivations R A` under `[CommRing R] [Ring A] [Algebra R A]`. -/
def superKMSLinearDerivationEquivDerivations
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    InfoGeometry.Modular.SuperKMS.LinearDerivation R A ≃ derivations R A where
  toFun D := ⟨D.toLinearMap, D.leibniz'⟩
  invFun D := ⟨(D : Module.End R A), D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

theorem superKMSLinearDerivation_add_apply
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D₁ D₂ : InfoGeometry.Modular.SuperKMS.LinearDerivation R A) (x : A) :
    ((superKMSLinearDerivationEquivDerivations D₁ +
        superKMSLinearDerivationEquivDerivations D₂ : derivations R A) :
      Module.End R A) x = D₁.toLinearMap x + D₂.toLinearMap x := rfl

theorem superKMSLinearDerivation_bracket_apply
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D₁ D₂ : InfoGeometry.Modular.SuperKMS.LinearDerivation R A) (x : A) :
    (⁅superKMSLinearDerivationEquivDerivations D₁,
        superKMSLinearDerivationEquivDerivations D₂⁆ : Module.End R A) x =
      D₁.toLinearMap (D₂.toLinearMap x) - D₂.toLinearMap (D₁.toLinearMap x) := rfl

/-- Scalar-restricted injective embedding of `SuperKMS.LinearDerivation R A` into
`NonAssocDerivation.derivations ℤ A` for arbitrary `[Ring R]`. -/
def superKMSLinearDerivationToZDerivations
    {R A : Type*} [Ring R] [Ring A] [Module R A]
    (D : InfoGeometry.Modular.SuperKMS.LinearDerivation R A) : derivations ℤ A :=
  ⟨D.toLinearMap.restrictScalars ℤ, D.leibniz'⟩

theorem superKMSLinearDerivationToZDerivations_injective
    {R A : Type*} [Ring R] [Ring A] [Module R A] :
    Function.Injective (superKMSLinearDerivationToZDerivations (R := R) (A := A)) := by
  intro D₁ D₂ h
  cases D₁ with
  | mk f₁ h₁ =>
    cases D₂ with
    | mk f₂ h₂ =>
      congr 1
      ext x
      exact congrArg (fun d : derivations ℤ A => (d : Module.End ℤ A) x) h

/-- Equivalence between `InfoGeometry.Modular.KMSState.LinearDerivation R A` and
`NonAssocDerivation.derivations R A` under `[CommRing R] [Ring A] [Algebra R A]`. -/
def kmsStateLinearDerivationEquivDerivations
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    InfoGeometry.Modular.KMSState.LinearDerivation R A ≃ derivations R A where
  toFun D := ⟨D.toLinearMap, D.leibniz'⟩
  invFun D := ⟨(D : Module.End R A), D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

theorem kmsStateLinearDerivation_add_apply
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D₁ D₂ : InfoGeometry.Modular.KMSState.LinearDerivation R A) (x : A) :
    ((kmsStateLinearDerivationEquivDerivations D₁ +
        kmsStateLinearDerivationEquivDerivations D₂ : derivations R A) :
      Module.End R A) x = D₁.toLinearMap x + D₂.toLinearMap x := rfl

theorem kmsStateLinearDerivation_bracket_apply
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D₁ D₂ : InfoGeometry.Modular.KMSState.LinearDerivation R A) (x : A) :
    (⁅kmsStateLinearDerivationEquivDerivations D₁,
        kmsStateLinearDerivationEquivDerivations D₂⁆ : Module.End R A) x =
      D₁.toLinearMap (D₂.toLinearMap x) - D₂.toLinearMap (D₁.toLinearMap x) := rfl

/-- Scalar-restricted injective embedding of `KMSState.LinearDerivation R A` into
`NonAssocDerivation.derivations ℤ A` for arbitrary `[Ring R]`. -/
def kmsStateLinearDerivationToZDerivations
    {R A : Type*} [Ring R] [Ring A] [Module R A]
    (D : InfoGeometry.Modular.KMSState.LinearDerivation R A) : derivations ℤ A :=
  ⟨D.toLinearMap.restrictScalars ℤ, D.leibniz'⟩

theorem kmsStateLinearDerivationToZDerivations_injective
    {R A : Type*} [Ring R] [Ring A] [Module R A] :
    Function.Injective (kmsStateLinearDerivationToZDerivations (R := R) (A := A)) := by
  intro D₁ D₂ h
  cases D₁ with
  | mk f₁ h₁ =>
    cases D₂ with
    | mk f₂ h₂ =>
      congr 1
      ext x
      exact congrArg (fun d : derivations ℤ A => (d : Module.End ℤ A) x) h

-- Three `IsLinearDerivation` predicates (`TrifoldRadonNikodymBridge`,
-- `Modular.ModularSurprisalDerivationBridge`, `Information.ModularSurprisalDerivationBridge`).

theorem trifoldIsLinearDerivation_iff_isLeibniz {R : Type*} [CommRing R] (D : R →ₗ[R] R) :
    InfoGeometry.Modular.IsLinearDerivation D ↔ IsLeibniz R R D :=
  Iff.rfl

/-- Equivalence for `TrifoldRadonNikodymBridge`'s `InfoGeometry.Modular.IsLinearDerivation`. -/
def trifoldIsLinearDerivationEquivDerivations {R : Type*} [CommRing R] :
    { D : R →ₗ[R] R // InfoGeometry.Modular.IsLinearDerivation D } ≃ derivations R R where
  toFun D := ⟨D.1, D.2⟩
  invFun D := ⟨(D : Module.End R R), D.property⟩
  left_inv D := by cases D; rfl
  right_inv _ := rfl

theorem modularSurprisalIsLinearDerivation_iff_isLeibniz
    {R : Type*} [CommRing R] (D : R →ₗ[R] R) :
    InfoGeometry.Modular.ModularSurprisalDerivationBridge.IsLinearDerivation D ↔
      IsLeibniz R R D :=
  Iff.rfl

/-- Equivalence for `Modular.ModularSurprisalDerivationBridge.IsLinearDerivation`. -/
def modularSurprisalIsLinearDerivationEquivDerivations {R : Type*} [CommRing R] :
    { D : R →ₗ[R] R //
      InfoGeometry.Modular.ModularSurprisalDerivationBridge.IsLinearDerivation D } ≃
      derivations R R where
  toFun D := ⟨D.1, D.2⟩
  invFun D := ⟨(D : Module.End R R), D.property⟩
  left_inv D := by cases D; rfl
  right_inv _ := rfl

theorem infoModularSurprisalIsLinearDerivation_iff_isLeibniz
    {R : Type*} [CommRing R] (D : R →ₗ[R] R) :
    InfoGeometry.Information.ModularSurprisalDerivationBridge.IsLinearDerivation D ↔
      IsLeibniz R R D :=
  Iff.rfl

/-- Equivalence for `Information.ModularSurprisalDerivationBridge.IsLinearDerivation`. -/
def infoModularSurprisalIsLinearDerivationEquivDerivations {R : Type*} [CommRing R] :
    { D : R →ₗ[R] R //
      InfoGeometry.Information.ModularSurprisalDerivationBridge.IsLinearDerivation D } ≃
      derivations R R where
  toFun D := ⟨D.1, D.2⟩
  invFun D := ⟨(D : Module.End R R), D.property⟩
  left_inv D := by cases D; rfl
  right_inv _ := rfl

/-- Equivalence between `InfoGeometry.Modular.SemidirectExterior.Derivation R A` and
`NonAssocDerivation.derivations R A` under `[CommRing R] [Ring A] [Algebra R A]`. -/
def semidirectDerivationEquivDerivations
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    InfoGeometry.Modular.SemidirectExterior.Derivation R A ≃ derivations R A where
  toFun D :=
    ⟨{ toFun := D.toFun
       map_add' := D.map_add'
       map_smul' := D.map_smul' }, D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End R A),
     fun x y => (D : Module.End R A).map_add x y,
     fun c x => (D : Module.End R A).map_smul c x,
     D.property⟩
  left_inv D := by
    apply InfoGeometry.Modular.SemidirectExterior.Derivation.ext
    intro x; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

theorem semidirectDerivationEquivDerivations_zero
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    semidirectDerivationEquivDerivations
        (0 : InfoGeometry.Modular.SemidirectExterior.Derivation R A) = 0 := by
  apply Subtype.ext; ext x; rfl

theorem semidirectDerivationEquivDerivations_commutator
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D₁ D₂ : InfoGeometry.Modular.SemidirectExterior.Derivation R A) :
    semidirectDerivationEquivDerivations
        (InfoGeometry.Modular.SemidirectExterior.Derivation.commutator D₁ D₂) =
      ⁅semidirectDerivationEquivDerivations D₁,
        semidirectDerivationEquivDerivations D₂⁆ := by
  apply Subtype.ext; ext x; rfl

/-- Scalar-restricted injective embedding of `SemidirectExterior.Derivation R A` into
`NonAssocDerivation.derivations ℤ A` for arbitrary `[Ring R]`. -/
def semidirectDerivationToZDerivations
    {R A : Type*} [Ring R] [Ring A] [Module R A]
    (D : InfoGeometry.Modular.SemidirectExterior.Derivation R A) : derivations ℤ A :=
  ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩

theorem semidirectDerivationToZDerivations_injective
    {R A : Type*} [Ring R] [Ring A] [Module R A] :
    Function.Injective (semidirectDerivationToZDerivations (R := R) (A := A)) := by
  intro D₁ D₂ h
  apply InfoGeometry.Modular.SemidirectExterior.Derivation.ext
  intro x
  exact congrArg (fun d : derivations ℤ A => (d : Module.End ℤ A) x) h

/-- Injective embedding of `TrifoldSurprisalIntertwiningBridge.OuterDerivation ι R` into
`NonAssocDerivation.derivations R (Matrix (ι ⊕ ι) (ι ⊕ ι) R)` under `[CommRing R]`. -/
def outerDerivationToDerivations
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (D : InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.OuterDerivation ι R) :
    derivations R (Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
  ⟨D.toLinearMap, D.leibniz'⟩

theorem outerDerivationToDerivations_injective
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] :
    Function.Injective (outerDerivationToDerivations (ι := ι) (R := R)) := by
  intro D₁ D₂ h
  cases D₁ with
  | mk f₁ l₁ o₁ g₁ =>
    cases D₂ with
    | mk f₂ l₂ o₂ g₂ =>
      congr 1
      exact LinearMap.ext fun x =>
        congrArg (fun d : derivations R (Matrix (ι ⊕ ι) (ι ⊕ ι) R) =>
          (d : Module.End R _) x) h

/-- Exact subtype equivalence characterizing `OuterDerivation ι R` as derivations
vanishing on `1` and `GammaGrading`. -/
def outerDerivationEquivSubtype
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] :
    InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.OuterDerivation ι R ≃
      { D : derivations R (Matrix (ι ⊕ ι) (ι ⊕ ι) R) //
        (D : Module.End R (Matrix (ι ⊕ ι) (ι ⊕ ι) R)) 1 = 0 ∧
        (D : Module.End R (Matrix (ι ⊕ ι) (ι ⊕ ι) R))
          (InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.GammaGrading :
            Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 0 } where
  toFun D := ⟨outerDerivationToDerivations D, D.map_one', D.map_gamma'⟩
  invFun D := ⟨(D.1 : Module.End R (Matrix (ι ⊕ ι) (ι ⊕ ι) R)), D.1.property, D.2.1, D.2.2⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; apply Subtype.ext; ext x; rfl

/-- Scalar-restricted injective embedding of `OuterDerivation ι R` into
`NonAssocDerivation.derivations ℤ (Matrix (ι ⊕ ι) (ι ⊕ ι) R)` for arbitrary `[Ring R]`. -/
def outerDerivationToZDerivations
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (D : InfoGeometry.Modular.TrifoldSurprisalIntertwiningBridge.OuterDerivation ι R) :
    derivations ℤ (Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
  ⟨D.toLinearMap.restrictScalars ℤ, D.leibniz'⟩

theorem outerDerivationToZDerivations_injective
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R] :
    Function.Injective (outerDerivationToZDerivations (ι := ι) (R := R)) := by
  intro D₁ D₂ h
  cases D₁ with
  | mk f₁ l₁ o₁ g₁ =>
    cases D₂ with
    | mk f₂ l₂ o₂ g₂ =>
      congr 1
      exact LinearMap.ext fun x =>
        congrArg (fun d : derivations ℤ (Matrix (ι ⊕ ι) (ι ⊕ ι) R) =>
          (d : Module.End ℤ _) x) h

/-- Equivalence between `InfoGeometry.Algebra.DualAlgebra.AlgDerivation R B` and
`NonAssocDerivation.derivations R B` on non-associative `B`. -/
def algDerivationEquivDerivations
    {R B : Type*} [CommRing R] [NonUnitalNonAssocRing B] [Module R B]
    [IsScalarTower R B B] [SMulCommClass R B B] :
    InfoGeometry.Algebra.DualAlgebra.AlgDerivation R B ≃ derivations R B where
  toFun D :=
    ⟨{ toFun := D.toFun
       map_add' := D.map_add'
       map_smul' := D.map_smul' }, D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End R B),
     fun x y => (D : Module.End R B).map_add x y,
     fun r x => (D : Module.End R B).map_smul r x,
     D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

theorem algDerivationEquivDerivations_zero
    {R B : Type*} [CommRing R] [NonUnitalNonAssocRing B] [Module R B]
    [IsScalarTower R B B] [SMulCommClass R B B] :
    algDerivationEquivDerivations
        (InfoGeometry.Algebra.DualAlgebra.AlgDerivation.zero :
          InfoGeometry.Algebra.DualAlgebra.AlgDerivation R B) = 0 := by
  apply Subtype.ext; ext x; rfl

theorem algDerivationEquivDerivations_add
    {R B : Type*} [CommRing R] [NonUnitalNonAssocRing B] [Module R B]
    [IsScalarTower R B B] [SMulCommClass R B B]
    (D₁ D₂ : InfoGeometry.Algebra.DualAlgebra.AlgDerivation R B) :
    algDerivationEquivDerivations
        (InfoGeometry.Algebra.DualAlgebra.AlgDerivation.add D₁ D₂) =
      algDerivationEquivDerivations D₁ + algDerivationEquivDerivations D₂ := by
  apply Subtype.ext; ext x; rfl

theorem algDerivationEquivDerivations_neg
    {R B : Type*} [CommRing R] [NonUnitalNonAssocRing B] [Module R B]
    [IsScalarTower R B B] [SMulCommClass R B B]
    (D : InfoGeometry.Algebra.DualAlgebra.AlgDerivation R B) :
    algDerivationEquivDerivations
        (InfoGeometry.Algebra.DualAlgebra.DualExt.negDerivation D) =
      -algDerivationEquivDerivations D := by
  apply Subtype.ext; ext x; rfl

/-- Scalar-restricted injective embedding of `AlgDerivation R B` into
`NonAssocDerivation.derivations ℤ B` for arbitrary `[Ring R]`. -/
def algDerivationToZDerivations
    {R B : Type*} [Ring R] [NonUnitalNonAssocRing B] [Module R B]
    (D : InfoGeometry.Algebra.DualAlgebra.AlgDerivation R B) : derivations ℤ B :=
  ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩

theorem algDerivationToZDerivations_injective
    {R B : Type*} [Ring R] [NonUnitalNonAssocRing B] [Module R B] :
    Function.Injective (algDerivationToZDerivations (R := R) (B := B)) := by
  intro D₁ D₂ h
  cases D₁ with
  | mk f₁ a₁ s₁ l₁ =>
    cases D₂ with
    | mk f₂ a₂ s₂ l₂ =>
      congr 1
      funext x
      exact congrArg (fun d : derivations ℤ B => (d : Module.End ℤ B) x) h

/-- Equivalence between `OperatorialFierz.OperatorDerivation 𝒜` and
`NonAssocDerivation.derivations ℝ 𝒜`. -/
def operatorDerivationEquivDerivations
    {𝒜 : Type*} [NonUnitalNonAssocRing 𝒜] [Module ℝ 𝒜]
    [IsScalarTower ℝ 𝒜 𝒜] [SMulCommClass ℝ 𝒜 𝒜] :
    InfoGeometry.Canonical.OperatorialFierz.OperatorDerivation 𝒜 ≃ derivations ℝ 𝒜 where
  toFun D :=
    ⟨{ toFun := D.toFun
       map_add' := D.map_add'
       map_smul' := D.map_smul' }, D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℝ 𝒜),
     fun x y => (D : Module.End ℝ 𝒜).map_add x y,
     fun r x => (D : Module.End ℝ 𝒜).map_smul r x,
     D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

theorem operatorDerivation_add_apply
    {𝒜 : Type*} [NonUnitalNonAssocRing 𝒜] [Module ℝ 𝒜]
    [IsScalarTower ℝ 𝒜 𝒜] [SMulCommClass ℝ 𝒜 𝒜]
    (D₁ D₂ : InfoGeometry.Canonical.OperatorialFierz.OperatorDerivation 𝒜) (x : 𝒜) :
    ((operatorDerivationEquivDerivations D₁ +
        operatorDerivationEquivDerivations D₂ : derivations ℝ 𝒜) :
      Module.End ℝ 𝒜) x = D₁ x + D₂ x := rfl

theorem operatorDerivation_bracket_apply
    {𝒜 : Type*} [NonUnitalNonAssocRing 𝒜] [Module ℝ 𝒜]
    [IsScalarTower ℝ 𝒜 𝒜] [SMulCommClass ℝ 𝒜 𝒜]
    (D₁ D₂ : InfoGeometry.Canonical.OperatorialFierz.OperatorDerivation 𝒜) (x : 𝒜) :
    (⁅operatorDerivationEquivDerivations D₁,
        operatorDerivationEquivDerivations D₂⁆ : Module.End ℝ 𝒜) x =
      D₁ (D₂ x) - D₂ (D₁ x) := rfl

/-- Equivalence between `InfoGeometry.EndToEnd.Derivation A` and
`NonAssocDerivation.derivations ℂ A`. -/
def endToEndDerivationEquivDerivations
    {A : Type*} [Ring A] [Algebra ℂ A] :
    InfoGeometry.EndToEnd.Derivation A ≃ derivations ℂ A where
  toFun D := ⟨D.toFun, D.leibniz'⟩
  invFun D := ⟨(D : Module.End ℂ A), D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

/-- Equivalence between `InfoGeometry.EndToEnd.KMS.ModularDerivation A` and
`NonAssocDerivation.derivations ℂ A`. -/
def kmsModularDerivationEquivDerivations
    {A : Type*} [Ring A] [Algebra ℂ A] :
    InfoGeometry.EndToEnd.KMS.ModularDerivation A ≃ derivations ℂ A where
  toFun D := ⟨D.toLinearMap, D.leibniz'⟩
  invFun D := ⟨(D : Module.End ℂ A), D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

/-- Equivalence between `InfoGeometry.QuantumGeometry.BerryKeating.ComplexDerivation A` and
`NonAssocDerivation.derivations ℂ A`. -/
def complexDerivationEquivDerivations
    {A : Type*} [Ring A] [Algebra ℂ A] :
    InfoGeometry.QuantumGeometry.BerryKeating.ComplexDerivation A ≃ derivations ℂ A where
  toFun D :=
    ⟨{ toFun := D.toFun
       map_add' := D.map_add'
       map_smul' := D.map_smul' }, D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℂ A),
     fun x y => (D : Module.End ℂ A).map_add x y,
     fun c x => (D : Module.End ℂ A).map_smul c x,
     D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

/-- Equivalence between `InfoGeometry.Canonical.G2Derivation R V`
(`AlbertAlgebraGenerationsBridge`) and `NonAssocDerivation.derivations R (ExteriorAlgebra R V)`. -/
def albertG2DerivationEquivDerivations
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V] :
    InfoGeometry.Canonical.G2Derivation R V ≃ derivations R (ExteriorAlgebra R V) where
  toFun D :=
    ⟨{ toFun := D.d
       map_add' := D.map_add'
       map_smul' := D.map_smul' }, D.map_mul'⟩
  invFun D :=
    ⟨(D : Module.End R (ExteriorAlgebra R V)),
     fun x y => (D : Module.End R (ExteriorAlgebra R V)).map_add x y,
     fun c x => (D : Module.End R (ExteriorAlgebra R V)).map_smul c x,
     D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

theorem albertG2Derivation_add_apply
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    (D₁ D₂ : InfoGeometry.Canonical.G2Derivation R V) (x : ExteriorAlgebra R V) :
    ((albertG2DerivationEquivDerivations D₁ +
        albertG2DerivationEquivDerivations D₂ : derivations R (ExteriorAlgebra R V)) :
      Module.End R (ExteriorAlgebra R V)) x = D₁.d x + D₂.d x := rfl

/-- `R`-linear equivalence between Mathlib `_root_.Derivation R A A` and
`NonAssocDerivation.derivations R A`. -/
def mathlibDerivationLinearEquivDerivations
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    _root_.Derivation R A A ≃ₗ[R] derivations R A where
  toFun D :=
    ⟨D.toLinearMap, fun x y => by
      change D (x * y) = D x * y + x * D y
      rw [D.leibniz x y, smul_eq_mul, smul_eq_mul, mul_comm y (D x), add_comm]⟩
  invFun D :=
    { toLinearMap := (D : Module.End R A)
      map_one_eq_zero' := by
        have h := D.property 1 1
        simp only [mul_one, one_mul] at h
        exact add_left_cancel (by simpa only [add_zero] using h.symm)
      leibniz' := fun a b => by
        change (D : Module.End R A) (a * b) =
          a • (D : Module.End R A) b + b • (D : Module.End R A) a
        rw [D.property a b, smul_eq_mul, smul_eq_mul, mul_comm ((D : Module.End R A) a) b,
          add_comm] }
  left_inv D := by ext x; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl
  map_add' D₁ D₂ := by apply Subtype.ext; ext x; rfl
  map_smul' r D := by apply Subtype.ext; ext x; rfl

/-- `R`-Lie algebra isomorphism between Mathlib `_root_.Derivation R A A` and
`NonAssocDerivation.derivations R A`. -/
def mathlibDerivationLieEquivDerivations
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    _root_.Derivation R A A ≃ₗ⁅R⁆ derivations R A :=
  { mathlibDerivationLinearEquivDerivations with
    map_lie' := fun {D₁ D₂} => by
      apply Subtype.ext; ext x; rfl }

/-- Embed a `BipolarObservableMetriplecticAlgebra.DerivationFrame A` into a triple of
`NonAssocDerivation.derivations ℝ A`. -/
def derivationFrameToDerivationsTriple
    {A : Type*} [CommRing A] [Algebra ℝ A]
    (F : InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra.DerivationFrame A) :
    derivations ℝ A × derivations ℝ A × derivations ℝ A :=
  (mathlibDerivationLinearEquivDerivations F.Deta,
   mathlibDerivationLinearEquivDerivations F.Dtheta,
   mathlibDerivationLinearEquivDerivations F.Da)

theorem derivationFrame_theta_a_commute
    {A : Type*} [CommRing A] [Algebra ℝ A]
    (F : InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra.DerivationFrame A) :
    ⁅mathlibDerivationLinearEquivDerivations F.Dtheta,
      mathlibDerivationLinearEquivDerivations F.Da⁆ = 0 := by
  apply Subtype.ext; ext x
  change F.Dtheta (F.Da x) - F.Da (F.Dtheta x) = 0
  rw [F.commute_theta_a x, sub_self]

end F7_3_LinearAndAssociativeDerivations

/-! ## F7.4: Tower and Colimit Derivation Bridges -/

section F7_4_TowerAndColimitDerivations

/-- Mutual equivalence between `ColimitFlowDerivation.TowerDerivation A iota` and
`ColimitKMSInfinitesimal.TowerDerivation A iota`. -/
def colimitFlowTowerEquivKMSTower
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1)) :
    InfoGeometry.Modular.ColimitFlowDerivation.TowerDerivation A iota ≃
      InfoGeometry.Modular.ColimitKMSInfinitesimal.TowerDerivation A iota where
  toFun D := ⟨D.deriv, D.leibniz, D.deriv_comm⟩
  invFun D := ⟨D.deriv, D.leibniz, D.deriv_comm⟩
  left_inv D := by cases D; rfl
  right_inv D := by cases D; rfl

/-- Stagewise derivation in `NonAssocDerivation.derivations ℂ (A n)` from
`ColimitFlowDerivation.TowerDerivation`. -/
def colimitFlowStageDerivation
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1))
    (tDeriv : InfoGeometry.Modular.ColimitFlowDerivation.TowerDerivation A iota)
    (n : ℕ) : derivations ℂ (A n) :=
  ⟨tDeriv.deriv n, tDeriv.leibniz n⟩

/-- Stagewise derivation in `NonAssocDerivation.derivations ℂ (A n)` from
`ColimitKMSInfinitesimal.TowerDerivation`. -/
def colimitKMSStageDerivation
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1))
    (tDeriv : InfoGeometry.Modular.ColimitKMSInfinitesimal.TowerDerivation A iota)
    (n : ℕ) : derivations ℂ (A n) :=
  ⟨tDeriv.deriv n, tDeriv.leibniz n⟩

private def towerIota
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1)) :
    ∀ {n k : ℕ}, n ≤ k → (A n →⋆ₐ[ℂ] A k)
  | n, 0, h => by
    have hn : n = 0 := Nat.eq_zero_of_le_zero h
    subst hn
    exact StarAlgHom.id ℂ (A 0)
  | n, k + 1, h =>
    if hnk : n ≤ k then (iota k).comp (towerIota A iota hnk)
    else by
      have hn : n = k + 1 := Nat.le_antisymm h (Nat.lt_of_not_ge hnk)
      subst hn
      exact StarAlgHom.id ℂ (A (k + 1))

private theorem towerIota_refl
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1)) (n : ℕ) :
    towerIota A iota (le_refl n) = StarAlgHom.id ℂ (A n) := by
  cases n with
  | zero => rfl
  | succ k => simp [towerIota]

private theorem psi_comp_towerIota
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1))
    (A_inf : Type*) [Ring A_inf] [Algebra ℂ A_inf] [StarRing A_inf] [StarModule ℂ A_inf]
    (psi : ∀ n, A n →⋆ₐ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n) :
    ∀ {n k : ℕ} (h : n ≤ k), (psi k).comp (towerIota A iota h) = psi n
  | n, 0, h => by
    have hn : n = 0 := Nat.eq_zero_of_le_zero h
    subst hn
    rfl
  | n, k + 1, h => by
    by_cases hnk : n ≤ k
    · simp only [towerIota, hnk, ↓reduceDIte]
      rw [← StarAlgHom.comp_assoc, psi_comm k]
      exact psi_comp_towerIota A iota A_inf psi psi_comm hnk
    · simp only [towerIota, hnk, ↓reduceDIte]
      have hn : n = k + 1 := Nat.le_antisymm h (Nat.lt_of_not_ge hnk)
      subst hn
      rfl

private theorem deriv_comp_towerIota
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1))
    (tDeriv : InfoGeometry.Modular.ColimitFlowDerivation.TowerDerivation A iota) :
    ∀ {n k : ℕ} (h : n ≤ k) (x : A n),
      tDeriv.deriv k (towerIota A iota h x) = towerIota A iota h (tDeriv.deriv n x)
  | n, 0, h, x => by
    have hn : n = 0 := Nat.eq_zero_of_le_zero h
    subst hn
    rfl
  | n, k + 1, h, x => by
    by_cases hnk : n ≤ k
    · simp only [towerIota, hnk, ↓reduceDIte, StarAlgHom.comp_apply]
      have h1 := congrArg (fun f : A k →ₗ[ℂ] A (k + 1) => f (towerIota A iota hnk x))
        (tDeriv.deriv_comm k)
      dsimp at h1
      rw [h1, deriv_comp_towerIota A iota tDeriv hnk x]
    · simp only [towerIota, hnk, ↓reduceDIte]
      have hn : n = k + 1 := Nat.le_antisymm h (Nat.lt_of_not_ge hnk)
      subst hn
      rfl

/-- Colimit lift of `ColimitFlowDerivation.TowerDerivation A iota` to
`NonAssocDerivation.derivations ℂ A_inf` under cocone density `h_surj` and eventual
injectivity `h_inj`. -/
noncomputable def colimitFlowTowerToColimitDerivation
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1))
    (A_inf : Type*) [Ring A_inf] [Algebra ℂ A_inf] [StarRing A_inf] [StarModule ℂ A_inf]
    (psi : ∀ n, A n →⋆ₐ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (h_surj : ∀ x : A_inf, ∃ (n : ℕ) (xn : A n), psi n xn = x)
    (h_inj : ∀ {n : ℕ} (x y : A n), psi n x = psi n y →
      ∃ m, InfoGeometry.Modular.ColimitFlowDerivation.iota_seq A iota n m x =
        InfoGeometry.Modular.ColimitFlowDerivation.iota_seq A iota n m y)
    (tDeriv : InfoGeometry.Modular.ColimitFlowDerivation.TowerDerivation A iota) :
    derivations ℂ A_inf := by
  classical
  let val : A_inf → A_inf := fun x =>
    let n := Classical.choose (h_surj x)
    let xn := Classical.choose (Classical.choose_spec (h_surj x))
    InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv A iota A_inf psi tDeriv n xn
  have h_well : ∀ {n₁ n₂ : ℕ} (x₁ : A n₁) (x₂ : A n₂),
      psi n₁ x₁ = psi n₂ x₂ →
      InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv A iota A_inf psi tDeriv n₁ x₁ =
        InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv A iota A_inf psi tDeriv n₂ x₂ := by
    intro n₁ n₂ x₁ x₂ h_eq
    let k := max n₁ n₂
    have hk1 : n₁ ≤ k := le_max_left n₁ n₂
    have hk2 : n₂ ≤ k := le_max_right n₁ n₂
    let y₁ : A k := towerIota A iota hk1 x₁
    let y₂ : A k := towerIota A iota hk2 x₂
    have hy : psi k y₁ = psi k y₂ := by
      have h1 := congrArg (fun f : A n₁ →⋆ₐ[ℂ] A_inf => f x₁)
        (psi_comp_towerIota A iota A_inf psi psi_comm hk1)
      have h2 := congrArg (fun f : A n₂ →⋆ₐ[ℂ] A_inf => f x₂)
        (psi_comp_towerIota A iota A_inf psi psi_comm hk2)
      exact h1.trans (h_eq.trans h2.symm)
    obtain ⟨m, hm⟩ := h_inj y₁ y₂ hy
    have lift_eq_k : ∀ {n : ℕ} (h : n ≤ k) (x : A n),
        InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv A iota A_inf psi tDeriv n x =
          psi k (tDeriv.deriv k (towerIota A iota h x)) := by
      intro n h x
      dsimp [InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv]
      rw [deriv_comp_towerIota A iota tDeriv h x]
      exact (congrArg (fun f : A n →⋆ₐ[ℂ] A_inf => f (tDeriv.deriv n x))
        (psi_comp_towerIota A iota A_inf psi psi_comm h)).symm
    have lift_k_shift : ∀ (z : A k),
        psi k (tDeriv.deriv k z) =
          psi (k + m) (tDeriv.deriv (k + m)
            (InfoGeometry.Modular.ColimitFlowDerivation.iota_seq A iota k m z)) :=
      fun z => (InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv_stage_shift
        A iota A_inf psi tDeriv psi_comm k m z).symm
    rw [lift_eq_k hk1 x₁, lift_eq_k hk2 x₂, lift_k_shift y₁, lift_k_shift y₂, hm]
  have h_val_psi : ∀ n (xn : A n),
      val (psi n xn) =
        InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv A iota A_inf psi tDeriv n xn := by
    intro n xn
    dsimp [val]
    exact h_well _ xn (Classical.choose_spec (Classical.choose_spec (h_surj (psi n xn))))
  refine
    ⟨{ toFun := val
       map_add' := fun x y => by
         obtain ⟨n₁, x₁, rfl⟩ := h_surj x
         obtain ⟨n₂, x₂, rfl⟩ := h_surj y
         let k := max n₁ n₂
         have hk1 : n₁ ≤ k := le_max_left n₁ n₂
         have hk2 : n₂ ≤ k := le_max_right n₁ n₂
         have hx : psi n₁ x₁ = psi k (towerIota A iota hk1 x₁) :=
           (congrArg (fun f : A n₁ →⋆ₐ[ℂ] A_inf => f x₁)
             (psi_comp_towerIota A iota A_inf psi psi_comm hk1)).symm
         have hy : psi n₂ x₂ = psi k (towerIota A iota hk2 x₂) :=
           (congrArg (fun f : A n₂ →⋆ₐ[ℂ] A_inf => f x₂)
             (psi_comp_towerIota A iota A_inf psi psi_comm hk2)).symm
         rw [hx, hy, ← map_add (psi k), h_val_psi k, h_val_psi k, h_val_psi k]
         dsimp [InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv]
         rw [map_add, map_add]
       map_smul' := fun c x => by
         obtain ⟨n, xn, rfl⟩ := h_surj x
         rw [← map_smul (psi n) c xn]
         change val (psi n (c • xn)) = c • val (psi n xn)
         rw [h_val_psi n (c • xn), h_val_psi n xn]
         dsimp [InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv]
         rw [map_smul, map_smul] },
     fun x y => by
       obtain ⟨n₁, x₁, rfl⟩ := h_surj x
       obtain ⟨n₂, x₂, rfl⟩ := h_surj y
       let k := max n₁ n₂
       have hk1 : n₁ ≤ k := le_max_left n₁ n₂
       have hk2 : n₂ ≤ k := le_max_right n₁ n₂
       have hx : psi n₁ x₁ = psi k (towerIota A iota hk1 x₁) :=
         (congrArg (fun f : A n₁ →⋆ₐ[ℂ] A_inf => f x₁)
           (psi_comp_towerIota A iota A_inf psi psi_comm hk1)).symm
       have hy : psi n₂ x₂ = psi k (towerIota A iota hk2 x₂) :=
         (congrArg (fun f : A n₂ →⋆ₐ[ℂ] A_inf => f x₂)
           (psi_comp_towerIota A iota A_inf psi psi_comm hk2)).symm
       change val (psi n₁ x₁ * psi n₂ x₂) =
         val (psi n₁ x₁) * psi n₂ x₂ + psi n₁ x₁ * val (psi n₂ x₂)
       rw [hx, hy, ← map_mul (psi k), h_val_psi k, h_val_psi k, h_val_psi k]
       exact InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv_leibniz
         A iota A_inf psi tDeriv k _ _⟩

theorem colimitFlowTowerToColimitDerivation_apply_psi
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1))
    (A_inf : Type*) [Ring A_inf] [Algebra ℂ A_inf] [StarRing A_inf] [StarModule ℂ A_inf]
    (psi : ∀ n, A n →⋆ₐ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (h_surj : ∀ x : A_inf, ∃ (n : ℕ) (xn : A n), psi n xn = x)
    (h_inj : ∀ {n : ℕ} (x y : A n), psi n x = psi n y →
      ∃ m, InfoGeometry.Modular.ColimitFlowDerivation.iota_seq A iota n m x =
        InfoGeometry.Modular.ColimitFlowDerivation.iota_seq A iota n m y)
    (tDeriv : InfoGeometry.Modular.ColimitFlowDerivation.TowerDerivation A iota)
    (n : ℕ) (x : A n) :
    (colimitFlowTowerToColimitDerivation A iota A_inf psi psi_comm h_surj h_inj tDeriv :
      Module.End ℂ A_inf) (psi n x) =
      InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv A iota A_inf psi tDeriv n x := by
  classical
  dsimp [colimitFlowTowerToColimitDerivation]
  let n₀ := Classical.choose (h_surj (psi n x))
  let x₀ := Classical.choose (Classical.choose_spec (h_surj (psi n x)))
  have h_eq : psi n₀ x₀ = psi n x :=
    Classical.choose_spec (Classical.choose_spec (h_surj (psi n x)))
  let k := max n₀ n
  have hk1 : n₀ ≤ k := le_max_left n₀ n
  have hk2 : n ≤ k := le_max_right n₀ n
  have hy : psi k (towerIota A iota hk1 x₀) = psi k (towerIota A iota hk2 x) := by
    have h1 := congrArg (fun f : A n₀ →⋆ₐ[ℂ] A_inf => f x₀)
      (psi_comp_towerIota A iota A_inf psi psi_comm hk1)
    have h2 := congrArg (fun f : A n →⋆ₐ[ℂ] A_inf => f x)
      (psi_comp_towerIota A iota A_inf psi psi_comm hk2)
    exact h1.trans (h_eq.trans h2.symm)
  obtain ⟨m, hm⟩ := h_inj _ _ hy
  have lift_eq_k : ∀ {m₀ : ℕ} (h : m₀ ≤ k) (z : A m₀),
      InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv A iota A_inf psi tDeriv m₀ z =
        psi k (tDeriv.deriv k (towerIota A iota h z)) := by
    intro m₀ h z
    dsimp [InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv]
    rw [deriv_comp_towerIota A iota tDeriv h z]
    exact (congrArg (fun f : A m₀ →⋆ₐ[ℂ] A_inf => f (tDeriv.deriv m₀ z))
      (psi_comp_towerIota A iota A_inf psi psi_comm h)).symm
  rw [lift_eq_k hk1 x₀, lift_eq_k hk2 x]
  have s1 := (InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv_stage_shift
    A iota A_inf psi tDeriv psi_comm k m (towerIota A iota hk1 x₀)).symm
  have s2 := (InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv_stage_shift
    A iota A_inf psi tDeriv psi_comm k m (towerIota A iota hk2 x)).symm
  dsimp [InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv] at s1 s2
  rw [s1, s2, hm]

/-- Colimit lift of `ColimitKMSInfinitesimal.TowerDerivation A iota` to
`NonAssocDerivation.derivations ℂ A_inf`. -/
noncomputable def colimitKMSInfinitesimalToColimitDerivation
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1))
    (A_inf : Type*) [Ring A_inf] [Algebra ℂ A_inf] [StarRing A_inf] [StarModule ℂ A_inf]
    (psi : ∀ n, A n →⋆ₐ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (h_surj : ∀ x : A_inf, ∃ (n : ℕ) (xn : A n), psi n xn = x)
    (h_inj : ∀ {n : ℕ} (x y : A n), psi n x = psi n y →
      ∃ m, InfoGeometry.Modular.ColimitFlowDerivation.iota_seq A iota n m x =
        InfoGeometry.Modular.ColimitFlowDerivation.iota_seq A iota n m y)
    (tDeriv : InfoGeometry.Modular.ColimitKMSInfinitesimal.TowerDerivation A iota) :
    derivations ℂ A_inf :=
  colimitFlowTowerToColimitDerivation A iota A_inf psi psi_comm h_surj h_inj
    ((colimitFlowTowerEquivKMSTower A iota).symm tDeriv)

/-- Extension-based colimit lift: given a dense cocone `h_surj` and an operator
`δ_inf : A_inf →ₗ[ℂ] A_inf` extending `liftedDeriv`, `δ_inf` is automatically a
derivation in `NonAssocDerivation.derivations ℂ A_inf`. -/
def colimitFlowExtensionToDerivation
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1))
    (A_inf : Type*) [Ring A_inf] [Algebra ℂ A_inf] [StarRing A_inf] [StarModule ℂ A_inf]
    (psi : ∀ n, A n →⋆ₐ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (h_surj : ∀ x : A_inf, ∃ (n : ℕ) (xn : A n), psi n xn = x)
    (tDeriv : InfoGeometry.Modular.ColimitFlowDerivation.TowerDerivation A iota)
    (δ_inf : A_inf →ₗ[ℂ] A_inf)
    (h_ext : ∀ n (x : A n),
      δ_inf (psi n x) =
        InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv A iota A_inf psi tDeriv n x) :
    derivations ℂ A_inf :=
  ⟨δ_inf, fun x y => by
    obtain ⟨n₁, x₁, rfl⟩ := h_surj x
    obtain ⟨n₂, x₂, rfl⟩ := h_surj y
    let k := max n₁ n₂
    have hk1 : n₁ ≤ k := le_max_left n₁ n₂
    have hk2 : n₂ ≤ k := le_max_right n₁ n₂
    have hx : psi n₁ x₁ = psi k (towerIota A iota hk1 x₁) :=
      (congrArg (fun f : A n₁ →⋆ₐ[ℂ] A_inf => f x₁)
        (psi_comp_towerIota A iota A_inf psi psi_comm hk1)).symm
    have hy : psi n₂ x₂ = psi k (towerIota A iota hk2 x₂) :=
      (congrArg (fun f : A n₂ →⋆ₐ[ℂ] A_inf => f x₂)
        (psi_comp_towerIota A iota A_inf psi psi_comm hk2)).symm
    rw [hx, hy, ← map_mul (psi k), h_ext k, h_ext k, h_ext k]
    exact InfoGeometry.Modular.ColimitFlowDerivation.liftedDeriv_leibniz
      A iota A_inf psi tDeriv k _ _⟩

/-- Stagewise derivation in `NonAssocDerivation.derivations R (A i)` from
`Modular.ColimitDerivation.LocalDerivationSystem`. -/
def localDerivationStage
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] {A : I → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    (dsys : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys)
    (i : I) : derivations R (A i) :=
  ⟨dsys.deriv i, dsys.deriv_leibniz i⟩

/-- Global colimit derivation in `NonAssocDerivation.derivations R A_inf` from
`Modular.ColimitDerivation.LocalDerivationSystem` and `AlgColimitCocone`. -/
noncomputable def colimitDerivationToDerivations
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    {A_inf : Type*} [Ring A_inf] [Algebra R A_inf]
    (colim : InfoGeometry.Modular.ColimitDerivation.AlgColimitCocone (R := R) I A sys A_inf)
    (dsys : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys) :
    derivations R A_inf :=
  ⟨InfoGeometry.Modular.ColimitDerivation.colimitDerivLinearMap sys dsys colim,
   InfoGeometry.Modular.ColimitDerivation.colimitDerivLinearMap_leibniz sys dsys colim⟩

/-- Explicit zero `LocalDerivationSystem` (without orphan instances). -/
def localDerivationSystemZero
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] {A : I → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A) :
    InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys where
  deriv _ := 0
  deriv_leibniz _ x y := by simp
  intertwine {i j} hij x := by simp

/-- Explicit sum of two `LocalDerivationSystem`s. -/
def localDerivationSystemAdd
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] {A : I → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    (dsys₁ dsys₂ : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys) :
    InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys where
  deriv i := dsys₁.deriv i + dsys₂.deriv i
  deriv_leibniz i x y := by
    simp only [LinearMap.add_apply, dsys₁.deriv_leibniz, dsys₂.deriv_leibniz, add_mul, mul_add]
    abel
  intertwine {i j} hij x := by
    simp only [LinearMap.add_apply, map_add, dsys₁.intertwine hij x, dsys₂.intertwine hij x]

/-- Explicit negation of a `LocalDerivationSystem`. -/
def localDerivationSystemNeg
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] {A : I → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    (dsys : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys) :
    InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys where
  deriv i := -dsys.deriv i
  deriv_leibniz i x y := by
    simp only [LinearMap.neg_apply, dsys.deriv_leibniz, neg_add, neg_mul, mul_neg]
  intertwine {i j} hij x := by
    simp only [LinearMap.neg_apply, map_neg, dsys.intertwine hij x]

/-- Explicit scalar multiple of a `LocalDerivationSystem`. -/
def localDerivationSystemSmul
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] {A : I → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    (c : R)
    (dsys : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys) :
    InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys where
  deriv i := c • dsys.deriv i
  deriv_leibniz i x y := by
    simp only [LinearMap.smul_apply, dsys.deriv_leibniz, smul_add, smul_mul_assoc, mul_smul_comm]
  intertwine {i j} hij x := by
    simp only [LinearMap.smul_apply, map_smul, dsys.intertwine hij x]

/-- Explicit commutator of two `LocalDerivationSystem`s. -/
def localDerivationSystemCommutator
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] {A : I → Type*}
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    (dsys₁ dsys₂ : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys) :
    InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys where
  deriv i := ⁅dsys₁.deriv i, dsys₂.deriv i⁆
  deriv_leibniz i :=
    InfoGeometry.Algebra.NonAssocDerivation.isLeibniz_lie
      (dsys₁.deriv_leibniz i) (dsys₂.deriv_leibniz i)
  intertwine {i j} hij x := by
    simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      map_sub, dsys₁.intertwine hij, dsys₂.intertwine hij]

theorem colimitDerivationToDerivations_zero
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    {A_inf : Type*} [Ring A_inf] [Algebra R A_inf]
    (colim : InfoGeometry.Modular.ColimitDerivation.AlgColimitCocone (R := R) I A sys A_inf) :
    colimitDerivationToDerivations sys colim (localDerivationSystemZero sys) = 0 := by
  apply Subtype.ext; ext x
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  change InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys
      (localDerivationSystemZero sys) colim (colim.inr i xi) = 0
  rw [InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr]
  simp [localDerivationSystemZero]

theorem colimitDerivationToDerivations_add
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    {A_inf : Type*} [Ring A_inf] [Algebra R A_inf]
    (colim : InfoGeometry.Modular.ColimitDerivation.AlgColimitCocone (R := R) I A sys A_inf)
    (dsys₁ dsys₂ : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys) :
    colimitDerivationToDerivations sys colim (localDerivationSystemAdd sys dsys₁ dsys₂) =
      colimitDerivationToDerivations sys colim dsys₁ +
        colimitDerivationToDerivations sys colim dsys₂ := by
  apply Subtype.ext; ext x
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  change InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys
      (localDerivationSystemAdd sys dsys₁ dsys₂) colim (colim.inr i xi) =
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys dsys₁ colim (colim.inr i xi) +
      InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys dsys₂ colim (colim.inr i xi)
  rw [InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr,
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr,
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr]
  simp [localDerivationSystemAdd]

theorem colimitDerivationToDerivations_neg
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    {A_inf : Type*} [Ring A_inf] [Algebra R A_inf]
    (colim : InfoGeometry.Modular.ColimitDerivation.AlgColimitCocone (R := R) I A sys A_inf)
    (dsys : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys) :
    colimitDerivationToDerivations sys colim (localDerivationSystemNeg sys dsys) =
      -colimitDerivationToDerivations sys colim dsys := by
  apply Subtype.ext; ext x
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  change InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys
      (localDerivationSystemNeg sys dsys) colim (colim.inr i xi) =
    -InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys dsys colim (colim.inr i xi)
  rw [InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr,
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr]
  simp [localDerivationSystemNeg]

theorem colimitDerivationToDerivations_smul
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    {A_inf : Type*} [Ring A_inf] [Algebra R A_inf]
    (colim : InfoGeometry.Modular.ColimitDerivation.AlgColimitCocone (R := R) I A sys A_inf)
    (c : R)
    (dsys : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys) :
    colimitDerivationToDerivations sys colim (localDerivationSystemSmul sys c dsys) =
      c • colimitDerivationToDerivations sys colim dsys := by
  apply Subtype.ext; ext x
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  change InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys
      (localDerivationSystemSmul sys c dsys) colim (colim.inr i xi) =
    c • InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys dsys colim (colim.inr i xi)
  rw [InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr,
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr]
  simp [localDerivationSystemSmul]

theorem colimitDerivationToDerivations_commutator
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    {A_inf : Type*} [Ring A_inf] [Algebra R A_inf]
    (colim : InfoGeometry.Modular.ColimitDerivation.AlgColimitCocone (R := R) I A sys A_inf)
    (dsys₁ dsys₂ : InfoGeometry.Modular.ColimitDerivation.LocalDerivationSystem (R := R) I A sys) :
    colimitDerivationToDerivations sys colim (localDerivationSystemCommutator sys dsys₁ dsys₂) =
      ⁅colimitDerivationToDerivations sys colim dsys₁,
        colimitDerivationToDerivations sys colim dsys₂⁆ := by
  apply Subtype.ext; ext x
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  change InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys
      (localDerivationSystemCommutator sys dsys₁ dsys₂) colim (colim.inr i xi) =
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys dsys₁ colim
      (InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys dsys₂ colim (colim.inr i xi)) -
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys dsys₂ colim
      (InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys dsys₁ colim (colim.inr i xi))
  rw [InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr,
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr,
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr,
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr,
    InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr]
  simp [localDerivationSystemCommutator]

theorem colimitDerivationToDerivations_injective
    {R : Type*} [CommRing R] {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
    (sys : InfoGeometry.Modular.ColimitDerivation.DirectedAlgSystem (R := R) I A)
    {A_inf : Type*} [Ring A_inf] [Algebra R A_inf]
    (colim : InfoGeometry.Modular.ColimitDerivation.AlgColimitCocone (R := R) I A sys A_inf)
    (hinj : ∀ i, Function.Injective (colim.inr i)) :
    Function.Injective (colimitDerivationToDerivations sys colim) := by
  intro d₁ d₂ h
  cases d₁ with
  | mk f₁ l₁ i₁ =>
    cases d₂ with
    | mk f₂ l₂ i₂ =>
      congr 1
      funext i
      ext x
      have hx := congrArg (fun d : derivations R A_inf => (d : Module.End R A_inf) (colim.inr i x)) h
      change InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys _ colim (colim.inr i x) =
        InfoGeometry.Modular.ColimitDerivation.colimitDerivVal sys _ colim (colim.inr i x) at hx
      rw [InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr,
        InfoGeometry.Modular.ColimitDerivation.colimitDerivVal_inr] at hx
      exact hinj i hx

end F7_4_TowerAndColimitDerivations

/-! ## F7.5: Standalone Associative and Involutive Wrappers -/

section F7_5_StandaloneWrappers

/-- Equivalence between `SouriauMetriplecticParabolicPoset.OpDerivation B` and
`NonAssocDerivation.derivations ℤ B`. -/
def posetOpDerivationEquivDerivations
    {B : Type*} [Ring B] :
    InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset.OpDerivation B ≃
      derivations ℤ B where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ B),
     fun x y => (D : Module.End ℤ B).map_add x y,
     fun x y => (D : Module.End ℤ B).map_sub x y,
     D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

/-- Equivalence between `HypothesisFoundations.CommRingDerivation R` and
`NonAssocDerivation.derivations ℤ R` (additive-only wrapper over `[CommRing R]`). -/
def commRingDerivationEquivDerivations
    {R : Type*} [CommRing R] :
    InfoGeometry.Canonical.HypothesisFoundations.CommRingDerivation R ≃ derivations ℤ R where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ R), fun x y => (D : Module.End ℤ R).map_add x y, D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

/-- Equivalence between `HypothesisFoundations.GenericDerivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def genericDerivationEquivDerivations
    {A : Type*} [Ring A] :
    InfoGeometry.Canonical.HypothesisFoundations.GenericDerivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by
    apply InfoGeometry.Canonical.HypothesisFoundations.GenericDerivation.extensionality
    intro x; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

/-- Equivalence between `DensityDLog.CommRingDerivation R` and
`NonAssocDerivation.derivations ℤ R`. -/
def densityDLogDerivationEquivDerivations
    {R : Type*} [Ring R] :
    InfoGeometry.QuantumGeometry.DensityDLog.CommRingDerivation R ≃ derivations ℤ R where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ R), fun x y => (D : Module.End ℤ R).map_add x y, D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

/-- Equivalence between `InfoGeometry.Synthesis.Derivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def synthesisDerivationEquivDerivations
    {A : Type*} [Ring A] :
    InfoGeometry.Synthesis.Derivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

/-- Equivalence between `DualExponentialArchitectureCertificate.Derivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def dualExpCertDerivationEquivDerivations
    {A : Type*} [Ring A] :
    InfoGeometry.QuantumGeometry.DualExponentialArchitectureCertificate.Derivation A ≃
      derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

/-- Equivalence between `InfoGeometry.QuantumGeometry.PhaseSpace.Derivation A` and
`NonAssocDerivation.derivations ℤ A`. -/
def phaseSpaceDerivationEquivDerivations
    {A : Type*} [Ring A] :
    InfoGeometry.QuantumGeometry.PhaseSpace.Derivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.toFun D.map_add', D.leibniz'⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

theorem phaseSpaceDerivationEquivDerivations_commutator
    {A : Type*} [Ring A]
    (D₁ D₂ : InfoGeometry.QuantumGeometry.PhaseSpace.Derivation A) :
    phaseSpaceDerivationEquivDerivations
        (InfoGeometry.QuantumGeometry.PhaseSpace.Derivation.commutator D₁ D₂) =
      ⁅phaseSpaceDerivationEquivDerivations D₁,
        phaseSpaceDerivationEquivDerivations D₂⁆ := by
  apply Subtype.ext; ext x; rfl

/-- Equivalence between `DonaldsonWitten.GaugeDerivation A` (on nonassociative
`[NonUnitalNonAssocRing A]`) and `NonAssocDerivation.derivations ℤ A`. -/
def gaugeDerivationEquivDerivations
    {A : Type*} [NonUnitalNonAssocRing A] :
    InfoGeometry.Topological.DonaldsonWitten.GaugeDerivation A ≃ derivations ℤ A where
  toFun D := ⟨intLinearEndOfAdd D.delta D.map_add, D.leibniz⟩
  invFun D :=
    ⟨(D : Module.End ℤ A), fun x y => (D : Module.End ℤ A).map_add x y, D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

theorem gaugeDerivation_commutator_apply
    {A : Type*} [NonUnitalNonAssocRing A]
    (D₁ D₂ : InfoGeometry.Topological.DonaldsonWitten.GaugeDerivation A) (x : A) :
    (⁅gaugeDerivationEquivDerivations D₁,
        gaugeDerivationEquivDerivations D₂⁆ : Module.End ℤ A) x =
      InfoGeometry.Topological.DonaldsonWitten.derivationCommutator D₁.delta D₂.delta x := rfl

/-- Lie subalgebra of `*-preserving` derivations in `NonAssocDerivation.derivations ℤ A`. -/
def starPreservingDerivations (A : Type*) [Ring A] [StarRing A] :
    LieSubalgebra ℤ (derivations ℤ A) where
  carrier := { D | ∀ x : A, (D : Module.End ℤ A) (star x) = star ((D : Module.End ℤ A) x) }
  zero_mem' := by
    intro x
    simp
  add_mem' h₁ h₂ x := by simp [h₁ x, h₂ x]
  smul_mem' c D h x := by
    have hx : (D : Module.End ℤ A) (star x) = star ((D : Module.End ℤ A) x) := h x
    change c • (D : Module.End ℤ A) (star x) = star (c • (D : Module.End ℤ A) x)
    rw [hx, star_zsmul]
  lie_mem' {D₁ D₂} h₁ h₂ x := by
    change (D₁ : Module.End ℤ A) ((D₂ : Module.End ℤ A) (star x)) -
        (D₂ : Module.End ℤ A) ((D₁ : Module.End ℤ A) (star x)) =
      star ((D₁ : Module.End ℤ A) ((D₂ : Module.End ℤ A) x) -
        (D₂ : Module.End ℤ A) ((D₁ : Module.End ℤ A) x))
    rw [h₂ x, h₁ ((D₂ : Module.End ℤ A) x), h₁ x, h₂ ((D₁ : Module.End ℤ A) x), star_sub]

/-- Injective embedding of `Cuntz.StarDerivation (A := A)` into
`NonAssocDerivation.derivations ℤ A`. -/
def starDerivationToDerivations
    {A : Type*} [Ring A] [StarRing A]
    (D : InfoGeometry.Algebra.Cuntz.StarDerivation (A := A)) : derivations ℤ A :=
  ⟨D.toAddHom.toIntLinearMap, D.leibniz'⟩

theorem starDerivationToDerivations_injective
    {A : Type*} [Ring A] [StarRing A] :
    Function.Injective (starDerivationToDerivations (A := A)) := by
  intro D₁ D₂ h
  cases D₁ with
  | mk f₁ l₁ s₁ =>
    cases D₂ with
    | mk f₂ l₂ s₂ =>
      congr 1
      ext x
      exact congrArg (fun d : derivations ℤ A => (d : Module.End ℤ A) x) h

/-- Exact equivalence between `Cuntz.StarDerivation (A := A)` and the Lie subalgebra
`starPreservingDerivations A`. -/
def starDerivationEquivStarSubalgebra
    {A : Type*} [Ring A] [StarRing A] :
    InfoGeometry.Algebra.Cuntz.StarDerivation (A := A) ≃ starPreservingDerivations A where
  toFun D := ⟨starDerivationToDerivations D, D.star'⟩
  invFun D :=
    ⟨(D.1 : Module.End ℤ A).toAddMonoidHom, D.1.property, D.2⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; apply Subtype.ext; ext x; rfl

/-- Injective embedding of `Cuntz.InvolutiveDerivation (A := A) sharp` into
`NonAssocDerivation.derivations ℤ A`. -/
def involutiveDerivationToDerivations
    {A : Type*} [Ring A] (sharp : A → A)
    (D : InfoGeometry.Algebra.Cuntz.InvolutiveDerivation (A := A) sharp) : derivations ℤ A :=
  ⟨D.toAddHom.toIntLinearMap, D.leibniz'⟩

theorem involutiveDerivationToDerivations_injective
    {A : Type*} [Ring A] (sharp : A → A) :
    Function.Injective (involutiveDerivationToDerivations (A := A) sharp) := by
  intro D₁ D₂ h
  cases D₁ with
  | mk f₁ l₁ s₁ =>
    cases D₂ with
    | mk f₂ l₂ s₂ =>
      congr 1
      ext x
      exact congrArg (fun d : derivations ℤ A => (d : Module.End ℤ A) x) h

/-- Exact equivalence between `Cuntz.InvolutiveDerivation (A := A) sharp` and
`sharp`-commuting derivations in `NonAssocDerivation.derivations ℤ A`. -/
def involutiveDerivationEquivSubtype
    {A : Type*} [Ring A] (sharp : A → A) :
    InfoGeometry.Algebra.Cuntz.InvolutiveDerivation (A := A) sharp ≃
      { D : derivations ℤ A //
        ∀ x : A, (D : Module.End ℤ A) (sharp x) = sharp ((D : Module.End ℤ A) x) } where
  toFun D := ⟨involutiveDerivationToDerivations sharp D, D.sharp'⟩
  invFun D := ⟨(D.1 : Module.End ℤ A).toAddMonoidHom, D.1.property, D.2⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; apply Subtype.ext; ext x; rfl

/-- Injective embedding of `InfoGeometry.OperatorAlgebra.KreinStarDerivation (H := H)` into
`NonAssocDerivation.derivations ℤ (H →L[ℝ] H)`. -/
noncomputable def kreinStarDerivationToDerivations
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    (D : InfoGeometry.OperatorAlgebra.KreinStarDerivation (H := H)) :
    derivations ℤ (H →L[ℝ] H) :=
  ⟨D.toAddHom.toIntLinearMap, D.leibniz'⟩

theorem kreinStarDerivationToDerivations_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H] :
    Function.Injective (kreinStarDerivationToDerivations (H := H)) := by
  intro D₁ D₂ h
  cases D₁ with
  | mk f₁ l₁ k₁ =>
    cases D₂ with
    | mk f₂ l₂ k₂ =>
      congr 1
      exact AddMonoidHom.ext fun x =>
        congrArg (fun d : derivations ℤ (H →L[ℝ] H) => (d : Module.End ℤ _) x) h

/-- Exact equivalence between `KreinStarDerivation (H := H)` and
`Cuntz.InvolutiveDerivation (A := H →L[ℝ] H) kreinAdjoint`. -/
noncomputable def kreinStarDerivationEquivInvolutive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H] :
    InfoGeometry.OperatorAlgebra.KreinStarDerivation (H := H) ≃
      InfoGeometry.Algebra.Cuntz.InvolutiveDerivation
        (A := H →L[ℝ] H) (InfoGeometry.OperatorAlgebra.kreinAdjoint (H := H)) where
  toFun D := ⟨D.toAddHom, D.leibniz', D.kreinStar'⟩
  invFun D := ⟨D.toAddHom, D.leibniz', D.sharp'⟩
  left_inv D := by cases D; rfl
  right_inv D := by cases D; rfl

/-- Equivalence between `CoordinateFreeSouriau.ScalarDerivation F` and
`NonAssocDerivation.derivations ℤ F` (strictly requiring `[CommRing F]` because of the
commuted second Leibniz factor `b * toFun a`). -/
def scalarDerivationEquivDerivations
    {F : Type*} [CommRing F] :
    InfoGeometry.Canonical.CoordinateFreeSouriau.ScalarDerivation F ≃ derivations ℤ F where
  toFun D :=
    ⟨intLinearEndOfAdd D.toFun D.map_add',
     fun a b => by
       change D.toFun (a * b) = D.toFun a * b + a * D.toFun b
       rw [D.map_mul' a b, mul_comm b (D.toFun a), add_comm]⟩
  invFun D :=
    ⟨(D : Module.End ℤ F),
     fun a b => (D : Module.End ℤ F).map_add a b,
     fun a b => by
       rw [D.property a b, mul_comm ((D : Module.End ℤ F) a) b, add_comm]⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

end F7_5_StandaloneWrappers

/-! ## F7.6: `DerivationLieLane` & `OnsagerFormPairing` Canonical Spine Attachment -/

section F7_6_CanonicalSpineAttachment

/-- Canonical `DerivationLieLane ℤ A` attaching every `ℤ`-linear / `[Ring A]`
bridged lane (`Modular.*`, `PhaseSpace`, `Synthesis`, `Cuntz`, etc.) to `ceExteriorDerivative`
and `ceCurvature`. -/
def modularZDerivationLieLane (A : Type*) [NonUnitalNonAssocRing A] :
    DerivationLieLane ℤ A :=
  fullDerivationLieLane ℤ A

/-- Canonical `DerivationLieLane ℤ A` on the inner derivation ideal `modularInnerIdeal A`. -/
def modularInnerIdealLieLane (A : Type*) [Ring A] : DerivationLieLane ℤ A :=
  lieSubalgebraLane (modularInnerIdeal A)

/-- Canonical `DerivationLieLane ℤ A` on `*-preserving` derivations `starPreservingDerivations A`. -/
def starDerivationLieLane (A : Type*) [Ring A] [StarRing A] : DerivationLieLane ℤ A :=
  lieSubalgebraLane (starPreservingDerivations A)

/-- Canonical `DerivationLieLane R A` for Mathlib `_root_.Derivation R A A`, proven
equivariant to `fullDerivationLieLane R A`. -/
def mathlibDerivationLieLane (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    DerivationLieLane R A where
  L := _root_.Derivation R A A
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := mathlibDerivationLieEquivDerivations.toLieHom
  faithful := mathlibDerivationLieEquivDerivations.injective

def mathlibDerivationLieLaneEquivFull (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    DerivationLaneEquiv (mathlibDerivationLieLane R A) (fullDerivationLieLane R A) where
  map := mathlibDerivationLieEquivDerivations
  equivariant _ := rfl

/-- Canonical `DerivationLieLane R A_inf` for `Modular.ColimitDerivation` colimit algebras. -/
def colimitDerivationLieLane
    (R A_inf : Type*) [CommRing R] [Ring A_inf] [Algebra R A_inf] :
    DerivationLieLane R A_inf :=
  fullDerivationLieLane R A_inf

/-- Canonical `DerivationLieLane ℂ A_inf` for `ColimitFlowDerivation` /
`ColimitKMSInfinitesimal` complex colimit algebras. -/
def colimitComplexTowerLieLane
    (A_inf : Type*) [Ring A_inf] [Algebra ℂ A_inf] :
    DerivationLieLane ℂ A_inf :=
  fullDerivationLieLane ℂ A_inf

theorem ceExteriorDerivative_zero_of_modularZDerivation
    {A : Type*} [Ring A] (a : A)
    (D : InfoGeometry.Modular.LieIdeal.RingDerivation A) :
    ceExteriorDerivative (modularZDerivationLieLane A) 0
        (zeroFormAlternatingEquiv (modularZDerivationLieLane A) a)
        ![lieIdealRingDerivationEquivDerivations D] = D a :=
  (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.actionExteriorDerivative_zero_apply
    (modularZDerivationLieLane A).toLieActionLane
    (zeroFormAlternatingEquiv (modularZDerivationLieLane A) a)
    ![lieIdealRingDerivationEquivDerivations D]).trans rfl

/-- Restrict a `ℂ`-linear derivation in `NonAssocDerivation.derivations ℂ A` to an
`ℝ`-linear derivation in `NonAssocDerivation.derivations ℝ A` under explicit
`[Algebra ℝ A] [IsScalarTower ℝ ℂ A]` (diamond-free). -/
def complexDerivationRestrictReal
    {A : Type*} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A]
    (D : derivations ℂ A) : derivations ℝ A :=
  ⟨(D : Module.End ℂ A).restrictScalars ℝ, D.property⟩

theorem complexDerivationRestrictReal_injective
    (A : Type*) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] :
    Function.Injective (complexDerivationRestrictReal (A := A)) := by
  intro D₁ D₂ h
  apply Subtype.ext; ext x
  exact congrArg (fun d : derivations ℝ A => (d : Module.End ℝ A) x) h

/-- Lie subalgebra of `NonAssocDerivation.derivations ℝ A` consisting of `ℂ`-linear derivations. -/
def complexDerivationsRealSubalgebra
    (A : Type*) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] :
    LieSubalgebra ℝ (derivations ℝ A) where
  carrier := { D | ∃ D' : derivations ℂ A, complexDerivationRestrictReal D' = D }
  zero_mem' := ⟨0, by apply Subtype.ext; ext x; rfl⟩
  add_mem' := by
    rintro _ _ ⟨D₁, rfl⟩ ⟨D₂, rfl⟩
    refine ⟨D₁ + D₂, ?_⟩
    apply Subtype.ext; ext x; rfl
  smul_mem' := by
    rintro r _ ⟨D, rfl⟩
    refine ⟨(algebraMap ℝ ℂ r) • D, ?_⟩
    apply Subtype.ext; ext x
    change ((algebraMap ℝ ℂ r • (D : Module.End ℂ A)) x) = r • ((D : Module.End ℂ A) x)
    simp only [LinearMap.smul_apply, algebraMap_smul]
  lie_mem' := by
    rintro _ _ ⟨D₁, rfl⟩ ⟨D₂, rfl⟩
    refine ⟨⁅D₁, D₂⁆, ?_⟩
    apply Subtype.ext; ext x; rfl

/-- Package a `ℂ`-linear derivation into `complexDerivationsRealSubalgebra A`. -/
def complexDerivationToRealSubalgebra
    {A : Type*} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A]
    (D : derivations ℂ A) : complexDerivationsRealSubalgebra A :=
  ⟨complexDerivationRestrictReal D, D, rfl⟩

/-- Lift a `ℤ`-linear derivation `D : NonAssocDerivation.derivations ℤ A` to
`NonAssocDerivation.derivations ℝ A` when `D` is `ℝ`-linear. -/
def modularLinearLiftToReal
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (D : derivations ℤ A)
    (hsmul : ∀ (c : ℝ) (x : A), (D : Module.End ℤ A) (c • x) = c • (D : Module.End ℤ A) x) :
    derivations ℝ A :=
  ⟨{ toFun := fun x => (D : Module.End ℤ A) x
     map_add' := fun x y => (D : Module.End ℤ A).map_add x y
     map_smul' := hsmul }, D.property⟩

/-- `DerivationLieLane ℝ A` attached to any `ℝ`-algebraic bridged lane (`OperatorDerivation`,
`G2Derivation ℝ V`, `DerivationFrame`, `SuperKMS.LinearDerivation ℝ A`, etc.). -/
def realDerivationLieLane (A : Type*) [NonUnitalNonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] :
    DerivationLieLane ℝ A :=
  fullDerivationLieLane ℝ A

/-- `DerivationLieLane ℝ A` attached to any `ℂ`-linear bridged lane (`EndToEnd`, `KMS`,
`ComplexDerivation`, `ColimitFlowDerivation` / `ColimitKMSInfinitesimal`) via
`complexDerivationsRealSubalgebra A`. -/
def complexToRealDerivationLieLane
    (A : Type*) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] :
    DerivationLieLane ℝ A :=
  lieSubalgebraLane (complexDerivationsRealSubalgebra A)

/-- Onsager–Casimir reciprocity for arbitrary-degree forms on any `ℝ`-bridged lane. -/
theorem realLane_onsager_pairing_reciprocity
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (K : DerivationLieLane ℝ A) {n : ℕ}
    (PP : ParityOnsagerFormPairing K.L A n)
    (ω η : DerivationOperatorForm K n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_derivationForm_reciprocity K PP ω η

/-- Evaluation of `inducedDerivationLaneOnsagerSystem` on `OperatorialFierz.OperatorDerivation`. -/
@[simp]
theorem operatorDerivation_inducedOnsager_eval
    {𝒜 : Type*} [NonUnitalNonAssocRing 𝒜] [Module ℝ 𝒜]
    [IsScalarTower ℝ 𝒜 𝒜] [SMulCommClass ℝ 𝒜 𝒜]
    (S : OnsagerCasimirSystem 𝒜) (a : 𝒜)
    (D₁ D₂ : InfoGeometry.Canonical.OperatorialFierz.OperatorDerivation 𝒜) :
    (inducedDerivationLaneOnsagerSystem S (realDerivationLieLane 𝒜) a).totalGenerator
        (operatorDerivationEquivDerivations D₁)
        (operatorDerivationEquivDerivations D₂) =
      S.totalGenerator (D₁ a) (D₂ a) :=
  inducedDerivationLaneOnsagerSystem_totalGenerator S (realDerivationLieLane 𝒜) a _ _

/-- Evaluation of `inducedDerivationLaneOnsagerSystem` on `BipolarObservableMetriplecticAlgebra.DerivationFrame`. -/
@[simp]
theorem derivationFrame_inducedOnsager_eval
    {A : Type*} [CommRing A] [Algebra ℝ A]
    (S : OnsagerCasimirSystem A) (a : A)
    (F : InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra.DerivationFrame A) :
    (inducedDerivationLaneOnsagerSystem S (mathlibDerivationLieLane ℝ A) a).totalGenerator
        F.Dtheta F.Da =
      S.totalGenerator (F.Dtheta a) (F.Da a) :=
  inducedDerivationLaneOnsagerSystem_totalGenerator S (mathlibDerivationLieLane ℝ A) a F.Dtheta F.Da

/-- Evaluation of `inducedDerivationLaneOnsagerSystem` on a `ℂ`-colimit `TowerDerivation`
restricted to `ℝ`. -/
@[simp]
theorem colimitTower_inducedOnsager_eval
    (A : ℕ → Type*) [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
    [∀ n, StarRing (A n)] [∀ n, StarModule ℂ (A n)]
    (iota : ∀ n, A n →⋆ₐ[ℂ] A (n + 1))
    (A_inf : Type*) [Ring A_inf] [Algebra ℂ A_inf] [StarRing A_inf] [StarModule ℂ A_inf]
    [Algebra ℝ A_inf] [IsScalarTower ℝ ℂ A_inf]
    (psi : ∀ n, A n →⋆ₐ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (h_surj : ∀ x : A_inf, ∃ (n : ℕ) (xn : A n), psi n xn = x)
    (h_inj : ∀ {n : ℕ} (x y : A n), psi n x = psi n y →
      ∃ m, InfoGeometry.Modular.ColimitFlowDerivation.iota_seq A iota n m x =
        InfoGeometry.Modular.ColimitFlowDerivation.iota_seq A iota n m y)
    (S : OnsagerCasimirSystem A_inf) (a : A_inf)
    (t₁ t₂ : InfoGeometry.Modular.ColimitFlowDerivation.TowerDerivation A iota) :
    (inducedDerivationLaneOnsagerSystem S (complexToRealDerivationLieLane A_inf) a).totalGenerator
        (complexDerivationToRealSubalgebra
          (colimitFlowTowerToColimitDerivation A iota A_inf psi psi_comm h_surj h_inj t₁))
        (complexDerivationToRealSubalgebra
          (colimitFlowTowerToColimitDerivation A iota A_inf psi psi_comm h_surj h_inj t₂)) =
      S.totalGenerator
        ((colimitFlowTowerToColimitDerivation A iota A_inf psi psi_comm h_surj h_inj t₁ :
          Module.End ℂ A_inf) a)
        ((colimitFlowTowerToColimitDerivation A iota A_inf psi psi_comm h_surj h_inj t₂ :
          Module.End ℂ A_inf) a) :=
  inducedDerivationLaneOnsagerSystem_totalGenerator S (complexToRealDerivationLieLane A_inf) a _ _

/-- Evaluation of `inducedDerivationLaneOnsagerSystem` on any `ℝ`-linear `ℤ`-derivation lifted
via `modularLinearLiftToReal`. -/
@[simp]
theorem modularZDerivation_inducedOnsager_eval
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (S : OnsagerCasimirSystem A) (a : A)
    (D₁ D₂ : derivations ℤ A)
    (h₁ : ∀ (c : ℝ) (x : A), (D₁ : Module.End ℤ A) (c • x) = c • (D₁ : Module.End ℤ A) x)
    (h₂ : ∀ (c : ℝ) (x : A), (D₂ : Module.End ℤ A) (c • x) = c • (D₂ : Module.End ℤ A) x) :
    (inducedDerivationLaneOnsagerSystem S (realDerivationLieLane A) a).totalGenerator
        (modularLinearLiftToReal D₁ h₁) (modularLinearLiftToReal D₂ h₂) =
      S.totalGenerator ((D₁ : Module.End ℤ A) a) ((D₂ : Module.End ℤ A) a) :=
  inducedDerivationLaneOnsagerSystem_totalGenerator S (realDerivationLieLane A) a _ _

end F7_6_CanonicalSpineAttachment

end InfoGeometry.Canonical.ModularDerivationLaneBridge
