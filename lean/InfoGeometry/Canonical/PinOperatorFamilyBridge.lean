/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NormalizedVectorPin
import InfoGeometry.Canonical.GradedCliffordOperatorRepresentation
import InfoGeometry.Canonical.Cl11MatrixCliffordBridge
import InfoGeometry.Canonical.OperatorValuedSouriauFamily
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Canonical.OperatorModularTemperatureDuality
import InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Pin actions on operator domains and transported operator families

This bridge keeps the carriers explicit. A normalized-vector Pin group acts
through an algebra representation into endomorphisms of a module. A separate
operator grading is recorded by its involutive endomorphism and its
anticommutation law on Clifford generators. The graded Morita bridge is the
native `C₂` action on the regular operator module. Operator-family covariance
is stated for the transported exponential-family packet; no analytic
invariance of the scalar readout is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.PinOperatorFamilyBridge

open CliffordAlgebra
open InfoGeometry.Clifford.NormalizedVectorPin
open InfoGeometry.Canonical
open InfoGeometry.Clifford.FreedCliffordSuspension
open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Canonical.OperatorModularTemperatureDuality

variable {R M W : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup W] [Module R W]
variable {Q : QuadraticForm R M}

/-- The group representation induced by an algebra representation of the
Clifford algebra on an operator domain `W`. -/
def cliffordUnitRepresentation
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End R W) :
    (CliffordAlgebra Q)ˣ →* (Module.End R W)ˣ :=
  Units.map ρ.toMonoidHom

/-- Pin representation on any noncommutative operator ring receiving the
Clifford algebra, without identifying that carrier with a scalar field. -/
def pinOperatorRingRepresentation
    {Obs : Type*} [Ring Obs] [Algebra R Obs]
    (ρ : CliffordAlgebra Q →ₐ[R] Obs) : pin Q →* Obsˣ :=
  (Units.map ρ.toMonoidHom).comp (pin Q).subtype

/-- The normalized-vector Pin group acts by the represented Clifford units. -/
def pinOperatorRepresentation
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End R W) :
    pin Q →* (Module.End R W)ˣ :=
  (cliffordUnitRepresentation ρ).comp (pin Q).subtype

/-- An operator from the represented Pin unit, acting on the stated domain. -/
def pinOperator
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End R W) (g : pin Q) :
    Module.End R W :=
  (pinOperatorRepresentation ρ g : (Module.End R W)ˣ)

/-- The domain action respects multiplication in the Pin group. -/
theorem pinOperatorRepresentation_mul
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End R W) (g h : pin Q) :
    pinOperatorRepresentation ρ (g * h) =
      pinOperatorRepresentation ρ g * pinOperatorRepresentation ρ h := by
  exact (pinOperatorRepresentation ρ).map_mul g h

/-- A normalized Clifford vector is represented by the specified algebra map. -/
@[simp] theorem pinOperatorRepresentation_vector
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End R W) (v : M)
    (hv : Q v = 1 ∨ Q v = -1) :
    pinOperator ρ (pinVector Q v hv) = ρ (ι Q v) := by
  change ρ (((pinVector Q v hv : pin Q) : (CliffordAlgebra Q)ˣ) :
    CliffordAlgebra Q) = _
  rw [pinVector_coe]

/-! ## Explicit real `Cl(1,1)` matrix representation and grading -/

abbrev Cl11OperatorDomain := Fin 2 → ℝ

/-- The existing `Cl(1,1)` matrix representation, viewed as operators on its
two-dimensional real domain. -/
def cl11OperatorRepresentation :
    InfoGeometry.Canonical.Cl11MatrixCliffordBridge.Cl11 →ₐ[ℝ]
      Module.End ℝ Cl11OperatorDomain :=
  (Matrix.toLinAlgEquiv').toAlgHom.comp
    InfoGeometry.Canonical.Cl11MatrixCliffordBridge.cl11MatrixRep

/-- The grading operator is the represented split-Clifford volume element. -/
def cl11OperatorGrading : Module.End ℝ Cl11OperatorDomain :=
  Matrix.toLinAlgEquiv'
    InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitIL

private theorem cl11SplitOne_eq_one :
    InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitOne =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext j k
  fin_cases j <;> fin_cases k <;> simp [InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitOne,
    BottPeriodicityReconciliation.I2]

theorem cl11OperatorGrading_sq :
    cl11OperatorGrading * cl11OperatorGrading = 1 := by
  dsimp [cl11OperatorGrading]
  rw [← map_mul, InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitIL_sq,
    cl11SplitOne_eq_one, Matrix.toLinAlgEquiv'_one]
  rfl

theorem cl11OperatorRepresentation_generator_odd (v : ℝ × ℝ) :
    cl11OperatorGrading *
        cl11OperatorRepresentation
          (CliffordAlgebra.ι
            InfoGeometry.Clifford.splitQ11 v) +
      cl11OperatorRepresentation
        (CliffordAlgebra.ι
          InfoGeometry.Clifford.splitQ11 v) *
        cl11OperatorGrading = 0 := by
  have hmat :
      InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitIL *
          InfoGeometry.Canonical.Cl11MatrixCliffordBridge.matrixGenerator v +
          InfoGeometry.Canonical.Cl11MatrixCliffordBridge.matrixGenerator v *
            InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitIL = 0 := by
    rcases v with ⟨a, b⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Canonical.Cl11MatrixCliffordBridge.matrixGenerator,
        InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitIL,
        InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitI,
        InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitL,
        InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge.splitOne,
        BottPeriodicityReconciliation.epsilon,
        BottPeriodicityReconciliation.sigma1R,
        BottPeriodicityReconciliation.I2,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  dsimp [cl11OperatorGrading, cl11OperatorRepresentation, AlgHom.comp_apply]
  rw [InfoGeometry.Canonical.Cl11MatrixCliffordBridge.cl11MatrixRep_ι]
  rw [← map_mul, ← map_mul, ← map_add, hmat, map_zero]

def cl11GradedOperatorRepresentation :
    GradedCliffordOperatorRepresentation
      (R := ℝ) (M := ℝ × ℝ) (W := Cl11OperatorDomain)
      (Q := InfoGeometry.Clifford.splitQ11) where
  representation := cl11OperatorRepresentation
  grading := cl11OperatorGrading
  grading_sq := cl11OperatorGrading_sq
  generator_odd := cl11OperatorRepresentation_generator_odd

/-! ## Freed suspension compatibility at the represented Pin level -/

variable (Q)

/-- The target even-Pin action obtained by representing the ambient target
Clifford units. -/
def positiveSuspendedPinOperatorRepresentation
    (τ : CliffordAlgebra (positiveForm Q) →ₐ[R] Module.End R W) :
    pin Q →* (Module.End R W)ˣ :=
  (Units.map τ.toMonoidHom).comp
    ((evenPinToUnits (positiveForm Q)).comp (positivePinHom Q))

/-- The operator representation commutes with the ordered positive Pin
suspension. -/
theorem positivePinOperatorRepresentation_compatibility
    (τ : CliffordAlgebra (positiveForm Q) →ₐ[R] Module.End R W) (g : pin Q) :
    positiveSuspendedPinOperatorRepresentation Q τ g =
      pinOperatorRepresentation (τ.comp (positiveMap Q)) g := by
  apply Units.ext
  change τ (((evenPinToUnits (positiveForm Q) (positivePinHom Q g) :
    (CliffordAlgebra (positiveForm Q))ˣ) : CliffordAlgebra (positiveForm Q))) =
    τ (positiveMap Q (((g : pin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
  rw [positivePinHom_ambient]

/-- The negative Freed suspension has the corresponding represented-Pin
compatibility, with source quadratic form `-Q`. -/
theorem negativePinOperatorRepresentation_compatibility
    (τ : CliffordAlgebra (negativeForm Q) →ₐ[R] Module.End R W)
    (g : pin (-Q)) :
    (Units.map τ.toMonoidHom).comp
        ((evenPinToUnits (negativeForm Q)).comp (negativePinHom Q)) g =
      pinOperatorRepresentation (τ.comp (negativeMap Q)) g := by
  apply Units.ext
  change τ (((evenPinToUnits (negativeForm Q) (negativePinHom Q g) :
    (CliffordAlgebra (negativeForm Q))ˣ) : CliffordAlgebra (negativeForm Q))) =
    τ (negativeMap Q (((g : pin (-Q)) : (CliffordAlgebra (-Q))ˣ) : CliffordAlgebra (-Q)))
  rw [negativePinHom_ambient]

/-! ## The represented grading as the native `C₂` action used by graded Morita -/

variable {A : Type*} [Ring A]

/-- Inner conjugation by an involution as an additive grading on the regular
operator module. -/
def innerGradingAddHom (G : A) : A →+ A where
  toFun x := G * x * G
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]

theorem innerGradingAddHom_sq (G : A) (hG : G * G = 1) (x : A) :
    innerGradingAddHom G (innerGradingAddHom G x) = x := by
  simp only [innerGradingAddHom]
  calc
    G * (G * x * G) * G = (G * G) * x * (G * G) := by noncomm_ring
    _ = x := by rw [hG]; noncomm_ring

theorem innerGradingAddHom_semilinear (G : A) (hG : G * G = 1) (a x : A) :
    innerGradingAddHom G (a * x) = (G * a * G) * innerGradingAddHom G x := by
  simp only [innerGradingAddHom]
  calc
    G * (a * x) * G = G * a * x * G := by noncomm_ring
    _ = G * a * (G * G) * x * G := by rw [hG]; noncomm_ring
    _ = (G * a * G) * (G * x * G) := by noncomm_ring

/-- A concrete inner grading determines the repository's native `C₂` action
on the regular module of the operator ring. -/
def pinOperatorGradedRegularAction (G : A) (hG : G * G = 1) :
    Action (ModuleCat A) InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.C2 :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.actionOfGrading
    G hG (ModuleCat.of A A) (innerGradingAddHom G)
    (innerGradingAddHom_semilinear G hG)
    (innerGradingAddHom_sq G hG)

/-- The regular-module grading is exactly reconstructed by the native graded
Morita owner. -/
theorem pinOperatorGradedRegularAction_grading
    (G : A) (hG : G * G = 1) (x : A) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.grading G
      (pinOperatorGradedRegularAction G hG) x = innerGradingAddHom G x := by
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.grading_reconstruct
    G hG (ModuleCat.of A A) (innerGradingAddHom G)
    (innerGradingAddHom_semilinear G hG) (innerGradingAddHom_sq G hG) x

/-- Existing Morita unit isomorphisms preserve the induced inner grading. -/
theorem pinGrading_morita_unit_compatibility
    (E : MoritaEquivalence ℤ A A) (G : A) (hG : G * G = 1)
    (X : Action (ModuleCat A)
      InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.C2) (x : X.V) :
    ((InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.gradedMoritaEquivalence E).unitIso.hom.app X).hom
        (InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.grading G X x) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.grading G _
        (((InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.gradedMoritaEquivalence E).unitIso.hom.app X).hom x) := by
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.morita_unit_even E G X x

/-- Existing Morita counit isomorphisms preserve the induced inner grading. -/
theorem pinGrading_morita_counit_compatibility
    (E : MoritaEquivalence ℤ A A) (G : A) (hG : G * G = 1)
    (Y : Action (ModuleCat A)
      InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.C2)
    (y : ((InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.gradedMoritaEquivalence E).functor.obj
      ((InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.gradedMoritaEquivalence E).inverse.obj Y)).V) :
    ((InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.gradedMoritaEquivalence E).counitIso.hom.app Y).hom
        (InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.grading G _ y) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.grading G Y
        (((InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.gradedMoritaEquivalence E).counitIso.hom.app Y).hom y) := by
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita.morita_counit_even E G Y y

/-! ## Operator-family transport under the Pin operator representation -/

variable {Obs LieAlg State Direction : Type*} [Ring Obs]

/-- Inner conjugation by an operator unit as an automorphism of the full
noncommutative operator ring. -/
def operatorInnerAut (u : Obsˣ) : Obs ≃+* Obs where
  toFun x := (u : Obs) * x * (↑u⁻¹ : Obs)
  invFun x := (↑u⁻¹ : Obs) * x * (u : Obs)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc, Units.inv_mul]
  map_add' x y := by noncomm_ring

/-- Transport all operator-valued exponential-family components along a ring
automorphism, with the parameter transformed by the same automorphism. -/
def transportOperatorialExponentialFamily
    (σ : Obs ≃+* Obs)
    (E : OperatorialExponentialFamily Obs Obs) :
    OperatorialExponentialFamily Obs Obs :=
  (fun β => σ (E.K (σ.symm β)),
   fun β => σ (E.untracedExponential (σ.symm β)),
   fun x => E.traceReadout (σ.symm x),
   fun β => σ (E.normalizedState (σ.symm β)))

/-- Transport the ordered Duhamel derivative packet in the same operator
coordinates as the exponential family. -/
def transportDuhamelOperatorDerivative
    (σ : Obs ≃+* Obs)
    (D : DuhamelOperatorDerivative Obs Obs Direction) :
    DuhamelOperatorDerivative Obs Obs Direction :=
  (fun β => σ (D.K (σ.symm β)),
   fun δ => σ (D.directionToInsertion δ),
   fun n β directions => σ (D.higherSimplexOrderedForms n (σ.symm β) directions),
   fun x => D.traceStateKMSReadout (σ.symm x))

@[simp] theorem transportOperatorialExponentialFamily_K
    (σ : Obs ≃+* Obs) (E : OperatorialExponentialFamily Obs Obs) (β : Obs) :
    (transportOperatorialExponentialFamily σ E).K (σ β) = σ (E.K β) := by
  change σ (E.K (σ.symm (σ β))) = σ (E.K β)
  rw [σ.symm_apply_apply]

@[simp] theorem transportOperatorialExponentialFamily_untraced
    (σ : Obs ≃+* Obs) (E : OperatorialExponentialFamily Obs Obs) (β : Obs) :
    (transportOperatorialExponentialFamily σ E).untracedExponential (σ β) =
      σ (E.untracedExponential β) := by
  change σ (E.untracedExponential (σ.symm (σ β))) = σ (E.untracedExponential β)
  rw [σ.symm_apply_apply]

@[simp] theorem transportOperatorialExponentialFamily_traceReadout
    (σ : Obs ≃+* Obs) (E : OperatorialExponentialFamily Obs Obs) (x : Obs) :
    (transportOperatorialExponentialFamily σ E).traceReadout (σ x) =
      E.traceReadout x := by
  change E.traceReadout (σ.symm (σ x)) = E.traceReadout x
  rw [σ.symm_apply_apply]

@[simp] theorem transportDuhamelOperatorDerivative_K
    (σ : Obs ≃+* Obs) (D : DuhamelOperatorDerivative Obs Obs Direction) (β : Obs) :
    (transportDuhamelOperatorDerivative σ D).K (σ β) = σ (D.K β) := by
  change σ (D.K (σ.symm (σ β))) = σ (D.K β)
  rw [σ.symm_apply_apply]

@[simp] theorem transportDuhamelOperatorDerivative_insertion
    (σ : Obs ≃+* Obs) (D : DuhamelOperatorDerivative Obs Obs Direction) (δ : Direction) :
    (transportDuhamelOperatorDerivative σ D).directionToInsertion δ =
      σ (D.directionToInsertion δ) := by
  rfl

@[simp] theorem transportDuhamelOperatorDerivative_orderedForm
    (σ : Obs ≃+* Obs) (D : DuhamelOperatorDerivative Obs Obs Direction)
    (n : ℕ) (β : Obs) (directions : List Direction) :
    (transportDuhamelOperatorDerivative σ D).higherSimplexOrderedForms
        n (σ β) directions =
      σ (D.higherSimplexOrderedForms n β directions) := by
  change σ (D.higherSimplexOrderedForms n (σ.symm (σ β)) directions) =
    σ (D.higherSimplexOrderedForms n β directions)
  rw [σ.symm_apply_apply]

/-- Pin conjugation transports the operator-family generator compatibly with
the existing Souriau-family equality. -/
theorem pin_transports_souriau_generator
    [Algebra R Obs]
    (ρ : CliffordAlgebra Q →ₐ[R] Obs)
    (P : OperatorValuedSouriauFamily LieAlg Obs State Direction)
    (g : pin Q) :
    (transportOperatorialExponentialFamily
      (operatorInnerAut (pinOperatorRingRepresentation (Q := Q) ρ g))
      P.exponentialFamily).K
        (operatorInnerAut (pinOperatorRingRepresentation (Q := Q) ρ g) P.betaOperator) =
      operatorInnerAut (pinOperatorRingRepresentation (Q := Q) ρ g) P.souriauGenerator := by
  rw [transportOperatorialExponentialFamily_K,
    P.exponentialFamily_K_beta_eq_souriauGenerator]

/-- Pin conjugation transports the untraced operator weight compatibly with
the existing Souriau-family equality. -/
theorem pin_transports_untraced_weight
    [Algebra R Obs]
    (ρ : CliffordAlgebra Q →ₐ[R] Obs)
    (P : OperatorValuedSouriauFamily LieAlg Obs State Direction)
    (g : pin Q) :
    (transportOperatorialExponentialFamily
      (operatorInnerAut (pinOperatorRingRepresentation (Q := Q) ρ g))
      P.exponentialFamily).untracedExponential
        (operatorInnerAut (pinOperatorRingRepresentation (Q := Q) ρ g) P.betaOperator) =
      operatorInnerAut (pinOperatorRingRepresentation (Q := Q) ρ g) P.expWeight := by
  rw [transportOperatorialExponentialFamily_untraced,
    P.exponentialFamily_untraced_beta_eq_expWeight]

end InfoGeometry.Canonical.PinOperatorFamilyBridge

end
