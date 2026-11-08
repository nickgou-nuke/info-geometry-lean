import InfoGeometry.Optics.QuaternionCl44QGTBianchiChernWeil
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorQGTFrechetChernCharacter

set_option autoImplicit false

/-!
# Normed Fréchet realization of the quaternionic `Cl(4,4)` QGT carrier

The algebraic Zorn spinor deliberately carries no global norm instance.  Its
existing exact coordinate equivalences instead identify it with a finite
complex coordinate space.  Conjugating endomorphisms through that equivalence
and using Mathlib's finite-dimensional continuity theorem gives a faithful
algebra homomorphism into a genuine normed algebra of continuous linear maps.
The traced characteristic powers therefore have native Mathlib Fréchet
derivatives without adding an arbitrary norm to the original Zorn type.
-/

noncomputable section

namespace InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization

open CanonicalZornCliffordRepresentation
open CanonicalZornCompositionTriality
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.OperatorQGTChernWeil
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance
open InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance

/-- Exact normed coordinate realization of one sixteen-component Zorn Dirac
spinor. -/
abbrev DiracSpinorCoordinates := (Fin 8 → ℂ) × (Fin 8 → ℂ)

/-- Coordinate realization of the causal two-sheet Dirac carrier. -/
abbrev DoubledDiracSpinorCoordinates := Fin 2 → DiracSpinorCoordinates

/-- Normed operator algebra used by the analytic realization. -/
abbrev CoordinateContinuousEnd :=
  DoubledDiracSpinorCoordinates →L[ℂ] DoubledDiracSpinorCoordinates

/-- The existing plus/minus Zorn coordinate equivalences assembled into the
full Dirac-spinor coordinate equivalence. -/
def diracSpinorCoordinateEquiv :
    DiracSpinor16 ≃ₗ[ℂ] DiracSpinorCoordinates :=
  LinearEquiv.prodCongr
    (copyLinearEquivCoordinates .spinorPlus)
    (copyLinearEquivCoordinates .spinorMinus)

/-- Apply the Dirac coordinate equivalence independently on both causal
sheets. -/
def doubledDiracSpinorCoordinateEquiv :
    (Fin 2 → DiracSpinor16) ≃ₗ[ℂ] DoubledDiracSpinorCoordinates :=
  LinearEquiv.piCongrRight (fun _ ↦ diracSpinorCoordinateEquiv)

/-- On a finite-dimensional normed coordinate space every algebraic linear
endomorphism is continuous; this inclusion preserves the complete algebra
structure. -/
def algebraicEndToContinuous :
    Module.End ℂ DoubledDiracSpinorCoordinates →ₐ[ℂ]
      CoordinateContinuousEnd where
  toFun f := LinearMap.toContinuousLinearMap f
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    change (1 : Module.End ℂ DoubledDiracSpinorCoordinates) x =
      (1 : CoordinateContinuousEnd) x
    rfl
  map_mul' f g := by
    apply ContinuousLinearMap.ext
    intro x
    change (f * g) x =
      (LinearMap.toContinuousLinearMap f *
        LinearMap.toContinuousLinearMap g) x
    rfl
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    change (0 : Module.End ℂ DoubledDiracSpinorCoordinates) x =
      (0 : CoordinateContinuousEnd) x
    rfl
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro x
    change (f + g) x =
      (LinearMap.toContinuousLinearMap f +
        LinearMap.toContinuousLinearMap g) x
    rfl
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    change (algebraMap ℂ (Module.End ℂ DoubledDiracSpinorCoordinates) c) x =
      (algebraMap ℂ CoordinateContinuousEnd c) x
    rfl

/-- Faithful normed realization of every doubled Zorn-spinor endomorphism. -/
def coordinateContinuousRepresentation :
    DiracDoubledEnd →ₐ[ℂ] CoordinateContinuousEnd :=
  algebraicEndToContinuous.comp
    (LinearEquiv.conjAlgEquiv ℂ doubledDiracSpinorCoordinateEquiv).toAlgHom

@[simp] theorem coordinateContinuousRepresentation_apply
    (A : DiracDoubledEnd) (v : Fin 2 → DiracSpinor16) :
    coordinateContinuousRepresentation A
        (doubledDiracSpinorCoordinateEquiv v) =
      doubledDiracSpinorCoordinateEquiv (A v) := by
  change doubledDiracSpinorCoordinateEquiv
      (A (doubledDiracSpinorCoordinateEquiv.symm
        (doubledDiracSpinorCoordinateEquiv v))) = _
  rw [doubledDiracSpinorCoordinateEquiv.symm_apply_apply]

theorem coordinateContinuousRepresentation_injective :
    Function.Injective coordinateContinuousRepresentation := by
  intro A B h
  apply (LinearEquiv.conjAlgEquiv ℂ doubledDiracSpinorCoordinateEquiv).injective
  apply LinearMap.toContinuousLinearMap.injective
  exact h

/-- An algebraic doubled-spinor frame transported faithfully into the normed
coordinate operator algebra. -/
def coordinateContinuousUnit (u : DiracDoubledEndˣ) :
    CoordinateContinuousEndˣ :=
  Units.map coordinateContinuousRepresentation.toMonoidHom u

@[simp] theorem coordinateContinuousUnit_val (u : DiracDoubledEndˣ) :
    (coordinateContinuousUnit u : CoordinateContinuousEnd) =
      coordinateContinuousRepresentation (u : DiracDoubledEnd) :=
  rfl

/-- Faithful coordinate realization intertwines the complete inner frame
action, including inversion of the implementer. -/
theorem coordinateContinuousRepresentation_innerConjugation
    (u : DiracDoubledEndˣ) (A : DiracDoubledEnd) :
    coordinateContinuousRepresentation (innerConjugation u A) =
      innerConjugation (coordinateContinuousUnit u)
        (coordinateContinuousRepresentation A) := by
  simp [innerConjugation, coordinateContinuousUnit]

/-- Transport an algebraic doubled Dirac-QGT connection to its faithful
normed coordinate realization. -/
def coordinateContinuousConnection {Point Tangent : Type*}
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd)) :
    Connection
      (Point := Point) (Tangent := Tangent)
      (Value := CoordinateContinuousEnd) :=
  mapConnection coordinateContinuousRepresentation.toRingHom C

@[simp] theorem coordinateContinuousConnection_form
    {Point Tangent : Type*}
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd))
    (p : Point) (X : Tangent) :
    (coordinateContinuousConnection C).form p X =
      coordinateContinuousRepresentation (C.form p X) :=
  rfl

/-- The faithful normed representation preserves the full curvature
two-operator form, not only the connection coefficients. -/
theorem coordinateContinuousConnection_curvature
    {Point Tangent : Type*}
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd))
    (p : Point) (X Y : Tangent) :
    curvature (coordinateContinuousConnection C) p X Y =
      coordinateContinuousRepresentation (curvature C p X Y) :=
  (mapConnection_curvature
    coordinateContinuousRepresentation.toRingHom C p X Y).symm

/-- Algebraic trace on continuous coordinate endomorphisms. -/
def coordinateTraceLinear : CoordinateContinuousEnd →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ DoubledDiracSpinorCoordinates).comp
    (ContinuousLinearMap.coeLM ℂ)

/-- The trace is continuous because its operator domain is finite-dimensional. -/
def coordinateTraceCLM : CoordinateContinuousEnd →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap coordinateTraceLinear

@[simp] theorem coordinateTraceCLM_apply (A : CoordinateContinuousEnd) :
    coordinateTraceCLM A =
      LinearMap.trace ℂ DoubledDiracSpinorCoordinates A.toLinearMap :=
  rfl

/-- The faithful normed coordinate representation preserves the native
finite-dimensional trace exactly. -/
@[simp] theorem coordinateTraceCLM_coordinateContinuousRepresentation
    (A : DiracDoubledEnd) :
    coordinateTraceCLM (coordinateContinuousRepresentation A) =
      LinearMap.trace ℂ (Fin 2 → DiracSpinor16) A := by
  change LinearMap.trace ℂ DoubledDiracSpinorCoordinates
      ((LinearEquiv.conjAlgEquiv ℂ doubledDiracSpinorCoordinateEquiv) A) =
    LinearMap.trace ℂ (Fin 2 → DiracSpinor16) A
  exact LinearMap.trace_conj' A doubledDiracSpinorCoordinateEquiv

/-- Consequently every represented characteristic power has exactly the
same trace as its algebraic doubled-spinor source. -/
theorem coordinateFrechetTracePower_representation
    (k : ℕ) (A : DiracDoubledEnd) :
    coordinateTraceCLM ((coordinateContinuousRepresentation A) ^ k) =
      LinearMap.trace ℂ (Fin 2 → DiracSpinor16) (A ^ k) := by
  rw [← map_pow, coordinateTraceCLM_coordinateContinuousRepresentation]

/-- The faithful normed realization also preserves the trace of every
ordered noncommutative power derivative. -/
theorem coordinateTrace_operatorPowerDerivative_representation
    (k : ℕ) (F dF : DiracDoubledEnd) :
    coordinateTraceCLM
        (operatorPowerDerivative k
          (coordinateContinuousRepresentation F)
          (coordinateContinuousRepresentation dF)) =
      LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        (operatorPowerDerivative k F dF) := by
  calc
    coordinateTraceCLM
        (operatorPowerDerivative k
          (coordinateContinuousRepresentation F)
          (coordinateContinuousRepresentation dF)) =
      coordinateTraceCLM
        (coordinateContinuousRepresentation
          (operatorPowerDerivative k F dF)) := by
            exact congrArg coordinateTraceCLM
              (map_operatorPowerDerivative
                coordinateContinuousRepresentation.toRingHom k F dF).symm
    _ = LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        (operatorPowerDerivative k F dF) :=
      coordinateTraceCLM_coordinateContinuousRepresentation _

/-- Cyclicity of the native finite-dimensional trace on continuous
coordinate endomorphisms. -/
theorem coordinateTraceCLM_mul_comm (A B : CoordinateContinuousEnd) :
    coordinateTraceCLM (A * B) = coordinateTraceCLM (B * A) := by
  change LinearMap.trace ℂ DoubledDiracSpinorCoordinates
      (A.toLinearMap * B.toLinearMap) =
    LinearMap.trace ℂ DoubledDiracSpinorCoordinates
      (B.toLinearMap * A.toLinearMap)
  exact LinearMap.trace_mul_comm ℂ A.toLinearMap B.toLinearMap

/-- The continuous coordinate trace is invariant under every invertible
continuous frame. -/
theorem coordinateTraceCLM_innerConjugation
    (u : CoordinateContinuousEndˣ) (A : CoordinateContinuousEnd) :
    coordinateTraceCLM (innerConjugation u A) = coordinateTraceCLM A := by
  unfold innerConjugation
  calc
    coordinateTraceCLM ((u : CoordinateContinuousEnd) * A *
        (↑(u⁻¹) : CoordinateContinuousEnd)) =
      coordinateTraceCLM ((↑(u⁻¹) : CoordinateContinuousEnd) *
        ((u : CoordinateContinuousEnd) * A)) :=
      coordinateTraceCLM_mul_comm
        ((u : CoordinateContinuousEnd) * A)
        (↑(u⁻¹) : CoordinateContinuousEnd)
    _ = coordinateTraceCLM
        (((↑(u⁻¹) : CoordinateContinuousEnd) *
          (u : CoordinateContinuousEnd)) * A) := by rw [mul_assoc]
    _ = coordinateTraceCLM A := by rw [Units.inv_mul, one_mul]

/-- Unnormalized analytic Chern character on the normed coordinate operator
algebra. -/
def coordinateFrechetChernCharacter (k : ℕ) :
    CoordinateContinuousEnd → ℂ :=
  fun A ↦ coordinateTraceCLM (A ^ k)

/-- Native ordered Fréchet derivative of the coordinate Chern character. -/
def coordinateFrechetChernCharacterDerivative
    (k : ℕ) (A : CoordinateContinuousEnd) :
    CoordinateContinuousEnd →L[ℂ] ℂ :=
  coordinateTraceCLM.comp (powerDerivative (𝕜 := ℂ) k A)

@[simp] theorem coordinateFrechetChernCharacterDerivative_apply
    (k : ℕ) (A H : CoordinateContinuousEnd) :
    coordinateFrechetChernCharacterDerivative k A H =
      coordinateTraceCLM (powerDerivative (𝕜 := ℂ) k A H) :=
  rfl

/-- Every analytic coordinate Chern character is invariant under a finite
continuous frame change. -/
theorem coordinateFrechetChernCharacter_innerConjugation
    (k : ℕ) (u : CoordinateContinuousEndˣ) (A : CoordinateContinuousEnd) :
    coordinateFrechetChernCharacter k (innerConjugation u A) =
      coordinateFrechetChernCharacter k A := by
  change coordinateTraceCLM ((innerConjugation u A) ^ k) =
    coordinateTraceCLM (A ^ k)
  change coordinateTraceCLM (((innerConjugationRingEquiv u) A) ^ k) = _
  rw [← map_pow]
  exact coordinateTraceCLM_innerConjugation u (A ^ k)

/-- Cyclic reduction of the ordered noncommutative Fréchet power
derivative in the normed coordinate realization. -/
theorem coordinateTraceCLM_powerDerivative
    (k : ℕ) (A H : CoordinateContinuousEnd) :
    coordinateTraceCLM (powerDerivative (𝕜 := ℂ) k A H) =
      (k : ℂ) * coordinateTraceCLM (H * A ^ k.pred) := by
  simp only [powerDerivative, ContinuousLinearMap.sum_apply]
  rw [map_sum]
  have hterm : ∀ i ∈ Finset.range k,
      coordinateTraceCLM (A ^ (k.pred - i) * H * A ^ i) =
        coordinateTraceCLM (H * A ^ k.pred) := by
    intro i hi
    have hilt : i < k := Finset.mem_range.mp hi
    have hile : i ≤ k.pred := Nat.le_pred_of_lt hilt
    calc
      coordinateTraceCLM (A ^ (k.pred - i) * H * A ^ i) =
          coordinateTraceCLM (A ^ (k.pred - i) * (H * A ^ i)) := by
            rw [mul_assoc]
      _ = coordinateTraceCLM ((H * A ^ i) * A ^ (k.pred - i)) :=
        coordinateTraceCLM_mul_comm _ _
      _ = coordinateTraceCLM (H * (A ^ i * A ^ (k.pred - i))) := by
        rw [mul_assoc]
      _ = coordinateTraceCLM (H * A ^ k.pred) := by
        rw [← pow_add, Nat.add_sub_of_le hile]
  calc
    ∑ i ∈ Finset.range k,
        coordinateTraceCLM (A ^ (k.pred - i) * H * A ^ i) =
      ∑ _i ∈ Finset.range k,
        coordinateTraceCLM (H * A ^ k.pred) := by
          exact Finset.sum_congr rfl (fun i hi ↦ hterm i hi)
    _ = (k : ℂ) * coordinateTraceCLM (H * A ^ k.pred) := by simp

theorem coordinateFrechetChernCharacterDerivative_eq
    (k : ℕ) (A H : CoordinateContinuousEnd) :
    coordinateFrechetChernCharacterDerivative k A H =
      (k : ℂ) * coordinateTraceCLM (H * A ^ k.pred) := by
  rw [coordinateFrechetChernCharacterDerivative_apply,
    coordinateTraceCLM_powerDerivative]

/-- A commutator tangent followed by the matching operator power has zero
continuous coordinate trace. -/
theorem coordinateTraceCLM_commutator_mul_pow_zero
    (m : ℕ) (X A : CoordinateContinuousEnd) :
    coordinateTraceCLM ((X * A - A * X) * A ^ m) = 0 := by
  rw [sub_mul, map_sub]
  have hcyc : coordinateTraceCLM (A * (X * A ^ m)) =
      coordinateTraceCLM ((X * A ^ m) * A) :=
    coordinateTraceCLM_mul_comm A (X * A ^ m)
  calc
    coordinateTraceCLM (X * A * A ^ m) -
        coordinateTraceCLM (A * X * A ^ m) =
      coordinateTraceCLM (X * A ^ (m + 1)) -
        coordinateTraceCLM (A * (X * A ^ m)) := by
          simp only [mul_assoc]
          rw [← pow_succ' A m]
    _ = coordinateTraceCLM (X * A ^ (m + 1)) -
        coordinateTraceCLM ((X * A ^ m) * A) := by rw [hcyc]
    _ = 0 := by rw [pow_succ]; exact sub_self _

/-- Infinitesimal inner-frame directions lie in the kernel of every analytic
coordinate Chern-character differential. -/
theorem coordinateFrechetChernCharacterDerivative_commutator
    (k : ℕ) (A X : CoordinateContinuousEnd) :
    coordinateFrechetChernCharacterDerivative k A (X * A - A * X) = 0 := by
  cases k with
  | zero => simp [coordinateFrechetChernCharacterDerivative]
  | succ m =>
      rw [coordinateFrechetChernCharacterDerivative_eq]
      simp only [Nat.cast_add, Nat.cast_one, Nat.pred_succ]
      rw [coordinateTraceCLM_commutator_mul_pow_zero, mul_zero]

theorem coordinateFrechetChernCharacterDerivative_associativeCommutator
    (k : ℕ) (A X : CoordinateContinuousEnd) :
    coordinateFrechetChernCharacterDerivative k A
      (associativeCommutator X A) = 0 :=
  coordinateFrechetChernCharacterDerivative_commutator k A X

/-- Naturality of the genuine Fréchet differential under simultaneous
conjugation of its base and tangent operators. -/
theorem coordinateFrechetChernCharacterDerivative_innerConjugation
    (k : ℕ) (u : CoordinateContinuousEndˣ) (A H : CoordinateContinuousEnd) :
    coordinateFrechetChernCharacterDerivative k (innerConjugation u A)
        (innerConjugation u H) =
      coordinateFrechetChernCharacterDerivative k A H := by
  rw [coordinateFrechetChernCharacterDerivative_eq,
    coordinateFrechetChernCharacterDerivative_eq]
  congr 1
  change coordinateTraceCLM
      ((innerConjugationRingEquiv u H) *
        (innerConjugationRingEquiv u A) ^ k.pred) = _
  rw [← map_pow, ← map_mul]
  exact coordinateTraceCLM_innerConjugation u (H * A ^ k.pred)

/-- Genuine Mathlib Fréchet differentiability of every traced
characteristic power in the faithful normed realization. -/
theorem hasFDerivAt_coordinateFrechetChernCharacter
    (k : ℕ) (A : CoordinateContinuousEnd) :
    HasFDerivAt (coordinateFrechetChernCharacter k)
      (coordinateFrechetChernCharacterDerivative k A) A := by
  exact coordinateTraceCLM.hasFDerivAt.comp A
    (hasFDerivAt_power_noncommutative (𝕜 := ℂ) k A)

theorem fderiv_coordinateFrechetChernCharacter
    (k : ℕ) (A : CoordinateContinuousEnd) :
    fderiv ℂ (coordinateFrechetChernCharacter k) A =
      coordinateFrechetChernCharacterDerivative k A :=
  (hasFDerivAt_coordinateFrechetChernCharacter k A).fderiv

/-- Native `fderiv` form of infinitesimal inner-frame invariance. -/
theorem fderiv_coordinateFrechetChernCharacter_associativeCommutator
    (k : ℕ) (A X : CoordinateContinuousEnd) :
    (fderiv ℂ (coordinateFrechetChernCharacter k) A)
      (associativeCommutator X A) = 0 := by
  rw [fderiv_coordinateFrechetChernCharacter]
  exact coordinateFrechetChernCharacterDerivative_associativeCommutator k A X

/-- Native `fderiv` naturality under every finite continuous frame change. -/
theorem fderiv_coordinateFrechetChernCharacter_innerConjugation
    (k : ℕ) (u : CoordinateContinuousEndˣ) (A H : CoordinateContinuousEnd) :
    (fderiv ℂ (coordinateFrechetChernCharacter k) (innerConjugation u A))
        (innerConjugation u H) =
      (fderiv ℂ (coordinateFrechetChernCharacter k) A) H := by
  rw [fderiv_coordinateFrechetChernCharacter,
    fderiv_coordinateFrechetChernCharacter]
  exact coordinateFrechetChernCharacterDerivative_innerConjugation k u A H

/-- The `fderiv` covariance theorem pulled back to algebraic doubled Zorn
operators through the faithful continuous representation. -/
theorem fderiv_coordinateFrechetChernCharacter_represented_innerConjugation
    (k : ℕ) (u : DiracDoubledEndˣ) (A H : DiracDoubledEnd) :
    (fderiv ℂ (coordinateFrechetChernCharacter k)
      (coordinateContinuousRepresentation (innerConjugation u A)))
      (coordinateContinuousRepresentation (innerConjugation u H)) =
    (fderiv ℂ (coordinateFrechetChernCharacter k)
      (coordinateContinuousRepresentation A))
      (coordinateContinuousRepresentation H) := by
  rw [coordinateContinuousRepresentation_innerConjugation,
    coordinateContinuousRepresentation_innerConjugation]
  exact fderiv_coordinateFrechetChernCharacter_innerConjugation
    k (coordinateContinuousUnit u)
      (coordinateContinuousRepresentation A)
      (coordinateContinuousRepresentation H)

/-- Concrete Clifford-frame specialization at the curvature of an arbitrary
doubled Dirac-QGT connection and an arbitrary curvature tangent operator. -/
theorem fderiv_coordinateFrechetChernCharacter_scalarPositive_curvature
    {Point Tangent : Type*}
    (k : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd))
    (p : Point) (X Y : Tangent) (H : DiracDoubledEnd) :
    (fderiv ℂ (coordinateFrechetChernCharacter k)
      (coordinateContinuousRepresentation
        (innerConjugation
          (doubledInternalUnit scalarPositiveComplexGammaUnit)
          (curvature C p X Y))))
      (coordinateContinuousRepresentation
        (innerConjugation
          (doubledInternalUnit scalarPositiveComplexGammaUnit) H)) =
    (fderiv ℂ (coordinateFrechetChernCharacter k)
      (coordinateContinuousRepresentation (curvature C p X Y)))
      (coordinateContinuousRepresentation H) :=
  fderiv_coordinateFrechetChernCharacter_represented_innerConjugation
    k (doubledInternalUnit scalarPositiveComplexGammaUnit)
      (curvature C p X Y) H

/-- The faithful normed representation preserves infinitesimal inner
derivations exactly. -/
theorem coordinateContinuousRepresentation_associativeCommutator
    (X A : DiracDoubledEnd) :
    coordinateContinuousRepresentation (associativeCommutator X A) =
      associativeCommutator
        (coordinateContinuousRepresentation X)
        (coordinateContinuousRepresentation A) := by
  simp [associativeCommutator]

/-- The positive Clifford generator in the faithful normed coordinate
algebra. -/
def coordinateScalarPositiveGenerator : CoordinateContinuousEnd :=
  coordinateContinuousRepresentation
    (doubledInternalOperator scalarPositiveComplexGamma)

/-- Infinitesimal positive-Clifford conjugation of a represented Dirac-QGT
curvature is killed by every analytic Chern-character differential. -/
theorem fderiv_coordinateFrechetChernCharacter_scalarPositive_commutator_curvature
    {Point Tangent : Type*}
    (k : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd))
    (p : Point) (X Y : Tangent) :
    (fderiv ℂ (coordinateFrechetChernCharacter k)
      (coordinateContinuousRepresentation (curvature C p X Y)))
      (associativeCommutator coordinateScalarPositiveGenerator
        (coordinateContinuousRepresentation (curvature C p X Y))) = 0 :=
  fderiv_coordinateFrechetChernCharacter_associativeCommutator k
    (coordinateContinuousRepresentation (curvature C p X Y))
    coordinateScalarPositiveGenerator

/-- Equivalent pullback statement: the analytic differential annihilates the
faithful image of the original algebraic Clifford commutator tangent. -/
theorem fderiv_coordinateFrechetChernCharacter_scalarPositive_algebraicCommutator
    {Point Tangent : Type*}
    (k : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd))
    (p : Point) (X Y : Tangent) :
    (fderiv ℂ (coordinateFrechetChernCharacter k)
      (coordinateContinuousRepresentation (curvature C p X Y)))
      (coordinateContinuousRepresentation
        (associativeCommutator
          (doubledInternalOperator scalarPositiveComplexGamma)
          (curvature C p X Y))) = 0 := by
  rw [coordinateContinuousRepresentation_associativeCommutator]
  exact
    fderiv_coordinateFrechetChernCharacter_scalarPositive_commutator_curvature
      k C p X Y

/-- The analytic Chern character is genuinely Fréchet differentiable at
the represented curvature of every algebraic doubled Dirac-QGT connection. -/
theorem hasFDerivAt_coordinateFrechetChernCharacter_at_curvature
    {Point Tangent : Type*}
    (k : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd))
    (p : Point) (X Y : Tangent) :
    HasFDerivAt (coordinateFrechetChernCharacter k)
      (coordinateFrechetChernCharacterDerivative k
        (coordinateContinuousRepresentation (curvature C p X Y)))
      (coordinateContinuousRepresentation (curvature C p X Y)) :=
  hasFDerivAt_coordinateFrechetChernCharacter k
    (coordinateContinuousRepresentation (curvature C p X Y))

/-- Equivalent formulation using the curvature computed directly after
mapping the complete connection into the normed coordinate algebra. -/
theorem hasFDerivAt_coordinateFrechetChernCharacter_at_mappedCurvature
    {Point Tangent : Type*}
    (k : ℕ)
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd))
    (p : Point) (X Y : Tangent) :
    HasFDerivAt (coordinateFrechetChernCharacter k)
      (coordinateFrechetChernCharacterDerivative k
        (curvature (coordinateContinuousConnection C) p X Y))
      (curvature (coordinateContinuousConnection C) p X Y) := by
  rw [coordinateContinuousConnection_curvature]
  exact hasFDerivAt_coordinateFrechetChernCharacter_at_curvature k C p X Y

end InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization

end noncomputable section
