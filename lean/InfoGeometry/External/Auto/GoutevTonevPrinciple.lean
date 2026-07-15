import Mathlib
import InfoGeometry.External.Auto.SouriauOperatorThermodynamics
import InfoGeometry.External.Auto.InformationGeometricCutoff
/-!
# Goutev--Tonev Principle: algebraic operator layer

The operator information unit is

  `exp(ε K) - 1 - ε K`.

This file records the finite/algebraic operator identity and connects it to the
already-proved scalar information-geometry layer.  Surprisal, divergence, free
energy, and entropy are consequential readouts of the operator/potential data;
what remains beyond this file is only the analytic realization data such as C⋆
functional calculus or continuum Einstein-limit interpretation.
-/

noncomputable section

namespace GoutevTonevPrinciple

open SouriauOperatorThermodynamics
open SouriauOperatorThermodynamics.OperatorSouriauSystem

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The operator-level Goutev--Tonev Bregman generator.
`K : A` is the modular Hamiltonian — an operator, not a scalar. -/
def informationUnit (expOp : A → A) (ε : ℝ) (K : A) : A :=
  operatorBregmanGenerator (A := A) expOp ε K

/-- The purely algebraic second-order unit, available without an exponential. -/
def quadraticInformationUnit (ε : ℝ) (K : A) : A :=
  goutevTonevUnit (A := A) ε K

/-- Zero-coupling normalization of the full operator unit, assuming `expOp 0 = 1`. -/
theorem informationUnit_zero (expOp : A → A) (h0 : expOp 0 = (1 : A)) (K : A) :
    informationUnit (A := A) expOp 0 K = 0 := by
  exact operatorBregmanGenerator_zero (A := A) expOp h0 K

/-- State readout of the operator unit.  The operator expression is primary;
scalar potentials appear only after applying a state/expectation. -/
theorem expectation_informationUnit
    (ω : A →ₗ[ℝ] ℝ) (expOp : A → A) (ε : ℝ) (K : A) :
    ω (informationUnit (A := A) expOp ε K) =
      ω (expOp (ε • K)) - ω (1 : A) - ε * ω K := by
  exact expectation_operatorBregmanGenerator (A := A) (ω := ω) expOp ε K

/-- State readout of the quadratic information unit. -/
theorem expectation_quadraticInformationUnit
    (ω : A →ₗ[ℝ] ℝ) (ε : ℝ) (K : A) :
    ω (quadraticInformationUnit (A := A) ε K) = (ε ^ 2 / 2) * ω (K * K) := by
  exact expectation_goutevTonevUnit (A := A) (ω := ω) ε K

/-- The Cramér--Rao cutoff is already the information-geometric consequence
proved in `InformationGeometricCutoff`. -/
theorem quantum_cutoff_from_information_geometry
    (cr : InformationGeometricCutoff.CramerRaoQuantumInequality) :
    0 < cr.phaseSpaceVariance :=
  InformationGeometricCutoff.fractal_resolution_limit cr

/-- The minimal positive phase-space pixel is already a proved consequence of
positive Fisher information in `InformationGeometricCutoff`. -/
theorem minimal_pixel_from_information_geometry
    (cr : InformationGeometricCutoff.CramerRaoQuantumInequality) :
    0 < InformationGeometricCutoff.MinimalPhaseSpaceVolume cr :=
  InformationGeometricCutoff.minimal_phase_space_volume_pos cr

/-- Closed algebraic synthesis of the Goutev--Tonev operator unit. -/
theorem goutev_tonev_algebraic_synthesis
    (ω : A →ₗ[ℝ] ℝ) (expOp : A → A) (h0 : expOp 0 = (1 : A)) :
    (∀ K : A, informationUnit (A := A) expOp 0 K = 0) ∧
    (∀ (ε : ℝ) (K : A),
      ω (informationUnit (A := A) expOp ε K) =
        ω (expOp (ε • K)) - ω (1 : A) - ε * ω K) ∧
    (∀ (ε : ℝ) (K : A),
      ω (quadraticInformationUnit (A := A) ε K) = (ε ^ 2 / 2) * ω (K * K)) := by
  refine And.intro ?zeroCoupling ?readouts
  · exact informationUnit_zero (A := A) expOp h0
  · refine And.intro ?fullReadout ?quadraticReadout
    · exact expectation_informationUnit (A := A) (ω := ω) expOp
    · exact expectation_quadraticInformationUnit (A := A) (ω := ω)

/-! ## Complex-linear maps on operator algebras -/

section ComplexOperatorLinearMaps

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- A scalar readout/state-like functional on a complex operator algebra. -/
abbrev OperatorLinearFunctional (B : Type*) [Ring B] [Algebra ℂ B] :=
  B →ₗ[ℂ] ℂ

/-- A complex-linear superoperator on a complex operator algebra. -/
abbrev OperatorLinearMap (B : Type*) [Ring B] [Algebra ℂ B] :=
  B →ₗ[ℂ] B

/-- Left multiplication by an operator is a complex-linear self-map of the operator algebra. -/
def leftMulLinear (K : B) : OperatorLinearMap B where
  toFun x := K * x
  map_add' x y := by
    rw [mul_add]
  map_smul' c x := by
    change K * (c • x) = c • (K * x)
    simp only [Algebra.smul_def]
    calc
      K * (algebraMap ℂ B c * x) = (K * algebraMap ℂ B c) * x := by
        rw [← mul_assoc]
      _ = (algebraMap ℂ B c * K) * x := by
        rw [← Algebra.commutes]
      _ = algebraMap ℂ B c * (K * x) := by
        rw [mul_assoc]

/-- Right multiplication by an operator is a complex-linear self-map of the operator algebra. -/
def rightMulLinear (K : B) : OperatorLinearMap B where
  toFun x := x * K
  map_add' x y := by
    rw [add_mul]
  map_smul' c x := by
    change (c • x) * K = c • (x * K)
    simp only [Algebra.smul_def]
    rw [mul_assoc]

/-- The inner derivation/commutator by `K`, as a complex-linear superoperator. -/
def commutatorLinear (K : B) : OperatorLinearMap B :=
  leftMulLinear (B := B) K - rightMulLinear (B := B) K

@[simp] theorem leftMulLinear_apply (K x : B) :
    leftMulLinear (B := B) K x = K * x := rfl

@[simp] theorem rightMulLinear_apply (K x : B) :
    rightMulLinear (B := B) K x = x * K := rfl

@[simp] theorem commutatorLinear_apply (K x : B) :
    commutatorLinear (B := B) K x = K * x - x * K := rfl

@[simp] theorem leftMulLinear_one (K : B) :
    leftMulLinear (B := B) K 1 = K := by
  rw [leftMulLinear_apply, mul_one]

@[simp] theorem rightMulLinear_one (K : B) :
    rightMulLinear (B := B) K 1 = K := by
  rw [rightMulLinear_apply, one_mul]

/-- Applying a state/readout after a superoperator is ordinary `LinearMap.comp`. -/
theorem readout_comp_operator
    (ω : OperatorLinearFunctional B) (T : OperatorLinearMap B) (x : B) :
    ω (T x) = (ω.comp T) x := rfl

/-- Operator-first readout: `K` stays in the algebra, and scalars appear only after `ω`. -/
theorem commutator_readout
    (ω : OperatorLinearFunctional B) (K x : B) :
    ω (commutatorLinear (B := B) K x) = ω (K * x - x * K) := rfl

end ComplexOperatorLinearMaps

section AlgebraLinearContrast

variable {B : Type*} [Ring B]

/-- If a self-map is linear over the whole operator algebra, then it is determined by `T 1`.
This records why physical superoperators should usually be scalar-linear, not algebra-linear. -/
theorem algebra_linear_selfmap_determined_by_one (T : B →ₗ[B] B) (x : B) :
    T x = x * T 1 := by
  calc
    T x = T (x • (1 : B)) := by rw [smul_eq_mul, mul_one]
    _ = x • T 1 := by rw [map_smul]
    _ = x * T 1 := by rw [smul_eq_mul]

end AlgebraLinearContrast

end GoutevTonevPrinciple
