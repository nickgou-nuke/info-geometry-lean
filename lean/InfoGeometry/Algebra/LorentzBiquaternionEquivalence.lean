import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Physics.MD001MatrixQuantumGeometry
import InfoGeometry.Physics.Section34StrengthenedFormalism

/-!
# Finite Lorentz / biquaternion equivalence packet

This file keeps only an exact finite slice of the Lorentz/biquaternion story:

* Hermitian `2 × 2` Pauli matrices encode spacetime points and their determinant
  reads out the Minkowski quadratic form;
* an exact determinant-one real `2 × 2` matrix provides a theorem-safe
  double-sided transport lane preserving that determinant;
* the central sign `-I` acts trivially on that transport;
* the source-compatible biquaternion basis table `i ↦ Iσ₂`, `j ↦ Iσ₁`,
  `k ↦ Iσ₃` is imported from the repaired Section 34 owner.

This does not claim the full Lie-group theorem `Spin(1,3) ≃ SL(2,ℂ)` or a global
classification of Lorentz/biquaternion equivalence.
-/

noncomputable section

namespace InfoGeometry.Algebra.LorentzBiquaternionEquivalence

open Matrix Complex
open InfoGeometry.Physics.MD001MatrixQuantumGeometry
open InfoGeometry.Physics.Section34StrengthenedFormalism
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Hermitian Pauli readout of a spacetime point. -/
def hermitianSpacetimePoint (t x y z : ℂ) : Mat2 :=
  pauliSpacetimeMatrix t x y z

/-- Exact determinant-one real matrix used for the finite transport lane. -/
def exactBoostQ : Mat2 :=
  !![(2 : ℂ), 1; 1, 1]

/-- The exact transport lane acts by double-sided multiplication. -/
def exactBoostTransport (X : Mat2) : Mat2 :=
  exactBoostQ * X * exactBoostQ

/-- The Pauli/Hermitian determinant is the Minkowski quadratic form. -/
theorem hermitianSpacetimePoint_det (t x y z : ℂ) :
    Matrix.det (hermitianSpacetimePoint t x y z) =
      t * t - (x * x + y * y + z * z) :=
  pauliSpacetimeMatrix_det t x y z

/-- The exact transport matrix has determinant `1`. -/
theorem exactBoostQ_det : Matrix.det exactBoostQ = 1 := by
  simp [exactBoostQ, Matrix.det_fin_two]
  ring

/-- Exact double-sided transport preserves the determinant. -/
theorem exactBoostTransport_det (X : Mat2) :
    Matrix.det (exactBoostTransport X) = Matrix.det X := by
  simp [exactBoostTransport, Matrix.det_mul, exactBoostQ_det, mul_assoc]

/-- The exact transport preserves the Minkowski determinant readout on Pauli spacetime points. -/
theorem exactBoostTransport_preserves_spacetime_det (t x y z : ℂ) :
    Matrix.det (exactBoostTransport (hermitianSpacetimePoint t x y z)) =
      t * t - (x * x + y * y + z * z) := by
  rw [exactBoostTransport_det, hermitianSpacetimePoint_det]

/-- The central sign `-I` acts trivially on double-sided transport. -/
theorem central_sign_transport_trivial (X : Mat2) :
    ((-1 : ℂ) • (1 : Mat2)) * X * ((-1 : ℂ) • (1 : Mat2)) = X := by
  simp

/-- Imported finite biquaternion table from Section 34. -/
theorem source_biquaternion_table :
    bqI * bqI = -1 ∧
    bqJ * bqJ = -1 ∧
    bqK * bqK = -1 ∧
    bqI * bqJ = bqK ∧
    bqJ * bqK = bqI ∧
    bqK * bqI = bqJ := by
  exact ⟨bqI_sq, bqJ_sq, bqK_sq, bqI_mul_bqJ, bqJ_mul_bqK, bqK_mul_bqI⟩

/-- Finite Lorentz/biquaternion packet: determinant readout, transport invariance, and sign kernel. -/
theorem finite_lorentz_biquaternion_packet (t x y z : ℂ) :
    Matrix.det (hermitianSpacetimePoint t x y z) =
      t * t - (x * x + y * y + z * z) ∧
    Matrix.det (exactBoostTransport (hermitianSpacetimePoint t x y z)) =
      t * t - (x * x + y * y + z * z) ∧
    ((-1 : ℂ) • (1 : Mat2)) * hermitianSpacetimePoint t x y z * ((-1 : ℂ) • (1 : Mat2)) =
      hermitianSpacetimePoint t x y z := by
  exact ⟨hermitianSpacetimePoint_det t x y z,
    exactBoostTransport_preserves_spacetime_det t x y z,
    central_sign_transport_trivial (hermitianSpacetimePoint t x y z)⟩

end InfoGeometry.Algebra.LorentzBiquaternionEquivalence

end noncomputable section
