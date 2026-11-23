/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.RealPauliPfaffianKernel
import InfoGeometry.Physics.LorentzBoostMinkowski
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Faithful real Dirac vectors and their Lorentz spin generators

The linear lift below wraps the existing `RealPauliPfaffianKernel.diracVector`.
Its Clifford square has signature `(-+++)`, whereas the reused Minkowski
pairing has timelike sign positive. Thus its Jordan polarization is
`D(u) D(v) + D(v) D(u) = -2 η(u,v) I`.

The null conclusion is square-zero of the Dirac operator and inclusion of
its image in its kernel. It asserts no isotropy for an unspecified spinor
bilinear form and no square-zero property for the Hermitian Pauli matrix.

The existing Pauli phase supplies the real Clifford volume. For spatial
coordinates `a`, the rotation and boost operators are
`J(a) = -Ω X(0,a)/2` and `K(a) = X(0,a)/2`. Their full bracket laws use
Mathlib's cross product. Casimir values are stated for these real,
skew-symmetric rotation generators, so the rotational value is `-3/4`.
These are finite matrix identities, without a Lie group classification or
an identification of the Lorentz real form with two compact real factors.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealDiracLorentzBridge

open scoped Matrix BigOperators
open InfoGeometry.Canonical.RealPauliPfaffianKernel
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge

abbrev Vector4 := InfoGeometry.Algebra.FiniteSpin.Vec4R
abbrev Vector3 := InfoGeometry.Algebra.FiniteSpin.Vec3R

/-- Coordinate adapter to the existing real Minkowski-pairing owner. -/
def toFourVector (v : Vector4) :
    InfoGeometry.Physics.LorentzBoostMinkowski.FourVector :=
  ⟨v 0, v 1, v 2, v 3⟩

/-- The existing `(+---)` pairing, on the function-space vector carrier. -/
def lorentzPair (u v : Vector4) : ℝ :=
  InfoGeometry.Physics.LorentzBoostMinkowski.minkowskiPair
    (toFourVector u) (toFourVector v)

theorem lorentzPair_self_eq_interval (v : Vector4) :
    lorentzPair v v = intervalSq (v 0) (v 1) (v 2) (v 3) := by
  simp [lorentzPair, toFourVector,
    InfoGeometry.Physics.LorentzBoostMinkowski.minkowskiPair, intervalSq, pow_two]

/-- Linear packaging of the previously constructed real Dirac vector. -/
def diracLift : Vector4 →ₗ[ℝ] Matrix4 where
  toFun v := diracVector (v 0) (v 1) (v 2) (v 3)
  map_add' u v := by
    simp only [diracVector, pauli_explicit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [timeGamma, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  map_smul' c v := by
    simp only [diracVector, pauli_explicit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [timeGamma, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem diracLift_explicit (v : Vector4) :
    diracLift v =
      !![-v 1, v 2, v 0 + v 3, 0;
         v 2, v 1, 0, -v 0 - v 3;
         -v 0 + v 3, 0, v 1, v 2;
         0, v 0 - v 3, v 2, -v 1] := by
  change diracVector (v 0) (v 1) (v 2) (v 3) = _
  simp only [diracVector, pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [timeGamma, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem diracLift_injective : Function.Injective diracLift := by
  intro u v h
  have h00 := congrArg (fun M : Matrix4 => M 0 0) h
  have h01 := congrArg (fun M : Matrix4 => M 0 1) h
  have h02 := congrArg (fun M : Matrix4 => M 0 2) h
  have h20 := congrArg (fun M : Matrix4 => M 2 0) h
  simp only [diracLift_explicit] at h00 h01 h02 h20
  simp at h00 h01 h02 h20
  funext i
  fin_cases i
  · change u 0 = v 0
    linarith
  · change u 1 = v 1
    exact h00
  · change u 2 = v 2
    exact h01
  · change u 3 = v 3
    linarith

theorem diracLift_sq (v : Vector4) :
    diracLift v * diracLift v = (-lorentzPair v v) • (1 : Matrix4) := by
  change diracVector (v 0) (v 1) (v 2) (v 3) *
    diracVector (v 0) (v 1) (v 2) (v 3) = _
  rw [lorentzPair_self_eq_interval]
  exact diracVector_sq (v 0) (v 1) (v 2) (v 3)

/-- Clifford polarization, derived from the existing square and linearity. -/
theorem diracLift_anticommutator (u v : Vector4) :
    diracLift u * diracLift v + diracLift v * diracLift u =
      (-2 * lorentzPair u v) • (1 : Matrix4) := by
  have hpolar : lorentzPair (u + v) (u + v) =
      lorentzPair u u + lorentzPair v v + 2 * lorentzPair u v := by
    simp [lorentzPair, toFourVector,
      InfoGeometry.Physics.LorentzBoostMinkowski.minkowskiPair]
    ring
  calc
    diracLift u * diracLift v + diracLift v * diracLift u =
        diracLift (u + v) * diracLift (u + v) -
          diracLift u * diracLift u - diracLift v * diracLift v := by
      simp only [map_add]
      noncomm_ring
    _ = (-lorentzPair (u + v) (u + v)) • (1 : Matrix4) -
          (-lorentzPair u u) • (1 : Matrix4) -
          (-lorentzPair v v) • (1 : Matrix4) := by
      rw [diracLift_sq, diracLift_sq, diracLift_sq]
    _ = (-2 * lorentzPair u v) • (1 : Matrix4) := by
      rw [hpolar]
      module

/-- This includes the zero vector; injectivity distinguishes nonzero null data. -/
theorem diracLift_sq_zero_iff (v : Vector4) :
    diracLift v * diracLift v = 0 ↔ lorentzPair v v = 0 := by
  rw [diracLift_sq]
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix4 => M 0 0) h
    simpa using h00
  · intro h
    simp [h]

/-- The trace product recovers the Minkowski pairing with the real dimension. -/
theorem diracLift_trace_product (u v : Vector4) :
    Matrix.trace (diracLift u * diracLift v) = -4 * lorentzPair u v := by
  have h := congrArg Matrix.trace (diracLift_anticommutator u v)
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Matrix.trace_mul_comm (diracLift v) (diracLift u)] at h
  norm_num at h
  linarith

/-- The same matrix as an endomorphism of the real spinor coordinate space. -/
def diracOperator (v : Vector4) : Module.End ℝ Vector4 :=
  Matrix.toLin' (diracLift v)

/-- A null Dirac operator maps its image into its kernel. -/
theorem diracOperator_range_le_ker (v : Vector4) (h : lorentzPair v v = 0) :
    LinearMap.range (diracOperator v) ≤ LinearMap.ker (diracOperator v) := by
  rw [LinearMap.range_le_ker_iff]
  unfold diracOperator
  rw [← Matrix.toLin'_mul, (diracLift_sq_zero_iff v).2 h, map_zero]

/-- The traceless spatial part of the existing real Pauli representative. -/
def spatialPauli (a : Vector3) : Matrix4 := pauli 0 (a 0) (a 1) (a 2)

/-- Real skew-symmetric infinitesimal rotations. -/
def rotation (a : Vector3) : Matrix4 :=
  (-1 / 2 : ℝ) • (realPhaseAxis * spatialPauli a)

/-- Real symmetric infinitesimal boosts on the same spinor carrier. -/
def boost (a : Vector3) : Matrix4 := (1 / 2 : ℝ) • spatialPauli a

theorem rotation_explicit (a : Vector3) :
    rotation a = (1 / 2 : ℝ) •
      !![0, a 2, -a 1, a 0;
         -a 2, 0, -a 0, -a 1;
         a 1, a 0, 0, -a 2;
         -a 0, a 1, a 2, 0] := by
  simp only [rotation, spatialPauli, pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realPhaseAxis] <;> ring

theorem boost_explicit (a : Vector3) :
    boost a = (1 / 2 : ℝ) •
      !![a 2, 0, a 0, a 1;
         0, a 2, -a 1, a 0;
         a 0, -a 1, -a 2, 0;
         a 1, a 0, 0, -a 2] := by
  simp [boost, spatialPauli, pauli_explicit]

/-- Boosts are the timelike-spacelike bivectors of the existing Dirac lift. -/
theorem boost_eq_timeGamma_mul_dirac (a : Vector3) :
    boost a = (1 / 2 : ℝ) •
      (timeGamma * diracLift ![0, a 0, a 1, a 2]) := by
  simp only [boost_explicit, diracLift_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [timeGamma]

theorem phase_mul_boost (a : Vector3) :
    realPhaseAxis * boost a = -rotation a := by
  simp only [boost_explicit, rotation_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realPhaseAxis, Matrix.mul_apply, Fin.sum_univ_four]

theorem phase_mul_rotation (a : Vector3) :
    realPhaseAxis * rotation a = boost a := by
  simp only [boost_explicit, rotation_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realPhaseAxis, Matrix.mul_apply, Fin.sum_univ_four]

theorem rotation_transpose (a : Vector3) :
    (rotation a).transpose = -rotation a := by
  simp only [rotation_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem boost_transpose (a : Vector3) : (boost a).transpose = boost a := by
  simp only [boost_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- All rotation brackets, expressed by the native three-dimensional cross product. -/
theorem rotation_comm_rotation (a b : Vector3) :
    rotation a * rotation b - rotation b * rotation a = rotation (a ⨯₃ b) := by
  simp only [rotation_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cross_apply] <;> ring

theorem rotation_comm_boost (a b : Vector3) :
    rotation a * boost b - boost b * rotation a = boost (a ⨯₃ b) := by
  simp only [rotation_explicit, boost_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cross_apply] <;> ring

theorem boost_comm_boost (a b : Vector3) :
    boost a * boost b - boost b * boost a = -rotation (a ⨯₃ b) := by
  simp only [rotation_explicit, boost_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cross_apply] <;> ring

/-- The three standard rotation axes, with indices `0,1,2`. -/
def rotationAxis (i : Fin 3) : Matrix4 := rotation (Pi.single i 1)

def boostAxis (i : Fin 3) : Matrix4 := boost (Pi.single i 1)

theorem rotationAxis_commutators :
    (rotationAxis 0 * rotationAxis 1 - rotationAxis 1 * rotationAxis 0 = rotationAxis 2) ∧
    (rotationAxis 1 * rotationAxis 2 - rotationAxis 2 * rotationAxis 1 = rotationAxis 0) ∧
    (rotationAxis 2 * rotationAxis 0 - rotationAxis 0 * rotationAxis 2 = rotationAxis 1) := by
  constructor
  · simpa [rotationAxis, rotation, spatialPauli, cross_apply] using
      rotation_comm_rotation (Pi.single 0 1) (Pi.single 1 1)
  constructor
  · simpa [rotationAxis, rotation, spatialPauli, cross_apply] using
      rotation_comm_rotation (Pi.single 1 1) (Pi.single 2 1)
  · simpa [rotationAxis, rotation, spatialPauli, cross_apply] using
      rotation_comm_rotation (Pi.single 2 1) (Pi.single 0 1)

theorem rotationAxis_noncommute :
    rotationAxis 0 * rotationAxis 1 ≠ rotationAxis 1 * rotationAxis 0 := by
  intro h
  have hz : rotationAxis 2 = 0 := by
    rw [← rotationAxis_commutators.1, h, sub_self]
  have h01 := congrArg (fun M : Matrix4 => M 0 1) hz
  norm_num [rotationAxis, rotation_explicit] at h01

theorem rotationAxis_sq (i : Fin 3) :
    rotationAxis i * rotationAxis i = (-1 / 4 : ℝ) • (1 : Matrix4) := by
  fin_cases i <;> simp only [rotationAxis, rotation_explicit] <;>
    ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [Pi.single_apply, Matrix.mul_apply, Fin.sum_univ_four]

theorem boostAxis_sq (i : Fin 3) :
    boostAxis i * boostAxis i = (1 / 4 : ℝ) • (1 : Matrix4) := by
  fin_cases i <;> simp only [boostAxis, boost_explicit] <;>
    ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [Pi.single_apply, Matrix.mul_apply, Fin.sum_univ_four]

theorem rotationAxis_mul_boostAxis (i : Fin 3) :
    rotationAxis i * boostAxis i = (-1 / 4 : ℝ) • realPhaseAxis := by
  fin_cases i <;> simp only [rotationAxis, boostAxis, rotation_explicit, boost_explicit] <;>
    ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [Pi.single_apply, realPhaseAxis, Matrix.mul_apply, Fin.sum_univ_four]

theorem rotation_casimir :
    (∑ i : Fin 3, rotationAxis i * rotationAxis i) =
      (-3 / 4 : ℝ) • (1 : Matrix4) := by
  simp only [rotationAxis_sq, Fin.sum_univ_three]
  module

theorem boost_casimir :
    (∑ i : Fin 3, boostAxis i * boostAxis i) =
      (3 / 4 : ℝ) • (1 : Matrix4) := by
  simp only [boostAxis_sq, Fin.sum_univ_three]
  module

theorem lorentz_casimir :
    (∑ i : Fin 3, rotationAxis i * rotationAxis i) -
        (∑ i : Fin 3, boostAxis i * boostAxis i) =
      (-3 / 2 : ℝ) • (1 : Matrix4) := by
  rw [rotation_casimir, boost_casimir]
  module

/-- The second quadratic readout has a negative volume coefficient. -/
theorem mixed_casimir :
    (∑ i : Fin 3, rotationAxis i * boostAxis i) =
      (-3 / 4 : ℝ) • realPhaseAxis := by
  simp only [rotationAxis_mul_boostAxis, Fin.sum_univ_three]
  module

end InfoGeometry.Canonical.RealDiracLorentzBridge

end
