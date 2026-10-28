/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Canonical.QuaternionTwistorSphereReal

/-!
# A flat twistor-spinor equation with an intrinsically real Clifford action

On real Euclidean three-space, imaginary quaternions act on the real
quaternion module by left multiplication. The actual affine spinor field
`a + x · b` has a native Frechet derivative. Its Dirac contraction is `-3 b`,
so the flat twistor equation `∇ᵥ ψ + (1/3) v · Dψ = 0` follows.

This is a concrete family of flat solutions, not a classification of all
solutions or a curved conformal-spin connection. The square-minus-one
operators are real-linear and are tied to the existing quaternionic twistor
sphere; the scalar field is never extended.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealFlatTwistorSpinor

abbrev Space := Fin 3 → ℝ
abbrev Spinor := Quaternion ℝ

/-- The native real soldering into the imaginary quaternion subspace. -/
def imaginary : Space →ₗ[ℝ] Spinor where
  toFun x := ⟨0, x 0, x 1, x 2⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

theorem imaginary_injective : Function.Injective imaginary := by
  intro v w h
  funext i
  fin_cases i
  · exact congrArg (fun q : Spinor => q.imI) h
  · exact congrArg (fun q : Spinor => q.imJ) h
  · exact congrArg (fun q : Spinor => q.imK) h

/-- Real Clifford multiplication; an endomorphism, not a scalar readout. -/
def clifford (v : Space) : Module.End ℝ Spinor :=
  InfoGeometry.Canonical.QuaternionTwistorSphereReal.leftAction (imaginary v)

@[simp] theorem clifford_apply (v : Space) (s : Spinor) :
    clifford v s = imaginary v * s := rfl

theorem imaginary_clifford_relation (v w : Space) :
    imaginary v * imaginary w + imaginary w * imaginary v =
      (-2 * ∑ i, v i * w i) • (1 : Spinor) := by
  ext <;> simp [imaginary, Fin.sum_univ_succ] <;> ring

/-- The Clifford anticommutator acts on every real quaternion spinor. -/
theorem clifford_anticommutator (v w : Space) :
    clifford v * clifford w + clifford w * clifford v =
      (-2 * ∑ i, v i * w i) • (1 : Module.End ℝ Spinor) := by
  apply LinearMap.ext
  intro s
  change imaginary v * (imaginary w * s) + imaginary w * (imaginary v * s) = _
  rw [← mul_assoc, ← mul_assoc, ← add_mul, imaginary_clifford_relation]
  simp

def slope (b : Spinor) : Space →ₗ[ℝ] Spinor where
  toFun x := imaginary x * b
  map_add' x y := by simp [add_mul]
  map_smul' r x := by simp

def field (a b : Spinor) (x : Space) : Spinor := a + slope b x

theorem field_hasFDerivAt (a b : Spinor) (x : Space) :
    HasFDerivAt (field a b) (slope b).toContinuousLinearMap x := by
  exact (slope b).toContinuousLinearMap.hasFDerivAt.const_add a

theorem field_fderiv (a b : Spinor) (x : Space) :
    fderiv ℝ (field a b) x = (slope b).toContinuousLinearMap :=
  (field_hasFDerivAt a b x).fderiv

def frame (i : Fin 3) : Space := Pi.single i 1

theorem imaginary_frame_sq (i : Fin 3) :
    imaginary (frame i) * imaginary (frame i) = -(1 : Spinor) := by
  fin_cases i <;> ext <;> norm_num [imaginary, frame, Pi.single_apply,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Dirac uses the actual Frechet derivative and the coordinate frame for the
displayed Euclidean quadratic form. The finite Pi norm is used only for calculus. -/
def dirac (ψ : Space → Spinor) (x : Space) : Spinor :=
  ∑ i, imaginary (frame i) * (fderiv ℝ ψ x (frame i))

theorem dirac_field (a b : Spinor) (x : Space) :
    dirac (field a b) x = (-3 : ℝ) • b := by
  unfold dirac
  rw [field_fderiv]
  have h (i : Fin 3) :
      imaginary (frame i) * ((slope b).toContinuousLinearMap (frame i)) = -b := by
    change imaginary (frame i) * (imaginary (frame i) * b) = -b
    rw [← mul_assoc, imaginary_frame_sq]
    simp
  simp_rw [h]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  module

/-- A differential equation on the real spinor field, with no derivative witness. -/
theorem flat_twistor_equation (a b : Spinor) (x v : Space) :
    fderiv ℝ (field a b) x v + (1 / 3 : ℝ) • clifford v (dirac (field a b) x) = 0 := by
  rw [field_fderiv, dirac_field]
  change imaginary v * b + (1 / 3 : ℝ) • (imaginary v * ((-3 : ℝ) • b)) = 0
  simp [smul_smul]

theorem field_translation (a b : Spinor) (d x : Space) :
    field a b (x + d) = field (a + slope b d) b x := by
  simp [field, add_left_comm, add_comm]

open InfoGeometry.Canonical.QuaternionTwistorSphereReal in
/-- Explicit compatibility with the existing real quaternionic twistor sphere. -/
theorem sphere_action (p : Point) (s : Spinor) :
    clifford ![p.a, p.b, p.c] s = complexStructure p s := rfl

end InfoGeometry.Twistor.RealFlatTwistorSpinor
