/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# The Minkowski quadratic form and real soldering matrices

These are the original spacetime quadratic data and real Pauli matrices,
shared by the even Clifford algebra and the operatorial soldering owner.
The explicit noncommutativity witness uses the real matrix carrier itself.
-/

open scoped Matrix

namespace InfoGeometry.Clifford.Spacetime

/--
Standard Minkowski 4-vector space.
-/
@[rep_depth projective]
abbrev Vec13 := ℝ × (ℝ × ℝ × ℝ)

/-- The Minkowski quadratic form: Q(t, x, y, z) = t² - x² - y² - z². -/
@[rep_depth projective]
noncomputable def minkiQ : QuadraticForm ℝ Vec13 :=
  QuadraticMap.ofPolar (fun v => v.1^2 - v.2.1^2 - v.2.2.1^2 - v.2.2.2^2)
    (fun a v => by dsimp; ring)
    (fun x x' y => by dsimp [QuadraticMap.polar]; ring)
    (fun a x y => by dsimp [QuadraticMap.polar]; ring)

@[simp] lemma minkiQ_apply (t x y z : ℝ) :
    minkiQ (t, x, y, z) = t^2 - x^2 - y^2 - z^2 := rfl

/-- The algebra of 2x2 complex matrices.
In STA (Space-Time Algebra), Cl(1,3) is represented by M₂(ℍ).
Here we use M₂(ℂ) for the vector soldering (Weyl representation).
-/
abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Real Pauli Matrices (used for the (1,1) slice or split-signature soldering). -/
def sigma0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
def sigma1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def sigma2_i : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0] -- iσ₂
def sigma3 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The real soldering matrices do not commute: their `(0, 1)` product entries
are respectively `1` and `-1`. -/
theorem sigma3_mul_sigma1_ne : sigma3 * sigma1 ≠ sigma1 * sigma3 := by
  intro h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  norm_num [sigma3, sigma1, Matrix.mul_apply, Fin.sum_univ_two] at h01

end InfoGeometry.Clifford.Spacetime
