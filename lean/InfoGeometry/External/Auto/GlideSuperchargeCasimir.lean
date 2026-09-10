import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Glide square, supercharge square, and Casimir energy-momentum

Yes: the relation is about square roots of translation generators and their
Casimirs.

* a nonsymmorphic momentum glide squares to a full reciprocal translation;
* a supercharge squares to the Hamiltonian/translation generator;
* the energy-momentum Casimir is the invariant `E²-|p|²`;
* at the nilpotent boundary, the square/translation/Casimir collapses to zero.
-/

noncomputable section

namespace GlideSuperchargeCasimir

open Matrix

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev Vec3 := Fin 3 → ℂ

/-! ## Momentum glide square -/

/-- Momentum-space glide with half reciprocal shift `h`. -/
def kGlide (h : ℂ) (k : ℂ × ℂ) : ℂ × ℂ := (-k.1, k.2 + h)

/-- Full reciprocal translation in the glide direction. -/
def recipTranslate (H : ℂ) (k : ℂ × ℂ) : ℂ × ℂ := (k.1, k.2 + H)

/-- The glide squared is a full reciprocal translation. -/
theorem kGlide_sq (h : ℂ) (k : ℂ × ℂ) :
    kGlide h (kGlide h k) = recipTranslate (2 * h) k := by
  cases k with
  | mk kx ky =>
    simp [kGlide, recipTranslate]
    ring

/-! ## Supercharge square -/

/-- Minimal bulk supercharge. -/
def Q : M2C := !![0, 1; 1, 0]

/-- Hamiltonian/translation atom. -/
def H : M2C := 1

/-- Boundary nilpotent supercharge. -/
def qNil : M2C := !![0, 1; 0, 0]

/-- Bulk supercharge squares to Hamiltonian. -/
theorem Q_sq : Q * Q = H := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Q, H, Matrix.mul_apply, Fin.sum_univ_two]

/-- `{Q,Q}=2H`. -/
theorem Q_anticomm : Q * Q + Q * Q = (2 : ℂ) • H := by
  rw [Q_sq]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [H] <;> norm_num

/-- Boundary nilpotent square collapses to zero Hamiltonian. -/
theorem qNil_sq_zero : qNil * qNil = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [qNil, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Casimir / mass shell -/

/-- Dot product on three-momentum. -/
def dot3 (p q : Vec3) : ℂ := ∑ i : Fin 3, p i * q i

/-- Energy-momentum quadratic Casimir. -/
def momentumCasimir (E : ℂ) (p : Vec3) : ℂ := E^2 - dot3 p p

/-- Fixed-line momentum `(px,0,0)`. -/
def fixedMomentum (px : ℂ) : Vec3
  | 0 => px
  | 1 => 0
  | 2 => 0

/-- On the Klein fixed line, the Casimir is `E²-px²`. -/
theorem fixedLine_casimir (E px : ℂ) :
    momentumCasimir E (fixedMomentum px) = E^2 - px^2 := by
  simp [momentumCasimir, fixedMomentum, dot3, Fin.sum_univ_three]
  ring

/-- Synthesis theorem. -/
theorem glide_supercharge_casimir_synthesis :
    (∀ h : ℂ, ∀ k : ℂ × ℂ, kGlide h (kGlide h k) = recipTranslate (2*h) k) ∧
    Q * Q = H ∧
    Q * Q + Q * Q = (2 : ℂ) • H ∧
    qNil * qNil = 0 ∧
    (∀ E px : ℂ, momentumCasimir E (fixedMomentum px) = E^2 - px^2) := by
  exact ⟨kGlide_sq, Q_sq, Q_anticomm, qNil_sq_zero, fixedLine_casimir⟩

#check kGlide_sq
#check Q_sq
#check qNil_sq_zero
#check fixedLine_casimir
#check glide_supercharge_casimir_synthesis

end GlideSuperchargeCasimir
