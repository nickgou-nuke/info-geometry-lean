import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Canonical.SL2CZhukovsky

namespace InfoGeometry.Algebra.AiStudioNativeMathlibFindings

open Matrix
open InfoGeometry.Canonical.SL2CZhukovsky

/-! ## Zorn spectral packet -/

/-- AI Studio alias: Cayley-Hamilton for split Zorn matrices. -/
theorem zorn_cayley_hamilton {R : Type*} [CommRing R]
    (X : InfoGeometry.Algebra.ZornMatrix R) :
    X * X - (InfoGeometry.Algebra.ZornMatrix.zornTrace X) • X +
        (InfoGeometry.Algebra.ZornMatrix.zornNorm X) •
          (InfoGeometry.Algebra.ZornMatrix.I : InfoGeometry.Algebra.ZornMatrix R) = 0 :=
  InfoGeometry.Algebra.ZornMatrix.cayley_hamilton X

/-- AI Studio alias: Fredholm-style quadratic determinant expansion. -/
theorem zorn_fredholm_expansion {R : Type*} [CommRing R]
    (t : R) (X : InfoGeometry.Algebra.ZornMatrix R) :
    InfoGeometry.Algebra.ZornMatrix.zornNorm
        ((InfoGeometry.Algebra.ZornMatrix.I : InfoGeometry.Algebra.ZornMatrix R) - t • X) =
      1 - t * InfoGeometry.Algebra.ZornMatrix.zornTrace X + t ^ 2 *
        InfoGeometry.Algebra.ZornMatrix.zornNorm X :=
  InfoGeometry.Algebra.ZornMatrix.fredholm_expansion t X

/-! ## Native `2 × 2` square-zero shear packet -/

/-- The standard square-zero `2 × 2` shear generator. -/
def shearGenerator (R : Type*) [Zero R] [One R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 0, 0]

/-- The standard shear generator is square-zero. -/
theorem shearGenerator_sq_zero {R : Type*} [NonAssocSemiring R] :
    shearGenerator R * shearGenerator R = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearGenerator, Matrix.mul_apply, Fin.sum_univ_two]

/-- The native unipotent shear `I + tN`. -/
def unipotentShear (R : Type*) [CommRing R] (t : R) : Matrix (Fin 2) (Fin 2) R :=
  1 + t • shearGenerator R

/-- Coordinate form of the native unipotent shear. -/
theorem unipotentShear_apply {R : Type*} [CommRing R] (t : R) :
    unipotentShear R t = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentShear, shearGenerator]

/-- Additive composition law for native unipotent shears. -/
theorem unipotentShear_mul {R : Type*} [CommRing R] (s t : R) :
    unipotentShear R s * unipotentShear R t = unipotentShear R (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentShear_apply, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The native unipotent shear has determinant one. -/
theorem det_unipotentShear {R : Type*} [CommRing R] (t : R) :
    (unipotentShear R t).det = 1 := by
  rw [unipotentShear_apply]
  simp

/-- Packet bundling the square-zero, additive-flow, and determinant laws. -/
theorem native_unipotent_shear_packet {R : Type*} [CommRing R] (s t : R) :
    shearGenerator R * shearGenerator R = 0 ∧
      unipotentShear R s * unipotentShear R t = unipotentShear R (s + t) ∧
      (unipotentShear R t).det = 1 := by
  exact ⟨shearGenerator_sq_zero, unipotentShear_mul s t, det_unipotentShear t⟩

/-! ## Native `2 × 2` characteristic-polynomial packet -/

/-- Native mathlib characteristic-polynomial formula for a `2 × 2` complex matrix. -/
theorem native_charPoly2x2_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    charPoly2x2 M x = x ^ 2 - Matrix.trace M * x + det2x2 M := by
  simpa using charPoly2x2_eq M x

/-- Determinant-one specialization of the native `2 × 2` characteristic polynomial. -/
theorem native_char_poly_eq_zhukovsky (M : Matrix (Fin 2) (Fin 2) ℂ) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : det2x2 M = 1) :
    charPoly2x2 M x = x ^ 2 - Tr * x + 1 := by
  simpa [h_tr, h_det] using
    (char_poly_eq_zhukovsky M x Tr h_tr h_det)

end InfoGeometry.Algebra.AiStudioNativeMathlibFindings
