import Mathlib

/-!
# Finite complex Hermitian decomposition

This owner supplies the native `3 × 3` matrix layer needed before any
structure-preserving comparison with a real Albert carrier.  It makes no
identification between complex Hermitian matrices and `H3Zorn ℝ`.
-/

namespace InfoGeometry.Exceptional.ComplexMatrix

noncomputable section

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

def Hermitian3 := {M : Mat3 // Matrix.conjTranspose M = M}

def AntiHermitian3 := {M : Mat3 // Matrix.conjTranspose M = -M}

def hermitianPart (M : Mat3) : Hermitian3 :=
  ⟨(1 / 2 : ℂ) • (M + Matrix.conjTranspose M), by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    norm_num
    module
⟩

def antiHermitianPart (M : Mat3) : AntiHermitian3 :=
  ⟨(1 / 2 : ℂ) • (M - Matrix.conjTranspose M), by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    norm_num
    module
⟩

theorem hermitianPart_add_antiHermitianPart (M : Mat3) :
    (hermitianPart M).1 + (antiHermitianPart M).1 = M := by
  rw [hermitianPart, antiHermitianPart]
  ext i j
  change (1 / 2 : ℂ) * (M i j + star (M j i)) +
      (1 / 2 : ℂ) * (M i j - star (M j i)) = M i j
  ring

theorem hermitianPart_conjTranspose (M : Mat3) :
    (hermitianPart (Matrix.conjTranspose M)).1 = (hermitianPart M).1 := by
  simp [hermitianPart]
  module

theorem antiHermitianPart_conjTranspose (M : Mat3) :
    (antiHermitianPart (Matrix.conjTranspose M)).1 = -(antiHermitianPart M).1 := by
  simp [antiHermitianPart]
  module

end
end InfoGeometry.Exceptional.ComplexMatrix
