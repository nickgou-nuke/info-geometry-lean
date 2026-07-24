import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace InfoGeometry.Projective.MobiusDual

open scoped Matrix

variable {R : Type*} [CommRing R]

abbrev ProjectivePoint (R : Type*) [CommRing R] := Matrix (Fin 2) (Fin 1) R
abbrev ProjectiveLine (R : Type*) [CommRing R] := Matrix (Fin 1) (Fin 2) R

structure SL2 (R : Type*) [CommRing R] where
  M : Matrix (Fin 2) (Fin 2) R
  det_one : M.det = 1

def contragredient (A : SL2 R) : Matrix (Fin 2) (Fin 2) R :=
  !![A.M 1 1, -A.M 0 1; -A.M 1 0, A.M 0 0]

def pairing (η : ProjectiveLine R) (θ : ProjectivePoint R) : R :=
  η 0 0 * θ 0 0 + η 0 1 * θ 1 0

def actPoint (A : SL2 R) (θ : ProjectivePoint R) : ProjectivePoint R :=
  !![A.M 0 0 * θ 0 0 + A.M 0 1 * θ 1 0;
    A.M 1 0 * θ 0 0 + A.M 1 1 * θ 1 0]

def actLine (A : SL2 R) (η : ProjectiveLine R) : ProjectiveLine R :=
  !![η 0 0 * A.M 1 1 - η 0 1 * A.M 1 0,
    -η 0 0 * A.M 0 1 + η 0 1 * A.M 0 0]

theorem contragredient_pairing_invariant (A : SL2 R) (η : ProjectiveLine R) (θ : ProjectivePoint R) :
    pairing (actLine A η) (actPoint A θ) = pairing η θ := by
  rcases A with ⟨M, hdet⟩
  have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  calc
    pairing (actLine ⟨M, hdet⟩ η) (actPoint ⟨M, hdet⟩ θ)
        = η 0 0 * θ 0 0 * (M 0 0 * M 1 1 - M 0 1 * M 1 0)
          + η 0 1 * θ 1 0 * (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
            simp [pairing, actPoint, actLine]
            ring
    _ = η 0 0 * θ 0 0 * 1 + η 0 1 * θ 1 0 * 1 := by rw [hdet']
    _ = pairing η θ := by simp [pairing]

end InfoGeometry.Projective.MobiusDual
