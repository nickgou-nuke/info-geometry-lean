import Mathlib

noncomputable section

open Matrix

variable {R : Type*} [CommRing R]

abbrev ImagePatch (R : Type*) :=
  Matrix (Fin 2) (Fin 2) R

section DeterminantInvariance

theorem det_mul_mul (g M h : ImagePatch R) :
    Matrix.det (g * M * h) = Matrix.det g * Matrix.det M * Matrix.det h := by
  rw [Matrix.det_mul, Matrix.det_mul]

theorem det_invariant_under_SL2_action
    (g M h : ImagePatch R)
    (hg : Matrix.det g = 1)
    (hh : Matrix.det h = 1) :
    Matrix.det (g * M * h) = Matrix.det M := by
  rw [det_mul_mul, hg, hh]
  ring

theorem det_invariant_under_conjugation
    (g gInv M : ImagePatch R)
    (hg : Matrix.det g = 1)
    (hgInv : Matrix.det gInv = 1) :
    Matrix.det (g * M * gInv) = Matrix.det M :=
  det_invariant_under_SL2_action g M gInv hg hgInv

theorem det_invariant_under_inverse_conjugation
    (g gInv M : ImagePatch R)
    (hleft : g * gInv = 1)
    (_hright : gInv * g = 1)
    (hg : Matrix.det g = 1) :
    Matrix.det (g * M * gInv) = Matrix.det M := by
  have hgInv : Matrix.det gInv = 1 := by
    have hdet := congrArg Matrix.det hleft
    rw [Matrix.det_mul, hg, Matrix.det_one, one_mul] at hdet
    exact hdet
  exact det_invariant_under_SL2_action g M gInv hg hgInv

end DeterminantInvariance

end
