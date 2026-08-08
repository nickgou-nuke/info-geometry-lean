import Mathlib

noncomputable section

open Matrix

variable {R : Type*} [CommRing R]

abbrev ImagePatch :=
  Matrix (Fin 2) (Fin 2) R

section DeterminantInvariance

theorem det_mul_mul (g M h : ImagePatch) :
    (g * M * h).det = g.det * M.det * h.det := by
  rw [Matrix.det_mul, Matrix.det_mul]
  ring

theorem det_invariant_under_SL2_action
    (g M h : ImagePatch)
    (hg : g.det = 1)
    (hh : h.det = 1) :
    (g * M * h).det = M.det := by
  rw [det_mul_mul, hg, hh]
  ring

theorem det_invariant_under_conjugation
    (g gInv M : ImagePatch)
    (hg : g.det = 1)
    (hgInv : gInv.det = 1) :
    (g * M * gInv).det = M.det :=
  det_invariant_under_SL2_action g M gInv hg hgInv

theorem det_invariant_under_inverse_conjugation
    (g gInv M : ImagePatch)
    (hleft : g * gInv = 1)
    (hright : gInv * g = 1)
    (hg : g.det = 1) :
    (g * M * gInv).det = M.det := by
  have hgInv : gInv.det = 1 := by
    have hdet := congrArg Matrix.det hleft
    rw [Matrix.det_mul, hg, Matrix.det_one, one_mul] at hdet
    exact hdet
  exact det_invariant_under_SL2_action g M gInv hg hgInv

end DeterminantInvariance

end
