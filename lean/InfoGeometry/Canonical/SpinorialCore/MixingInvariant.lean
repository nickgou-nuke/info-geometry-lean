import Mathlib

/-!
# Rephasing-invariant quartets in finite unitary matrices

Two-dimensional vanishing follows from row orthogonality, not Artin's theorem.
Three dimensions admit both zero and nonzero invariants; no generation count
or identification with an octonionic associator is postulated.
-/

noncomputable section
namespace InfoGeometry.Canonical.SpinorialCore.Mixing
open Matrix

/-- Imaginary part of the standard four-entry rephasing invariant. -/
def quartet (a b c d : ℂ) : ℝ := (a * d * star b * star c).im

theorem quartet_zero_of_row_orthogonality (a b c d : ℂ)
    (h : a * star c + b * star d = 0) : quartet a b c d = 0 := by
  have hx : a * star c = -(b * star d) := eq_neg_iff_add_eq_zero.mpr h
  unfold quartet
  calc
    (a * d * star b * star c).im = ((a * star c) * star (b * star d)).im := by
      congr 1
      simp only [star_mul, star_star]
      ring
    _ = (-(b * star d) * star (b * star d)).im := by rw [hx]
    _ = 0 := by simp [Complex.mul_im]; ring

theorem two_flavor_quartet_zero (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U * U.conjTranspose = 1) : quartet (U 0 0) (U 0 1) (U 1 0) (U 1 1) = 0 := by
  apply quartet_zero_of_row_orthogonality
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hU
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using h

/-- Independent unit phases on both rows and columns leave the quartet unchanged. -/
theorem quartet_rephasing (a b c d r s u v : ℂ)
    (hr : star r * r = 1) (hs : star s * s = 1)
    (hu : star u * u = 1) (hv : star v * v = 1) :
    quartet (r * a * u) (r * b * v) (s * c * u) (s * d * v) = quartet a b c d := by
  unfold quartet
  congr 1
  simp only [star_mul]
  calc
    r * a * u * (s * d * v) * (star v * (star b * star r)) *
        (star u * (star c * star s)) =
      (star r * r) * (star s * s) * (star u * u) * (star v * v) *
        (a * d * star b * star c) := by ring
    _ = a * d * star b * star c := by rw [hr, hs, hu, hv]; simp

/-- An exact unitary witness with rational real and imaginary entries. -/
def threeFlavorWitness : Matrix (Fin 3) (Fin 3) ℂ :=
  !![9 / 25, 12 / 25, -(4 / 5) * Complex.I;
     -(12 / 25) - (48 / 125) * Complex.I, 9 / 25 - (64 / 125) * Complex.I, 12 / 25;
     16 / 25 - (36 / 125) * Complex.I, -(12 / 25) - (48 / 125) * Complex.I, 9 / 25]

theorem threeFlavorWitness_unitary :
    threeFlavorWitness * threeFlavorWitness.conjTranspose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [threeFlavorWitness, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

theorem threeFlavorWitness_quartet :
    quartet (threeFlavorWitness 0 0) (threeFlavorWitness 0 1)
      (threeFlavorWitness 1 0) (threeFlavorWitness 1 1) = 5184 / 78125 := by
  norm_num [quartet, threeFlavorWitness, Complex.mul_re, Complex.mul_im]

theorem three_flavors_allow_nonzero :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, U * U.conjTranspose = 1 ∧
      quartet (U 0 0) (U 0 1) (U 1 0) (U 1 1) ≠ 0 := by
  refine ⟨threeFlavorWitness, threeFlavorWitness_unitary, ?_⟩
  rw [threeFlavorWitness_quartet]
  norm_num

theorem three_flavors_allow_zero :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, U * U.conjTranspose = 1 ∧
      quartet (U 0 0) (U 0 1) (U 1 0) (U 1 1) = 0 := by
  refine ⟨1, by simp, ?_⟩
  norm_num [quartet]

end InfoGeometry.Canonical.SpinorialCore.Mixing
