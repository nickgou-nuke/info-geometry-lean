import Mathlib.Tactic

/-!
# Fourier--Mellin Dirac zero modes as biquaternion resolvent poles

This module seals the algebraic part of the claimed bridge:

* the Fourier--Mellin Dirac-Hodge operator factors as
  `D_FM = -σ₃ (sI-X)` in `DiracFourierMellin`;
* the determinant of the resolvent core is the lightcone polynomial
  `s²-kx²-ky²`;
* the determinant of `D_FM` differs only by the nonzero determinant of
  `-σ₃`, hence it has the same zero locus;
* at zero boundary momentum the scale pole is exactly `s=0`;
* this matches the zero-mode pole of the tripotent determinant
  `s(s-1)(s+1)`.
-/

noncomputable section

namespace DiracResolventZeroModeTripotent

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ

/-- The Fourier--Mellin transformed Dirac operator. -/
def D_FM (s kx ky : ℂ) : M2C :=
  !![-s, Complex.I * kx + ky; Complex.I * kx - ky, s]

/-- The radial Pauli matrix σ₃. -/
def sigma3 : M2C := !![1, 0; 0, -1]

/-- The biquaternion resolvent core `sI-X`, with `X=ky σ₁-kx σ₂`. -/
def sI_minus_X (s kx ky : ℂ) : M2C :=
  !![s, -Complex.I * kx - ky; Complex.I * kx - ky, s]

/-- Exact Dirac/resolvent factorization. -/
theorem dirac_factors_resolvent (s kx ky : ℂ) :
    D_FM s kx ky = -sigma3 * sI_minus_X s kx ky := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [D_FM, sigma3, sI_minus_X, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Determinant of the biquaternion scale-resolvent core. -/
theorem det_sI_minus_X (s kx ky : ℂ) :
    (sI_minus_X s kx ky).det = s^2 - kx^2 - ky^2 := by
  have hI : Complex.I * Complex.I = -1 := by simpa [pow_two] using Complex.I_sq
  simp [sI_minus_X, Matrix.det_fin_two]
  calc
    s * s - (-(Complex.I * kx) - ky) * (Complex.I * kx - ky)
        = s^2 - ((-(Complex.I * Complex.I)) * kx^2 + ky^2) := by ring_nf
    _ = s^2 - ((-(-1 : ℂ)) * kx^2 + ky^2) := by rw [hI]
    _ = s^2 - kx^2 - ky^2 := by ring

/-- Determinant of the Fourier--Mellin Dirac operator. -/
theorem det_D_FM (s kx ky : ℂ) :
    (D_FM s kx ky).det = -(s^2 - kx^2 - ky^2) := by
  have hI : Complex.I * Complex.I = -1 := by simpa [pow_two] using Complex.I_sq
  simp [D_FM, Matrix.det_fin_two]
  calc
    -(s * s) - (Complex.I * kx + ky) * (Complex.I * kx - ky)
        = -s^2 - ((Complex.I * Complex.I) * kx^2 - ky^2) := by ring_nf
    _ = -s^2 - ((-1 : ℂ) * kx^2 - ky^2) := by rw [hI]
    _ = -s^2 + kx^2 + ky^2 := by ring
    _ = ky^2 - (s^2 - kx^2) := by ring

/-- The Dirac determinant and resolvent determinant have the same zero locus. -/
theorem dirac_zero_iff_resolvent_singular (s kx ky : ℂ) :
    (D_FM s kx ky).det = 0 ↔ (sI_minus_X s kx ky).det = 0 := by
  rw [det_D_FM, det_sI_minus_X]
  constructor <;> intro h
  · exact neg_eq_zero.mp h
  · exact neg_eq_zero.mpr h

/-- At zero boundary momentum, singularity is equivalent to `s²=0`. -/
theorem zero_momentum_resolvent_pole (s : ℂ) :
    (sI_minus_X s 0 0).det = 0 ↔ s^2 = 0 := by
  rw [det_sI_minus_X]
  ring_nf

/-- Over the complex numbers, the zero-momentum scale pole is exactly `s=0`. -/
theorem zero_momentum_scale_zero (s : ℂ) :
    (sI_minus_X s 0 0).det = 0 ↔ s = 0 := by
  rw [zero_momentum_resolvent_pole]
  constructor
  · intro h
    exact sq_eq_zero_iff.mp h
  · intro h
    rw [h]
    norm_num

/-- Tripotent boundary scale operator with poles `+1,-1,0`. -/
def Trip : M3C := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- Tripotent scale matrix `sI-T`. -/
def tripScale (s : ℂ) : M3C := s • (1 : M3C) - Trip

/-- Tripotent determinant. -/
theorem tripScale_det (s : ℂ) :
    (tripScale s).det = (s - 1) * (s + 1) * s := by
  simp [tripScale, Trip, Matrix.det_fin_three, Matrix.smul_apply, Matrix.sub_apply]

/-- The tripotent boundary has the zero-mode pole at `s=0`. -/
theorem tripotent_zero_pole : (tripScale 0).det = 0 := by
  simp [tripScale_det]

/-- Zero boundary momentum bulk pole matches the tripotent zero-mode boundary pole. -/
theorem bulk_zero_mode_matches_tripotent_defect :
    (sI_minus_X 0 0 0).det = 0 ∧ (tripScale 0).det = 0 := by
  exact ⟨(zero_momentum_scale_zero 0).mpr rfl, tripotent_zero_pole⟩



end DiracResolventZeroModeTripotent
