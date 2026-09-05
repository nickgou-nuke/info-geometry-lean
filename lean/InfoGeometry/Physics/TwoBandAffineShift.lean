import Mathlib

/-!
# Electrostatic band shifts are not lapse rescalings or BdG charge shifts

`hamiltonian b m d` is an electron two-band Hermitian matrix. A common scalar
shift b changes the band centre, not the splitting. This is not automatically
a Nambu Hamiltonian. The explicit same-momentum particle-hole test below shows
the obstruction, including the off-diagonal restriction for a spinless block.
-/

namespace InfoGeometry.Physics.TwoBandAffineShift

noncomputable section

open scoped ComplexConjugate

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

def hamiltonian (b m : ℝ) (d : ℂ) : Mat2 :=
  !![((b + m : ℝ) : ℂ), d; conj d, ((b - m : ℝ) : ℂ)]

theorem hamiltonian_hermitian (b m : ℝ) (d : ℂ) :
    (hamiltonian b m d).IsHermitian := by
  change (hamiltonian b m d).conjTranspose = hamiltonian b m d
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hamiltonian, Matrix.conjTranspose_apply]

theorem affine_shift (b m : ℝ) (d : ℂ) :
    hamiltonian b m d = (b : ℂ) • (1 : Mat2) + hamiltonian 0 m d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hamiltonian] <;> ring

theorem hamiltonian_trace (b m : ℝ) (d : ℂ) :
    Matrix.trace (hamiltonian b m d) = (2 : ℂ) * b := by
  simp [hamiltonian, Matrix.trace, Fin.sum_univ_two]
  ring

def gapSquare (m : ℝ) (d : ℂ) : ℝ := m ^ 2 + Complex.normSq d

theorem gapSquare_nonneg (m : ℝ) (d : ℂ) : 0 ≤ gapSquare m d := by
  dsimp [gapSquare, Complex.normSq]
  positivity

theorem centered_square (m : ℝ) (d : ℂ) :
    hamiltonian 0 m d * hamiltonian 0 m d =
      (gapSquare m d : ℂ) • (1 : Mat2) := by
  have hconj : conj d * d = (Complex.normSq d : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hamiltonian, gapSquare, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_conj, hconj] <;> ring

/-- Characteristic determinant with a real spectral parameter. -/
theorem characteristic_determinant (b m : ℝ) (d : ℂ) (E : ℝ) :
    Matrix.det (hamiltonian b m d - (E : ℂ) • (1 : Mat2)) =
      (((b - E) ^ 2 - gapSquare m d : ℝ) : ℂ) := by
  simp [hamiltonian, gapSquare, Matrix.det_fin_two, Complex.mul_conj]
  ring

def energyPlus (b m : ℝ) (d : ℂ) : ℝ := b + Real.sqrt (gapSquare m d)
def energyMinus (b m : ℝ) (d : ℂ) : ℝ := b - Real.sqrt (gapSquare m d)

theorem energyPlus_characteristic_root (b m : ℝ) (d : ℂ) :
    Matrix.det (hamiltonian b m d - (energyPlus b m d : ℂ) • (1 : Mat2)) = 0 := by
  rw [characteristic_determinant]
  have h := Real.sq_sqrt (gapSquare_nonneg m d)
  have hz : (b - energyPlus b m d) ^ 2 - gapSquare m d = 0 := by
    dsimp [energyPlus]
    nlinarith
  rw [hz]
  rfl

theorem energyMinus_characteristic_root (b m : ℝ) (d : ℂ) :
    Matrix.det (hamiltonian b m d - (energyMinus b m d : ℂ) • (1 : Mat2)) = 0 := by
  rw [characteristic_determinant]
  have h := Real.sq_sqrt (gapSquare_nonneg m d)
  have hz : (b - energyMinus b m d) ^ 2 - gapSquare m d = 0 := by
    dsimp [energyMinus]
    nlinarith
  rw [hz]
  rfl

/-- The hybridized gap is independent of the electrostatic centre b. -/
theorem gap_independent_of_shift (b m : ℝ) (d : ℂ) :
    energyPlus b m d - energyMinus b m d = 2 * Real.sqrt (gapSquare m d) := by
  dsimp [energyPlus, energyMinus]
  ring

theorem midpoint_eq_shift (b m : ℝ) (d : ℂ) :
    (energyPlus b m d + energyMinus b m d) / 2 = b := by
  dsimp [energyPlus, energyMinus]
  ring

/-- Common electrostatic shifts and lapse multiplication coincide only trivially if m is nonzero. -/
theorem lapse_not_affine (N b m : ℝ) (d : ℂ) (hm : m ≠ 0)
    (h : (N : ℂ) • hamiltonian 0 m d = hamiltonian b m d) :
    N = 1 ∧ b = 0 := by
  have h0 := congrArg (fun A : Mat2 => (A 0 0).re) h
  have h1 := congrArg (fun A : Mat2 => (A 1 1).re) h
  simp [hamiltonian] at h0 h1
  have hb : b = 0 := by linarith
  have hn : (N - 1) * m = 0 := by nlinarith
  have hN : N = 1 := by
    have := (mul_eq_zero.mp hn).resolve_right hm
    linarith
  exact ⟨hN, hb⟩

def particleHoleMatrix (A : Mat2) : Mat2 :=
  !![conj (A 1 1), conj (A 1 0); conj (A 0 1), conj (A 0 0)]

/-- This is entrywise conjugation with the two Nambu coordinates interchanged. -/
theorem particleHoleMatrix_hamiltonian (b m : ℝ) (d : ℂ) :
    particleHoleMatrix (hamiltonian b m d) = hamiltonian b (-m) d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [particleHoleMatrix, hamiltonian, sub_eq_add_neg]

/-- A real scalar shift is even under particle-hole conjugation, not odd. -/
theorem particleHole_scalar (b : ℝ) :
    particleHoleMatrix ((b : ℂ) • (1 : Mat2)) = (b : ℂ) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [particleHoleMatrix]

/-- At a fixed momentum, this spinless 2x2 model has PHS only with b=d=0.
Momentum reversal or a larger spin block changes this test and must be supplied explicitly. -/
theorem same_point_particleHole_iff (b m : ℝ) (d : ℂ) :
    particleHoleMatrix (hamiltonian b m d) = -hamiltonian b m d ↔ b = 0 ∧ d = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun A : Mat2 => (A 0 0).re) h
    have hd := congrArg (fun A : Mat2 => A 0 1) h
    simp [particleHoleMatrix, hamiltonian] at h0 hd
    constructor
    · linarith
    · apply Complex.ext
      · have hr := congrArg Complex.re hd
        simp at hr
        linarith
      · have hi := congrArg Complex.im hd
        simp at hi
        linarith
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [particleHoleMatrix, hamiltonian]

/-- The sign of an electrostatic band shift is fixed independently of any lapse. -/
theorem electrostatic_shift_derivative
    {phi : ℝ → ℝ} {x phi' : ℝ} (hphi : HasDerivAt phi phi' x) (e : ℝ) :
    HasDerivAt (fun y => -e * phi y) (e * (-phi')) x := by
  convert hphi.const_mul (-e) using 1 <;> ring

end
end InfoGeometry.Physics.TwoBandAffineShift
