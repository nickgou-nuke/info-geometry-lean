import Mathlib.Tactic

/-!
# Projective kappa mechanism as Brillouin Klein/Möbius twist

This module integrates the Zhang--Yang--Zhao `κ_R` mechanism with the thesis
boundary dictionary:

* `κ_M=(0,1/2)` makes a projective mirror into a momentum-space glide;
* the glide squares to a full reciprocal translation;
* the half-shift contributes the phase `-1`;
* the projective matrices anticommute, hence generate a Pauli/Clifford atom;
* the Mackey square defect is the reciprocal lattice vector `(0,1)`;
* the Riemann fixed coordinate `1/2` recenters to the Klein fixed coordinate `0`.
-/

noncomputable section

namespace ProjectiveKappaKleinMobius

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev KPoint := ℚ × ℚ

/-! ## Projective Pauli/Clifford atom -/

def Mx : M2C := !![0, 1; 1, 0]
def Ly : M2C := !![1, 0; 0, -1]

theorem Mx_sq : Mx * Mx = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Mx, Matrix.mul_apply, Fin.sum_univ_two]

theorem Ly_sq : Ly * Ly = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Ly, Matrix.mul_apply, Fin.sum_univ_two]

theorem Mx_Ly_anticomm : Mx * Ly = - (Ly * Mx) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]

/-- The product of two anticommuting involutions squares to `-1`. -/
theorem MxLy_sq_neg_one : (Mx * Ly) * (Mx * Ly) = (-1 : ℂ) • (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Mx, Ly, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

/-! ## κ-shift / Möbius momentum glide -/

/-- Projective mirror with half reciprocal shift: `(kx,ky) ↦ (-kx,ky+1/2)`. -/
def affineM (k : KPoint) : KPoint := (-k.1, k.2 + 1/2)

/-- Full reciprocal `y` translation. -/
def recipY (k : KPoint) : KPoint := (k.1, k.2 + 1)

/-- The projective mirror squares to reciprocal translation. -/
theorem affineM_sq (k : KPoint) : affineM (affineM k) = recipY k := by
  cases k with
  | mk kx ky =>
    simp [affineM, recipY]
    ring

/-- Half-shift phase, abstracted as multiplication by `-1`. -/
def halfShiftPhase (z : ℂ) : ℂ := -z

theorem halfShiftPhase_sq (z : ℂ) : halfShiftPhase (halfShiftPhase z) = z := by
  simp [halfShiftPhase]

/-! ## Mackey consistency -/

def mirrorK (k : KPoint) : KPoint := (-k.1, k.2)
def addK (a b : KPoint) : KPoint := (a.1 + b.1, a.2 + b.2)
def subK (a b : KPoint) : KPoint := (a.1 - b.1, a.2 - b.2)

def kappaM : KPoint := (0, 1/2)
def kappaE : KPoint := (0, 0)

def ReciprocalLatticePoint (v : KPoint) : Prop := ∃ m n : ℤ, v = ((m : ℚ), (n : ℚ))

/-- Mackey square defect is `(0,1)`. -/
theorem kappa_square_defect : subK (addK kappaM (mirrorK kappaM)) kappaE = (0, 1) := by
  norm_num [subK, addK, mirrorK, kappaM, kappaE]

/-- Hence the defect is a reciprocal lattice vector. -/
theorem kappa_square_defect_in_lattice :
    ReciprocalLatticePoint (subK (addK kappaM (mirrorK kappaM)) kappaE) := by
  refine ⟨0, 1, ?_⟩
  rw [kappa_square_defect]
  norm_num

/-! ## Fixed-line recentering -/

def riemannReflectReal (x : ℚ) : ℚ := 1 - x
def recenterCriticalLine (x : ℚ) : ℚ := x - 1/2

theorem riemann_half_fixed : riemannReflectReal (1/2 : ℚ) = 1/2 := by
  norm_num [riemannReflectReal]

theorem riemann_half_recenters_to_klein_zero : recenterCriticalLine (1/2 : ℚ) = 0 := by
  norm_num [recenterCriticalLine]

/-- Main synthesis theorem. -/
theorem projective_kappa_klein_mobius_synthesis :
    Mx * Ly = - (Ly * Mx) ∧
    (Mx * Ly) * (Mx * Ly) = (-1 : ℂ) • (1 : M2C) ∧
    (∀ k : KPoint, affineM (affineM k) = recipY k) ∧
    (∀ z : ℂ, halfShiftPhase (halfShiftPhase z) = z) ∧
    subK (addK kappaM (mirrorK kappaM)) kappaE = (0, 1) ∧
    ReciprocalLatticePoint (subK (addK kappaM (mirrorK kappaM)) kappaE) ∧
    riemannReflectReal (1/2 : ℚ) = 1/2 ∧
    recenterCriticalLine (1/2 : ℚ) = 0 := by
  exact ⟨Mx_Ly_anticomm, MxLy_sq_neg_one, affineM_sq, halfShiftPhase_sq,
    kappa_square_defect, kappa_square_defect_in_lattice, riemann_half_fixed,
    riemann_half_recenters_to_klein_zero⟩

#check Mx_Ly_anticomm
#check MxLy_sq_neg_one
#check affineM_sq
#check kappa_square_defect_in_lattice
#check projective_kappa_klein_mobius_synthesis

end ProjectiveKappaKleinMobius
