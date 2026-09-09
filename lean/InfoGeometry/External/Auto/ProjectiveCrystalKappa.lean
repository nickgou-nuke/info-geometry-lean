import Mathlib.Tactic

/-!
# Projective crystal kappa mechanism

Digest of arXiv:2509.19735v1, Zhang--Yang--Zhao,
*Projective crystal symmetry and topological phases*.

This module focuses on the `κ_R` mechanism:
`γ(t,R)=exp(-i κ_R·t)` produces a momentum-space nonsymmorphic action
`R : k ↦ Rk+κ_R`.  For the `Pg` example, `κ_M=G_y/2`, so the projective
mirror acts as a momentum-space glide and squares to a full reciprocal
translation.
-/

noncomputable section

namespace ProjectiveCrystalKappa

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Explicit `Pm -> Pg` algebra -/

def Mx : M2C := !![0, 1; 1, 0]
def Ly : M2C := !![1, 0; 0, -1]

theorem Mx_Ly_anticomm : Mx * Ly = - (Ly * Mx) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]

theorem Mx_sq : Mx * Mx = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Mx, Matrix.mul_apply, Fin.sum_univ_two]

theorem Mx_conj_Ly : Mx * Ly * Mx = -Ly := by
  calc
    Mx * Ly * Mx = (Mx * Ly) * Mx := by rw [mul_assoc]
    _ = (-(Ly * Mx)) * Mx := by rw [Mx_Ly_anticomm]
    _ = -(Ly * (Mx * Mx)) := by simp [mul_assoc]
    _ = -Ly := by rw [Mx_sq]; simp

/-! ## `κ_M=G_y/2` as momentum-space glide -/

abbrev KPoint := ℚ × ℚ

/-- Mirror plus half reciprocal translation: `(kx,ky) ↦ (-kx,ky+1/2)`. -/
def kMirrorGlide (k : KPoint) : KPoint := (-k.1, k.2 + (1/2 : ℚ))

/-- Full reciprocal translation in the `y` direction. -/
def fullYTranslate (k : KPoint) : KPoint := (k.1, k.2 + 1)

/-- The momentum-space glide squares to a full reciprocal translation. -/
theorem kMirrorGlide_sq (k : KPoint) : kMirrorGlide (kMirrorGlide k) = fullYTranslate k := by
  cases k with
  | mk kx ky =>
    simp [kMirrorGlide, fullYTranslate]
    ring

/-- Abstract half-shift phase `z ↦ -z`. -/
def halfShiftPhase (z : ℂ) : ℂ := -z

/-- Two half reciprocal translations give a trivial phase. -/
theorem halfShiftPhase_sq (z : ℂ) : halfShiftPhase (halfShiftPhase z) = z := by
  simp [halfShiftPhase]

/-- Parity-valued `Z₂` invariant. -/
def z2Invariant (n : ℤ) : ℤ := n % 2

theorem z2Invariant_periodic (n : ℤ) : z2Invariant (n + 2) = z2Invariant n := by
  unfold z2Invariant
  omega

/-- Main synthesis theorem for the arXiv kappa mechanism. -/
theorem projective_crystal_kappa_synthesis :
    Mx * Ly = - (Ly * Mx) ∧
    Mx * Ly * Mx = -Ly ∧
    (∀ k : KPoint, kMirrorGlide (kMirrorGlide k) = fullYTranslate k) ∧
    (∀ z : ℂ, halfShiftPhase (halfShiftPhase z) = z) ∧
    (∀ n : ℤ, z2Invariant (n + 2) = z2Invariant n) := by
  exact ⟨Mx_Ly_anticomm, Mx_conj_Ly, kMirrorGlide_sq, halfShiftPhase_sq,
    z2Invariant_periodic⟩

#check Mx_Ly_anticomm
#check Mx_conj_Ly
#check kMirrorGlide_sq
#check z2Invariant_periodic
#check projective_crystal_kappa_synthesis

end ProjectiveCrystalKappa
