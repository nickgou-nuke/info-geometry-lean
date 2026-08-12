import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Projective Crystal Symmetry and Momentum-Space Nonsymmorphicity

Formalizes the topological insight from Zhang et al. (arXiv:2509.19735)
showing that a projective Z2 gauge flux acting on a spatial mirror 
and a lattice translation forces the mirror to act as a fractional 
translation (glide) in momentum space.
-/

namespace ProjectiveCrystal

open Complex

/-- 
In momentum space, the translation operator L_y acting on a state 
with quasimomentum k_y produces a phase shift e^{i k_y b}.
-/
noncomputable def translation_phase (k_y b : ℝ) : ℂ :=
  exp (I * (k_y * b : ℂ))

/-- 
The algebraic constraint of the projective representation:
The pi-flux plaquette enforces that conjugating L_y by the mirror M_x 
results in a negative sign: M_x⁻¹ L_y M_x = -L_y.
-/
noncomputable def projective_algebra_constraint (k_y b : ℝ) : ℂ :=
  -translation_phase k_y b

/-- 
The geometric action:
If M_x shifts the momentum k_y by a fractional amount κ_y, 
then the transformed translation operator evaluated at the new 
momentum is e^{i (k_y + κ_y) b}.
-/
noncomputable def geometric_shifted_phase (k_y κ_y b : ℝ) : ℂ :=
  translation_phase (k_y + κ_y) b

/--
Theorem: Equating the projective algebraic constraint with the geometric 
action STRICTLY requires that the fractional momentum shift κ_y satisfies 
e^{i κ_y b} = -1, forcing a half-twist of the Brillouin Zone.
-/
theorem projective_forces_momentum_glide (k_y κ_y b : ℝ) 
    (h_eq : geometric_shifted_phase k_y κ_y b = projective_algebra_constraint k_y b) :
    exp (I * (κ_y * b : ℂ)) = -1 := by
  dsimp [geometric_shifted_phase, projective_algebra_constraint, translation_phase] at h_eq
  have h_mul : exp (I * (k_y + κ_y) * (b : ℂ)) = exp (I * k_y * b) * exp (I * κ_y * b) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [h_mul] at h_eq
  -- We know e^{i k_y b} * e^{i κ_y b} = - e^{i k_y b}
  -- Since e^{i k_y b} is non-zero, we can cancel it
  have h_nz : exp (I * k_y * b) ≠ 0 := Complex.exp_ne_zero _
  calc
    exp (I * κ_y * b) = (exp (I * k_y * b))⁻¹ * (exp (I * k_y * b) * exp (I * κ_y * b)) := by
      rw [← mul_assoc, inv_mul_cancel₀ h_nz, one_mul]
    _ = (exp (I * k_y * b))⁻¹ * (-exp (I * k_y * b)) := by rw [h_eq]
    _ = - ((exp (I * k_y * b))⁻¹ * exp (I * k_y * b)) := by ring
    _ = -1 := by rw [inv_mul_cancel₀ h_nz]

end ProjectiveCrystal
