import Mathlib.Tactic

/-!
# Projective crystal symmetry and momentum-space nonsymmorphicity

Digest source:
Chen Zhang, Shengyuan A. Yang, Y.X. Zhao,
*Projective crystal symmetry and topological phases*, Materials Today Quantum 8
(2025) 100055.

The paper emphasizes that projective crystal-symmetry representations
`ρ(g)ρ(h)=ν(g,h)ρ(gh)` can produce nonsymmorphic symmetry operations in
momentum space.  In particular, a projective representation of real-space `Pm`
can realize the momentum-space glide group `Pg`, with the projective relation
`ρ(Mₓ)ρ(Lᵧ)=-ρ(Lᵧ)ρ(Mₓ)`.  This phase `-1` is the half reciprocal-lattice
translation `k_y ↦ k_y+π`, and the quotient fundamental domain can become a
Brillouin Klein bottle with `Z₂` band classification.
-/

noncomputable section

namespace ProjectiveCrystalSymmetry

open Matrix

/-! ## Projective factor systems -/

variable {G : Type} [Group G]

/-- A `U(1)`-valued multiplier written as a complex phase. -/
def TwoCocycle (ν : G → G → ℂ) : Prop :=
  ∀ g h k : G, ν g h * ν (g * h) k = ν g (h * k) * ν h k

/-- The trivial multiplier is a valid two-cocycle. -/
theorem trivial_twoCocycle : TwoCocycle (fun _ _ : G => (1 : ℂ)) := by
  intro g h k
  simp

/-- Coboundary/gauge transform of a multiplier. -/
def coboundaryTwist (ν : G → G → ℂ) (χ : G → ℂ) (g h : G) : ℂ :=
  ν g h * χ g * χ h / χ (g * h)

/-! ## The `Pm -> Pg` projective algebra -/

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Projective mirror operator. -/
def Mx : M2C := !![0, 1; 1, 0]

/-- Translation/eigenphase sector representative. -/
def Ly : M2C := !![1, 0; 0, -1]

/-- The projective algebra relation `Mx Ly = - Ly Mx`. -/
theorem Mx_Ly_anticomm : Mx * Ly = - (Ly * Mx) := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
    · simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
  · fin_cases j
    · simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
    · simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]

/-- `Mx` squares to identity, as a mirror representative. -/
theorem Mx_sq : Mx * Mx = 1 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [Mx, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Mx, Matrix.mul_apply, Fin.sum_univ_two]
  · fin_cases j
    · simp [Mx, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Mx, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugating `Ly` by `Mx` flips its sign, the algebraic half-translation phase. -/
theorem Mx_conj_Ly : Mx * Ly * Mx = -Ly := by
  calc
    Mx * Ly * Mx = (Mx * Ly) * Mx := by rw [mul_assoc]
    _ = (-(Ly * Mx)) * Mx := by rw [Mx_Ly_anticomm]
    _ = -(Ly * (Mx * Mx)) := by simp [mul_assoc]
    _ = -Ly := by rw [Mx_sq]; simp

/-- Phase shift by a half reciprocal lattice vector, represented algebraically. -/
def halfReciprocalShiftPhase (z : ℂ) : ℂ := -z

/-- Applying the half reciprocal shift twice returns the original phase. -/
theorem halfReciprocalShiftPhase_sq (z : ℂ) :
    halfReciprocalShiftPhase (halfReciprocalShiftPhase z) = z := by
  simp [halfReciprocalShiftPhase]

/-! ## Momentum-space nonsymmorphic action and Klein bottle parity -/

/-- Momentum-space glide action in the paper's `Pg` example, with `π` represented abstractly by `half`. -/
def kGlide (half : ℝ) (k : ℝ × ℝ) : ℝ × ℝ := (-k.1, k.2 + half)

/-- Applying the glide twice gives a full reciprocal translation in the glide direction. -/
theorem kGlide_sq (half : ℝ) (k : ℝ × ℝ) :
    kGlide half (kGlide half k) = (k.1, k.2 + 2 * half) := by
  cases k with
  | mk kx ky =>
    simp [kGlide]
    ring

/-- Parity-valued `Z₂` invariant for the Brillouin Klein bottle. -/
def z2Invariant (n : ℤ) : ℤ := n % 2

/-- The invariant is parity-valued. -/
theorem z2Invariant_periodic (n : ℤ) : z2Invariant (n + 2) = z2Invariant n := by
  unfold z2Invariant
  omega

/-- Main synthesis theorem for the paper digest. -/
theorem projective_crystal_symmetry_synthesis :
    Mx * Ly = - (Ly * Mx) ∧
    Mx * Ly * Mx = -Ly ∧
    (∀ z : ℂ, halfReciprocalShiftPhase (halfReciprocalShiftPhase z) = z) ∧
    (∀ half : ℝ, ∀ k : ℝ × ℝ, kGlide half (kGlide half k) = (k.1, k.2 + 2 * half)) ∧
    (∀ n : ℤ, z2Invariant (n + 2) = z2Invariant n) := by
  constructor
  · ext i j
    fin_cases i
    · fin_cases j
      · simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
      · simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
    · fin_cases j
      · simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
      · simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
  constructor
  · calc
      Mx * Ly * Mx = (Mx * Ly) * Mx := by rw [mul_assoc]
      _ = (-(Ly * Mx)) * Mx := by rw [Mx_Ly_anticomm]
      _ = -(Ly * (Mx * Mx)) := by simp [mul_assoc]
      _ = -Ly := by rw [Mx_sq]; simp
  constructor
  · intro z
    simp [halfReciprocalShiftPhase]
  constructor
  · intro half k
    cases k with
    | mk kx ky =>
      simp [kGlide]
      ring
  · intro n
    unfold z2Invariant
    omega

#check trivial_twoCocycle
#check Mx_Ly_anticomm
#check Mx_conj_Ly
#check kGlide_sq
#check z2Invariant_periodic
#check projective_crystal_symmetry_synthesis

end ProjectiveCrystalSymmetry
