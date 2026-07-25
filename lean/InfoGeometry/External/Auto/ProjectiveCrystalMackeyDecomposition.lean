import Mathlib.Tactic

/-!
# Projective crystal symmetry and Mackey kappa decomposition

Digest source: arXiv:2509.19735v1,
Chen Zhang, Shengyuan A. Yang, Y. X. Zhao,
*Projective crystal symmetry and topological phases*.

This file complements `ProjectiveCrystalKappa.lean` by formalizing the
Mackey-decomposition core:

* a projective `Z₂×Z₂` sign factor satisfying the 2-cocycle equation;
* explicit matrices with `Mx Ly = - Ly Mx`;
* the `κ_M=(0,1/2)` momentum-space mirror/glide;
* the constraint `κ_M + M κ_M - κ_E ∈ L̂`, here proved by the vector `(0,1)`;
* a `Z₂` invariant stable under adding two.
-/

noncomputable section

namespace ProjectiveCrystalMackeyDecomposition

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev KPoint := ℚ × ℚ
abbrev Z2Pair := Bool × Bool

/-! ## A concrete projective factor system -/

/-- Multiplication in `Z₂×Z₂`, represented by xor. -/
def z2mul (g h : Z2Pair) : Z2Pair := (xor g.1 h.1, xor g.2 h.2)

/-- Sign factor for generators `M,L` with `M L = - L M`. -/
def signFactor (g h : Z2Pair) : ℤ := if g.1 && h.2 then -1 else 1

/-- The sign factor is a normalized 2-cocycle on `Z₂×Z₂`. -/
theorem signFactor_cocycle (g h k : Z2Pair) :
    signFactor g h * signFactor (z2mul g h) k =
      signFactor g (z2mul h k) * signFactor h k := by
  rcases g with ⟨g₁, g₂⟩
  rcases h with ⟨h₁, h₂⟩
  rcases k with ⟨k₁, k₂⟩
  cases g₁ <;> cases g₂ <;> cases h₁ <;> cases h₂ <;> cases k₁ <;> cases k₂ <;>
    decide

/-! ## Explicit `Pm → Pg` projective matrix relation -/

def Mx : M2C := !![0, 1; 1, 0]
def Ly : M2C := !![1, 0; 0, -1]

theorem Mx_Ly_anticomm : Mx * Ly = - (Ly * Mx) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Mx, Ly, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]

theorem Mx_conj_Ly : Mx * Ly * Mx = -Ly := by
  have hsq : Mx * Mx = 1 := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [Mx, Matrix.mul_apply, Fin.sum_univ_two]
  calc
    Mx * Ly * Mx = (Mx * Ly) * Mx := by rw [mul_assoc]
    _ = (-(Ly * Mx)) * Mx := by rw [Mx_Ly_anticomm]
    _ = -(Ly * (Mx * Mx)) := by simp [mul_assoc]
    _ = -Ly := by rw [hsq]; simp

/-! ## Mackey `κ` constraint and momentum-space nonsymmorphicity -/

/-- Mirror part of the momentum action: `(kx,ky) ↦ (-kx,ky)`. -/
def mirrorK (k : KPoint) : KPoint := (-k.1, k.2)

/-- Pair addition on rational reciprocal coordinates. -/
def addK (a b : KPoint) : KPoint := (a.1 + b.1, a.2 + b.2)

/-- Pair subtraction. -/
def subK (a b : KPoint) : KPoint := (a.1 - b.1, a.2 - b.2)

/-- Projective `κ_M=(0,1/2)` from the `Pg` example. -/
def kappaM : KPoint := (0, 1/2)

/-- Trivial identity-sector kappa. -/
def kappaE : KPoint := (0, 0)

/-- Affine Mackey momentum action `k ↦ M k + κ_M`. -/
def affineM (k : KPoint) : KPoint := addK (mirrorK k) kappaM

/-- Full reciprocal translation in the `y` direction. -/
def recipY (k : KPoint) : KPoint := (k.1, k.2 + 1)

/-- The projective mirror is a momentum-space glide: its square is reciprocal translation. -/
theorem affineM_sq : ∀ k : KPoint, affineM (affineM k) = recipY k := by
  intro k
  cases k with
  | mk kx ky =>
    simp [affineM, addK, mirrorK, kappaM, recipY]
    ring

/-- Mackey constraint for the mirror square: `κ_M + Mκ_M - κ_E = (0,1) ∈ L̂`. -/
theorem kappaM_square_constraint : subK (addK kappaM (mirrorK kappaM)) kappaE = (0, 1) := by
  norm_num [subK, addK, kappaM, mirrorK, kappaE]

/-- Reciprocal lattice membership for integer rational pairs. -/
def ReciprocalLatticePoint (v : KPoint) : Prop := ∃ m n : ℤ, v = ((m : ℚ), (n : ℚ))

/-- The mirror-square kappa defect is an actual reciprocal lattice vector. -/
theorem kappaM_square_in_lattice :
    ReciprocalLatticePoint (subK (addK kappaM (mirrorK kappaM)) kappaE) := by
  refine ⟨0, 1, ?_⟩
  rw [kappaM_square_constraint]
  norm_num

/-- Parity-valued topological invariant. -/
def z2Invariant (n : ℤ) : ℤ := n % 2

theorem z2Invariant_periodic : ∀ n : ℤ, z2Invariant (n + 2) = z2Invariant n := by
  intro n
  unfold z2Invariant
  exact Int.add_emod_right n 2

#check signFactor_cocycle
#check affineM_sq
#check kappaM_square_in_lattice

end ProjectiveCrystalMackeyDecomposition
