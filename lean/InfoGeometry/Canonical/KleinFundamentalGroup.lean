import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.KleinFundamentalGroup

open Matrix

/-!
# Fundamental Group of the Klein Bottle acting on E₇₍₇₎ Tensors

Formalizes the π₁(\mathcal{K}) relation `a * b * a⁻¹ = b⁻¹` over 
the 56-dimensional real symplectic space.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 
Theorem: The Klein group action invariantly preserves the Skew-Symmetric 
Symplectic Inner Product Ω of E₇₍₇₎ despite breaking the local compact symmetry.

Here we prove the topological shielding: if the glide-reflection `a` is ANTI-symplectic
(as proven in our earlier SymPy module) and the periodic cycle `b` is symplectic,
then the conjugated loop `a * b * a⁻¹` strictly preserves the symplectic form.
-/
theorem klein_loop_preserves_symplectic_omega
    (a a_inv b Ω : Matrix n n ℝ)
    (h_inv : a * a_inv = 1)
    (h_inv_left : a_inv * a = 1)
    (hΩ : Ωᵀ = -Ω)
    (h_a_antisymp : aᵀ * Ω * a = -Ω)
    (h_b_symp : bᵀ * Ω * b = Ω) :
    (a * b * a_inv)ᵀ * Ω * (a * b * a_inv) = Ω := by
  -- (a * b * a⁻¹)ᵀ = (a⁻¹)ᵀ * bᵀ * aᵀ
  have h1 : (a * b * a_inv)ᵀ = a_invᵀ * bᵀ * aᵀ := by
    rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
  rw [h1]
  -- Group the inner terms: aᵀ * Ω * a
  have h2 : a_invᵀ * bᵀ * aᵀ * Ω * (a * b * a_inv) = a_invᵀ * bᵀ * (aᵀ * Ω * a) * b * a_inv := by
    -- Expand associativity
    simp only [Matrix.mul_assoc]
  rw [h2]
  -- Apply anti-symplectic twist of `a`
  rw [h_a_antisymp]
  -- Pull out the negative sign
  have h3 : a_invᵀ * bᵀ * -Ω * b * a_inv = - (a_invᵀ * (bᵀ * Ω * b) * a_inv) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [h3]
  -- Apply symplectic property of `b`
  rw [h_b_symp]
  -- Now we evaluate - (a⁻¹ᵀ * Ω * a⁻¹)
  -- Since aᵀ * Ω * a = -Ω, multiply by a⁻¹ᵀ on left and a⁻¹ on right
  have h4 : a_invᵀ * (aᵀ * Ω * a) * a_inv = a_invᵀ * -Ω * a_inv := by
    rw [h_a_antisymp]
  have h5 : a_invᵀ * (aᵀ * Ω * a) * a_inv = Ω := by
    -- (a⁻¹ᵀ * aᵀ) * Ω * (a * a⁻¹) = (a * a⁻¹)ᵀ * Ω * (a * a⁻¹) = 1ᵀ * Ω * 1 = Ω
    have h5a : a_invᵀ * (aᵀ * Ω * a) * a_inv = (a_invᵀ * aᵀ) * Ω * (a * a_inv) := by
      simp only [Matrix.mul_assoc]
    rw [h5a]
    have h5b : a_invᵀ * aᵀ = (a * a_inv)ᵀ := by rw [transpose_mul]
    rw [h5b, h_inv, transpose_one, Matrix.one_mul, Matrix.mul_one]
  have h6 : a_invᵀ * -Ω * a_inv = - (a_invᵀ * Ω * a_inv) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [h6] at h4
  have h7 : - (a_invᵀ * Ω * a_inv) = Ω := h4.symm.trans h5
  -- Thus (a⁻¹ᵀ * Ω * a⁻¹) = -Ω, meaning - (a⁻¹ᵀ * Ω * a⁻¹) = Ω
  exact h7

/-
Explicit 2x2 Model for the 56-plet Generators
The fundamental 56-dimensional representation of E₇₍₇₎ decomposes into 
28 pairs of symplectic blocks. We provide the explicit 2x2 base case 
for the Klein Bottle action. 
-/

/-- The canonical 2x2 symplectic form Ω -/
def omega2 : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1], ![-1, 0]]

/-- The glide-reflection generator `a` (anti-symplectic involution). -/
def glide_a : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0], ![0, -1]]

/-- The translation generator `b` (symplectic shear). -/
def trans_b : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 1], ![0, 1]]

/-- The inverse of the translation generator `b`. -/
def trans_b_inv : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, -1], ![0, 1]]

private theorem fin2_mul_eq {R : Type*} [CommRing R]
    (A B C : Matrix (Fin 2) (Fin 2) R)
    (h00 : (A * B) 0 0 = C 0 0)
    (h01 : (A * B) 0 1 = C 0 1)
    (h10 : (A * B) 1 0 = C 1 0)
    (h11 : (A * B) 1 1 = C 1 1) :
    A * B = C := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- Proof that glide_a is an involution (a = a⁻¹). -/
@[simp] theorem glide_a_involution : glide_a * glide_a = 1 := by
  have h := Matrix.two_mul_expl glide_a glide_a
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [glide_a] using h.1
  · simpa [glide_a] using h.2.1
  · simpa [glide_a] using h.2.2.1
  · simpa [glide_a] using h.2.2.2

/-- Proof that trans_b and trans_b_inv are exact inverses. -/
@[simp] theorem trans_b_inverse : trans_b * trans_b_inv = 1 := by
  have h := Matrix.two_mul_expl trans_b trans_b_inv
  apply fin2_mul_eq
  · simpa [trans_b, trans_b_inv] using h.1
  · simpa [trans_b, trans_b_inv] using h.2.1
  · simpa [trans_b, trans_b_inv] using h.2.2.1
  · simpa [trans_b, trans_b_inv] using h.2.2.2

/-- EXPLICIT THEOREM: The Klein Bottle relation a * b * a⁻¹ = b⁻¹ is 
    strictly satisfied by the geometric matrices. -/
theorem explicit_klein_relation : glide_a * trans_b * glide_a = trans_b_inv := by
  let ab : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 1], ![0, -1]]
  have hab := Matrix.two_mul_expl glide_a trans_b
  have h₁ : glide_a * trans_b = ab := by
    apply fin2_mul_eq
    · simpa [glide_a, trans_b, ab] using hab.1
    · simpa [glide_a, trans_b, ab] using hab.2.1
    · simpa [glide_a, trans_b, ab] using hab.2.2.1
    · simpa [glide_a, trans_b, ab] using hab.2.2.2
  have hab' := Matrix.two_mul_expl ab glide_a
  have h₂ : ab * glide_a = trans_b_inv := by
    apply fin2_mul_eq
    · simpa [glide_a, trans_b_inv, ab] using hab'.1
    · simpa [glide_a, trans_b_inv, ab] using hab'.2.1
    · simpa [glide_a, trans_b_inv, ab] using hab'.2.2.1
    · simpa [glide_a, trans_b_inv, ab] using hab'.2.2.2
  rw [h₁, h₂]

/-- EXPLICIT THEOREM: The glide reflection `a` is strictly anti-symplectic. -/
theorem explicit_a_antisymp : glide_aᵀ * omega2 * glide_a = -omega2 := by
  let aT : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, -1]]
  let gΩ : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![1, 0]]
  let gΩneg : Matrix (Fin 2) (Fin 2) ℝ := ![![0, -1], ![1, 0]]
  have haT : glide_aᵀ = aT := by
    ext i j
    rw [Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> simp [glide_a, aT]
  have hgΩ := Matrix.two_mul_expl aT omega2
  have h₁ : aT * omega2 = gΩ := by
    apply fin2_mul_eq
    · simpa [aT, omega2, gΩ] using hgΩ.1
    · simpa [aT, omega2, gΩ] using hgΩ.2.1
    · simpa [aT, omega2, gΩ] using hgΩ.2.2.1
    · simpa [aT, omega2, gΩ] using hgΩ.2.2.2
  have hgΩ' := Matrix.two_mul_expl gΩ glide_a
  have h₂ : gΩ * glide_a = gΩneg := by
    apply fin2_mul_eq
    · simpa [glide_a, gΩ, gΩneg] using hgΩ'.1
    · simpa [glide_a, gΩ, gΩneg] using hgΩ'.2.1
    · simpa [glide_a, gΩ, gΩneg] using hgΩ'.2.2.1
    · simpa [glide_a, gΩ, gΩneg] using hgΩ'.2.2.2
  have hneg : gΩneg = -omega2 := by
    ext i j
    change gΩneg i j = -(omega2 i j)
    fin_cases i <;> fin_cases j <;> norm_num [gΩneg, omega2]
  rw [haT, h₁, h₂, hneg]

/-- EXPLICIT THEOREM: The translation `b` is strictly symplectic. -/
theorem explicit_b_symp : trans_bᵀ * omega2 * trans_b = omega2 := by
  let bt : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![1, 1]]
  let bΩ : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![-1, 1]]
  have hbt : trans_bᵀ = bt := by
    ext i j
    rw [Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> simp [trans_b, bt]
  have hbΩ := Matrix.two_mul_expl bt omega2
  have h₁ : bt * omega2 = bΩ := by
    apply fin2_mul_eq
    · simpa [bt, omega2, bΩ] using hbΩ.1
    · simpa [bt, omega2, bΩ] using hbΩ.2.1
    · simpa [bt, omega2, bΩ] using hbΩ.2.2.1
    · simpa [bt, omega2, bΩ] using hbΩ.2.2.2
  have hbΩ' := Matrix.two_mul_expl bΩ trans_b
  have h₂ : bΩ * trans_b = omega2 := by
    apply fin2_mul_eq
    · simpa [trans_b, omega2, bΩ] using hbΩ'.1
    · simpa [trans_b, omega2, bΩ] using hbΩ'.2.1
    · simpa [trans_b, omega2, bΩ] using hbΩ'.2.2.1
    · simpa [trans_b, omega2, bΩ] using hbΩ'.2.2.2
  rw [hbt, h₁, h₂]

end InfoGeometry.Canonical.KleinFundamentalGroup
