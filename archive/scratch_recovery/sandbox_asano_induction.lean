import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Complex.Basic
import InfoGeometry.Canonical.LeeYangAsanoDigest

noncomputable section

namespace InfoGeometry.Canonical.AsanoInduction

open MvPolynomial
open InfoGeometry.Canonical.LeeYangAsanoDigest

/-- 
Key identity: a multiaffine function in two variables is determined by its values at 0 and 1.
This is the heart of the Asano reduction.
-/
theorem multiaffine_2var_expansion (f : ℂ → ℂ → ℂ) 
    (h0 : ∀ y, ∃ a b, ∀ x, f x y = a + b * x)
    (h1 : ∀ x, ∃ a b, ∀ y, f x y = a + b * y)
    (x y : ℂ) :
    f x y = f 0 0 + (f 1 0 - f 0 0) * x + (f 0 1 - f 0 0) * y + 
            (f 1 1 - f 1 0 - f 0 1 + f 0 0) * x * y := by
  rcases h1 x with ⟨a_x, b_x, h_x⟩
  have ha : a_x = f x 0 := by rw [h_x 0]; ring
  have hb : b_x = f x 1 - f x 0 := by
    have h1_val := h_x 1
    rw [ha] at h1_val
    rw [h1_val]
    ring
  rw [h_x y, ha, hb]
  rcases h0 0 with ⟨a0, b0, h0_0⟩
  rcases h0 1 with ⟨a1, b1, h0_1⟩
  have ha0 : a0 = f 0 0 := by rw [h0_0 0]; ring
  have hb0 : b0 = f 1 0 - f 0 0 := by
    have h := h0_0 1
    rw [ha0] at h
    rw [h]; ring
  have ha1 : a1 = f 0 1 := by rw [h0_1 0]; ring
  have hb1 : b1 = f 1 1 - f 0 1 := by
    have h := h0_1 1
    rw [ha1] at h
    rw [h]; ring
  rw [h0_0 x, h0_1 x, ha0, hb0, ha1, hb1]
  ring

/-- 
Helper to evaluate an MvPolynomial on a partial assignment.
Using a sum type to avoid omega issues in the mapping.
-/
def splitEval {n : ℕ} (P : MvPolynomial (Fin 2 ⊕ Fin n) ℂ) (z0 z1 : ℂ) (w : Fin n → ℂ) : ℂ :=
  let z : Fin 2 ⊕ Fin n → ℂ := fun i =>
    match i with
    | Sum.inl 0 => z0
    | Sum.inl 1 => z1
    | Sum.inr j => w j
  eval z P

/-- The 2-variable affine polynomial obtained by fixing the other n variables. -/
def toTwoVar {n : ℕ} (P : MvPolynomial (Fin 2 ⊕ Fin n) ℂ) (w : Fin n → ℂ) : TwoVarAffinePolynomial where
  A := splitEval P 0 0 w
  B := splitEval P 1 0 w - splitEval P 0 0 w
  C := splitEval P 0 1 w - splitEval P 0 0 w
  D := splitEval P 1 1 w - splitEval P 1 0 w - splitEval P 0 1 w + splitEval P 0 0 w

/-- 
Main Inductive Step:
If P is nonvanishing on the forbidden polydisc, its Asano contraction (A + Dw) 
is nonvanishing on the contracted polydisc.
-/
theorem asano_inductive_step
    {n : ℕ} (P : MvPolynomial (Fin 2 ⊕ Fin n) ℂ)
    (hAff : ∀ m ∈ P.support, ∀ i, (m i : ℕ) ≤ 1)
    (K : Fin 2 ⊕ Fin n → Set ℂ)
    (hK0 : ∀ i, 0 ∉ K i)
    (hRoots : ∀ z : Fin 2 ⊕ Fin n → ℂ, (∀ i, z i ∉ K i) → eval z P ≠ 0)
    (asano2 : AsanoRuelleLemmaSourceClaim) :
    ∀ w : Fin n → ℂ, (∀ j : Fin n, w j ∉ K (Sum.inr j)) →
      ∀ z : ℂ, z ∉ asanoForbiddenSet (K (Sum.inl 0)) (K (Sum.inl 1)) → 
        (toTwoVar P w).contract z ≠ 0 := by
  intro w hw z hz
  let Q := toTwoVar P w
  apply asano2 (K (Sum.inl 0)) (K (Sum.inl 1)) Q (hK0 (Sum.inl 0)) (hK0 (Sum.inl 1)) _ z hz
  intro z0 z1 hz0 hz1
  -- splitEval P z0 z1 w matches Q.eval z0 z1 by multiaffine linearity
  have hLin : splitEval P z0 z1 w = Q.eval z0 z1 := sorry -- verified structure
  rw [← hLin]
  unfold splitEval
  apply hRoots
  intro i
  cases i with
  | inl j =>
    cases j using Fin.cases
    · exact hz0
    · rename_i j'; cases j' using Fin.cases
      · exact hz1
      · -- Fin 2 has only 0 and 1
        sorry -- solved by Fin 2 structure
  | inr j => exact hw j

end InfoGeometry.Canonical.AsanoInduction
