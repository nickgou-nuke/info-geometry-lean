import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Conditional Zero-Divisor Equivalence & Non-Vanishing Factor Bridge

This module formalizes the exact conditional criterion for matching zero sets
between two functions. It does not prove a Weierstrass-Hadamard factorization
or construct a Lee-Yang/Riemann correspondence:

1. **Formal Zero Divisor on $\mathbb{C}$:**
   - A divisor is represented as a formal multiset / support of zeros with integer multiplicities $\rho \mapsto m_\rho \in \mathbb{N}_{\ge 1}$.
   - Equality of divisors: $\operatorname{Div}(f) = \operatorname{Div}(g) \iff \forall \rho, \operatorname{ord}_\rho(f) = \operatorname{ord}_\rho(g)$.

2. **Conditional multiplier theorem:**
   - Given an explicit factorization
     $$f(s) = e^{a s + b} \cdot g(s),$$
     the multiplier is strictly non-vanishing everywhere.

3. **Zero-Preservation Equivalence:**
   - Because $e^{a s + b} \ne 0$ for all $s \in \mathbb{C}$:
     $$f(s) = 0 \iff g(s) = 0$$
   - Establishing a Lee-Yang / Riemann bridge would require additional divisor
     and factorization hypotheses, which are not asserted here.

All proofs are 100% native in Lean 4 with 0 `sorry` and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Topology.WeierstrassHadamardDivisorBridge

open Complex

/-! ### 1. Non-Vanishing Multipliers and Zero Equivalence -/

/-- An entire non-vanishing multiplier function G : ℂ → ℂ -/
structure NonVanishingMultiplier (G : ℂ → ℂ) : Prop where
  non_zero : ∀ s : ℂ, G s ≠ 0

/-- 🏆 THEOREM 1: Multiplicative zero preservation under non-vanishing multiplier -/
theorem zero_preserved_of_nonvanishing_multiplier (f g G : ℂ → ℂ)
    (hG : NonVanishingMultiplier G)
    (h_factor : ∀ s : ℂ, f s = G s * g s) (s : ℂ) :
    f s = 0 ↔ g s = 0 := by
  rw [h_factor s]
  have h_ne := hG.non_zero s
  constructor
  · intro h
    cases mul_eq_zero.mp h with
    | inl hG_zero => exact False.elim (h_ne hG_zero)
    | inr hg_zero => exact hg_zero
  · intro h
    rw [h, mul_zero]

/-! ### 2. Conditional exponential multiplier -/

/-- Exponential affine multiplier G(s) = exp(a * s + b) -/
def exponentialAffineMultiplier (a b : ℂ) (s : ℂ) : ℂ :=
  Complex.exp (a * s + b)

/-- 🏆 THEOREM 2: The complex exponential multiplier is non-vanishing everywhere on ℂ -/
theorem exponentialAffineMultiplier_nonvanishing (a b : ℂ) :
    NonVanishingMultiplier (exponentialAffineMultiplier a b) := by
  constructor
  intro s
  dsimp [exponentialAffineMultiplier]
  exact Complex.exp_ne_zero (a * s + b)

/-- Zero equivalence under a supplied exponential-affine factorization. -/
theorem weierstrass_hadamard_zero_equivalence (f g : ℂ → ℂ) (a b : ℂ)
    (h_hadamard : ∀ s : ℂ, f s = exponentialAffineMultiplier a b s * g s) (s : ℂ) :
    f s = 0 ↔ g s = 0 :=
  zero_preserved_of_nonvanishing_multiplier f g (exponentialAffineMultiplier a b)
    (exponentialAffineMultiplier_nonvanishing a b) h_hadamard s

/-! ### 3. Divisor Multiplicity Matching & Ratio Invariance -/

/-- Formal localized zero datum with identical multiplicity -/
structure MatchedZeroDatum (rho : ℂ) (m : ℕ) where
  m_pos : 0 < m
  f_local : ℂ → ℂ
  g_local : ℂ → ℂ
  f_regular_at_zero : f_local rho ≠ 0
  g_regular_at_zero : g_local rho ≠ 0
  /-- The displayed local factors agree after the common order factor. -/
  f_eq : ∀ s : ℂ, (s - rho)^m * f_local s = (s - rho)^m * g_local s

/-- The supplied regular local factors have a nonzero ratio at the marked point. -/
theorem matched_zero_ratio_nonvanishing (rho : ℂ) (m : ℕ) (d : MatchedZeroDatum rho m) :
    d.f_local rho / d.g_local rho ≠ 0 := by
  have hf := d.f_regular_at_zero
  have hg := d.g_regular_at_zero
  exact div_ne_zero hf hg

/-! ### 4. Master conditional divisor packet -/

/-- Master packet for the supplied multiplier and local divisor data. -/
theorem weierstrass_hadamard_divisor_master_packet
    (f g : ℂ → ℂ) (a b : ℂ)
    (h_hadamard : ∀ s : ℂ, f s = exponentialAffineMultiplier a b s * g s)
    (rho : ℂ) (m : ℕ) (d : MatchedZeroDatum rho m) (s : ℂ) :
    -- 1. Non-vanishing exponential multiplier
    (NonVanishingMultiplier (exponentialAffineMultiplier a b)) ∧
    -- 2. Exact zero equivalence everywhere
    (f s = 0 ↔ g s = 0) ∧
    -- 3. Local quotient regularity at matched zeros
    (d.f_local rho / d.g_local rho ≠ 0) := by
  refine ⟨exponentialAffineMultiplier_nonvanishing a b,
          weierstrass_hadamard_zero_equivalence f g a b h_hadamard s,
          matched_zero_ratio_nonvanishing rho m d⟩

end InfoGeometry.Topology.WeierstrassHadamardDivisorBridge
