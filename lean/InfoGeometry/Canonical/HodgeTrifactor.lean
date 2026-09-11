import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.HodgeKreinTriFacet

namespace InfoGeometry.Canonical.HodgeTrifactor

open InfoGeometry.Canonical.HodgeKreinTriFacet

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Hodge-Trifactor operator T = P_ext - P_coext. -/
def HodgeT (O : V →ₗ[ℝ] V) (half : ℝ) : V →ₗ[ℝ] V :=
  P_ext O half - P_coext O half

/-- Theorem: T = O (once half + half = 1). -/
theorem HodgeT_eq_O
    (O : V →ₗ[ℝ] V)
    (half : ℝ)
    (h_half : half + half = 1) :
    HodgeT O half = O := by
  ext x
  unfold HodgeT P_ext P_coext
  dsimp
  rw [smul_add, smul_sub]
  have h : half • O (O x) + half • O x - (half • O (O x) - half • O x) =
           half • O x + half • O x := by abel
  rw [h, ← add_smul, h_half, one_smul]

/-- Theorem: If O satisfies the cubic law O^3 = O, then T satisfies T^3 = T. -/
theorem HodgeT_cubic
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x, O (O (O x)) = O x)
    (half : ℝ)
    (h_half : half + half = 1)
    (x : V) :
    HodgeT O half (HodgeT O half (HodgeT O half x)) = HodgeT O half x := by
  rw [HodgeT_eq_O O half h_half]
  exact hO3 x

/-! ## The Statistical Mapping -/

/-- Exact Bosonic factor Euler term: 1 / (1 - x). -/
noncomputable def bosonicFactor (x : ℝ) : ℝ := 1 / (1 - x)

/-- Coexact Fermionic factor Euler term: 1 + x. -/
def fermionicFactor (x : ℝ) : ℝ := 1 + x

/-- Harmonic Möbius factor Euler term: 1 - x. -/
def harmonicFactor (x : ℝ) : ℝ := 1 - x

/-- Theorem: Bosonic factor and Harmonic factor are multiplicative inverses. -/
theorem bosonic_times_harmonic_eq_one (x : ℝ) (h : x ≠ 1) :
    bosonicFactor x * harmonicFactor x = 1 := by
  unfold bosonicFactor harmonicFactor
  have h_diff : 1 - x ≠ 0 := by
    intro hc
    have : x = 1 := by linarith
    exact h this
  exact div_mul_cancel₀ 1 h_diff

/-- Theorem: Fermionic factor and Harmonic factor yield 1 - x^2. -/
theorem fermionic_times_harmonic_eq_one_sub_sq (x : ℝ) :
    fermionicFactor x * harmonicFactor x = 1 - x^2 := by
  unfold fermionicFactor harmonicFactor
  ring

end InfoGeometry.Canonical.HodgeTrifactor
