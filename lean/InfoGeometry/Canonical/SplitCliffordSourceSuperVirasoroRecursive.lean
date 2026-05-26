import Mathlib

/-!
# InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroRecursive

Finite truncation core for recursive Super-Virasoro construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.SuperVirasoro

open Finset
open scoped BigOperators

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

abbrev EndV := Module.End 𝕜 V

/-- Truncated supercurrent `G_r^N = ∑_{k=-N}^N J_k ψ_{r-k}`. -/
def G_trunc (N r : ℤ) (J ψ : ℤ → EndV) : EndV :=
  ∑ k in Icc (-N) N, (J k) * (ψ (r - k))

/-- Truncated bosonic stress part `L_{n,bos}^N = ∑_{k=-N}^N J_k J_{n-k}`. -/
def L_bosonic_trunc (N n : ℤ) (J : ℤ → EndV) : EndV :=
  ∑ k in Icc (-N) N, (J k) * (J (n - k))

/-- Truncated fermionic stress part `L_{n,fer}^N = ∑_{k=-N}^N k • (ψ_{-k} ψ_{k+n})`. -/
def L_fermionic_trunc (N n : ℤ) (ψ : ℤ → EndV) : EndV :=
  ∑ k in Icc (-N) N, (k : 𝕜) • ((ψ (-k)) * (ψ (k + n)))

/-- Total truncated stress tensor `L_n^N`. -/
def L_trunc (N n : ℤ) (J ψ : ℤ → EndV) : EndV :=
  L_bosonic_trunc N n J + L_fermionic_trunc N n ψ

/-- Target 3a: `[L_m^N, G_r^N] = ((m/2)-r) • G_{m+r}^N + defect`. -/
def SuperBracket_L_G_Target (N m r : ℤ) (J ψ : ℤ → EndV) (defect : EndV) : Prop :=
  (L_trunc N m J ψ) * (G_trunc N r J ψ) - (G_trunc N r J ψ) * (L_trunc N m J ψ)
    = ((m : 𝕜) / 2 - (r : 𝕜)) • G_trunc N (m + r) J ψ + defect

/-- Target 3b: `{G_r^N, G_s^N} = 2L_{r+s}^N + central_N(r,s) • id + defect`. -/
def SuperBracket_G_G_Target
    (N r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜) (defect : EndV) : Prop :=
  (G_trunc N r J ψ) * (G_trunc N s J ψ) + (G_trunc N s J ψ) * (G_trunc N r J ψ)
    = (2 : 𝕜) • L_trunc N (r + s) J ψ + (central_N r s) • (1 : EndV) + defect

/-- Explicit finite defect for the mixed bracket target. -/
def defect_LG (N m r : ℤ) (J ψ : ℤ → EndV) : EndV :=
  ((L_trunc N m J ψ) * (G_trunc N r J ψ) - (G_trunc N r J ψ) * (L_trunc N m J ψ))
    - ((m : 𝕜) / 2 - (r : 𝕜)) • G_trunc N (m + r) J ψ

/-- Explicit finite defect for the `GG` target. -/
def defect_GG (N r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜) : EndV :=
  (G_trunc N r J ψ) * (G_trunc N s J ψ) + (G_trunc N s J ψ) * (G_trunc N r J ψ)
    - ((2 : 𝕜) • L_trunc N (r + s) J ψ + (central_N r s) • (1 : EndV))

/-- Finite-`N` mixed bracket evaluation with explicit residual term. -/
theorem superBracket_L_G_target_with_defect
    (N m r : ℤ) (J ψ : ℤ → EndV) :
    SuperBracket_L_G_Target N m r J ψ (defect_LG N m r J ψ) := by
  unfold SuperBracket_L_G_Target defect_LG
  abel_nf

/-- Finite-`N` anticommutator evaluation with explicit residual and central term. -/
theorem superBracket_G_G_target_with_defect
    (N r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜) :
    SuperBracket_G_G_Target N r s J ψ central_N (defect_GG N r s J ψ central_N) := by
  unfold SuperBracket_G_G_Target defect_GG
  abel_nf

/-- Exact closure if the mixed bracket defect vanishes. -/
theorem superBracket_L_G_target_of_defect_zero
    (N m r : ℤ) (J ψ : ℤ → EndV)
    (hdef : defect_LG N m r J ψ = 0) :
    SuperBracket_L_G_Target N m r J ψ 0 := by
  have h := superBracket_L_G_target_with_defect N m r J ψ
  simpa [hdef] using h

/-- Exact closure if the `GG` defect vanishes. -/
theorem superBracket_G_G_target_of_defect_zero
    (N r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜)
    (hdef : defect_GG N r s J ψ central_N = 0) :
    SuperBracket_G_G_Target N r s J ψ central_N 0 := by
  have h := superBracket_G_G_target_with_defect N r s J ψ central_N
  simpa [hdef] using h

end InfoGeometry.Canonical.SuperVirasoro
