import Mathlib

noncomputable section

namespace InfoGeometry.Canonical.SuperVirasoro

open Finset

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Truncated supercurrent `G_r^N`. -/
def G_trunc (N r : ℤ) (J ψ : ℤ → Module.End 𝕜 V) : Module.End 𝕜 V :=
  Finset.sum (Icc (-N) N) (fun k => (J k) * (ψ (r - k)))

/-- Truncated bosonic stress part. -/
def L_bosonic_trunc (N n : ℤ) (J : ℤ → Module.End 𝕜 V) : Module.End 𝕜 V :=
  Finset.sum (Icc (-N) N) (fun k => (J k) * (J (n - k)))

/-- Truncated fermionic stress part. -/
def L_fermionic_trunc (N n : ℤ) (ψ : ℤ → Module.End 𝕜 V) : Module.End 𝕜 V :=
  Finset.sum (Icc (-N) N) (fun k => (k : 𝕜) • ((ψ (-k)) * (ψ (k + n))))

/-- Total truncated stress tensor. -/
def L_trunc (N n : ℤ) (J ψ : ℤ → Module.End 𝕜 V) : Module.End 𝕜 V :=
  L_bosonic_trunc N n J + L_fermionic_trunc N n ψ

/-- Step-3 target for `[L,G]`. -/
def SuperBracket_L_G_Target
    (N m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V) (defect : Module.End 𝕜 V) : Prop :=
  (L_trunc N m J ψ) * (G_trunc N r J ψ) - (G_trunc N r J ψ) * (L_trunc N m J ψ)
    = ((m : 𝕜) / 2 - (r : 𝕜)) • G_trunc N (m + r) J ψ + defect

/-- Step-3 target for `{G,G}`. -/
def SuperBracket_G_G_Target
    (N r s : ℤ) (J ψ : ℤ → Module.End 𝕜 V)
    (central_N : ℤ → ℤ → 𝕜) (defect : Module.End 𝕜 V) : Prop :=
  (G_trunc N r J ψ) * (G_trunc N s J ψ) + (G_trunc N s J ψ) * (G_trunc N r J ψ)
    = (2 : 𝕜) • L_trunc N (r + s) J ψ + (central_N r s) • (1 : Module.End 𝕜 V) + defect

/-- Explicit finite defect for `[L,G]`. -/
def defect_LG
    (N m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V) : Module.End 𝕜 V :=
  ((L_trunc N m J ψ) * (G_trunc N r J ψ) - (G_trunc N r J ψ) * (L_trunc N m J ψ))
    - ((m : 𝕜) / 2 - (r : 𝕜)) • G_trunc N (m + r) J ψ

/-- Explicit finite defect for `{G,G}`. -/
def defect_GG
    (N r s : ℤ) (J ψ : ℤ → Module.End 𝕜 V)
    (central_N : ℤ → ℤ → 𝕜) : Module.End 𝕜 V :=
  (G_trunc N r J ψ) * (G_trunc N s J ψ) + (G_trunc N s J ψ) * (G_trunc N r J ψ)
    - ((2 : 𝕜) • L_trunc N (r + s) J ψ + (central_N r s) • (1 : Module.End 𝕜 V))

/-- Finite evaluation of `[L,G]` with explicit defect. -/
theorem superBracket_L_G_target_with_defect
    (N m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V) :
    SuperBracket_L_G_Target N m r J ψ (defect_LG N m r J ψ) := by
  unfold SuperBracket_L_G_Target defect_LG
  abel_nf

/-- Finite evaluation of `{G,G}` with explicit defect. -/
theorem superBracket_G_G_target_with_defect
    (N r s : ℤ) (J ψ : ℤ → Module.End 𝕜 V) (central_N : ℤ → ℤ → 𝕜) :
    SuperBracket_G_G_Target N r s J ψ central_N (defect_GG N r s J ψ central_N) := by
  unfold SuperBracket_G_G_Target defect_GG
  abel_nf

end InfoGeometry.Canonical.SuperVirasoro

