import Mathlib.Tactic

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

/- Step-3 finite targets for `[L,G]` and `{G,G}`. -/
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
theorem superBracket_L_G_eq_with_defect
    (N m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V) :
    (L_trunc N m J ψ) * (G_trunc N r J ψ) - (G_trunc N r J ψ) * (L_trunc N m J ψ)
      = ((m : 𝕜) / 2 - (r : 𝕜)) • G_trunc N (m + r) J ψ + defect_LG N m r J ψ := by
  unfold defect_LG
  abel_nf

/-- Finite evaluation of `{G,G}` with explicit defect. -/
theorem superBracket_G_G_eq_with_defect
    (N r s : ℤ) (J ψ : ℤ → Module.End 𝕜 V) (central_N : ℤ → ℤ → 𝕜) :
    (G_trunc N r J ψ) * (G_trunc N s J ψ) + (G_trunc N s J ψ) * (G_trunc N r J ψ)
      = (2 : 𝕜) • L_trunc N (r + s) J ψ + (central_N r s) • (1 : Module.End 𝕜 V)
        + defect_GG N r s J ψ central_N := by
  unfold defect_GG
  abel_nf

/--
Stabilization readback for `[L,G]` on a fixed vector:
if the defect eventually vanishes on `v` along `N → +∞`, then the bracket
identity is eventually exact on `v`.
-/
theorem eventually_exact_LG_on_vector
    (m r : ℤ) (J ψ : ℤ → Module.End 𝕜 V) (v : V)
    (hdef :
      ∀ᶠ N : ℤ in Filter.atTop,
        defect_LG N m r J ψ v = 0) :
    ∀ᶠ N : ℤ in Filter.atTop,
      (((L_trunc N m J ψ) * (G_trunc N r J ψ) - (G_trunc N r J ψ) * (L_trunc N m J ψ)) v)
        =
      ((((m : 𝕜) / 2 - (r : 𝕜)) • G_trunc N (m + r) J ψ) v) := by
  filter_upwards [hdef] with N hN
  have h := superBracket_L_G_eq_with_defect (N := N) (m := m) (r := r) J ψ
  have hv := congrArg (fun T : Module.End 𝕜 V => T v) h
  simpa [hN, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv

/--
Stabilization readback for `{G,G}` on a fixed vector:
if the defect eventually vanishes on `v` along `N → +∞`, then the
anticommutator identity is eventually exact on `v`.
-/
theorem eventually_exact_GG_on_vector
    (r s : ℤ) (J ψ : ℤ → Module.End 𝕜 V) (central_N : ℤ → ℤ → 𝕜) (v : V)
    (hdef :
      ∀ᶠ N : ℤ in Filter.atTop,
        defect_GG N r s J ψ central_N v = 0) :
    ∀ᶠ N : ℤ in Filter.atTop,
      (((G_trunc N r J ψ) * (G_trunc N s J ψ) + (G_trunc N s J ψ) * (G_trunc N r J ψ)) v)
        =
      (((((2 : 𝕜) • L_trunc N (r + s) J ψ) + (central_N r s) • (1 : Module.End 𝕜 V)) v)) := by
  filter_upwards [hdef] with N hN
  have h := superBracket_G_G_eq_with_defect (N := N) (r := r) (s := s) J ψ central_N
  have hv := congrArg (fun T : Module.End 𝕜 V => T v) h
  -- use the supplied eventual vanishing of the concrete defect action
  -- to remove the residual term on this vector
  simpa [hN, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv

end InfoGeometry.Canonical.SuperVirasoro
