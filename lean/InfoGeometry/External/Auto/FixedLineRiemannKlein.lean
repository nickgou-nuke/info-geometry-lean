import Mathlib.Tactic

/-!
# Fixed lines: Brillouin Klein glide axis and Riemann critical line

This module formalizes the structural parallel without claiming/proving RH.

* Spatial reciprocal glide: `(k₁,k₂) ↦ (k₁,-k₂)` has fixed locus `k₂=0`.
* The geometric scale reflection fixing the critical line is the anti-linear
  reflection `s=x+it ↦ 1-x+it` (equivalently `s ↦ 1-conj(s)`), whose fixed
  locus is `x=1/2`.
* `pg` glide phase extinguishes odd fixed-line Fourier modes.
* Nilpotent modes have zero truncated Itakura--Saito remainder.
-/

noncomputable section

namespace FixedLineRiemannKlein

open Matrix

/-! ## Spatial fixed line -/

/-- Reciprocal glide reflection. -/
def glideReflect (k : ℤ × ℤ) : ℤ × ℤ := (k.1, -k.2)

/-- The glide fixed locus is exactly `k₂=0`. -/
theorem glide_fixed_iff (k : ℤ × ℤ) : glideReflect k = k ↔ k.2 = 0 := by
  constructor
  · intro h
    have h2 : -k.2 = k.2 := congrArg Prod.snd h
    omega
  · intro h
    cases k with
    | mk k1 k2 =>
      simp [glideReflect] at h ⊢
      omega

/-! ## Critical line as scale-reflection fixed line -/

/-- Complex scale coordinate represented as real pair `(x,t) = Re(s), Im(s)`. -/
abbrev ScalePoint := ℝ × ℝ

/-- Anti-linear scale reflection `x+it ↦ 1-x+it`. -/
def scaleReflect (s : ScalePoint) : ScalePoint := (1 - s.1, s.2)

/-- Critical-line predicate `Re(s)=1/2`, represented as `2x=1`. -/
def criticalLine (s : ScalePoint) : Prop := 2 * s.1 = 1

/-- The scale reflection fixes exactly the critical line. -/
theorem scale_fixed_iff_critical (s : ScalePoint) : scaleReflect s = s ↔ criticalLine s := by
  constructor
  · intro h
    have hx : 1 - s.1 = s.1 := congrArg Prod.fst h
    unfold criticalLine
    linarith
  · intro h
    unfold criticalLine at h
    cases s with
    | mk x t =>
      simp [scaleReflect]
      linarith

/-! ## Verberck glide extinction -/

/-- The `pg` glide phase. -/
def pgPhase (k : ℕ) : ℂ := (-1 : ℂ) ^ k

/-- Odd momenta acquire phase `-1`. -/
theorem pgPhase_odd {k : ℕ} (hodd : Odd k) : pgPhase k = -1 := by
  simpa [pgPhase] using hodd.neg_one_pow

/-- Odd fixed-line Fourier coefficients vanish. -/
theorem pg_fixed_line_extinction {k : ℕ} {c : ℂ}
    (hodd : Odd k) (hrel : c = pgPhase k * c) : c = 0 := by
  rw [pgPhase_odd hodd] at hrel
  have hneg : c = -c := by simpa using hrel
  have hsub : c - (-c) = 0 := sub_eq_zero.mpr hneg
  have h2 : (2 : ℂ) * c = 0 := by
    calc
      (2 : ℂ) * c = c - (-c) := by ring
      _ = 0 := hsub
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Surviving nonzero fixed-line modes are not odd. -/
theorem surviving_mode_not_odd {k : ℕ} {c : ℂ}
    (hrel : c = pgPhase k * c) (hnz : c ≠ 0) : ¬ Odd k := by
  intro hodd
  apply hnz
  exact pg_fixed_line_extinction hodd hrel

/-! ## Nilpotent Itakura--Saito zero -/

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

def nilExp (K : M2C) : M2C := 1 + K

def nilItakuraSaito (K : M2C) : M2C := nilExp K - 1 - K

/-- The truncated nilpotent Itakura--Saito remainder vanishes. -/
theorem nilItakuraSaito_zero (K : M2C) : nilItakuraSaito K = 0 := by
  ext i j
  simp [nilItakuraSaito, nilExp, Matrix.sub_apply]

#check glide_fixed_iff
#check scale_fixed_iff_critical
#check pg_fixed_line_extinction
#check nilItakuraSaito_zero

end FixedLineRiemannKlein
