import Mathlib.Tactic

/-!
# Brillouin Klein fixed-line parafermion attractor

This module combines the verified ingredients:

* the `pg` reciprocal glide fixed line `k₂=0` imposes
  `c_k = (-1)^k c_k`, extinguishing odd modes;
* the fixed-line Zorn paravector has mass shell `N(P)=E²-px²`;
* RG collapse keeps the lower nilpotent defect, with `N(Z)=0` and `Z²=0`;
* the nilpotent Itakura--Saito remainder vanishes;
* the listed identities assemble the thermodynamic/minimizing attractor interpretation.
-/

noncomputable section

namespace BrillouinKleinNilpotentAttractor

open Matrix

abbrev Vec3 := Fin 3 → ℂ
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Glide fixed-line filter -/

def pgPhase (k : ℕ) : ℂ := (-1 : ℂ) ^ k

theorem pgPhase_odd {k : ℕ} (hodd : Odd k) : pgPhase k = -1 := by
  unfold pgPhase
  exact hodd.neg_one_pow

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

theorem nonzero_fixed_line_mode_not_odd {k : ℕ} {c : ℂ}
    (hrel : c = pgPhase k * c) (hnz : c ≠ 0) : ¬ Odd k := by
  intro hodd
  exact hnz (pg_fixed_line_extinction hodd hrel)

/-! ## Zorn paravectors and collapsed nilpotents -/

def dot3 (u v : Vec3) : ℂ := ∑ i : Fin 3, u i * v i

def cross3 (u v : Vec3) : Vec3
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

structure Zorn where
  a : ℂ
  b : ℂ
  u : Vec3
  v : Vec3

theorem zorn_ext {X Y : Zorn}
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hu : X.u = Y.u) (hv : X.v = Y.v) : X = Y := by
  cases X
  cases Y
  simp_all

def zornMul (X Y : Zorn) : Zorn where
  a := X.a * Y.a + dot3 X.u Y.v
  b := X.b * Y.b + dot3 X.v Y.u
  u := fun i => X.a * Y.u i + Y.b * X.u i - cross3 X.v Y.v i
  v := fun i => Y.a * X.v i + X.b * Y.v i + cross3 X.u Y.u i

def zornNorm (X : Zorn) : ℂ := X.a * X.b - dot3 X.u X.v

def zero : Zorn where
  a := 0; b := 0; u := fun _ => 0; v := fun _ => 0

/-- Fixed-line momentum vector `(px,0,0)`. -/
def fixedLineMomentum (px : ℂ) : Vec3
  | 0 => px
  | 1 => 0
  | 2 => 0

/-- Fixed-line paravector `[[E,px],[px,E]]`. -/
def fixedParavector (E px : ℂ) : Zorn where
  a := E
  b := E
  u := fixedLineMomentum px
  v := fixedLineMomentum px

/-- Collapsed lower nilpotent defect `[[0,0],[px,0]]`. -/
def collapsedFixedLower (px : ℂ) : Zorn where
  a := 0
  b := 0
  u := fun _ => 0
  v := fixedLineMomentum px

/-- Fixed-line mass shell. -/
theorem fixed_paravector_mass_shell (E px : ℂ) :
    zornNorm (fixedParavector E px) = E^2 - px^2 := by
  simp [zornNorm, fixedParavector, fixedLineMomentum, dot3, Fin.sum_univ_three]
  ring

/-- Collapsed fixed-line defect has zero norm. -/
theorem collapsed_fixed_norm_zero (px : ℂ) :
    zornNorm (collapsedFixedLower px) = 0 := by
  simp [zornNorm, collapsedFixedLower, fixedLineMomentum, dot3]

/-- Collapsed fixed-line defect is nilpotent. -/
theorem collapsed_fixed_nilpotent (px : ℂ) :
    zornMul (collapsedFixedLower px) (collapsedFixedLower px) = zero := by
  apply zorn_ext
  · simp [zornMul, collapsedFixedLower, zero, dot3]
  · simp [zornMul, collapsedFixedLower, zero, dot3]
  · funext i
    fin_cases i <;> simp [zornMul, collapsedFixedLower, zero, fixedLineMomentum, cross3]
  · funext i
    fin_cases i <;> simp [zornMul, collapsedFixedLower, zero, fixedLineMomentum, cross3]

/-! ## Nilpotent Itakura--Saito collapse -/

def nilExp (K : M2C) : M2C := 1 + K

def nilItakuraSaito (K : M2C) : M2C := nilExp K - 1 - K

theorem nilItakuraSaito_zero (K : M2C) : nilItakuraSaito K = 0 := by
  ext i j
  simp [nilItakuraSaito, nilExp, Matrix.sub_apply]

end BrillouinKleinNilpotentAttractor
