import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Verberck wallpaper Fourier coefficient rules

Digest source:
Bart Verberck, *Symmetry-Adapted Fourier Series for the Wallpaper Groups*,
Symmetry 4 (2012), 379--426.

The paper derives symmetry-adapted Fourier expansions for all 17 wallpaper
groups. Direct-space rotations/reflections/glides become constraints on the
reciprocal lattice coefficients. This file formalizes two core algebraic
mechanisms used repeatedly in the tables:

* the `p6` reciprocal-index rotation cycle
  `(k₁,k₂) ↦ (k₂,-k₁+k₂)` has order six;
* the `pg` nonsymmorphic glide contributes a phase `(-1)^k₁`, so on the fixed
  line `k₂=0`, odd `k₁` coefficients are forced to vanish.
-/

noncomputable section

namespace VerberckWallpaperFourier

/-- Integer Fourier-index pair. -/
abbrev KIndex := ℤ × ℤ

/-- The p6 reciprocal-index rotation from Verberck Eq. (28). -/
def p6R (k : KIndex) : KIndex := (k.2, -k.1 + k.2)

/-- The six-step p6 orbit from Verberck Eq. (30). -/
theorem p6_orbit_eq30 (k₁ k₂ : ℤ) :
    p6R (k₁, k₂) = (k₂, -k₁ + k₂) ∧
    p6R (p6R (k₁, k₂)) = (-k₁ + k₂, -k₁) ∧
    p6R (p6R (p6R (k₁, k₂))) = (-k₁, -k₂) ∧
    p6R (p6R (p6R (p6R (k₁, k₂)))) = (-k₂, k₁ - k₂) ∧
    p6R (p6R (p6R (p6R (p6R (k₁, k₂))))) = (k₁ - k₂, k₁) ∧
    p6R (p6R (p6R (p6R (p6R (p6R (k₁, k₂)))))) = (k₁, k₂) := by
  simp [p6R]
  omega

/-- If coefficients are invariant under the p6 index action, all six orbit coefficients agree. -/
theorem p6_coefficient_cycle
    (c : KIndex → ℂ) (h : ∀ k, c (p6R k) = c k) (k₁ k₂ : ℤ) :
    c (k₁, k₂) = c (k₂, -k₁ + k₂) ∧
    c (k₁, k₂) = c (-k₁ + k₂, -k₁) ∧
    c (k₁, k₂) = c (-k₁, -k₂) ∧
    c (k₁, k₂) = c (-k₂, k₁ - k₂) ∧
    c (k₁, k₂) = c (k₁ - k₂, k₁) := by
  have h1 : c (k₂, -k₁ + k₂) = c (k₁, k₂) := h (k₁, k₂)
  have h2 : c (-k₁ + k₂, -k₁) = c (k₂, -k₁ + k₂) := by
    simpa [p6R] using h (k₂, -k₁ + k₂)
  have h3 : c (-k₁, -k₂) = c (-k₁ + k₂, -k₁) := by
    simpa [p6R] using h (-k₁ + k₂, -k₁)
  have h4 : c (-k₂, k₁ - k₂) = c (-k₁, -k₂) := by
    simpa [p6R] using h (-k₁, -k₂)
  have h5 : c (k₁ - k₂, k₁) = c (-k₂, k₁ - k₂) := by
    simpa [p6R] using h (-k₂, k₁ - k₂)
  exact ⟨h1.symm, (h2.trans h1).symm, (h3.trans (h2.trans h1)).symm,
    (h4.trans (h3.trans (h2.trans h1))).symm,
    (h5.trans (h4.trans (h3.trans (h2.trans h1)))).symm⟩

/-- The `pg` glide phase for natural reciprocal index `k₁`: `(-1)^k₁`. -/
def pgPhase (k₁ : ℕ) : ℂ := (-1 : ℂ) ^ k₁

/-- The glide phase squares to one: the glide squared is a lattice translation. -/
theorem pgPhase_sq (k₁ : ℕ) : pgPhase k₁ * pgPhase k₁ = 1 := by
  unfold pgPhase
  rw [← pow_two, ← pow_mul]
  norm_num

/-- Odd powers of `-1` are `-1`. -/
theorem pgPhase_odd {k₁ : ℕ} (hodd : Odd k₁) : pgPhase k₁ = -1 := by
  unfold pgPhase
  exact hodd.neg_one_pow

/-- Even powers of `-1` are `+1`. -/
theorem pgPhase_even {k₁ : ℕ} (heven : Even k₁) : pgPhase k₁ = 1 := by
  unfold pgPhase
  exact heven.neg_one_pow

/-- Verberck pg fixed-line extinction: `c_{k₁,0}=0` for odd `k₁`. -/
theorem pg_fixed_line_extinction {k₁ : ℕ} {c : ℂ}
    (hodd : Odd k₁) (hrel : c = pgPhase k₁ * c) : c = 0 := by
  rw [pgPhase_odd hodd] at hrel
  have hneg : c = -c := by simpa using hrel
  have hsub : c - (-c) = 0 := sub_eq_zero.mpr hneg
  have h2 : (2 : ℂ) * c = 0 := by
    calc
      (2 : ℂ) * c = c - (-c) := by ring
      _ = 0 := hsub
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Combined synthesis of the Verberck Fourier mechanisms. -/
theorem verberck_wallpaper_fourier_synthesis :
    (∀ k₁ k₂ : ℤ,
      p6R (p6R (p6R (p6R (p6R (p6R (k₁, k₂)))))) = (k₁, k₂)) ∧
    (∀ k₁ : ℕ, pgPhase k₁ * pgPhase k₁ = 1) ∧
    (∀ k₁ : ℕ, Odd k₁ → pgPhase k₁ = -1) ∧
    (∀ {k₁ : ℕ} {c : ℂ}, Odd k₁ → c = pgPhase k₁ * c → c = 0) := by
  constructor
  · intro k₁ k₂
    exact (p6_orbit_eq30 k₁ k₂).2.2.2.2.2
  constructor
  · exact pgPhase_sq
  constructor
  · intro k₁ hodd
    exact pgPhase_odd hodd
  · intro k₁ c hodd hrel
    exact pg_fixed_line_extinction hodd hrel

#check p6_orbit_eq30
#check p6_coefficient_cycle
#check pgPhase_sq
#check pg_fixed_line_extinction
#check verberck_wallpaper_fourier_synthesis

end VerberckWallpaperFourier
