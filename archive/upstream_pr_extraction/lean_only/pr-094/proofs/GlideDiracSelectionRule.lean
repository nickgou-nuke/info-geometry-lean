import Mathlib

/-!
# Glide Fourier extinctions as Dirac--Mellin scale selection rules

This module couples Verberck's `pg` fixed-axis extinction with the
Fourier--Mellin Dirac determinant on the same fixed line.

On the glide axis `k₂=0`:

* Verberck: `cₖ = (-1)^k cₖ`, so odd `k` forces `cₖ=0`.
* Dirac--Mellin: `det D(s,k,0)=-(s²-k²)`, so zero modes sit at `s=±k`.

Therefore odd fixed-axis scale poles are extinguished by the nonsymmorphic
glide selection rule.
-/

noncomputable section

namespace GlideDiracSelectionRule

/-- The pg glide phase `(-1)^k`. -/
def pgPhase (k : ℕ) : ℂ := (-1 : ℂ) ^ k

/-- Odd powers give the nontrivial glide phase. -/
theorem pgPhase_odd {k : ℕ} (hodd : Odd k) : pgPhase k = -1 := by
  simpa [pgPhase] using hodd.neg_one_pow

/-- Even powers give the trivial glide phase. -/
theorem pgPhase_even {k : ℕ} (heven : Even k) : pgPhase k = 1 := by
  simpa [pgPhase] using heven.neg_one_pow

/-- Glide fixed-line extinction: odd `k` coefficients must vanish. -/
theorem pg_fixed_axis_extinction {k : ℕ} {c : ℂ}
    (hodd : Odd k) (hrel : c = pgPhase k * c) : c = 0 := by
  rw [pgPhase_odd hodd] at hrel
  have hneg : c = -c := by simpa using hrel
  have hsub : c - (-c) = 0 := sub_eq_zero.mpr hneg
  have h2 : (2 : ℂ) * c = 0 := by
    calc
      (2 : ℂ) * c = c - (-c) := by ring
      _ = 0 := hsub
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Fixed-axis Dirac--Mellin determinant polynomial, `det D(s,k,0)`. -/
def fixedAxisDiracDet (s : ℂ) (k : ℕ) : ℂ := -(s^2 - (k : ℂ)^2)

/-- The fixed-axis zero-mode equation is the scale pole equation `s²=k²`. -/
theorem fixedAxis_zero_mode_iff (s : ℂ) (k : ℕ) :
    fixedAxisDiracDet s k = 0 ↔ s^2 = (k : ℂ)^2 := by
  unfold fixedAxisDiracDet
  constructor
  · intro h
    have h' : s^2 - (k : ℂ)^2 = 0 := neg_eq_zero.mp h
    exact sub_eq_zero.mp h'
  · intro h
    rw [h]
    simp

/-- Positive branch of the scale pole: `s=k`. -/
theorem fixedAxis_positive_pole (k : ℕ) : fixedAxisDiracDet (k : ℂ) k = 0 := by
  rw [fixedAxis_zero_mode_iff]

/-- Negative branch of the scale pole: `s=-k`. -/
theorem fixedAxis_negative_pole (k : ℕ) : fixedAxisDiracDet (-(k : ℂ)) k = 0 := by
  rw [fixedAxis_zero_mode_iff]
  ring

/-- A fixed-axis Fourier/Dirac mode. -/
structure GlideDiracMode where
  k : ℕ
  coeff : ℂ
  glide_relation : coeff = pgPhase k * coeff
  scale : ℂ
  zero_mode : fixedAxisDiracDet scale k = 0

/-- Odd glide-axis modes are extinguished. -/
theorem odd_mode_extinguished (M : GlideDiracMode) (hodd : Odd M.k) :
    M.coeff = 0 :=
  pg_fixed_axis_extinction hodd M.glide_relation

/-- Any nonzero fixed-axis glide mode cannot have odd momentum. -/
theorem nonzero_mode_not_odd (M : GlideDiracMode) (hnz : M.coeff ≠ 0) :
    ¬ Odd M.k := by
  intro hodd
  have hzero : M.coeff = 0 := odd_mode_extinguished M hodd
  contradiction

/-- Odd positive scale poles are killed by the glide Fourier coefficient. -/
theorem odd_positive_pole_extinguished {k : ℕ} {c : ℂ}
    (hodd : Odd k) (hrel : c = pgPhase k * c) :
    fixedAxisDiracDet (k : ℂ) k = 0 ∧ c = 0 := by
  refine ⟨?_, ?_⟩
  · rw [fixedAxis_zero_mode_iff]
  · exact pg_fixed_axis_extinction hodd hrel

/-- Odd negative scale poles are killed by the glide Fourier coefficient. -/
theorem odd_negative_pole_extinguished {k : ℕ} {c : ℂ}
    (hodd : Odd k) (hrel : c = pgPhase k * c) :
    fixedAxisDiracDet (-(k : ℂ)) k = 0 ∧ c = 0 := by
  refine ⟨?_, ?_⟩
  · rw [fixedAxis_zero_mode_iff]
    ring
  · exact pg_fixed_axis_extinction hodd hrel

/-- Main synthesis: nonsymmorphic glide phases impose a holographic scale filter. -/
theorem glide_dirac_selection_rule_synthesis :
    (∀ {k : ℕ} {c : ℂ}, Odd k → c = pgPhase k * c → c = 0) ∧
    (∀ s : ℂ, ∀ k : ℕ, fixedAxisDiracDet s k = 0 ↔ s^2 = (k : ℂ)^2) ∧
    (∀ k : ℕ, fixedAxisDiracDet (k : ℂ) k = 0) ∧
    (∀ k : ℕ, fixedAxisDiracDet (-(k : ℂ)) k = 0) ∧
    (∀ M : GlideDiracMode, M.coeff ≠ 0 → ¬ Odd M.k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k c hodd hrel
    exact pg_fixed_axis_extinction hodd hrel
  · intro s k
    exact fixedAxis_zero_mode_iff s k
  · intro k
    exact fixedAxis_positive_pole k
  · intro k
    exact fixedAxis_negative_pole k
  · intro M hnz
    exact nonzero_mode_not_odd M hnz

#check pg_fixed_axis_extinction
#check fixedAxis_zero_mode_iff
#check odd_mode_extinguished
#check nonzero_mode_not_odd
#check odd_positive_pole_extinguished
#check glide_dirac_selection_rule_synthesis

end GlideDiracSelectionRule
