/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.SarnakLocalCertification

/-! # Finite zero counts under critical reflection

Symmetry gives equal counts on the two sides, not confinement. All counts
below concern distinct points in explicitly finite reflection-invariant sets.
-/

noncomputable section
namespace InfoGeometry.Arithmetic.SarnakLocalCertification

open scoped Classical

/-- Reflection bijects the two open half-planes in a finite invariant set. -/
theorem reflection_card_left_eq_right (s : Finset ℂ)
    (hs : ∀ z ∈ s, critical_reflection z ∈ s) :
    (s.filter fun z => z.re < 1 / 2).card =
      (s.filter fun z => 1 / 2 < z.re).card := by
  classical
  apply Finset.card_bij (fun z _ => critical_reflection z)
  · intro z hz
    obtain ⟨hz, hleft⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hs z hz, ?_⟩
    simp only [critical_reflection, Complex.sub_re, Complex.one_re,
      Complex.star_def, Complex.conj_re]
    linarith
  · intro z hz w hw h
    exact critical_reflection_involutive.injective h
  · intro z hz
    obtain ⟨hz, hright⟩ := Finset.mem_filter.mp hz
    refine ⟨critical_reflection z, Finset.mem_filter.mpr ⟨hs z hz, ?_⟩,
      critical_reflection_involutive z⟩
    simp only [critical_reflection, Complex.sub_re, Complex.one_re,
      Complex.star_def, Complex.conj_re]
    linarith

/-- The off-line points contribute an even summand to the total count. -/
theorem reflection_card_decomposition (s : Finset ℂ)
    (hs : ∀ z ∈ s, critical_reflection z ∈ s) :
    s.card = (s.filter fun z => z.re = 1 / 2).card +
      2 * (s.filter fun z => z.re < 1 / 2).card := by
  classical
  have hsplit := s.card_filter_add_card_filter_not (fun z => z.re < 1 / 2)
  have hrest := (s.filter fun z => ¬z.re < 1 / 2).card_filter_add_card_filter_not
    (fun z => z.re = 1 / 2)
  have heq : (s.filter fun z => ¬z.re < 1 / 2).filter (fun z => z.re = 1 / 2) =
      s.filter (fun z => z.re = 1 / 2) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hz, h⟩
      exact ⟨⟨hz, by rw [h]; exact lt_irrefl _⟩, h⟩
  have hgt : (s.filter fun z => ¬z.re < 1 / 2).filter (fun z => ¬z.re = 1 / 2) =
      s.filter (fun z => 1 / 2 < z.re) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, hle⟩, hne⟩
      exact ⟨hz, lt_of_le_of_ne (le_of_not_gt hle) (Ne.symm hne)⟩
    · rintro ⟨hz, hgt⟩
      exact ⟨⟨hz, not_lt_of_ge hgt.le⟩, ne_of_gt hgt⟩
  rw [heq, hgt, ← reflection_card_left_eq_right s hs] at hrest
  omega

/-- An odd finite invariant set has a point fixed by critical reflection. -/
theorem reflection_exists_on_line_of_odd_card (s : Finset ℂ)
    (hs : ∀ z ∈ s, critical_reflection z ∈ s) (hodd : Odd s.card) :
    ∃ z ∈ s, z.re = 1 / 2 := by
  classical
  have hc := reflection_card_decomposition s hs
  have hpos : 0 < (s.filter fun z => z.re = 1 / 2).card := by
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  exact ⟨z, (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩

/-- The zero filter inherits reflection closure from the region and function. -/
theorem zero_filter_reflection_closed {f : ℂ → ℂ} [RiemannSymmetric f]
    (s : Finset ℂ) (hs : ∀ z ∈ s, critical_reflection z ∈ s) :
    ∀ z ∈ s.filter (fun z => f z = 0),
      critical_reflection z ∈ s.filter (fun z => f z = 0) := by
  intro z hz
  obtain ⟨hz, hzero⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr
    ⟨hs z hz, (RiemannSymmetric.zero_reflection z).mp hzero⟩

/-- Odd cardinality of a finite symmetric zero set certifies an on-line zero. -/
theorem exists_zero_on_line_of_odd_count {f : ℂ → ℂ} [RiemannSymmetric f]
    (s : Finset ℂ) (hs : ∀ z ∈ s, critical_reflection z ∈ s)
    (hodd : Odd (s.filter fun z => f z = 0).card) :
    ∃ z ∈ s, f z = 0 ∧ z.re = 1 / 2 := by
  obtain ⟨z, hz, hline⟩ := reflection_exists_on_line_of_odd_card _
    (zero_filter_reflection_closed s hs) hodd
  exact ⟨z, (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2, hline⟩

end InfoGeometry.Arithmetic.SarnakLocalCertification
