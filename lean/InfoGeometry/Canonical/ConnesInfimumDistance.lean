/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CuntzConnesSpectralDistance

/-!
# Connes distance as an infimum of admissible bounds

The placeholder-bearing `UHFCantorSpectralTriple` stash lane defined the
finite-stage distance as `sSup {d | StateDistanceBound … d}`.  That bound set
is upward closed, hence unbounded above in `ℝ`, so `sSup` returns a junk value
and the claimed metric axioms are not meaningful.  Here the correct definition
uses `sInf` of the same bound set, and the metric axioms are proved from the
owner's `distance_bound_symmetry`, `distance_bound_triangle`, and
`distance_bound_self`.  The triangle axiom needs the bound sets to be nonempty
(explicit hypothesis) — without a finite upper bound there is no genuine
distance.  No proof hole and no `sorry`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConnesInfimumDistance

open InfoGeometry.Canonical.CuntzConnesSpectralDistance

variable {A : Type*} [NormedRing A]

/-- The Connes distance as the infimum of admissible uniform bounds. -/
def connesInfDistance (D : A) (μ ν : A → ℝ) : ℝ :=
  sInf {d : ℝ | StateDistanceBound D μ ν d}

private def bounds (D : A) (μ ν : A → ℝ) : Set ℝ :=
  {d : ℝ | StateDistanceBound D μ ν d}

private theorem bounds_nonneg (D : A) (μ ν : A → ℝ) :
    ∀ d ∈ bounds D μ ν, 0 ≤ d := by
  intro d hd
  exact hd.2

/-- Nonnegativity of the infimum distance. -/
theorem connesInfDistance_nonneg (D : A) (μ ν : A → ℝ) :
    0 ≤ connesInfDistance D μ ν := by
  by_cases hne : (bounds D μ ν).Nonempty
  · exact le_csInf hne (bounds_nonneg D μ ν)
  · have hempty : bounds D μ ν = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hset : {d : ℝ | StateDistanceBound D μ ν d} = ∅ := by
      simpa [bounds] using hempty
    unfold connesInfDistance
    rw [hset]
    simp

/-- The distance vanishes on identical states. -/
theorem connesInfDistance_self (D : A) (μ : A → ℝ) :
    connesInfDistance D μ μ = 0 := by
  have hne : (bounds D μ μ).Nonempty := ⟨0, distance_bound_self D μ⟩
  apply le_antisymm
  · exact csInf_le ⟨0, bounds_nonneg D μ μ⟩ (distance_bound_self D μ)
  · exact le_csInf hne (bounds_nonneg D μ μ)

/-- Symmetry of the infimum distance. -/
theorem connesInfDistance_symm (D : A) (μ ν : A → ℝ) :
    connesInfDistance D μ ν = connesInfDistance D ν μ := by
  unfold connesInfDistance
  congr 1
  ext d
  constructor
  · intro h
    exact distance_bound_symmetry D μ ν d h
  · intro h
    exact distance_bound_symmetry D ν μ d h

/-- Triangle inequality for the infimum distance, assuming admissible bounds
exist for all three pairs. -/
theorem connesInfDistance_triangle (D : A) (μ ν ρ : A → ℝ)
    (hμν : (bounds D μ ν).Nonempty)
    (hνρ : (bounds D ν ρ).Nonempty)
    (hμρ : (bounds D μ ρ).Nonempty) :
    connesInfDistance D μ ρ ≤ connesInfDistance D μ ν + connesInfDistance D ν ρ := by
  unfold connesInfDistance
  have hb_lower : BddBelow (bounds D μ ρ) := ⟨0, bounds_nonneg D μ ρ⟩
  have hfix : ∀ d₂ ∈ bounds D ν ρ,
      sInf (bounds D μ ρ) - d₂ ≤ sInf (bounds D μ ν) := by
    intro d₂ hd₂
    apply le_csInf hμν
    intro d₁ hd₁
    have hsum : d₁ + d₂ ∈ bounds D μ ρ :=
      distance_bound_triangle D μ ν ρ d₁ d₂ hd₁ hd₂
    have hle : sInf (bounds D μ ρ) ≤ d₁ + d₂ := csInf_le hb_lower hsum
    linarith
  have hfix' : ∀ d₂ ∈ bounds D ν ρ,
      sInf (bounds D μ ρ) - sInf (bounds D μ ν) ≤ d₂ := by
    intro d₂ hd₂
    have := hfix d₂ hd₂
    linarith
  have hfinal : sInf (bounds D μ ρ) - sInf (bounds D μ ν) ≤
      sInf (bounds D ν ρ) := le_csInf hνρ hfix'
  change sInf (bounds D μ ρ) ≤ sInf (bounds D μ ν) + sInf (bounds D ν ρ)
  linarith

end InfoGeometry.Canonical.ConnesInfimumDistance
