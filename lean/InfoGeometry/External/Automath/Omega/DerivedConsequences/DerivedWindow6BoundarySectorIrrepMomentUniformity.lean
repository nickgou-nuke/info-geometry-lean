import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.DerivedConsequences.DerivedWindow6BoundarySectorGroupalgebraIsotypy

namespace Omega.DerivedConsequences

/-- The common irreducible-count data carried by every boundary parity sector. -/
def derived_window6_boundary_sector_irrep_moment_uniformity_irrepCount (_χ : Fin 8) : ℕ :=
  2 ^ 5 * 3 ^ 4 * 5 ^ 9

/-- The common second moment equals the interior group order from the sector-isotypy theorem. -/
def derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment (_χ : Fin 8) : ℕ :=
  derived_window6_boundary_sector_groupalgebra_isotypy_interiorGroupOrder

/-- Paper label: `thm:derived-window6-boundary-sector-irrep-moment-uniformity`.
Each of the eight boundary parity sectors has the same irreducible-count and second-moment data,
namely the common interior algebra values already identified by sector isotypy; consequently the
Plancherel mass of every sector is exactly `1 / 8`. -/
theorem paper_derived_window6_boundary_sector_irrep_moment_uniformity :
    (∀ χ : Fin 8,
      derived_window6_boundary_sector_irrep_moment_uniformity_irrepCount χ =
        2 ^ 5 * 3 ^ 4 * 5 ^ 9 ∧
        derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment χ =
          Nat.factorial 2 ^ 5 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9) ∧
      (∀ χ ψ : Fin 8,
        derived_window6_boundary_sector_irrep_moment_uniformity_irrepCount χ =
          derived_window6_boundary_sector_irrep_moment_uniformity_irrepCount ψ ∧
          derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment χ =
            derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment ψ) ∧
      (∀ χ : Fin 8,
        derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount *
            derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment χ =
          derived_window6_boundary_sector_groupalgebra_isotypy_totalGroupOrder) ∧
      (∀ χ : Fin 8,
        (derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment χ : ℚ) /
            derived_window6_boundary_sector_groupalgebra_isotypy_totalGroupOrder =
          1 / 8) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro χ
    refine ⟨rfl, ?_⟩
    norm_num [derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment,
      derived_window6_boundary_sector_groupalgebra_isotypy_interiorGroupOrder]
  · intro χ ψ
    exact ⟨rfl, rfl⟩
  · intro χ
    simpa [derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment] using
      (show derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount *
          derived_window6_boundary_sector_groupalgebra_isotypy_interiorGroupOrder =
        derived_window6_boundary_sector_groupalgebra_isotypy_totalGroupOrder by
        native_decide)
  · intro χ
    simpa [derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment] using
      (show (derived_window6_boundary_sector_groupalgebra_isotypy_interiorGroupOrder : ℚ) /
          derived_window6_boundary_sector_groupalgebra_isotypy_totalGroupOrder = 1 / 8 by
        native_decide)

end Omega.DerivedConsequences
