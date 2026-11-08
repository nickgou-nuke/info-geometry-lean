import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CayleyPeirceKleinFourBridge

/-!
# Cayley/Hodge action on the parity sectors

This owner records the concrete permutation of the four coordinate-sector
projections by the Cayley/Hodge involutions.  It is an algebraic intertwining
packet only: it does not identify these sectors with physical observables.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyDualityParityActionBridge

open InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
open InfoGeometry.Canonical.CayleyPeirceKleinFourBridge

abbrev Coord :=
  InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge.Coord

theorem proj0_mul_cayleyConj_eq_cayleyConj_mul_proj3 :
    proj0 * cayleyConj = cayleyConj * proj3 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj0, proj3, cayleyConj]

theorem proj3_mul_cayleyConj_eq_cayleyConj_mul_proj0 :
    proj3 * cayleyConj = cayleyConj * proj0 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj0, proj3, cayleyConj]

theorem proj1_mul_cayleyConj_eq_cayleyConj_mul_proj1 :
    proj1 * cayleyConj = cayleyConj * proj1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj1, cayleyConj]

theorem proj2_mul_cayleyConj_eq_cayleyConj_mul_proj2 :
    proj2 * cayleyConj = cayleyConj * proj2 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj2, cayleyConj]

theorem proj0_mul_hodgeStar_eq_hodgeStar_mul_proj3 :
    proj0 * hodgeStar = hodgeStar * proj3 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj0, proj3, hodgeStar]

theorem proj3_mul_hodgeStar_eq_hodgeStar_mul_proj0 :
    proj3 * hodgeStar = hodgeStar * proj0 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj0, proj3, hodgeStar]

theorem proj1_mul_hodgeStar_eq_hodgeStar_mul_proj2 :
    proj1 * hodgeStar = hodgeStar * proj2 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj1, proj2, hodgeStar]

theorem proj2_mul_hodgeStar_eq_hodgeStar_mul_proj1 :
    proj2 * hodgeStar = hodgeStar * proj1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj1, proj2, hodgeStar]

theorem proj0_mul_middleExchangeFlip_eq_middleExchangeFlip_mul_proj0 :
    proj0 * middleExchangeFlip = middleExchangeFlip * proj0 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj0, middleExchangeFlip]

theorem proj3_mul_middleExchangeFlip_eq_middleExchangeFlip_mul_proj3 :
    proj3 * middleExchangeFlip = middleExchangeFlip * proj3 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj3, middleExchangeFlip]

theorem proj1_mul_middleExchangeFlip_eq_middleExchangeFlip_mul_proj2 :
    proj1 * middleExchangeFlip = middleExchangeFlip * proj2 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj1, proj2, middleExchangeFlip]

theorem proj2_mul_middleExchangeFlip_eq_middleExchangeFlip_mul_proj1 :
    proj2 * middleExchangeFlip = middleExchangeFlip * proj1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [proj1, proj2, middleExchangeFlip]

theorem cayleyConj_maps_E_plus_plus_to_E_minus_minus
    {x : Coord} (hx : x ∈ E_plus_plus) :
    cayleyConj x ∈ E_minus_minus := by
  rw [mem_E_plus_plus_iff] at hx
  rw [mem_E_minus_minus_iff]
  rcases hx with ⟨hx₁, hx₂, hx₃⟩
  exact ⟨by simp [cayleyConj, hx₃], by simp [cayleyConj, hx₁],
    by simp [cayleyConj, hx₂]⟩

theorem cayleyConj_maps_E_minus_minus_to_E_plus_plus
    {x : Coord} (hx : x ∈ E_minus_minus) :
    cayleyConj x ∈ E_plus_plus := by
  rw [mem_E_minus_minus_iff] at hx
  rw [mem_E_plus_plus_iff]
  rcases hx with ⟨hx₀, hx₁, hx₂⟩
  exact ⟨by simp [cayleyConj, hx₁], by simp [cayleyConj, hx₂],
    by simp [cayleyConj, hx₀]⟩

theorem cayleyConj_preserves_E_plus_minus
    {x : Coord} (hx : x ∈ E_plus_minus) :
    cayleyConj x ∈ E_plus_minus := by
  rw [mem_E_plus_minus_iff] at hx
  rw [mem_E_plus_minus_iff]
  rcases hx with ⟨hx₀, hx₂, hx₃⟩
  exact ⟨by simp [cayleyConj, hx₃], by simp [cayleyConj, hx₂],
    by simp [cayleyConj, hx₀]⟩

theorem cayleyConj_preserves_E_minus_plus
    {x : Coord} (hx : x ∈ E_minus_plus) :
    cayleyConj x ∈ E_minus_plus := by
  rw [mem_E_minus_plus_iff] at hx
  rw [mem_E_minus_plus_iff]
  rcases hx with ⟨hx₀, hx₁, hx₃⟩
  exact ⟨by simp [cayleyConj, hx₃], by simp [cayleyConj, hx₁],
    by simp [cayleyConj, hx₀]⟩

theorem hodgeStar_maps_E_plus_plus_to_E_minus_minus
    {x : Coord} (hx : x ∈ E_plus_plus) :
    hodgeStar x ∈ E_minus_minus := by
  rw [mem_E_plus_plus_iff] at hx
  rw [mem_E_minus_minus_iff]
  rcases hx with ⟨hx₁, hx₂, hx₃⟩
  exact ⟨by simp [hodgeStar, hx₃], by simp [hodgeStar, hx₂],
    by simp [hodgeStar, hx₁]⟩

theorem hodgeStar_maps_E_minus_minus_to_E_plus_plus
    {x : Coord} (hx : x ∈ E_minus_minus) :
    hodgeStar x ∈ E_plus_plus := by
  rw [mem_E_minus_minus_iff] at hx
  rw [mem_E_plus_plus_iff]
  rcases hx with ⟨hx₀, hx₁, hx₂⟩
  exact ⟨by simp [hodgeStar, hx₂], by simp [hodgeStar, hx₁],
    by simp [hodgeStar, hx₀]⟩

theorem hodgeStar_maps_E_plus_minus_to_E_minus_plus
    {x : Coord} (hx : x ∈ E_plus_minus) :
    hodgeStar x ∈ E_minus_plus := by
  rw [mem_E_plus_minus_iff] at hx
  rw [mem_E_minus_plus_iff]
  rcases hx with ⟨hx₀, hx₂, hx₃⟩
  exact ⟨by simp [hodgeStar, hx₃], by simp [hodgeStar, hx₂],
    by simp [hodgeStar, hx₀]⟩

theorem hodgeStar_maps_E_minus_plus_to_E_plus_minus
    {x : Coord} (hx : x ∈ E_minus_plus) :
    hodgeStar x ∈ E_plus_minus := by
  rw [mem_E_minus_plus_iff] at hx
  rw [mem_E_plus_minus_iff]
  rcases hx with ⟨hx₀, hx₁, hx₃⟩
  exact ⟨by simp [hodgeStar, hx₃], by simp [hodgeStar, hx₁],
    by simp [hodgeStar, hx₀]⟩

theorem middleExchangeFlip_preserves_E_plus_plus
    {x : Coord} (hx : x ∈ E_plus_plus) :
    middleExchangeFlip x ∈ E_plus_plus := by
  rw [mem_E_plus_plus_iff] at hx
  rw [mem_E_plus_plus_iff]
  rcases hx with ⟨hx₁, hx₂, hx₃⟩
  exact ⟨by simp [middleExchangeFlip, hx₂], by simp [middleExchangeFlip, hx₁],
    by simp [middleExchangeFlip, hx₃]⟩

theorem middleExchangeFlip_preserves_E_minus_minus
    {x : Coord} (hx : x ∈ E_minus_minus) :
    middleExchangeFlip x ∈ E_minus_minus := by
  rw [mem_E_minus_minus_iff] at hx
  rw [mem_E_minus_minus_iff]
  rcases hx with ⟨hx₀, hx₁, hx₂⟩
  exact ⟨by simp [middleExchangeFlip, hx₀], by simp [middleExchangeFlip, hx₂],
    by simp [middleExchangeFlip, hx₁]⟩

theorem middleExchangeFlip_maps_E_plus_minus_to_E_minus_plus
    {x : Coord} (hx : x ∈ E_plus_minus) :
    middleExchangeFlip x ∈ E_minus_plus := by
  rw [mem_E_plus_minus_iff] at hx
  rw [mem_E_minus_plus_iff]
  rcases hx with ⟨hx₀, hx₂, hx₃⟩
  exact ⟨by simp [middleExchangeFlip, hx₀], by simp [middleExchangeFlip, hx₂],
    by simp [middleExchangeFlip, hx₃]⟩

theorem middleExchangeFlip_maps_E_minus_plus_to_E_plus_minus
    {x : Coord} (hx : x ∈ E_minus_plus) :
    middleExchangeFlip x ∈ E_plus_minus := by
  rw [mem_E_minus_plus_iff] at hx
  rw [mem_E_plus_minus_iff]
  rcases hx with ⟨hx₀, hx₁, hx₃⟩
  exact ⟨by simp [middleExchangeFlip, hx₀], by simp [middleExchangeFlip, hx₁],
    by simp [middleExchangeFlip, hx₃]⟩

end InfoGeometry.Canonical.CayleyDualityParityActionBridge
