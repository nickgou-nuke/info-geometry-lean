import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Normed.Module.Basic
import InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

/-!
# InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint

Symmetric counterpart of the topological endpoint limit argument.
-/

namespace InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint

open Set Filter Topology
open InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint
open InfoGeometry.Analysis.AsanoMobiusPole
open InfoGeometry.Canonical.LeeYangAsanoNativeCore

/--
Right-pole inclusion from boundedness of `K₁` (symmetric to left-pole theorem).
-/
theorem asano_right_pole_in_K2
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK2_closed : IsClosed K2)
    (hK1_bdd : Bornology.IsBounded K1)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (-B / D) ∈ K2 := by
  by_contra h_notin
  let p := -B / D
  have hp_nhds : K2ᶜ ∈ nhds p := (isOpen_compl_iff.mpr hK2_closed).mem_nhds h_notin
  have hp_punctured : K2ᶜ ∈ nhdsWithin p {p}ᶜ :=
    mem_nhdsWithin_of_mem_nhds hp_nhds
  have hroot_mem :
      ∀ᶠ z in nhdsWithin p {p}ᶜ, asanoRootMap A C B D z ∈ K1 := by
    filter_upwards [hp_punctured, self_mem_nhdsWithin] with z hz_notin hz_neq
    have h_denom : B + D * z ≠ 0 := by
      exact denominator_ne_zero_off_pole hD (by simpa [p, neg_div] using hz_neq)
    by_contra hroot_notin
    apply h_zerofree (asanoRootMap A C B D z) z hroot_notin hz_notin
    have hzero :
        asanoPhi A C B D z (asanoRootMap A C B D z) = 0 :=
      asanoPhi_rootMap_zero h_denom
    calc
      A + B * asanoRootMap A C B D z + C * z +
          D * asanoRootMap A C B D z * z =
          asanoPhi A C B D z (asanoRootMap A C B D z) := by
            unfold asanoPhi
            ring
      _ = 0 := hzero
  have hNondeg_swapped : A * D - C * B ≠ 0 := by
    simpa [mul_comm] using hNondeg
  apply
    (asanoRootMap_not_eventually_mem_bounded
      (A := A) (B := C) (C := B) (D := D) (K := K1)
      hD hNondeg_swapped hK1_bdd)
  simpa [p, neg_div] using hroot_mem

/--
If `-B/D ∈ K₂` and `0 ∉ K₂`, then `B ≠ 0`.
-/
theorem right_pole_nonzero
    (B D : ℂ) (K2 : Set ℂ)
    (hK2_no_zero : (0 : ℂ) ∉ K2)
    (h_in : (-B / D) ∈ K2) :
    B ≠ 0 := by
  intro hB
  rw [hB, neg_zero, zero_div] at h_in
  exact hK2_no_zero h_in

/--
Combined endpoint disjunction:
if `K₁`, `K₂` are closed and at least one is bounded, then the nondegenerate
endpoint disjunction holds.
-/
theorem asano_endpoint_disjunction_combined
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_closed : IsClosed K2)
    (h_bdd_or : Bornology.IsBounded K1 ∨ Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (hK2_no_zero : (0 : ℂ) ∉ K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (C ≠ 0 ∧ (-C / D) ∈ K1) ∨ (B ≠ 0 ∧ (-B / D) ∈ K2) := by
  rcases h_bdd_or with hK1_bdd | hK2_bdd
  · have h_in := asano_right_pole_in_K2 A B C D K1 K2 hD hNondeg hK2_closed hK1_bdd h_zerofree
    exact Or.inr ⟨right_pole_nonzero B D K2 hK2_no_zero h_in, h_in⟩
  · exact asano_endpoint_disjunction_left
      A B C D K1 K2 hD hNondeg hK1_closed hK2_bdd hK1_no_zero h_zerofree

end InfoGeometry.Canonical.AsanoRuelleSymmetricEndpoint
