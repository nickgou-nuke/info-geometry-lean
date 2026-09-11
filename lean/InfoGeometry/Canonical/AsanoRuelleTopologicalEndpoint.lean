import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Normed.Module.Basic
import InfoGeometry.Analysis.AsanoMobiusPole

/-!
# InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

Mathematical Proof:
This file executes the formal topological limit for the Asano-Ruelle
contraction (nondegenerate branch).

It proves that the algebraic metric inequality bounding the roots, when
evaluated at the non-degenerate pole over a punctured neighborhood filter,
forces the pole directly into the forbidden set `K₁`.

This establishes the exact endpoint disjunction required by Ruelle A.1,
ready to feed into the algebraic product lemmas.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

open Set Filter Topology
open InfoGeometry.Analysis.AsanoMobiusPole
open InfoGeometry.Canonical.LeeYangAsanoNativeCore

/--
Topological Pole Inclusion (The Limit Contradiction).

If `K₂` is bounded, the root `w = -(A+Bz)/(C+Dz)` cannot escape to infinity.
Evaluating this bound over the punctured neighborhood of the pole `-C/D`
forces the numerator to vanish, contradicting non-degeneracy.
Therefore, the pole must lie inside the closed set `K₁`.
-/
theorem asano_left_pole_in_K1
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (-C / D) ∈ K1 := by
  by_contra h_notin
  let p := -C / D
  have hp_nhds : K1ᶜ ∈ nhds p := (isOpen_compl_iff.mpr hK1_closed).mem_nhds h_notin
  have hp_punctured : K1ᶜ ∈ nhdsWithin p {p}ᶜ :=
    mem_nhdsWithin_of_mem_nhds hp_nhds
  have hroot_mem :
      ∀ᶠ z in nhdsWithin p {p}ᶜ, asanoRootMap A B C D z ∈ K2 := by
    filter_upwards [hp_punctured, self_mem_nhdsWithin] with z hz_notin hz_neq
    have h_denom : C + D * z ≠ 0 := by
      exact denominator_ne_zero_off_pole hD (by simpa [p, neg_div] using hz_neq)
    by_contra hroot_notin
    apply h_zerofree z (asanoRootMap A B C D z) hz_notin hroot_notin
    simpa [asanoPhi] using
      (asanoPhi_rootMap_zero
        (A := A) (B := B) (C := C) (D := D) (z1 := z) h_denom)
  apply
    (asanoRootMap_not_eventually_mem_bounded
      (A := A) (B := B) (C := C) (D := D) (K := K2)
      hD hNondeg hK2_bdd)
  simpa [p, neg_div] using hroot_mem

/--
Trivial lemma isolating the origin avoidance requirement.
If `-C/D ∈ K1` but `0 ∉ K1`, then `C ≠ 0`.
-/
theorem left_pole_nonzero
    (C D : ℂ) (K1 : Set ℂ)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (h_in : (-C / D) ∈ K1) :
    C ≠ 0 := by
  intro hC
  rw [hC, neg_zero, zero_div] at h_in
  exact hK1_no_zero h_in

/--
The Nondegenerate Endpoint Disjunction (Left Branch).

Derived purely from closed/bounded and zero-free hypotheses.
This perfectly matches the Ruelle A.1 endpoint statement, ready to be
fed into `contracted_root_mem_negProductSet_of_endpoint_root`.
-/
theorem asano_endpoint_disjunction_left
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (C ≠ 0 ∧ (-C / D) ∈ K1) ∨ (B ≠ 0 ∧ (-B / D) ∈ K2) := by
  have h_in := asano_left_pole_in_K1 A B C D K1 K2 hD hNondeg hK1_closed hK2_bdd h_zerofree
  exact Or.inl ⟨left_pole_nonzero C D K1 hK1_no_zero h_in, h_in⟩

end InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint
