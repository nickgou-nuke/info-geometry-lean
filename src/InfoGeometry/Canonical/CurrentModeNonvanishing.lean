/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitCliffordFiniteCurrentObstruction
import InfoGeometry.Canonical.SugawaraFiveGradingObstruction

/-!
# Nonvanishing and exact boundary criteria for Heisenberg currents

The existing `CurrentHeisenbergRep` carries endomorphisms with a scalar
Heisenberg commutator and vectorwise eventual truncation. On a nontrivial
module every nonzero-index mode is nonzero, so no uniform operator cutoff
exists. The Sugawara mode-shift identity gives the exact zero-bracket criterion.
In particular the proposed positive five-grading boundary cannot vanish.

Dependencies: Heisenberg commutator → nonzero modes → no uniform cutoff;
Sugawara shift + nonzero modes → nonvanishing boundary bracket.
The concrete charged-Fock construction inhabits the existing current interface;
no finite CAR family is promoted to that interface here.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- One vanishing nonzero-index mode already contradicts the central law. -/
theorem mode_ne_zero [Nontrivial V] (H : CurrentHeisenbergRep 𝕜 V)
    (k : ℤ) (hk : k ≠ 0) : H.J k ≠ 0 := by
  intro hz
  have hc := H.comm k (-k)
  have hscalar : (k : 𝕜) • (1 : V →ₗ[𝕜] V) = 0 := by
    simpa [hz, LinearMap.commutator] using hc.symm
  have hk' : (k : 𝕜) ≠ 0 := Int.cast_ne_zero.mpr hk
  exact one_ne_zero ((smul_eq_zero.mp hscalar).resolve_left hk')

/-- Vectorwise truncation cannot be replaced by a uniform operator cutoff. -/
theorem not_uniformly_truncated [Nontrivial V] (H : CurrentHeisenbergRep 𝕜 V) :
    ¬ ∃ N : ℤ, ∀ k, N ≤ k → H.J k = 0 := by
  rintro ⟨N, hN⟩
  have hpos : (0 : ℤ) < max N 1 := lt_of_lt_of_le (by decide) (le_max_right N 1)
  exact H.mode_ne_zero (max N 1) (ne_of_gt hpos) (hN _ (le_max_left N 1))

/-- The exact vanishing criterion retains the zero-mode possibility. -/
theorem sugawara_current_commutator_eq_zero_iff
    (H : CurrentHeisenbergRep 𝕜 V) (n m : ℤ) :
    (H.sugawaraStressMode n).commutator (H.J m) = 0 ↔
      m = 0 ∨ H.J (n + m) = 0 := by
  change (VirasoroProject.sugawaraGen H.trunc n).commutator (H.J m) = 0 ↔ _
  rw [InfoGeometry.Canonical.SugawaraFiveGradingObstruction.sugawara_current_mode_shift
    H.J H.trunc H.comm, ← Int.cast_smul_eq_zsmul 𝕜]
  simp only [smul_eq_zero, Int.cast_eq_zero, neg_eq_zero]

/-- A shift to a nonzero index cannot disappear when the input coefficient is nonzero. -/
theorem sugawara_current_commutator_ne_zero [Nontrivial V]
    (H : CurrentHeisenbergRep 𝕜 V) (n m : ℤ) (hm : m ≠ 0) (hnm : n + m ≠ 0) :
    (H.sugawaraStressMode n).commutator (H.J m) ≠ 0 := by
  intro hz
  rcases (H.sugawara_current_commutator_eq_zero_iff n m).mp hz with h | h
  · exact hm h
  · exact H.mode_ne_zero (n + m) hnm h

/-- The first positive mixed bracket cannot satisfy a boundary-zero law. -/
theorem positive_sugawara_boundary_ne_zero [Nontrivial V]
    (H : CurrentHeisenbergRep 𝕜 V) :
    (H.sugawaraStressMode 1).commutator (H.J 1) ≠ 0 :=
  H.sugawara_current_commutator_ne_zero 1 1 (by decide) (by decide)

end InfoGeometry.Canonical.CurrentSugawaraBridge.CurrentHeisenbergRep
