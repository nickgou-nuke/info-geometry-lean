/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzConnesSpectralDistance

noncomputable section

namespace InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum

/-!
# Supremum Connes spectral distance over a noncommutative normed algebra

This module owns the supremum construction only.  The algebraic commutator and
its norm are imported from `CuntzConnesSpectralDistance`; no commutative
diagonal subalgebra or finite matrix surrogate is used here.
-/

open InfoGeometry.Canonical.CuntzConnesSpectralDistance

variable {A : Type*} [NormedRing A]

/-- The Lip-1 ball for an algebra element relative to a Dirac element `D`. -/
def LipSet (D : A) : Set A :=
  {a | LipschitzBall D a}

/-- Values whose supremum defines the Connes spectral distance. -/
def spectralDistanceSet (D : A) (ω₁ ω₂ : A → ℝ) : Set ℝ :=
  {r | ∃ a ∈ LipSet D, r = |ω₁ a - ω₂ a|}

/-- Connes' supremum spectral distance for two real-valued state readouts. -/
def supremumSpectralDist (D : A) (ω₁ ω₂ : A → ℝ) : ℝ :=
  sSup (spectralDistanceSet D ω₁ ω₂)

/-- Every admissible observable is bounded above by the defining supremum. -/
theorem pointwise_le_supremum_spectral_dist
    (D : A) (ω₁ ω₂ : A → ℝ) (a : A)
    (ha : a ∈ LipSet D)
    (h_bdd : BddAbove (spectralDistanceSet D ω₁ ω₂)) :
    |ω₁ a - ω₂ a| ≤ supremumSpectralDist D ω₁ ω₂ := by
  apply le_csSup h_bdd
  exact ⟨a, ha, rfl⟩

/-- The Lip-1 constraint is equivariant under an isometric ring equivalence
when both the Dirac element and observable are transported. -/
theorem lipschitzBall_isometric_ringEquiv_iff
    (e : A ≃+* A) (D a : A)
    (hisom : ∀ x : A, ‖e x‖ = ‖x‖) :
    LipschitzBall D a ↔ LipschitzBall (e D) (e a) := by
  have hT : commutatorNorm (e D) (e a) = commutatorNorm D a :=
    commutatorNorm_transport e.toRingHom D (e D) rfl hisom a
  change commutatorNorm D a ≤ 1 ↔ commutatorNorm (e D) (e a) ≤ 1
  rw [hT]

/-- The Connes distance value set is unchanged by an isometric algebra
equivalence when the two readouts are transported contravariantly. -/
theorem spectralDistanceSet_isometric_ringEquiv
    (e : A ≃+* A) (D : A) (ω₁ ω₂ : A → ℝ)
    (hisom : ∀ x : A, ‖e x‖ = ‖x‖) :
    spectralDistanceSet (e D) (ω₁ ∘ e.symm) (ω₂ ∘ e.symm) =
      spectralDistanceSet D ω₁ ω₂ := by
  ext r
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨e.symm b, ?_, rfl⟩
    change LipschitzBall D (e.symm b)
    apply (lipschitzBall_isometric_ringEquiv_iff e D (e.symm b) hisom).mpr
    change LipschitzBall (e D) b at hb
    simpa using hb
  · rintro ⟨a, ha, rfl⟩
    refine ⟨e a, ?_, ?_⟩
    · change LipschitzBall (e D) (e a)
      exact (lipschitzBall_isometric_ringEquiv_iff e D a hisom).mp ha
    · simp

/-- The supremum Connes distance is invariant under an isometric algebra
equivalence with contravariantly transported readouts. The equality is exact
even when the value set is unbounded, since the underlying sets agree. -/
theorem supremumSpectralDist_isometric_ringEquiv
    (e : A ≃+* A) (D : A) (ω₁ ω₂ : A → ℝ)
    (hisom : ∀ x : A, ‖e x‖ = ‖x‖) :
    supremumSpectralDist (e D) (ω₁ ∘ e.symm) (ω₂ ∘ e.symm) =
      supremumSpectralDist D ω₁ ω₂ := by
  unfold supremumSpectralDist
  rw [spectralDistanceSet_isometric_ringEquiv e D ω₁ ω₂ hisom]

/-- If two additive readouts distinguish an element commuting with the Dirac
operator, the spectral-distance value set is unbounded above. Integer
multiples of that element remain in the commutator Lip-1 ball while their
readout difference grows without bound. -/
theorem spectralDistanceSet_not_bddAbove_of_commuting_readouts
    (D : A) (ω₁ ω₂ : A →+ ℝ) (c : A)
    (hComm : CuntzConnesSpectralDistance.commutator D c = 0)
    (hReadout : ω₁ c ≠ ω₂ c) :
    ¬ BddAbove
      (spectralDistanceSet D ω₁ ω₂) := by
  let δ : ℝ := ω₁ c - ω₂ c
  have hδ : δ ≠ 0 := by
    dsimp [δ]
    exact sub_ne_zero.mpr hReadout
  have hδpos : 0 < |δ| := abs_pos.mpr hδ
  intro hBdd
  rcases hBdd with ⟨b, hb⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (b / |δ|)
  have hstrict : b < (n : ℝ) * |δ| := by
    rwa [div_lt_iff₀ hδpos] at hn
  let commMap : A →+ A :=
    { toFun := fun a => CuntzConnesSpectralDistance.commutator D a
      map_zero' := by
        change D * 0 - 0 * D = 0
        simp
      map_add' := by
        intro a b
        change D * (a + b) - (a + b) * D =
          (D * a - a * D) + (D * b - b * D)
        noncomm_ring }
  have hLip : n • c ∈ LipSet D := by
    change CuntzConnesSpectralDistance.LipschitzBall D (n • c)
    change CuntzConnesSpectralDistance.commutatorNorm D (n • c) ≤ 1
    change ‖commMap (n • c)‖ ≤ 1
    have hc : commMap c = 0 := hComm
    rw [commMap.map_nsmul, hc]
    simp
  have hread :
      |ω₁ (n • c) - ω₂ (n • c)| = (n : ℝ) * |δ| := by
    simp only [ω₁.map_nsmul, ω₂.map_nsmul]
    rw [nsmul_eq_mul, nsmul_eq_mul]
    calc
      |(n : ℝ) * ω₁ c - (n : ℝ) * ω₂ c| =
          |(n : ℝ) * (ω₁ c - ω₂ c)| := by congr 1 <;> ring
      _ = |(n : ℝ)| * |ω₁ c - ω₂ c| := abs_mul _ _
      _ = (n : ℝ) * |δ| := by
        rw [abs_of_nonneg (Nat.cast_nonneg n)]
  have hmem : |ω₁ (n • c) - ω₂ (n • c)| ∈ spectralDistanceSet D ω₁ ω₂ :=
    ⟨n • c, hLip, rfl⟩
  have hle := hb hmem
  rw [hread] at hle
  linarith

end InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum
