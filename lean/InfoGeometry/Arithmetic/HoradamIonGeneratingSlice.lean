import InfoGeometry.Arithmetic.HoradamIonMatrixMethods
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Horadam `2^k`-ion finite generating-function slice

This module formalizes a finite/truncated version of the ordinary generating
function identity from `preprints201906.0303.v1`, *Horadam 2^k-ions*.

For a recurrence `W_{i+2}=pW_{i+1}+qW_i` and
`G_n(t)=∑_{i=0}^n W_i t^i`, it proves

`(1-p t-q t^2)G_n(t) = W_0 + (W_1-pW_0)t - W_{n+1}t^{n+1} - qW_n t^{n+2}`.

The theorem has explicit boundary terms and therefore does not assert an
infinite power-series identity or any convergence statement.  A coordinate
`2^k`-ion lift is proved componentwise.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.HoradamIonGeneratingSlice

open Finset
open HoradamIonMatrixMethods

variable {R : Type*} [CommRing R]

/-- Finite truncated generating polynomial `∑_{i=0}^n W_i t^i`. -/
def seqGeneratingTrunc (W : ℕ → R) (t : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n + 1), W i * t ^ i

/-- One-step extension of the finite generating polynomial. -/
theorem seqGeneratingTrunc_succ (W : ℕ → R) (t : R) (n : ℕ) :
    seqGeneratingTrunc W t (n + 1) =
      seqGeneratingTrunc W t n + W (n + 1) * t ^ (n + 1) := by
  unfold seqGeneratingTrunc
  rw [show n + 1 + 1 = n + 2 by omega]
  rw [show n + 1 = Nat.succ n by rfl]
  rw [Finset.sum_range_succ]

/-- Finite denominator identity for a truncated generating polynomial. -/
theorem seqGeneratingTrunc_clear_denominator
    (W : ℕ → R) (p q t : R)
    (hrec : ∀ n : ℕ, W (n + 2) = p * W (n + 1) + q * W n) :
    ∀ n : ℕ,
    (1 - p * t - q * t ^ 2) * seqGeneratingTrunc W t n =
      W 0 + (W 1 - p * W 0) * t - W (n + 1) * t ^ (n + 1) -
        q * W n * t ^ (n + 2)
  | 0 => by
      simp [seqGeneratingTrunc]
      ring
  | n + 1 => by
      rw [seqGeneratingTrunc_succ]
      rw [mul_add]
      rw [seqGeneratingTrunc_clear_denominator W p q t hrec n]
      have hW : W (n + 2) = p * W (n + 1) + q * W n := hrec n
      rw [hW]
      ring

/-- Horadam truncated generating polynomial. -/
def horadamGeneratingTrunc (a b p q t : R) (n : ℕ) : R :=
  seqGeneratingTrunc (horadam a b p q) t n

/-- Finite/truncated ordinary generating-function identity for Horadam numbers. -/
theorem horadamGeneratingTrunc_clear_denominator
    (a b p q t : R) (n : ℕ) :
    (1 - p * t - q * t ^ 2) * horadamGeneratingTrunc a b p q t n =
      a + (b - p * a) * t - horadam a b p q (n + 1) * t ^ (n + 1) -
        q * horadam a b p q n * t ^ (n + 2) := by
  unfold horadamGeneratingTrunc
  simpa [horadam] using
    seqGeneratingTrunc_clear_denominator (horadam a b p q) p q t
      (horadam_succ_succ a b p q) n

/-- Coordinate truncated generating polynomial for the Horadam `2^k`-ion shadow. -/
def horadamIonGeneratingTrunc {N : ℕ} (a b p q t : R) (n : ℕ) : Ion N R :=
  fun s => ∑ i ∈ Finset.range (n + 1), horadam a b p q (i + s.val) * t ^ i

/-- Componentwise finite generating identity for Horadam `2^k`-ion coordinates. -/
theorem horadamIonGeneratingTrunc_clear_denominator {N : ℕ}
    (a b p q t : R) (n : ℕ) :
    ionScale (1 - p * t - q * t ^ 2) (horadamIonGeneratingTrunc (N := N) a b p q t n) =
      fun s =>
        horadam a b p q s.val +
          (horadam a b p q (s.val + 1) - p * horadam a b p q s.val) * t -
          horadam a b p q (n + 1 + s.val) * t ^ (n + 1) -
          q * horadam a b p q (n + s.val) * t ^ (n + 2) := by
  ext s
  simp [horadamIonGeneratingTrunc, ionScale]
  let W : ℕ → R := fun i => horadam a b p q (i + s.val)
  have hrecW : ∀ i : ℕ, W (i + 2) = p * W (i + 1) + q * W i := by
    intro i
    dsimp [W]
    rw [show i + 2 + s.val = i + s.val + 2 by omega]
    rw [show i + 1 + s.val = i + s.val + 1 by omega]
    exact horadam_succ_succ a b p q (i + s.val)
  have h := seqGeneratingTrunc_clear_denominator W p q t hrecW n
  dsimp [seqGeneratingTrunc, W] at h
  simpa [show s.val + 1 = 1 + s.val by omega] using h

/-- Consolidated finite generating-function slice packet. -/
theorem horadam_ion_generating_slice_packet {N : ℕ}
    (a b p q t : R) :
    (∀ n : ℕ,
      (1 - p * t - q * t ^ 2) * horadamGeneratingTrunc a b p q t n =
        a + (b - p * a) * t - horadam a b p q (n + 1) * t ^ (n + 1) -
          q * horadam a b p q n * t ^ (n + 2)) ∧
    (∀ n : ℕ,
      ionScale (1 - p * t - q * t ^ 2) (horadamIonGeneratingTrunc (N := N) a b p q t n) =
        fun s =>
          horadam a b p q s.val +
            (horadam a b p q (s.val + 1) - p * horadam a b p q s.val) * t -
            horadam a b p q (n + 1 + s.val) * t ^ (n + 1) -
            q * horadam a b p q (n + s.val) * t ^ (n + 2)) := by
  exact ⟨horadamGeneratingTrunc_clear_denominator a b p q t,
    horadamIonGeneratingTrunc_clear_denominator a b p q t⟩

end InfoGeometry.Arithmetic.HoradamIonGeneratingSlice

end noncomputable section
