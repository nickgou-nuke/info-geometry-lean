import InfoGeometry.Prequantum.AlgebraicGNSState
import InfoGeometry.Algebra.CuntzGNSRepresentation
import InfoGeometry.Algebra.CuntzKMSState
import InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

/-!
# Cuntz GNS Filtered Hilbert Completion Bridge

This module instantiates the abstract `RealAlgebraicState` on the Cuntz diagonal
subalgebra using the Bost-Connes KMS state, providing the algebraic pre-inner product.
It bridges the Cuntz finite-stage KMS state into the algebraic GNS machinery,
which in turn supplies the data for the filtered isometric Hilbert completion.
-/

noncomputable section

open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Algebra.CuntzGNSRepresentation
open InfoGeometry.Algebra.CuntzKMSState
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion
open Complex

namespace InfoGeometry.Canonical.CuntzGNSFilteredHilbertBridge

variable (n : ℕ) (primes : Fin n → ℕ) (β : ℝ)
variable (hZ : primonPartition n primes (β : ℂ) ≠ 0)
variable (hWeightReal : ∀ i, star (kmsWeight n primes (β : ℂ) i) = kmsWeight n primes (β : ℂ) i)
variable (hWeightNonneg : ∀ i, 0 ≤ (kmsWeight n primes (β : ℂ) i).re)

/-- The diagonal subalgebra of O_n represented as functions Fin n → ℂ. -/
abbrev DiagonalAlgebra := Fin n → ℂ

/-- The Cuntz KMS state as a real-linear functional on the diagonal subalgebra. -/
def cuntzKMSLinearMap : DiagonalAlgebra n →ₗ[ℝ] ℝ where
  toFun := fun x => (∑ i : Fin n, x i * kmsWeight n primes (β : ℂ) i).re
  map_add' := by
    intro x y
    dsimp
    have : (∑ i : Fin n, (x i + y i) * kmsWeight n primes (β : ℂ) i) =
      (∑ i : Fin n, x i * kmsWeight n primes (β : ℂ) i) + (∑ i : Fin n, y i * kmsWeight n primes (β : ℂ) i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [this, add_re]
  map_smul' := by
    intro c x
    dsimp
    have : (∑ i : Fin n, (↑c * x i) * kmsWeight n primes (β : ℂ) i) =
      ↑c * (∑ i : Fin n, x i * kmsWeight n primes (β : ℂ) i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [this, mul_re]
    have hc : (c : ℂ).im = 0 := Complex.ofReal_im c
    rw [hc]
    simp only [Complex.ofReal_re]
    ring

/-- The Cuntz KMS state instantiated as a generalized real algebraic state. -/
def cuntzKMSRealAlgebraicState : RealAlgebraicState (DiagonalAlgebra n) where
  toLinearMap := cuntzKMSLinearMap n primes β
  normalized := by
    dsimp [cuntzKMSLinearMap]
    have H := (DiagonalKMSState.canonical primes (β : ℂ) hZ).weights_sum_one
    have H2 : (∑ i : Fin n, 1 * kmsWeight n primes (β : ℂ) i) = 1 := by
      simpa using H
    rw [H2]
    rfl
  positive := by
    intro x
    dsimp [cuntzKMSLinearMap, star]
    change 0 ≤ (∑ i : Fin n, star (x i) * x i * kmsWeight n primes (β : ℂ) i).re
    have h_sum_re : (∑ i : Fin n, star (x i) * x i * kmsWeight n primes (β : ℂ) i).re =
      ∑ i : Fin n, (star (x i) * x i * kmsWeight n primes (β : ℂ) i).re := by
      exact map_sum (AddMonoidHom.mk' Complex.re Complex.add_re) _ _
    rw [h_sum_re]
    have : ∀ i, (star (x i) * x i * kmsWeight n primes (β : ℂ) i).re =
      (star (x i) * x i).re * (kmsWeight n primes (β : ℂ) i).re -
      (star (x i) * x i).im * (kmsWeight n primes (β : ℂ) i).im := fun _ => rfl
    have H_im : ∀ i, (star (x i) * x i).im = 0 := fun i => by simp [mul_im] ; ring
    have H_w_im : ∀ i, (kmsWeight n primes (β : ℂ) i).im = 0 := fun i => by
      have hw3 : -(kmsWeight n primes (β : ℂ) i).im = (kmsWeight n primes (β : ℂ) i).im := by
        have H := congr_arg Complex.im (hWeightReal i)
        simpa using H
      linarith
    apply Finset.sum_nonneg
    intro i _
    rw [this, H_im, H_w_im]
    simp only [mul_zero, sub_zero]
    have h1 : 0 ≤ (star (x i) * x i).re := by
      simp [mul_re]
      apply add_nonneg <;> apply mul_self_nonneg
    exact mul_nonneg h1 (hWeightNonneg i)
  symmetric := by
    intro x y
    dsimp [cuntzKMSLinearMap, star]
    change (∑ i : Fin n, star (y i) * x i * kmsWeight n primes (β : ℂ) i).re =
      (∑ i : Fin n, star (x i) * y i * kmsWeight n primes (β : ℂ) i).re
    have h_sum_re1 : (∑ i : Fin n, star (y i) * x i * kmsWeight n primes (β : ℂ) i).re =
      ∑ i : Fin n, (star (y i) * x i * kmsWeight n primes (β : ℂ) i).re := by
      exact map_sum (AddMonoidHom.mk' Complex.re Complex.add_re) _ _
    have h_sum_re2 : (∑ i : Fin n, star (x i) * y i * kmsWeight n primes (β : ℂ) i).re =
      ∑ i : Fin n, (star (x i) * y i * kmsWeight n primes (β : ℂ) i).re := by
      exact map_sum (AddMonoidHom.mk' Complex.re Complex.add_re) _ _
    rw [h_sum_re1, h_sum_re2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_w := hWeightReal i
    have h1 : star (star (y i) * x i * kmsWeight n primes (β : ℂ) i) =
      star (x i) * y i * kmsWeight n primes (β : ℂ) i := by
      calc
        star (star (y i) * x i * kmsWeight n primes (β : ℂ) i)
          = star (kmsWeight n primes (β : ℂ) i) * star (x i) * star (star (y i)) := by
            simp [star_mul]
            ring
        _ = kmsWeight n primes (β : ℂ) i * star (x i) * y i := by
            rw [h_w, star_star]
        _ = star (x i) * y i * kmsWeight n primes (β : ℂ) i := by
            ring
    have h2 := Complex.ext_iff.mp h1 |>.left
    have h3 : (star (star (y i) * x i * kmsWeight n primes (β : ℂ) i)).re = (star (y i) * x i * kmsWeight n primes (β : ℂ) i).re := rfl
    rw [h3] at h2
    exact h2

end InfoGeometry.Canonical.CuntzGNSFilteredHilbertBridge
