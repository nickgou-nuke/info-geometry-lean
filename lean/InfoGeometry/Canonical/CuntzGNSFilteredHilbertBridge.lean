import InfoGeometry.Prequantum.AlgebraicGNSState
import InfoGeometry.Prequantum.GNSBridge
import InfoGeometry.Algebra.CuntzGNSRepresentation
import InfoGeometry.Algebra.CuntzKMSState
import InfoGeometry.Algebra.CuntzModularAutomorphism
import InfoGeometry.Algebra.BostConnesAnalytic
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
open InfoGeometry.Prequantum.GNSBridge
open InfoGeometry.Algebra.CuntzGNSRepresentation
open InfoGeometry.Algebra.CuntzKMSState
open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Algebra.BostConnesAnalytic
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion
open Complex

namespace InfoGeometry.Canonical.CuntzGNSFilteredHilbertBridge

variable (n : ℕ) [NeZero n] (primes : Fin n → ℕ) (β : ℝ)

theorem boltzmannFactor_eq_real (p : ℕ) (β : ℝ) :
    boltzmannFactor p (β : ℂ) = (realBoltzmannFactor (p : ℝ) β : ℂ) := by
  dsimp [boltzmannFactor, realBoltzmannFactor]
  have hp_nonneg : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have h1 : (p : ℂ) = ((p : ℝ) : ℂ) := by simp
  have h2 : (- (β : ℂ)) = ((-β : ℝ) : ℂ) := by simp
  rw [h1, h2, ← Complex.ofReal_cpow hp_nonneg]

theorem primonPartition_eq_real :
    primonPartition n primes (β : ℂ) = (realPartitionSum n primes β : ℂ) := by
  dsimp [primonPartition, realPartitionSum]
  simp_rw [boltzmannFactor_eq_real]
  push_cast
  rfl

theorem kmsWeight_eq_real (i : Fin n) :
    kmsWeight n primes (β : ℂ) i = (realKMSWeight n primes β i : ℂ) := by
  dsimp [kmsWeight, realKMSWeight]
  rw [boltzmannFactor_eq_real (primes i) β]
  rw [primonPartition_eq_real n primes β]
  push_cast
  rfl

theorem hWeightReal (i : Fin n) :
    star (kmsWeight n primes (β : ℂ) i) = kmsWeight n primes (β : ℂ) i := by
  rw [kmsWeight_eq_real n primes β i]
  exact conj_ofReal (realKMSWeight n primes β i)

theorem hWeightNonneg (hpos : ∀ i, 0 < primes i) (i : Fin n) :
    0 ≤ (kmsWeight n primes (β : ℂ) i).re := by
  rw [kmsWeight_eq_real n primes β i]
  rw [ofReal_re]
  dsimp [realKMSWeight, realBoltzmannFactor]
  exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) (-β)) (le_of_lt (realPartitionSum_pos n primes hpos β))

variable (hZ : primonPartition n primes (β : ℂ) ≠ 0)

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
def cuntzKMSRealAlgebraicState (hpos : ∀ i, 0 < primes i) : RealAlgebraicState (DiagonalAlgebra n) where
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
        have H := congr_arg Complex.im (hWeightReal n primes β i)
        simpa using H
      linarith
    apply Finset.sum_nonneg
    intro i _
    rw [this, H_im, H_w_im]
    simp only [mul_zero, sub_zero]
    have h1 : 0 ≤ (star (x i) * x i).re := by
      simp [mul_re]
      apply add_nonneg <;> apply mul_self_nonneg
    exact mul_nonneg h1 (hWeightNonneg n primes β hpos i)
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
    have h_w := hWeightReal n primes β i
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

/-! ### Exact identification with the complex KMS pre-inner product

The real algebraic state above is not a replacement for the complex GNS
pairing.  On the diagonal stage it is its real readout.  Recording this
identity explicitly is the bridge needed before a compatible family of stages
can be supplied to the filtered Hilbert-colimit owner.
-/

@[simp] theorem cuntzKMSRealAlgebraicState_pairing_eq_re_kmsInner
    (hpos : ∀ i, 0 < primes i) (x y : DiagonalAlgebra n) :
    (cuntzKMSRealAlgebraicState n primes β hZ hpos).eval
        (star y * x) =
      (kmsInner n primes (β : ℂ) y x).re := by
  rfl

@[simp] theorem cuntzKMSRealAlgebraicState_quadratic_eq_re_kmsInner
    (hpos : ∀ i, 0 < primes i) (x : DiagonalAlgebra n) :
    (cuntzKMSRealAlgebraicState n primes β hZ hpos).eval
        (star x * x) =
      (kmsInner n primes (β : ℂ) x x).re := by
  exact cuntzKMSRealAlgebraicState_pairing_eq_re_kmsInner
    n primes β hZ hpos x x

/-! The algebraic quotient is named at the Cuntz stage, while completion is
deliberately left to the filtered-system layer. -/

abbrev CuntzKMSGNSQuotient (hpos : ∀ i, 0 < primes i) : Type _ :=
  RealAlgebraicState.GNSQuotient
    (cuntzKMSRealAlgebraicState n primes β hZ hpos)

theorem cuntzKMSGNS_vacuum_norm_eq_one (hpos : ∀ i, 0 < primes i) :
    (cuntzKMSRealAlgebraicState n primes β hZ hpos).eval
        (star (1 : DiagonalAlgebra n) * 1) = 1 := by
  exact RealAlgebraicState.gns_vacuum_norm_eq_one
    (cuntzKMSRealAlgebraicState n primes β hZ hpos)

/-! ### Finite modular action on the diagonal

The algebraic modular automorphism is nontrivial on the Cuntz generators but
acts trivially on the diagonal projectors.  This is the finite-stage
compatibility statement needed before transporting the KMS state through a
filtered GNS system.
-/

@[simp] theorem sigma_diagonalElement_fixed
    (t : ℝ) (x : DiagonalAlgebra n) :
    sigma n primes t (diagonalElement n x) = diagonalElement n x := by
  dsimp [diagonalElement]
  simp only [map_sum, map_smul, sigma_fixes_projector]

end InfoGeometry.Canonical.CuntzGNSFilteredHilbertBridge
