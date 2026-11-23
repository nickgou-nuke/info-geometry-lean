/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Algebraic identities for finite Gabor operators

This file formalizes finite algebraic consequences associated with Gabor
localization. It does not formalize the analytic fractal uncertainty estimates
of Knutsen's paper: those require Hilbert-space and quantitative porosity
hypotheses absent from a bare star-ring.
-/

namespace InfoGeometry.OperatorAlgebra.KnutsenGaborOperatorAlgebra

attribute [local instance] LieRing.ofAssociativeRing

section ProjectionLocalization

variable {B : Type*} [Ring B] [StarRing B]

def separateLocalization (pΩ u pT : B) : B := pΩ * u * pT

theorem separateLocalization_pore_conservation {pΩ u pT : B}
    (hu : star u * u = 1) (hT : pT * pT = pT) (hTstar : star pT = pT)
    (hΩ : pΩ * pΩ = pΩ) (hΩstar : star pΩ = pΩ) :
    star (separateLocalization pΩ u pT) * separateLocalization pΩ u pT +
      star (separateLocalization (1 - pΩ) u pT) *
        separateLocalization (1 - pΩ) u pT = pT := by
  dsimp [separateLocalization]
  simp only [star_mul, star_sub, star_one, hTstar, hΩstar]
  have hcomp : (1 - pΩ) * (1 - pΩ) = 1 - pΩ := by
    noncomm_ring [hΩ]
  have hsplit : pΩ * pΩ + (1 - pΩ) * (1 - pΩ) = 1 := by
    rw [hΩ, hcomp]
    noncomm_ring
  calc
    pT * (star u * pΩ) * (pΩ * u * pT) +
        pT * (star u * (1 - pΩ)) * ((1 - pΩ) * u * pT) =
        pT * star u * (pΩ * pΩ + (1 - pΩ) * (1 - pΩ)) * u * pT := by
          noncomm_ring
    _ = pT * star u * 1 * u * pT := by rw [hsplit]
    _ = pT := by
      calc
        pT * star u * 1 * u * pT = pT * (star u * u) * pT := by noncomm_ring
        _ = pT * 1 * pT := by rw [hu]
        _ = pT * pT := by noncomm_ring
        _ = pT := hT

def compressedLocalization (p q : B) : B := p * q * p

def poreLeakage (p q : B) : B := (1 - p) * q * p

theorem compressedLocalization_variance_eq_leakage {p q : B}
    (hp : p * p = p) (hps : star p = p)
    (hq : q * q = q) (hqs : star q = q) :
    compressedLocalization p q - compressedLocalization p q *
        compressedLocalization p q =
      star (poreLeakage p q) * poreLeakage p q := by
  dsimp [compressedLocalization, poreLeakage]
  have hstar : star ((1 - p) * q * p) = p * q * (1 - p) := by
    simp only [star_mul, star_sub, star_one, hps, hqs]
    noncomm_ring
  have hcompressed : (p * q * p) * (p * q * p) = p * q * p * q * p := by
    calc
      (p * q * p) * (p * q * p) = p * q * (p * p) * q * p := by noncomm_ring
      _ = p * q * p * q * p := by rw [hp]
  have hcorner : p * q * p = p * q * q * p := by
    calc
      p * q * p = p * (q * q) * p := by rw [hq]
      _ = p * q * q * p := by noncomm_ring
  have hcomp : (1 - p) * (1 - p) = 1 - p := by noncomm_ring [hp]
  have hexpand : p * q * (1 - p) * q * p = p * q * q * p - p * q * p * q * p := by
    noncomm_ring
  calc
    p * q * p - (p * q * p) * (p * q * p) =
        p * q * p - p * q * p * q * p := by rw [hcompressed]
    _ = p * q * q * p - p * q * p * q * p :=
          congrArg (fun x : B => x - p * q * p * q * p) hcorner
    _ = p * q * (1 - p) * q * p := hexpand.symm
    _ = p * q * ((1 - p) * (1 - p)) * q * p := by rw [hcomp]
    _ = star ((1 - p) * q * p) * ((1 - p) * q * p) := by
          rw [hstar]
          noncomm_ring [hcomp]

theorem compressedLocalization_variance_eq_pore_leakage
    {P Q : B} (hP_idem : P * P = P) (hP_sa : star P = P)
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    compressedLocalization P Q - compressedLocalization P Q * compressedLocalization P Q =
      star ((1 - P) * Q * P) * ((1 - P) * Q * P) := by
  exact compressedLocalization_variance_eq_leakage hP_idem hP_sa hQ_idem hQ_sa

theorem compressedLocalization_variance_eq_commutator {p q : B}
    (hp : p * p = p) (hps : star p = p)
    (hq : q * q = q) (hqs : star q = q) :
    compressedLocalization p q - compressedLocalization p q *
        compressedLocalization p q =
      (p * star ⁅p, q⁆) * (⁅p, q⁆ * p) := by
  rw [compressedLocalization_variance_eq_leakage hp hps hq hqs]
  have hright : ⁅p, q⁆ * p = -poreLeakage p q := by
    simp only [LieRing.of_associative_ring_bracket]
    dsimp [poreLeakage]
    noncomm_ring [hp]
  have hleft : p * star ⁅p, q⁆ = -star (poreLeakage p q) := by
    calc
      p * star ⁅p, q⁆ = star (⁅p, q⁆ * p) := by
        simp only [LieRing.of_associative_ring_bracket, star_sub, star_mul, hps]
      _ = -star (poreLeakage p q) := by rw [hright, star_neg]
  rw [hleft, hright]
  noncomm_ring

end ProjectionLocalization

section FockIntertwining

variable {B : Type*} [Ring B] [StarRing B]

def fockProjection (v : B) : B := v * star v
def daubechiesOperator (v s : B) : B := star v * s * v
def toeplitzOperator (v s : B) : B := fockProjection v * s * fockProjection v

/-- Compression by the self-adjoint Fock range projection preserves
self-adjointness of a symbol. No isometry hypothesis on `v` is needed for
this algebraic statement. -/
theorem toeplitzOperator_selfAdjoint {v s : B} (hs : star s = s) :
    star (toeplitzOperator v s) = toeplitzOperator v s := by
  simp only [toeplitzOperator, fockProjection, star_mul, star_star, hs]
  noncomm_ring

theorem fockProjection_idempotent {v : B} (hv : star v * v = 1) :
    fockProjection v * fockProjection v = fockProjection v := by
  dsimp [fockProjection]
  calc
    (v * star v) * (v * star v) = v * (star v * v) * star v := by noncomm_ring
    _ = v * 1 * star v := by rw [hv]
    _ = v * star v := by noncomm_ring

theorem fockProjection_selfAdjoint (v : B) :
    star (fockProjection v) = fockProjection v := by
  dsimp [fockProjection]
  calc
    star (v * star v) = star (star v) * star v := by rw [star_mul]
    _ = v * star v := by rw [star_star]

theorem daubechies_toeplitz_intertwining {v s : B} (hv : star v * v = 1) :
    v * daubechiesOperator v s = toeplitzOperator v s * v ∧
    v * daubechiesOperator v s * star v = toeplitzOperator v s ∧
    star v * toeplitzOperator v s * v = daubechiesOperator v s := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [daubechiesOperator, toeplitzOperator, fockProjection]
    calc
      v * (star v * s * v) = v * star v * s * v * (star v * v) := by
        rw [hv]
        noncomm_ring
      _ = (v * star v) * s * (v * star v) * v := by noncomm_ring
  · dsimp [daubechiesOperator, toeplitzOperator, fockProjection]
    noncomm_ring
  · dsimp [daubechiesOperator, toeplitzOperator, fockProjection]
    calc
      star v * ((v * star v) * s * (v * star v)) * v =
          (star v * v) * star v * s * v * (star v * v) := by noncomm_ring
      _ = 1 * star v * s * v * 1 := by rw [hv]
      _ = star v * s * v := by noncomm_ring

/-- Every power of the Fock Toeplitz operator intertwines with the corresponding power
of the Daubechies operator through the isometry `v`. -/
theorem daubechies_toeplitz_pow_intertwining {v s : B} (hv : star v * v = 1)
    (n : ℕ) :
    (daubechiesOperator v s) ^ n =
      star v * (toeplitzOperator v s) ^ n * v := by
  let p := daubechiesOperator v s
  let t := toeplitzOperator v s
  have htv : t * v = v * p :=
    (daubechies_toeplitz_intertwining hv).1.symm
  have hpow : ∀ k : ℕ, t ^ k * v = v * p ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        calc
          t ^ k * t * v = t ^ k * (t * v) := by rw [mul_assoc]
          _ = t ^ k * (v * p) := by rw [htv]
          _ = (t ^ k * v) * p := by rw [mul_assoc]
          _ = (v * p ^ k) * p := by rw [ih]
          _ = v * (p ^ k * p) := by rw [mul_assoc]
          _ = v * p ^ (k + 1) := by rw [← pow_succ]
  calc
    p ^ n = (star v * v) * p ^ n := by rw [hv]; simp
    _ = star v * (t ^ n * v) := by rw [hpow n, mul_assoc]
    _ = star v * t ^ n * v := by noncomm_ring

theorem daubechies_complement_partition {v : B} (hv : star v * v = 1) (s : B) :
    daubechiesOperator v s + daubechiesOperator v (1 - s) = 1 := by
  dsimp [daubechiesOperator]
  calc
    star v * s * v + star v * (1 - s) * v = star v * v := by noncomm_ring
    _ = 1 := hv

/-- The two complementary Toeplitz compressions sum to the range projection of
the isometry. This is the operator-level pore partition on the Fock subspace. -/
theorem toeplitz_complement_partition {v : B} (hv : star v * v = 1) (s : B) :
    toeplitzOperator v s + toeplitzOperator v (1 - s) = fockProjection v := by
  calc
    toeplitzOperator v s + toeplitzOperator v (1 - s) =
        fockProjection v * fockProjection v := by
          dsimp [toeplitzOperator, fockProjection]
          noncomm_ring
    _ = fockProjection v := fockProjection_idempotent hv

end FockIntertwining

section GaborOperators

variable {B : Type*} [Ring B] [StarRing B] {m : ℕ}

def gaborFrameOperator (φ : Fin m → B) : B :=
  ∑ i : Fin m, φ i * star (φ i)

def gaborMultiplier (φ b : Fin m → B) : B :=
  ∑ i : Fin m, φ i * b i * star (φ i)

def gaborGram (φ : Fin m → B) : Matrix (Fin m) (Fin m) B :=
  Matrix.of fun i j => star (φ i) * φ j

theorem gaborFrameOperator_selfAdjoint (φ : Fin m → B) :
    star (gaborFrameOperator φ) = gaborFrameOperator φ := by
  dsimp [gaborFrameOperator]
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [star_mul]

theorem gaborMultiplier_adjoint (φ b : Fin m → B) :
    star (gaborMultiplier φ b) = gaborMultiplier φ (fun i => star (b i)) := by
  dsimp [gaborMultiplier]
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [star_mul, mul_assoc]

theorem gaborMultiplier_complement (φ b : Fin m → B) :
    gaborMultiplier φ b + gaborMultiplier φ (fun i => 1 - b i) =
      gaborFrameOperator φ := by
  dsimp [gaborMultiplier, gaborFrameOperator]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  noncomm_ring

theorem gaborGram_sq_apply (φ : Fin m → B) (i j : Fin m) :
    (gaborGram φ * gaborGram φ) i j =
      star (φ i) * gaborFrameOperator φ * φ j := by
  simp only [gaborGram, gaborFrameOperator, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  noncomm_ring

theorem gaborGram_selfAdjoint (φ : Fin m → B) :
    Matrix.conjTranspose (gaborGram φ) = gaborGram φ := by
  ext i j
  simp [gaborGram, star_mul]

theorem gaborGram_idempotent_of_parseval {φ : Fin m → B}
    (hparseval : gaborFrameOperator φ = 1) : gaborGram φ * gaborGram φ = gaborGram φ := by
  ext i j
  rw [gaborGram_sq_apply, hparseval, mul_one]
  rfl

end GaborOperators

section PorosityThickening

/-- The rational porosity parameter after `j` thickening steps in the
geometric recurrence from Knutsen's proof. This is the exact scalar parameter
used by the multiscale argument; it is separate from the operator identities
above. -/
def thickenedPorosity (ν : ℚ) : ℕ → ℚ
  | 0 => ν
  | j + 1 => thickenedPorosity ν j - (ν / 3) ^ (j + 1)

/-- Closed form for the exact finite thickening recurrence. -/
theorem thickenedPorosity_closed_form (ν : ℚ) (j : ℕ) :
    (3 - ν) * thickenedPorosity ν j = ν * (2 - ν) + ν * (ν / 3) ^ j := by
  induction j with
  | zero => simp [thickenedPorosity]; ring
  | succ j ih =>
      calc
        (3 - ν) * thickenedPorosity ν (j + 1) =
            (3 - ν) * thickenedPorosity ν j - (3 - ν) * (ν / 3) ^ (j + 1) := by
              change (3 - ν) * (thickenedPorosity ν j - (ν / 3) ^ (j + 1)) = _
              rw [mul_sub]
        _ = (ν * (2 - ν) + ν * (ν / 3) ^ j) -
            (3 - ν) * ((ν / 3) ^ j * (ν / 3)) := by
              rw [ih, pow_succ]
        _ = ν * (2 - ν) + ν * (ν / 3) ^ (j + 1) := by
              rw [pow_succ]
              ring

/-- If the initial porosity lies in `[0,1]`, every finite thickening step
retains at least half of it. -/
theorem thickenedPorosity_ge_half {ν : ℚ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (j : ℕ) :
    ν / 2 ≤ thickenedPorosity ν j := by
  have h_ratio : 0 ≤ ν / 3 := by positivity
  have h_pow : 0 ≤ (ν / 3) ^ j := pow_nonneg h_ratio j
  have h_term : 0 ≤ ν * (ν / 3) ^ j := mul_nonneg hν0 h_pow
  have h_base : 0 ≤ ν * (1 - ν) := mul_nonneg hν0 (sub_nonneg.mpr hν1)
  have hclosed := thickenedPorosity_closed_form ν j
  have hdiff : (3 - ν) * (thickenedPorosity ν j - ν / 2) =
      ν * (1 - ν) / 2 + ν * (ν / 3) ^ j := by
    linear_combination hclosed
  have hnonneg : 0 ≤ (3 - ν) * (thickenedPorosity ν j - ν / 2) := by
    rw [hdiff]
    exact add_nonneg (div_nonneg h_base (by norm_num)) h_term
  have hfactor : 0 < 3 - ν := by linarith [hν1]
  nlinarith

end PorosityThickening

end InfoGeometry.OperatorAlgebra.KnutsenGaborOperatorAlgebra
