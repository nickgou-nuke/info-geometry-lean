/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.AlpogeDeligneFrobeniusBoundBridge
import InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore
import InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence
import InfoGeometry.Analysis.RectangleVerticalCauchyIntegral
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# InfoGeometry.Arithmetic.AlpogeDeligneKreinResidueBridge

Connects the scalar Frobenius-eigenvalue purity and spectral-radius engine of
`AlpogeDeligneFrobeniusBoundBridge` (`hexagon:2611.00789v1`) with:

1. **Scalar purity coordinates and a two-point reflection model**
   (`WeilLiKreinGhostEquivalence`):
   For `q > 1`, `α ≠ 0`, and weight-degree target `(w + i) / 2`, the centered
   logarithmic spectral coordinate
   `centeredSpectralPoint q w i α t := ⟨Real.log ‖α‖ / Real.log q - (w + i) / 2, t⟩`
   satisfies the exact equivalence:
   - Deligne purity `‖α‖ = q ^ ((w + i) / 2)`,
   - Critical-horizon membership `CriticalLine (1 / 2 + centeredSpectralPoint q w i α t)`,
   - positivity of the unrestricted two-point model pairing
     `∀ Φ, 0 ≤ weilPairMode _ Φ`, and
   - Apollonian unit-circle balance `Complex.normSq (apollonianDiskMap _) = 1`.
   This is only a scalar-coordinate equivalence plus a toy pairing property; it
   is not a Weil explicit-formula or Krein-space criterion.
2. **Finite positive-multiplicity simple-pole integrals**
   (`RectangleVerticalCauchyIntegral`):
   A single pole contributes its multiplicity times `2πi`. A finite family of
   positive integer multiplicities at poles strictly inside one rectangle has
   nonzero total contour integral. `finite_powerResolvent_cauchy_integral_nonzero`
   identifies the finite resolvent `-∑ m μ/(1 - μ z)` with that pole sum at
   `z = μ⁻¹`. `coeff_finitePowerResolventSeries` independently identifies its
   formal power-series coefficients with negative Frobenius power sums.
   Neither result proves a resolvent norm bound or the geometric eigenvalue
   theorem.
3. **Finite-dimensional operator trace passage**:
   `trace_pow_eq_sum_diagonal_powers_of_upperTriangular` identifies traces of
   powers with diagonal power sums for an explicitly upper-triangular complex
   matrix, and `spectrum_norm_le_of_trace_power_bound_of_upperTriangular`
   derives a bound for its whole spectrum from trace growth, including repeated
      diagonal values and Jordan blocks. Trace powers and characteristic roots are
      also transported across an explicit matrix similarity by
      `trace_pow_eq_of_matrix_similarity` and `charpoly_eq_of_matrix_similarity`.
      The `Module.End` results
   `trace_pow_eq_sum_eigenvalue_powers` and
   `eigenvalue_norm_le_of_trace_power_bound` retain their explicit eigenbasis
   hypothesis. Finite resolvent coefficients are identified with negative
   iterated traces. None of these results constructs triangular form or derives
   the trace-growth estimate from geometry.

Scope note: this bridge inherits the exact scalar/analytic scope of
`AlpogeDeligneFrobeniusBoundBridge` and does not construct schemes, constructible
`ℓ`-adic sheaves, or a geometric Frobenius action on étale cohomology.
-/

noncomputable section

open Complex Set
open InfoGeometry.Arithmetic.AlpogeDeligneFrobeniusBoundBridge
open InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence
open InfoGeometry.Analysis.RectangleVerticalCauchyIntegral

namespace InfoGeometry.Arithmetic.AlpogeDeligneKreinResidueBridge

private theorem upperTriangular_pow_isUpperTriangular
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (k : ℕ) :
    (A ^ k).IsUpperTriangular := by
  induction k with
  | zero =>
      intro i j hij
      change j < i at hij
      simp [ne_of_gt hij]
  | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l hl
      by_cases hli : l < i
      · simp [ih hli]
      · have hil : i ≤ l := le_of_not_gt hli
        have hjl : j < l := lt_of_lt_of_le hij hil
        simp [hA hjl]

private theorem upperTriangular_pow_diag
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (k : ℕ) (i : Fin n) :
    (A ^ k) i i = (A i i) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_eq_single i]
      · rw [ih, pow_succ]
      · intro j hj hji
        by_cases hji' : j < i
        · simp [upperTriangular_pow_isUpperTriangular A hA k hji']
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji') (Ne.symm hji)
          simp [hA hij]
      · simp

/-- For an upper-triangular complex matrix, the trace of every power is the
power sum of its diagonal entries. This includes Jordan blocks: no
diagonalizability assumption is used. -/
theorem trace_pow_eq_sum_diagonal_powers_of_upperTriangular
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (k : ℕ) :
    Matrix.trace (A ^ k) = ∑ i : Fin n, (A i i) ^ k := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact upperTriangular_pow_diag A hA k i

/-- A power-growth bound on traces controls every diagonal entry of an
upper-triangular matrix, with algebraic multiplicity counted by repeated
indices. In particular, the estimate applies to non-diagonalizable Jordan
blocks. -/
theorem diagonal_norm_le_of_trace_power_bound_of_upperTriangular
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) {C B : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ k : ℕ, 1 ≤ k →
      ‖Matrix.trace (A ^ k)‖ ≤ C * B ^ k) :
    ∀ i : Fin n, ‖A i i‖ ≤ B := by
  classical
  have hspec :=
    InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore.positive_multiplicity_power_sum_bound
      (Finset.univ : Finset (Fin n)) (fun i => A i i) (fun _ => 1)
      (C := C) (B := B) hB
  have hpos : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 < (1 : ℝ) := by
    intro i hi
    norm_num
  have hpow : ∀ k : ℕ, 1 ≤ k →
      ‖∑ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℂ) * (A i i) ^ k‖ ≤ C * B ^ k := by
    intro k hk
    simpa [trace_pow_eq_sum_diagonal_powers_of_upperTriangular A hA k] using
      hBound k hk
  intro i
  exact hspec hpos hpow i (Finset.mem_univ i)

/-- Every spectral value of an upper-triangular complex matrix is bounded by
the same trace-power estimate. The characteristic polynomial factorization
reduces a spectral value to one diagonal entry; repeated diagonal values retain
their multiplicities in the preceding power-sum bound. -/
theorem spectrum_norm_le_of_trace_power_bound_of_upperTriangular
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) {C B : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ k : ℕ, 1 ≤ k →
      ‖Matrix.trace (A ^ k)‖ ≤ C * B ^ k) :
    ∀ α ∈ spectrum ℂ A, ‖α‖ ≤ B := by
  have hdiag := diagonal_norm_le_of_trace_power_bound_of_upperTriangular A hA hB hBound
  intro α hα
  have hroot : Polynomial.IsRoot A.charpoly α :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hα
  rw [Polynomial.IsRoot.def,
    Matrix.charpoly_of_isUpperTriangular A hA, Polynomial.eval_prod] at hroot
  obtain ⟨i, hi, hfactor⟩ := (Finset.prod_eq_zero_iff.mp hroot)
  have hvalue : α = A i i := sub_eq_zero.mp (by simpa using hfactor)
  rw [hvalue]
  exact hdiag i

/-- Trace of every natural power is invariant under an explicit matrix
similarity. The inverse equations are stated separately to keep the carrier
and multiplication convention visible. -/
theorem trace_pow_eq_of_matrix_similarity
    {n : ℕ} (A B P Q : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hA : A = P * B * Q) (k : ℕ) :
    Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by
  have hpow (k : ℕ) : A ^ k = P * B ^ k * Q := by
    induction k with
    | zero => simp [hPQ]
    | succ k ih =>
        calc
          A ^ (k + 1) = A ^ k * A := by rw [pow_succ]
          _ = (P * B ^ k * Q) * (P * B * Q) := by rw [ih, hA]
          _ = P * (B ^ k * (Q * P) * B) * Q := by noncomm_ring
          _ = P * (B ^ k * B) * Q := by rw [hQP, mul_one]
          _ = P * B ^ (k + 1) * Q := by rw [pow_succ]
  rw [hpow k]
  calc
    Matrix.trace (P * B ^ k * Q) = Matrix.trace (P * (B ^ k * Q)) := by rw [mul_assoc]
    _ = Matrix.trace ((B ^ k * Q) * P) := Matrix.trace_mul_comm P (B ^ k * Q)
    _ = Matrix.trace (B ^ k * (Q * P)) := by rw [mul_assoc]
    _ = Matrix.trace (B ^ k) := by rw [hQP, mul_one]

/-- Similar matrices have the same characteristic polynomial, with explicit
left and right inverse witnesses for the change-of-basis matrices. -/
theorem charpoly_eq_of_matrix_similarity
    {n : ℕ} (A B P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hA : A = P * B * Q) :
    A.charpoly = B.charpoly := by
  calc
    A.charpoly = (P * B * Q).charpoly := congrArg Matrix.charpoly hA
    _ = (Q * (P * B)).charpoly := Matrix.charpoly_mul_comm (P * B) Q
    _ = ((Q * P) * B).charpoly := by rw [mul_assoc]
    _ = B.charpoly := by rw [hQP, one_mul]

/-- Similarity transports the trace-power spectral estimate from an explicitly
upper-triangular representative to the original matrix. The hypotheses are
only the two inverse equations and the factorization; no Schur decomposition
is asserted to exist here. -/
theorem spectrum_norm_le_of_trace_power_bound_of_similar_upperTriangular
    {n : ℕ} (A B P Q : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hA : A = P * B * Q)
    (hB : B.IsUpperTriangular) {C R : ℝ} (hR : 0 ≤ R)
    (hBound : ∀ k : ℕ, 1 ≤ k →
      ‖Matrix.trace (A ^ k)‖ ≤ C * R ^ k) :
    ∀ α ∈ spectrum ℂ A, ‖α‖ ≤ R := by
  have hBoundB : ∀ k : ℕ, 1 ≤ k →
      ‖Matrix.trace (B ^ k)‖ ≤ C * R ^ k := by
    intro k hk
    rw [← trace_pow_eq_of_matrix_similarity A B P Q hPQ hQP hA k]
    exact hBound k hk
  have hspecB :=
    spectrum_norm_le_of_trace_power_bound_of_upperTriangular B hB hR hBoundB
  intro α hα
  have hαroot : Polynomial.IsRoot A.charpoly α :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hα
  have hβroot : Polynomial.IsRoot B.charpoly α := by
    rw [← charpoly_eq_of_matrix_similarity A B P Q hQP hA]
    exact hαroot
  exact hspecB α ((Matrix.mem_spectrum_iff_isRoot_charpoly).mpr hβroot)

/-! ### Actual finite-dimensional trace sequences from an eigenbasis

The scalar positive-multiplicity estimate can be applied to traces only after
an operator and its spectral decomposition have been supplied. The next two
lemmas make that finite-dimensional passage explicit; they do not assume a
geometric trace formula or construct a Frobenius action.
-/

theorem trace_pow_eq_sum_eigenvalue_powers
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (b : Module.Basis ι ℂ V) (F : Module.End ℂ V) (μ : ι → ℂ)
    (hEig : ∀ i, F (b i) = μ i • b i) (n : ℕ) :
    LinearMap.trace ℂ V (F ^ n) = ∑ i, μ i ^ n := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  have hdiag : LinearMap.toMatrix b b F = Matrix.diagonal μ := by
    ext i j
    by_cases hij : i = j <;>
      simp [LinearMap.toMatrix_apply, hEig, Matrix.diagonal, hij]
  rw [← LinearMap.toMatrix_pow, hdiag, Matrix.diagonal_pow,
    Matrix.trace_diagonal]
  simp only [Pi.pow_apply]

theorem eigenvalue_norm_le_of_trace_power_bound
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (b : Module.Basis ι ℂ V) (F : Module.End ℂ V) (μ : ι → ℂ)
    (hEig : ∀ i, F (b i) = μ i • b i)
    {C B : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ n : ℕ, 1 ≤ n →
      ‖LinearMap.trace ℂ V (F ^ n)‖ ≤ C * B ^ n) :
    ∀ i, ‖μ i‖ ≤ B := by
  have hspec :=
    InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore.positive_multiplicity_power_sum_bound
      (Finset.univ : Finset ι) μ (fun _ => 1) (C := C) (B := B) hB
  have hpos : ∀ i ∈ (Finset.univ : Finset ι), 0 < (1 : ℝ) := by
    intro i hi
    norm_num
  have hpow : ∀ n : ℕ, 1 ≤ n →
      ‖∑ i ∈ (Finset.univ : Finset ι), (1 : ℂ) * μ i ^ n‖ ≤ C * B ^ n := by
    intro n hn
    simpa [trace_pow_eq_sum_eigenvalue_powers b F μ hEig n] using hBound n hn
  intro i
  exact hspec hpos hpow i (Finset.mem_univ i)

/-- Formal geometric expansion of the single-eigenvalue resolvent summand
`-m μ / (1 - μ z)`. -/
def localPowerResolventSeries (μ : ℂ) (m : ℕ) : PowerSeries ℂ :=
  -(PowerSeries.C ((m : ℂ) * μ) * PowerSeries.mk (fun n : ℕ => μ ^ n))

/-- The coefficient of degree `n` in a local power resolvent is
`-m μ^(n+1)`. -/
theorem coeff_localPowerResolventSeries (μ : ℂ) (m n : ℕ) :
    PowerSeries.coeff n (localPowerResolventSeries μ m) =
      -((m : ℂ) * μ ^ (n + 1)) := by
  simp only [localPowerResolventSeries, map_neg, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk]
  rw [pow_succ]
  ring

/-- The geometric power series is an inverse of its linear Euler factor. -/
theorem geometricSeries_mul_linearResolventFactor (μ : ℂ) :
    PowerSeries.mk (fun n : ℕ => μ ^ n) *
      (1 - PowerSeries.C μ * PowerSeries.X) = 1 := by
  simpa [PowerSeries.rescale_mk, PowerSeries.rescale_X] using
    congrArg (PowerSeries.rescale μ)
      (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)

/-- Multiplying the formal local resolvent by its Euler factor recovers its
constant residue coefficient. -/
theorem localPowerResolventSeries_mul_linearFactor (μ : ℂ) (m : ℕ) :
    localPowerResolventSeries μ m *
      (1 - PowerSeries.C μ * PowerSeries.X) =
        -PowerSeries.C ((m : ℂ) * μ) := by
  rw [localPowerResolventSeries]
  calc
    -(PowerSeries.C ((m : ℂ) * μ) * PowerSeries.mk (fun n : ℕ => μ ^ n)) *
        (1 - PowerSeries.C μ * PowerSeries.X) =
      -(PowerSeries.C ((m : ℂ) * μ) *
        (PowerSeries.mk (fun n : ℕ => μ ^ n) *
          (1 - PowerSeries.C μ * PowerSeries.X))) := by ring
    _ = -PowerSeries.C ((m : ℂ) * μ) := by
      rw [geometricSeries_mul_linearResolventFactor]
      simp

/-- Finite sum of local Frobenius power resolvents as an honest Mathlib formal
power series. -/
def finitePowerResolventSeries {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (μ : ι → ℂ) (m : ι → ℕ) : PowerSeries ℂ :=
  ∑ j ∈ S, localPowerResolventSeries (μ j) (m j)

/-- The finite resolvent's formal coefficients are exactly the negative
Frobenius power sums, with multiplicities retained. -/
theorem coeff_finitePowerResolventSeries
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (μ : ι → ℂ) (m : ι → ℕ) (n : ℕ) :
    PowerSeries.coeff n (finitePowerResolventSeries S μ m) =
      -∑ j ∈ S, (m j : ℂ) * (μ j) ^ (n + 1) := by
  simp [finitePowerResolventSeries, coeff_localPowerResolventSeries,
    Finset.sum_neg_distrib]

/-- For a finite-dimensional endomorphism with an explicit eigenbasis, the
coefficients of its finite power resolvent are the negatives of its actual
iterated traces. The multiplicity-one index set is the eigenbasis index. -/
theorem coeff_finitePowerResolventSeries_eq_neg_trace_pow_of_eigenbasis
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (b : Module.Basis ι ℂ V) (F : Module.End ℂ V) (μ : ι → ℂ)
    (hEig : ∀ i, F (b i) = μ i • b i) (n : ℕ) :
    PowerSeries.coeff n
        (finitePowerResolventSeries (Finset.univ : Finset ι) μ (fun _ => 1)) =
      -LinearMap.trace ℂ V (F ^ (n + 1)) := by
  rw [coeff_finitePowerResolventSeries,
    trace_pow_eq_sum_eigenvalue_powers b F μ hEig]
  simp

/-- A coefficient-growth bound on the actual finite operator resolvent implies
the eigenvalue radius bound, provided the operator has the stated eigenbasis.
The exponent shift is exactly the resolvent convention: coefficient `n`
records the trace of the `(n + 1)`-st iterate. -/
theorem eigenvalue_norm_le_of_finitePowerResolvent_coeff_bound
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (b : Module.Basis ι ℂ V) (F : Module.End ℂ V) (μ : ι → ℂ)
    (hEig : ∀ i, F (b i) = μ i • b i)
    {C B : ℝ} (hB : 0 ≤ B)
    (hCoeff : ∀ n : ℕ,
      ‖PowerSeries.coeff n
          (finitePowerResolventSeries (Finset.univ : Finset ι) μ (fun _ => 1))‖ ≤
        C * B ^ (n + 1)) :
    ∀ i, ‖μ i‖ ≤ B := by
  apply eigenvalue_norm_le_of_trace_power_bound b F μ hEig hB
  intro k hk
  let n := k - 1
  have hn : n + 1 = k := Nat.sub_add_cancel hk
  have hcoeff := coeff_finitePowerResolventSeries_eq_neg_trace_pow_of_eigenbasis
    b F μ hEig n
  rw [hn] at hcoeff
  have hnorm : ‖LinearMap.trace ℂ V (F ^ k)‖ =
      ‖PowerSeries.coeff n
        (finitePowerResolventSeries (Finset.univ : Finset ι) μ (fun _ => 1))‖ := by
    rw [hcoeff, norm_neg]
  rw [hnorm]
  simpa [hn] using hCoeff n

/-- Exponential coefficient control for a finite positive-multiplicity
resolvent forces the same radius bound on each spectral value. The coefficient
of degree `n` is the negative power sum at exponent `n + 1`; positivity lets
the existing power-sum theorem group coincident eigenvalues without cancellation.
This implication is the norm-growth input needed alongside, and distinct from,
the positive-residue contour identity below. -/
theorem finitePowerResolvent_coeff_bound_implies_spectral_bound
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (μ : ι → ℂ) (m : ι → ℕ) {C B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ j ∈ S, 0 < m j)
    (hcoeff : ∀ n : ℕ,
      ‖PowerSeries.coeff n (finitePowerResolventSeries S μ m)‖ ≤ C * B ^ (n + 1)) :
    ∀ j ∈ S, ‖μ j‖ ≤ B := by
  apply InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore.positive_multiplicity_power_sum_bound
    S μ (fun j => (m j : ℝ)) hB
  · intro j hj
    exact_mod_cast hm j hj
  · intro n hn
    let k := n - 1
    have hk : k + 1 = n := Nat.sub_add_cancel hn
    have hseries := coeff_finitePowerResolventSeries S μ m k
    have hpow :
        (∑ j ∈ S, ((m j : ℝ) : ℂ) * (μ j) ^ n) =
          ∑ j ∈ S, (m j : ℂ) * (μ j) ^ (k + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Complex.ofReal_natCast]
      rw [hk]
    calc
      ‖∑ j ∈ S, ((m j : ℝ) : ℂ) * (μ j) ^ n‖ =
          ‖∑ j ∈ S, (m j : ℂ) * (μ j) ^ (k + 1)‖ := congrArg norm hpow
      _ = ‖-∑ j ∈ S, (m j : ℂ) * (μ j) ^ (k + 1)‖ := by rw [norm_neg]
      _ = ‖PowerSeries.coeff k (finitePowerResolventSeries S μ m)‖ := by
            rw [← hseries]
      _ ≤ C * B ^ n := by simpa [hk] using hcoeff k

/-- Weight-normalized Frobenius eigenvalue `α / q ^ ((w + i) / 2)`. -/
def normalizedFrobenius (q w i : ℝ) (α : ℂ) : ℂ :=
  α / ((q ^ ((w + i) / 2) : ℝ) : ℂ)

/-- Under Deligne purity `‖α‖ = q ^ ((w + i) / 2)` with `q > 0`, the normalized
Frobenius eigenvalue lies on the complex unit circle (`normSq = 1`). -/
theorem normalizedFrobenius_normSq_eq_one_of_purity
    {q w i : ℝ} (hq : 0 < q) {α : ℂ}
    (hpure : ‖α‖ = q ^ ((w + i) / 2)) :
    Complex.normSq (normalizedFrobenius q w i α) = 1 := by
  have hqpow : 0 < q ^ ((w + i) / 2) := Real.rpow_pos_of_pos hq _
  have hnorm : ‖normalizedFrobenius q w i α‖ = 1 := by
    rw [normalizedFrobenius, norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hqpow),
      hpure, div_self (ne_of_gt hqpow)]
  rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]

/-- Centered logarithmic spectral coordinate of a nonzero Frobenius eigenvalue `α`
relative to weight `w + i` at arbitrary imaginary height `t`. -/
def centeredSpectralPoint (q w i : ℝ) (α : ℂ) (t : ℝ) : ℂ :=
  ⟨Real.log ‖α‖ / Real.log q - (w + i) / 2, t⟩

@[simp] theorem centeredSpectralPoint_re (q w i : ℝ) (α : ℂ) (t : ℝ) :
    (centeredSpectralPoint q w i α t).re = Real.log ‖α‖ / Real.log q - (w + i) / 2 :=
  rfl

/-- For `q > 1` and `α ≠ 0`, Deligne purity `‖α‖ = q ^ ((w + i) / 2)` is
equivalent to vanishing real part of the centered logarithmic spectral point. -/
theorem purity_iff_centeredSpectralPoint_re_eq_zero
    {q w i : ℝ} (hq : 1 < q) {α : ℂ} (hα : α ≠ 0) (t : ℝ) :
    ‖α‖ = q ^ ((w + i) / 2) ↔ (centeredSpectralPoint q w i α t).re = 0 := by
  have hqpos : 0 < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hlogq_ne : Real.log q ≠ 0 := ne_of_gt hlogq
  have hnorm_pos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hqpow_pos : 0 < q ^ ((w + i) / 2) := Real.rpow_pos_of_pos hqpos _
  rw [centeredSpectralPoint_re, sub_eq_zero, div_eq_iff hlogq_ne]
  constructor
  · intro h
    rw [h, Real.log_rpow hqpos]
  · intro h
    have hlog : Real.log ‖α‖ = Real.log (q ^ ((w + i) / 2)) := by
      rw [Real.log_rpow hqpos, h]
    exact Real.log_injOn_pos hnorm_pos hqpow_pos hlog

/-- Scalar purity is equivalent to centered-coordinate vanishing, positivity
for the unrestricted two-point reflection model, and Cayley unit-circle
balance. The pairing clause is not a global Weil or Krein criterion. -/
theorem scalarPurity_iff_centered_coordinate_and_toy_pairing
    {q w i : ℝ} (hq : 1 < q) {α : ℂ} (hα : α ≠ 0) (t : ℝ) :
    (‖α‖ = q ^ ((w + i) / 2) ↔ (centeredSpectralPoint q w i α t).re = 0) ∧
    (‖α‖ = q ^ ((w + i) / 2) ↔
      ∀ Φ : ℂ → ℂ, 0 ≤ weilPairMode (centeredSpectralPoint q w i α t) Φ) ∧
    (‖α‖ = q ^ ((w + i) / 2) ↔
      Complex.normSq (apollonianDiskMap (centeredSpectralPoint q w i α t)) = 1) ∧
    (‖α‖ ≠ q ^ ((w + i) / 2) →
      ∃ Φ : ℂ → ℂ,
        weilPairMode (centeredSpectralPoint q w i α t) Φ = -2 ∧
        weilPairMode (centeredSpectralPoint q w i α t) Φ < 0) := by
  have hre := purity_iff_centeredSpectralPoint_re_eq_zero (w := w) (i := i) hq hα t
  refine ⟨hre,
    hre.trans (re_eq_zero_iff_forall_weilPairMode_nonneg _),
    hre.trans (normSq_apollonianDiskMap_eq_one_iff_re_eq_zero _).symm,
    fun hne => exists_negative_weilPairMode_of_re_ne_zero (fun h0 => hne (hre.mpr h0))⟩

/-- Positive-multiplicity simple-pole Cauchy rectangle residue is strictly nonzero:
for `0 < m` and `ρ` strictly inside the rectangle `(z, w)`,
`∮ (m : ℂ) * (s - ρ)⁻¹ ds = (m : ℂ) * (2 * π * I) ≠ 0`. -/
theorem positiveMultiplicity_pole_cauchyResidue_nonzero
    {z w ρ : ℂ} (hρ : ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    {m : ℕ} (hm : 0 < m) :
    rectangleIntegral (fun s : ℂ ↦ (m : ℂ) * (s - ρ)⁻¹) z w =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ∧
      rectangleIntegral (fun s : ℂ ↦ (m : ℂ) * (s - ρ)⁻¹) z w ≠ 0 := by
  have heq : rectangleIntegral (fun s : ℂ ↦ (m : ℂ) * (s - ρ)⁻¹) z w =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [rectangleIntegral_const_mul, rectangleIntegral_sub_inv hρ]
  refine ⟨heq, ?_⟩
  rw [heq]
  have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero hm_ne (mul_ne_zero (mul_ne_zero two_ne_zero hpi_ne) Complex.I_ne_zero)

/-- A finite sum of simple poles, all strictly inside one rectangle and with
positive integer multiplicities, has nonzero contour integral. This uses
linearity and positivity of the sum of multiplicities; it does not assert a
cohomological trace formula. -/
theorem finite_positiveMultiplicities_pole_cauchyResidue_nonzero
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {z w : ℂ} (hρ : ∀ j ∈ S, ρ j ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hm : ∀ j ∈ S, 0 < m j) (hS : S.Nonempty) :
    rectangleIntegral (fun s : ℂ ↦ ∑ j ∈ S, (m j : ℂ) * (s - ρ j)⁻¹) z w ≠ 0 := by
  obtain ⟨j₀, hj₀⟩ := hS
  have hw : z.re ≤ w.re := ((hρ j₀ hj₀).1.1.le).trans (hρ j₀ hj₀).1.2.le
  have ht : z.im ≤ w.im := ((hρ j₀ hj₀).2.1.le).trans (hρ j₀ hj₀).2.2.le
  let boundary : Set ℂ :=
    (Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)
  have heq : rectangleIntegral (fun s : ℂ ↦ ∑ j ∈ S, (m j : ℂ) * (s - ρ j)⁻¹) z w =
      (∑ j ∈ S, (m j : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
    calc
      _ = ∑ j ∈ S, rectangleIntegral (fun s : ℂ ↦ (m j : ℂ) * (s - ρ j)⁻¹) z w :=
        rectangleIntegral_finsetSum hw ht (by
          intro j hj
          apply continuousOn_const.mul
          apply (continuousOn_id.sub continuousOn_const).inv₀
          intro s hs hzero
          have heq : s = ρ j := sub_eq_zero.mp hzero
          apply hs.2
          simpa [heq] using hρ j hj)
      _ = ∑ j ∈ S, (m j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [rectangleIntegral_const_mul, rectangleIntegral_sub_inv (hρ j hj)]
      _ = _ := by rw [Finset.sum_mul]
  rw [heq]
  apply mul_ne_zero
  · have hpos : 0 < ∑ j ∈ S, m j :=
      Finset.sum_pos' (fun j hj => (hm j hj).le) ⟨j₀, hj₀, hm j₀ hj₀⟩
    have hsum_ne : ((∑ j ∈ S, m j : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)
    simpa only [Nat.cast_sum] using hsum_ne
  · exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

/-- A finite Frobenius power resolvent has the same contour integral as the
positive-multiplicity simple-pole sum at the reciprocal eigenvalues. The
negative sign in front of the resolvent is essential:
`-μ / (1 - μ z) = 1 / (z - μ⁻¹)`. This is an exact finite-dimensional
residue calculation; it supplies neither a bound on the resolvent nor the
geometric cohomology trace formula. -/
theorem finite_powerResolvent_cauchy_integral_nonzero
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (μ : ι → ℂ) (m : ι → ℕ)
    (hμ : ∀ j ∈ S, μ j ≠ 0)
    {z w : ℂ}
    (hρ : ∀ j ∈ S, (μ j)⁻¹ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hm : ∀ j ∈ S, 0 < m j) (hS : S.Nonempty) :
    rectangleIntegral
      (fun s : ℂ ↦ -∑ j ∈ S, (m j : ℂ) * μ j * (1 - μ j * s)⁻¹) z w ≠ 0 := by
  have hterms : ∀ j ∈ S,
      (fun s : ℂ ↦ -((m j : ℂ) * μ j * (1 - μ j * s)⁻¹)) =
        fun s : ℂ ↦ (m j : ℂ) * (s - (μ j)⁻¹)⁻¹ := by
    intro j hj
    funext s
    by_cases hden : 1 - μ j * s = 0
    · have hprod : μ j * s = 1 := by linear_combination -hden
      have hs : s = (μ j)⁻¹ := by
        calc
          s = ((μ j)⁻¹ * μ j) * s := by rw [inv_mul_cancel₀ (hμ j hj), one_mul]
          _ = (μ j)⁻¹ * (μ j * s) := by ring
          _ = (μ j)⁻¹ := by rw [hprod, mul_one]
      rw [hden, inv_zero, mul_zero, neg_zero]
      rw [hs, sub_self, inv_zero, mul_zero]
    · have hden₂ : s - (μ j)⁻¹ ≠ 0 := by
        intro hs
        apply hden
        rw [sub_eq_zero.mp hs]
        simp [mul_inv_cancel₀ (hμ j hj)]
      have hinv : (s - (μ j)⁻¹)⁻¹ = -μ j * (1 - μ j * s)⁻¹ := by
        symm
        apply eq_inv_of_mul_eq_one_left
        field_simp [hden, hden₂, hμ j hj]
        ring
      rw [hinv]
      ring
  have hfun :
      (fun s : ℂ ↦ -∑ j ∈ S, (m j : ℂ) * μ j * (1 - μ j * s)⁻¹) =
        fun s : ℂ ↦ ∑ j ∈ S, (m j : ℂ) * (s - (μ j)⁻¹)⁻¹ := by
    funext s
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrFun (hterms j hj) s
  rw [hfun]
  exact finite_positiveMultiplicities_pole_cauchyResidue_nonzero
    S (fun j => (μ j)⁻¹) m hρ hm hS

end InfoGeometry.Arithmetic.AlpogeDeligneKreinResidueBridge
