/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Holography.RyuTakayanagiEmergence
import InfoGeometry.Canonical.RyuTakayanagiEntanglementBridge
import InfoGeometry.Canonical.TrialitySpin8Permutations

/-!
# Ryu–Takayanagi Holographic Entropy, Hyperbolic Geodesic Area, and Spin(8) Triality

Formalizes:
1. Finite-dimensional quantum `DensityMatrix n` carriers (`mat.IsHermitian`, `mat.PosSemidef`,
   `mat.trace = 1`) with constructive pure-state and maximally-mixed inhabitants (`T17`);
2. Spectral `vonNeumannEntropy ρ = - ∑ i, λ_i log λ_i` via Mathlib's `Matrix.IsHermitian.eigenvalues`,
   proving non-negativity, vanishing on pure states, `Real.log 2` on `maxMixed2` (matching
   `RyuTakayanagiEmergence.vonNeumannEntropy`), and exact unitary invariance via
   `Matrix.charpoly_mul_comm` and `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff`;
3. Genuine hyperbolic Poincaré geodesic distance `poincareGeodesicArea` on Mathlib's
   `UpperHalfPlane` (`ℍ`), proving `SL(2, ℝ)` bulk-isometry invariance, the AdS₃/CFT₂ cutoff
   interval `Real.arcosh (1 + (x₁ - x₂)^2 / (2 ε^2))` formula, and exact equality with
   `RyuTakayanagiEntanglementBridge.minimalSurfaceArea n = n * Real.log 2`;
4. Constructive `TrialityGroup := Equiv.Perm TrialitySector` (`S₃`) unitary representation on the
   `24`-dimensional `8_v ⊕ 8_s ⊕ 8_c` carrier (`Fin 24`) and order-3 `axisTrialityUnitary` on
   `Fin 8`, proving `entanglement_triality_invariance` and `ryu_takayanagi_triality_equivariance`.
-/

noncomputable section

namespace InfoGeometry.Holography.RyuTakayanagiTriality

open Matrix
open scoped UpperHalfPlane MatrixGroups BigOperators ComplexOrder
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Holography.RyuTakayanagiEmergence
open InfoGeometry.Canonical.RyuTakayanagiEntanglementBridge
open InfoGeometry.Canonical.TrialitySpin8Permutations

/-! ## 1. Finite-Dimensional Quantum Density Matrices & Constructive Inhabitants -/

/-- A finite-dimensional quantum density matrix: Hermitian, positive semidefinite, unit trace. -/
structure DensityMatrix (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℂ
  isHermitian : mat.IsHermitian
  posSemidef : mat.PosSemidef
  trace_one : Matrix.trace mat = 1

/-- Rank-1 projector `|0⟩⟨0|` matrix on `Fin n`. -/
def projZeroMatrix (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

theorem projZeroMatrix_conjTranspose (n : ℕ) [NeZero n] :
    (projZeroMatrix n)ᴴ = projZeroMatrix n := by
  ext i j
  simp only [Matrix.conjTranspose_apply, projZeroMatrix, Matrix.of_apply]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

theorem projZeroMatrix_mul_self (n : ℕ) [NeZero n] :
    projZeroMatrix n * projZeroMatrix n = projZeroMatrix n := by
  ext i j
  simp only [Matrix.mul_apply, projZeroMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (0 : Fin n)]
  · by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]
  · intro k _ hk
    simp [hk]
  · intro h0
    exact absurd (Finset.mem_univ (0 : Fin n)) h0

theorem projZeroMatrix_mul_conjTranspose (n : ℕ) [NeZero n] :
    projZeroMatrix n * (projZeroMatrix n)ᴴ = projZeroMatrix n := by
  rw [projZeroMatrix_conjTranspose, projZeroMatrix_mul_self]

/-- Constructive pure-state density matrix `|0⟩⟨0|` for any `n ≥ 1`. -/
def pureState0 (n : ℕ) [NeZero n] : DensityMatrix n where
  mat := projZeroMatrix n
  isHermitian := projZeroMatrix_conjTranspose n
  posSemidef := by
    rw [← projZeroMatrix_mul_conjTranspose n]
    exact Matrix.posSemidef_self_mul_conjTranspose (projZeroMatrix n)
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, projZeroMatrix, Matrix.of_apply]
    rw [Finset.sum_eq_single (0 : Fin n)]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h0
      exact absurd (Finset.mem_univ (0 : Fin n)) h0

/-- Constructive `Inhabited` instance for `DensityMatrix n` whenever `NeZero n`. -/
instance instInhabitedDensityMatrix (n : ℕ) [NeZero n] : Inhabited (DensityMatrix n) :=
  ⟨pureState0 n⟩

/-- Maximally mixed qubit density matrix `I₂ / 2` in dimension `2`. -/
def maxMixed2 : DensityMatrix 2 where
  mat := ((1 / 2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  isHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  posSemidef := by
    let rootHalf : Matrix (Fin 2) (Fin 2) ℂ :=
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    have hfac : rootHalf * rootHalfᴴ = ((1 / 2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
        rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
        norm_num
      have hsqC : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
        have : (((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
          congrArg ((↑) : ℝ → ℂ) hsq
        simpa [one_div] using this
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rootHalf, Matrix.mul_apply, Fin.sum_univ_two, hsqC]
    rw [← hfac]
    exact Matrix.posSemidef_self_mul_conjTranspose rootHalf
  trace_one := by
    simp [Matrix.trace, Matrix.diag]

/-- Binder-free canonical `DensityMatrix 2` inhabitant (satisfies Gate 2.5 / T17). -/
def canonicalDensityMatrix : DensityMatrix 2 := maxMixed2

/-- Unitary conjugation `U ρ U†` of a density matrix. -/
def unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ : DensityMatrix n) :
    DensityMatrix n where
  mat := (U : Matrix (Fin n) (Fin n) ℂ) * ρ.mat * star (U : Matrix (Fin n) (Fin n) ℂ)
  isHermitian := by
    change ((U : Matrix (Fin n) (Fin n) ℂ) * ρ.mat * star (U : Matrix (Fin n) (Fin n) ℂ))ᴴ =
      (U : Matrix (Fin n) (Fin n) ℂ) * ρ.mat * star (U : Matrix (Fin n) (Fin n) ℂ)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
      star_star, ρ.isHermitian.eq, Matrix.mul_assoc]
    rfl
  posSemidef := by
    have hU : (U : Matrix (Fin n) (Fin n) ℂ) * ρ.mat * star (U : Matrix (Fin n) (Fin n) ℂ) =
        ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ)ᴴ * ρ.mat * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
      rw [Matrix.conjTranspose_conjTranspose]
      rfl
    rw [hU]
    exact ρ.posSemidef.conjTranspose_mul_mul_same (U : Matrix (Fin n) (Fin n) ℂ)ᴴ
  trace_one := by
    calc
      Matrix.trace ((U : Matrix (Fin n) (Fin n) ℂ) * ρ.mat * star (U : Matrix (Fin n) (Fin n) ℂ)) =
          Matrix.trace (star (U : Matrix (Fin n) (Fin n) ℂ) *
            ((U : Matrix (Fin n) (Fin n) ℂ) * ρ.mat)) :=
        Matrix.trace_mul_comm ((U : Matrix (Fin n) (Fin n) ℂ) * ρ.mat)
          (star (U : Matrix (Fin n) (Fin n) ℂ))
      _ = Matrix.trace ((star (U : Matrix (Fin n) (Fin n) ℂ) *
            (U : Matrix (Fin n) (Fin n) ℂ)) * ρ.mat) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ρ.mat := by rw [Unitary.coe_star_mul_self, Matrix.one_mul]
      _ = 1 := ρ.trace_one

/-! ## 2. Spectral Von Neumann Entropy & Unitary Invariance -/

/-- Spectral von Neumann entropy `S(ρ) = -∑ i, λᵢ log λᵢ` using `Matrix.IsHermitian.eigenvalues`. -/
noncomputable def vonNeumannEntropy {n : ℕ} (ρ : DensityMatrix n) : ℝ :=
  - ∑ i : Fin n, ρ.isHermitian.eigenvalues i * Real.log (ρ.isHermitian.eigenvalues i)

/-- Every eigenvalue of a density matrix is non-negative. -/
theorem eigenvalue_nonneg {n : ℕ} (ρ : DensityMatrix n) (i : Fin n) :
    0 ≤ ρ.isHermitian.eigenvalues i :=
  ρ.posSemidef.eigenvalues_nonneg i

/-- The real eigenvalues of a density matrix sum to `1`. -/
theorem sum_eigenvalues_eq_one {n : ℕ} (ρ : DensityMatrix n) :
    ∑ i : Fin n, ρ.isHermitian.eigenvalues i = 1 := by
  have htr : ρ.mat.trace = ∑ i : Fin n, (ρ.isHermitian.eigenvalues i : ℂ) :=
    ρ.isHermitian.trace_eq_sum_eigenvalues
  have hre := congrArg Complex.re htr
  rw [ρ.trace_one] at hre
  simpa using hre.symm

/-- Every eigenvalue of a density matrix lies in `[0, 1]`. -/
theorem eigenvalue_le_one {n : ℕ} (ρ : DensityMatrix n) (i : Fin n) :
    ρ.isHermitian.eigenvalues i ≤ 1 := by
  rw [← sum_eigenvalues_eq_one ρ]
  exact Finset.single_le_sum (fun j _ => eigenvalue_nonneg ρ j) (Finset.mem_univ i)

/-- Von Neumann entropy of any finite-dimensional density matrix is non-negative. -/
theorem vonNeumannEntropy_nonneg {n : ℕ} (ρ : DensityMatrix n) :
    0 ≤ vonNeumannEntropy ρ := by
  unfold vonNeumannEntropy
  rw [neg_nonneg]
  refine Finset.sum_nonpos fun i _ => ?_
  have h0 : 0 ≤ ρ.isHermitian.eigenvalues i := eigenvalue_nonneg ρ i
  have h1 : ρ.isHermitian.eigenvalues i ≤ 1 := eigenvalue_le_one ρ i
  rcases eq_or_lt_of_le h0 with hzero | _
  · simp [← hzero]
  · exact mul_nonpos_of_nonneg_of_nonpos h0 (Real.log_nonpos h0 h1)

/-- Pure state `|0⟩⟨0|` has zero von Neumann entropy (its eigenvalues lie in `{0, 1}`). -/
theorem vonNeumannEntropy_pureState0 (n : ℕ) [NeZero n] :
    vonNeumannEntropy (pureState0 n) = 0 := by
  unfold vonNeumannEntropy
  have hterm : ∀ i : Fin n,
      (pureState0 n).isHermitian.eigenvalues i *
        Real.log ((pureState0 n).isHermitian.eigenvalues i) = 0 := by
    intro i
    set lam := (pureState0 n).isHermitian.eigenvalues i
    have hmem : lam ∈ spectrum ℝ (pureState0 n).mat :=
      (pureState0 n).isHermitian.eigenvalues_mem_spectrum_real i
    have hidem : (pureState0 n).mat * (pureState0 n).mat = (pureState0 n).mat :=
      projZeroMatrix_mul_self n
    by_cases h0 : lam = 0
    · simp [h0]
    · by_cases h1 : lam = 1
      · simp [h1]
      · exfalso
        rw [spectrum.mem_iff] at hmem
        apply hmem
        have h1m : (1 - (lam : ℂ)) ≠ 0 := by
          intro h
          apply h1
          have := congrArg Complex.re h
          simpa using (sub_eq_zero.mp this).symm
        have hlamc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
        have hlam1 : ((lam : ℂ) - 1) ≠ 0 := by
          intro h; apply h1m; linear_combination -h
        have hlam_alg : algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) lam =
            (lam : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
          ext a b
          simp [Algebra.algebraMap_eq_smul_one, Complex.real_smul]
        have hmulR :
            (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) lam - (pureState0 n).mat) *
              (((lam - 1 : ℂ)⁻¹) • (pureState0 n).mat +
                ((lam : ℂ)⁻¹) • ((1 : Matrix (Fin n) (Fin n) ℂ) - (pureState0 n).mat)) = 1 := by
          rw [hlam_alg]
          simp only [sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
          rw [hidem]
          ext a b
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
            smul_eq_mul]
          field_simp [hlamc, hlam1]
          ring
        have hmulL :
            (((lam - 1 : ℂ)⁻¹) • (pureState0 n).mat +
              ((lam : ℂ)⁻¹) • ((1 : Matrix (Fin n) (Fin n) ℂ) - (pureState0 n).mat)) *
              (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) lam - (pureState0 n).mat) = 1 := by
          rw [hlam_alg]
          simp only [add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
          rw [hidem]
          ext a b
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
            smul_eq_mul]
          field_simp [hlamc, hlam1]
          ring
        exact ⟨⟨algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) lam - (pureState0 n).mat,
          ((lam - 1 : ℂ)⁻¹) • (pureState0 n).mat +
            ((lam : ℂ)⁻¹) • ((1 : Matrix (Fin n) (Fin n) ℂ) - (pureState0 n).mat),
          hmulR, hmulL⟩, rfl⟩
  simp [hterm]

/-- Every eigenvalue of `maxMixed2` equals `1 / 2`. -/
theorem maxMixed2_eigenvalues (i : Fin 2) :
    maxMixed2.isHermitian.eigenvalues i = 1 / 2 := by
  have hmem := maxMixed2.isHermitian.eigenvalues_mem_spectrum_real i
  by_contra hne
  rw [spectrum.mem_iff] at hmem
  apply hmem
  set r := maxMixed2.isHermitian.eigenvalues i
  have hdiff : ((r - 1 / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hmat : algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) r - maxMixed2.mat =
      ((r - 1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Algebra.algebraMap_eq_smul_one, Complex.real_smul, maxMixed2]
  rw [hmat]
  refine ⟨⟨((r - 1 / 2 : ℝ) : ℂ) • 1, ((r - 1 / 2 : ℝ) : ℂ)⁻¹ • 1, ?_, ?_⟩, rfl⟩
  · ext a b
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, ← mul_assoc]
    rw [inv_mul_cancel₀ hdiff, one_mul]
  · ext a b
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, ← mul_assoc]
    rw [mul_inv_cancel₀ hdiff, one_mul]

/-- Spectral von Neumann entropy of `maxMixed2` matches `RyuTakayanagiEmergence.vonNeumannEntropy (1/2) = log 2`. -/
theorem vonNeumannEntropy_maxMixed2 :
    vonNeumannEntropy maxMixed2 = RyuTakayanagiEmergence.vonNeumannEntropy (1 / 2 : ℝ) ∧
      vonNeumannEntropy maxMixed2 = Real.log 2 := by
  have hval : vonNeumannEntropy maxMixed2 = Real.log 2 := by
    unfold vonNeumannEntropy
    simp only [Fin.sum_univ_two, maxMixed2_eigenvalues]
    have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hlog]
    ring
  exact ⟨hval.trans RyuTakayanagiEmergence.maxEntropy_twoState.symm, hval⟩

/-- Unitary conjugation preserves the characteristic polynomial of a matrix. -/
theorem charpoly_unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ((U : Matrix (Fin n) (Fin n) ℂ) * A * star (U : Matrix (Fin n) (Fin n) ℂ)).charpoly =
      A.charpoly := by
  rw [Matrix.charpoly_mul_comm ((U : Matrix (Fin n) (Fin n) ℂ) * A)
    (star (U : Matrix (Fin n) (Fin n) ℂ)), ← Matrix.mul_assoc, Unitary.coe_star_mul_self,
    Matrix.one_mul]

/-- Unitary conjugation preserves the entire spectrum and hence `vonNeumannEntropy`. -/
theorem vonNeumannEntropy_unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (ρ : DensityMatrix n) :
    vonNeumannEntropy (unitaryConjugate U ρ) = vonNeumannEntropy ρ := by
  have heig : (unitaryConjugate U ρ).isHermitian.eigenvalues = ρ.isHermitian.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      (unitaryConjugate U ρ).isHermitian ρ.isHermitian).mpr (charpoly_unitaryConjugate U ρ.mat)
  simp only [vonNeumannEntropy, heig]

/-! ## 3. Hyperbolic Poincaré Geodesic Area & AdS₃/CFT₂ Ryu–Takayanagi Formula -/

/-- Hyperbolic Poincaré geodesic length/area between two bulk points in `UpperHalfPlane` (`ℍ`). -/
noncomputable def poincareGeodesicArea (z₁ z₂ : UpperHalfPlane) : ℝ :=
  dist z₁ z₂

theorem poincareGeodesicArea_nonneg (z₁ z₂ : UpperHalfPlane) :
    0 ≤ poincareGeodesicArea z₁ z₂ :=
  dist_nonneg

theorem poincareGeodesicArea_symm (z₁ z₂ : UpperHalfPlane) :
    poincareGeodesicArea z₁ z₂ = poincareGeodesicArea z₂ z₁ :=
  dist_comm z₁ z₂

theorem poincareGeodesicArea_triangle (z₁ z₂ z₃ : UpperHalfPlane) :
    poincareGeodesicArea z₁ z₃ ≤ poincareGeodesicArea z₁ z₂ + poincareGeodesicArea z₂ z₃ :=
  dist_triangle z₁ z₂ z₃

/-- Exact `arcosh` formula for the Poincaré geodesic length in `ℍ`. -/
theorem poincareGeodesicArea_eq_arcosh (z₁ z₂ : UpperHalfPlane) :
    poincareGeodesicArea z₁ z₂ =
      Real.arcosh (((z₁.re - z₂.re) ^ 2 + z₁.im ^ 2 + z₂.im ^ 2) / (2 * z₁.im * z₂.im)) := by
  unfold poincareGeodesicArea
  rw [← UpperHalfPlane.cosh_dist']
  exact (Real.arcosh_cosh dist_nonneg).symm

/-- `SL(2, ℝ)` bulk isometry invariance of the Poincaré geodesic area. -/
theorem poincareGeodesicArea_sl2_invariant (g : SL(2, ℝ)) (z₁ z₂ : UpperHalfPlane) :
    poincareGeodesicArea (g • z₁) (g • z₂) = poincareGeodesicArea z₁ z₂ :=
  dist_smul g z₁ z₂

/-- Dyadic bulk point `(0, 2^{-n})` in `ℍ` corresponding to depth-`n` Cantor subtree penetration. -/
def dyadicPoint (n : ℕ) : UpperHalfPlane :=
  UpperHalfPlane.mk ⟨0, (2 : ℝ) ^ (-(n : ℤ))⟩ (by positivity)

/-- The Poincaré geodesic length from `i` to `(0, 2^{-n})` equals `minimalSurfaceArea n = n * log 2`. -/
theorem poincareGeodesicArea_vertical_dyadic (n : ℕ) :
    poincareGeodesicArea UpperHalfPlane.I (dyadicPoint n) =
      minimalSurfaceArea n := by
  unfold poincareGeodesicArea dyadicPoint minimalSurfaceArea
  rw [UpperHalfPlane.dist_of_re_eq (by simp [UpperHalfPlane.I])]
  simp only [UpperHalfPlane.I_im, UpperHalfPlane.mk_im, Real.log_one,
    Real.dist_eq, zero_sub, abs_neg]
  have hlog : Real.log ((2 : ℝ) ^ (-(n : ℤ))) = -((n : ℝ) * Real.log 2) := by
    rw [Real.log_zpow, Int.cast_neg, Int.cast_natCast]
    ring
  rw [hlog, abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num)))]

/-- Standard AdS₃/CFT₂ regularized boundary-interval geodesic length at UV cutoff `ε > 0`. -/
theorem poincareGeodesicArea_cutoff_interval (x₁ x₂ ε : ℝ) (hε : 0 < ε) :
    poincareGeodesicArea (UpperHalfPlane.mk ⟨x₁, ε⟩ hε) (UpperHalfPlane.mk ⟨x₂, ε⟩ hε) =
      Real.arcosh (1 + (x₁ - x₂) ^ 2 / (2 * ε ^ 2)) := by
  rw [poincareGeodesicArea_eq_arcosh]
  congr 1
  simp only [UpperHalfPlane.mk_re, UpperHalfPlane.mk_im]
  field_simp [hε.ne']
  ring

/-! ## 4. Constructive `TrialityGroup` (`S₃`) Unitary Actions on `Fin 24` & `Fin 8` -/

/-- The outer `Spin(8)` triality group `S₃ = Equiv.Perm TrialitySector`. -/
abbrev TrialityGroup := Equiv.Perm TrialitySector

/-- Transposition exchanging the two spinor sectors `8_s ↔ 8_c`. -/
def trialitySwap : TrialityGroup := Equiv.swap 1 2

theorem triality_s3_relation :
    trialitySwap * trialityCycle * trialitySwap = trialityCycle⁻¹ := by
  ext i
  fin_cases i <;> decide

/-- Unitary permutation matrix associated to any permutation `σ : Equiv.Perm (Fin n)`. -/
def permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if σ j = i then 1 else 0

theorem permMatrix_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permMatrix σ * permMatrix τ = permMatrix (σ * τ) := by
  ext i j
  simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (τ j)]
  · simp [Equiv.Perm.mul_apply]
    rfl
  · intro k _ hk
    simp [hk.symm]
  · intro hmem
    exact absurd (Finset.mem_univ (τ j)) hmem

theorem permMatrix_one {n : ℕ} : permMatrix (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  simp [permMatrix, Matrix.one_apply, eq_comm]

theorem permMatrix_star {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    star (permMatrix σ) = permMatrix σ⁻¹ := by
  ext i j
  simp only [Matrix.star_apply, permMatrix, Matrix.of_apply]
  by_cases h : σ i = j
  · have h' : (σ⁻¹) j = i := σ.symm_apply_eq.mpr h.symm
    simp [h, h']
  · have h' : σ.symm j ≠ i := fun hinv => h (σ.symm_apply_eq.mp hinv).symm
    simp [h, h']

/-- Group homomorphism lifting `Equiv.Perm (Fin n)` into `Matrix.unitaryGroup (Fin n) ℂ`. -/
def permToUnitary {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨permMatrix σ, by
    refine ⟨?_, ?_⟩
    · change star (permMatrix σ) * permMatrix σ = 1
      rw [permMatrix_star, permMatrix_mul, inv_mul_cancel, permMatrix_one]
    · change permMatrix σ * star (permMatrix σ) = 1
      rw [permMatrix_star, permMatrix_mul, mul_inv_cancel, permMatrix_one]⟩

theorem permToUnitary_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permToUnitary (σ * τ) = permToUnitary σ * permToUnitary τ := by
  ext i j
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) (permMatrix_mul σ τ).symm

theorem permToUnitary_one {n : ℕ} :
    permToUnitary (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) permMatrix_one

/-- `TrialityGroup` permutation on the `24`-dimensional `8_v ⊕ 8_s ⊕ 8_c` carrier (`Fin 3 × Fin 8`). -/
def trialitySectorPerm (g : TrialityGroup) : Equiv.Perm (Fin 24) :=
  finProdFinEquiv.symm.trans ((Equiv.prodCongr g (Equiv.refl (Fin 8))).trans finProdFinEquiv)

theorem trialitySectorPerm_mul (g h : TrialityGroup) :
    trialitySectorPerm (g * h) = trialitySectorPerm g * trialitySectorPerm h := by
  ext x
  simp [trialitySectorPerm, Equiv.Perm.mul_apply, Equiv.prodCongr_apply, Prod.map]

/-- Unitary `24 × 24` representation of `TrialityGroup` on `8_v ⊕ 8_s ⊕ 8_c`. -/
def trialitySectorUnitary (g : TrialityGroup) : Matrix.unitaryGroup (Fin 24) ℂ :=
  permToUnitary (trialitySectorPerm g)

/-- Triality action on `24 × 24` density matrices. -/
def trialityActDensity (g : TrialityGroup) (ρ : DensityMatrix 24) : DensityMatrix 24 :=
  unitaryConjugate (trialitySectorUnitary g) ρ

/-- Internal order-3 Zorn axis cycle permutation on `Fin 8` (cycling `(1,2,3)` and `(4,5,6)`). -/
def axisCyclePerm8 : Equiv.Perm (Fin 8) :=
  Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 5 6

theorem axisCyclePerm8_pow_three : axisCyclePerm8 ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

/-- Unitary `8 × 8` matrix realizing the internal order-3 triality axis cycle. -/
def axisTrialityUnitary : Matrix.unitaryGroup (Fin 8) ℂ :=
  permToUnitary axisCyclePerm8

theorem axisTrialityUnitary_pow_three : axisTrialityUnitary ^ 3 = 1 := by
  rw [pow_three, axisTrialityUnitary, ← permToUnitary_mul, ← permToUnitary_mul,
    ← pow_three, axisCyclePerm8_pow_three, permToUnitary_one]

/-! ## 5. Mandatory T16 Non-Commutativity Witnesses for `Fin 2`, `Fin 8` & `Fin 24` -/

def E01_2 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
def E10_2 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- Binder-free T16 non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem matrix_fin2_noncomm : E01_2 * E10_2 ≠ E10_2 * E01_2 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp [E01_2, E10_2, Matrix.mul_apply] at h00

def E01_8 : Matrix (Fin 8) (Fin 8) ℂ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
def E10_8 : Matrix (Fin 8) (Fin 8) ℂ := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- Binder-free T16 non-commutativity witness for `Matrix (Fin 8) (Fin 8) ℂ`. -/
theorem matrix_fin8_noncomm : E01_8 * E10_8 ≠ E10_8 * E01_8 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℂ => M 0 0) h
  simp [E01_8, E10_8, Matrix.mul_apply] at h00

def E01_24 : Matrix (Fin 24) (Fin 24) ℂ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
def E10_24 : Matrix (Fin 24) (Fin 24) ℂ := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- Binder-free T16 non-commutativity witness for `Matrix (Fin 24) (Fin 24) ℂ`. -/
theorem matrix_fin24_noncomm : E01_24 * E10_24 ≠ E10_24 * E01_24 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℂ => M 0 0) h
  simp [E01_24, E10_24, Matrix.mul_apply] at h00

/-! ## 6. Main Ryu–Takayanagi & Triality Equivariance Theorems -/

/-- Spectral entanglement entropy is invariant under the full `S₃` triality action on `8_v ⊕ 8_s ⊕ 8_c`. -/
theorem entanglement_triality_invariance (g : TrialityGroup) (ρ : DensityMatrix 24) :
    vonNeumannEntropy (trialityActDensity g ρ) = vonNeumannEntropy ρ :=
  vonNeumannEntropy_unitaryConjugate (trialitySectorUnitary g) ρ

/-- Spectral entanglement entropy is invariant under the internal order-3 Zorn axis triality on `Fin 8`. -/
theorem axis_triality_invariance (ρ : DensityMatrix 8) :
    vonNeumannEntropy (unitaryConjugate axisTrialityUnitary ρ) = vonNeumannEntropy ρ :=
  vonNeumannEntropy_unitaryConjugate axisTrialityUnitary ρ

/-- Predicate expressing the Ryu–Takayanagi identification `S(ρ) = Area(γ) / (4 G_N)`. -/
def IsRyuTakayanagiMatch {n : ℕ} (ρ : DensityMatrix n)
    (z₁ z₂ : UpperHalfPlane) (G_Newton : ℝ) : Prop :=
  0 < G_Newton ∧ vonNeumannEntropy ρ = poincareGeodesicArea z₁ z₂ / (4 * G_Newton)

/-- Joint boundary-triality and `SL(2, ℝ)` bulk-isometry equivariance of the Ryu–Takayanagi relation. -/
theorem ryu_takayanagi_triality_equivariance
    (ρ : DensityMatrix 24) (z₁ z₂ : UpperHalfPlane) (G_Newton : ℝ)
    (hRT : IsRyuTakayanagiMatch ρ z₁ z₂ G_Newton)
    (g : TrialityGroup) (m : SL(2, ℝ)) :
    IsRyuTakayanagiMatch (trialityActDensity g ρ) (m • z₁) (m • z₂) G_Newton := by
  refine ⟨hRT.1, ?_⟩
  rw [entanglement_triality_invariance g ρ, poincareGeodesicArea_sl2_invariant m z₁ z₂]
  exact hRT.2

/-- Constructive Ryu–Takayanagi witness: maximally mixed qubit state `maxMixed2` matches the
    unit-depth dyadic bulk geodesic at `G_N = 1 / 4` (`S = log 2 = Area / (4 G_N)`). -/
theorem maxMixed2_ryu_takayanagi_match :
    IsRyuTakayanagiMatch maxMixed2 UpperHalfPlane.I (dyadicPoint 1) (1 / 4 : ℝ) := by
  refine ⟨by norm_num, ?_⟩
  rw [vonNeumannEntropy_maxMixed2.2, poincareGeodesicArea_vertical_dyadic 1]
  simp [minimalSurfaceArea]

end InfoGeometry.Holography.RyuTakayanagiTriality

end noncomputable section
