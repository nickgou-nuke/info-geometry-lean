/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.RealSupportCoercivity
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Real logarithms on the actual support of positive operators

All operators and inner products are real. The finite spectral theorem constructs
an operator logarithm; diagonal coordinates are proof data for the full operator.
The support is the native orthogonal complement of the entire kernel. Its
restriction is positive and invertible. Extending the support logarithm by zero
has the compressed exponential identity, and its exponential is the identity
on the discarded kernel.
-/

noncomputable section

namespace InfoGeometry.Analysis.RealSupportLogarithm

open scoped InnerProductSpace
open RealSupportCoercivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section SpectralCalculus

variable [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Real spectral multiplication in an orthonormal basis, as a full operator. -/
def spectralMultiplier (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) : E →L[ℝ] E :=
  (b.toBasis.constr ℝ (fun i => a i • b i)).toContinuousLinearMap

@[simp] theorem spectralMultiplier_apply_basis (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) (i : ι) : spectralMultiplier b a (b i) = a i • b i := by
  exact b.toBasis.constr_basis ℝ _ i

private theorem eq_of_basis (b : OrthonormalBasis ι ℝ E)
    {A B : E →L[ℝ] E} (h : ∀ i, A (b i) = B (b i)) : A = B := by
  apply ContinuousLinearMap.coe_injective
  exact b.toBasis.ext h

/-- Coordinate expansion is an identity of the original full operator. -/
theorem spectralMultiplier_apply (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (x : E) :
    spectralMultiplier b a x = ∑ i, (inner ℝ (b i) x * a i) • b i := by
  calc
    spectralMultiplier b a x =
        spectralMultiplier b a (∑ i, inner ℝ (b i) x • b i) :=
      congrArg (spectralMultiplier b a) (b.sum_repr' x).symm
    _ = _ := by simp only [map_sum, map_smul, spectralMultiplier_apply_basis, smul_smul]

/-- Every real spectral multiplier is symmetric in the positive Hilbert metric. -/
theorem spectralMultiplier_isSymmetric (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) :
    (spectralMultiplier b a).IsSymmetric := by
  intro x y
  change inner ℝ (spectralMultiplier b a x) y = inner ℝ x (spectralMultiplier b a y)
  rw [spectralMultiplier_apply, spectralMultiplier_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_comm x (b i)]
  ring

/-- The spectral multiplier respects the algebra operations. -/
def spectralMultiplierHom (b : OrthonormalBasis ι ℝ E) :
    (ι → ℝ) →ₐ[ℝ] (E →L[ℝ] E) where
  toFun := spectralMultiplier b
  map_one' := by
    apply eq_of_basis b
    intro i
    simp
  map_mul' a d := by
    apply eq_of_basis b
    intro i
    change spectralMultiplier b (a * d) (b i) =
      spectralMultiplier b a (spectralMultiplier b d (b i))
    rw [spectralMultiplier_apply_basis, spectralMultiplier_apply_basis,
      map_smul, spectralMultiplier_apply_basis, smul_smul]
    exact congrArg (fun r : ℝ => r • b i) (mul_comm (a i) (d i))
  map_zero' := by
    apply eq_of_basis b
    intro i
    simp
  map_add' a d := by
    apply eq_of_basis b
    intro i
    simp [add_smul]
  commutes' r := by
    apply eq_of_basis b
    intro i
    simp [Algebra.algebraMap_eq_smul_one]

/-- The native power-series exponential has the expected real spectral action. -/
theorem exp_spectralMultiplier (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) :
    NormedSpace.exp (spectralMultiplier b a) =
      spectralMultiplier b (fun i => Real.exp (a i)) := by
  letI : Algebra ℚ (E →L[ℝ] E) := RestrictScalars.algebra ℚ ℝ (E →L[ℝ] E)
  have hm := NormedSpace.map_exp (spectralMultiplierHom b)
    (spectralMultiplierHom b).toLinearMap.continuous_of_finiteDimensional a
  change spectralMultiplier b (NormedSpace.exp a) =
    NormedSpace.exp (spectralMultiplier b a) at hm
  rw [Pi.exp_def] at hm
  simpa only [← Real.exp_eq_exp_ℝ] using hm.symm

/-- Spectral multiplication by the total scalar `Real.log`. The exponential
inverse law requires positive injective input; this definition makes no inverse
claim at zero or negative spectral values. -/
def realLog (T : Module.End ℝ E) (hT : T.IsSymmetric) : E →L[ℝ] E :=
  spectralMultiplier (hT.eigenvectorBasis rfl)
    (fun i => Real.log (hT.eigenvalues (n := Module.finrank ℝ E) rfl i))

/-- The constructed logarithm is symmetric in the original real Hilbert metric. -/
theorem realLog_isSymmetric (T : Module.End ℝ E) (hT : T.IsSymmetric) :
    (realLog T hT).IsSymmetric := spectralMultiplier_isSymmetric _ _

/-- Symmetry of the bounded logarithm is native self-adjointness. -/
theorem realLog_isSelfAdjoint (T : Module.End ℝ E) (hT : T.IsSymmetric) :
    IsSelfAdjoint (realLog T hT) := (realLog_isSymmetric T hT).isSelfAdjoint

/-- The logarithm acts on every eigenvector by the scalar real logarithm,
not merely on the selected spectral basis. -/
theorem realLog_apply_eigenvector (T : Module.End ℝ E) (hT : T.IsSymmetric)
    (r : ℝ) (x : E) (hx : T x = r • x) :
    realLog T hT x = Real.log r • x := by
  let b := hT.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let μ := hT.eigenvalues (n := Module.finrank ℝ E) rfl
  have hb : ∀ i, T (b i) = μ i • b i := hT.apply_eigenvectorBasis rfl
  have hc : ∀ i, inner ℝ (b i) x ≠ 0 → μ i = r := by
    intro i hi
    have hs := hT (b i) x
    rw [hb i, hx, real_inner_smul_left, real_inner_smul_right] at hs
    exact mul_right_cancel₀ hi hs
  change spectralMultiplier b (fun i => Real.log (μ i)) x = _
  rw [spectralMultiplier_apply]
  calc
    (∑ i, (inner ℝ (b i) x * Real.log (μ i)) • b i) =
        ∑ i, Real.log r • (inner ℝ (b i) x • b i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : inner ℝ (b i) x = 0
      · simp [hi]
      · rw [hc i hi, smul_smul, mul_comm]
    _ = Real.log r • x := by rw [← Finset.smul_sum, b.sum_repr']

/-- Any orthonormal eigenbasis computes the same full operator logarithm. -/
theorem realLog_eq_spectralMultiplier (T : Module.End ℝ E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (hb : ∀ i, T (b i) = μ i • b i) :
    realLog T hT = spectralMultiplier b (fun i => Real.log (μ i)) := by
  apply eq_of_basis b
  intro i
  rw [realLog_apply_eigenvector T hT (μ i) (b i) (hb i),
    spectralMultiplier_apply_basis]

/-- The logarithm commutes with its original full operator. -/
theorem realLog_commutes (T : Module.End ℝ E) (hT : T.IsSymmetric) :
    Commute (LinearMap.toContinuousLinearMap T) (realLog T hT) := by
  apply eq_of_basis (hT.eigenvectorBasis (n := Module.finrank ℝ E) rfl)
  intro i
  simp only [mul_apply_eq_comp, realLog, spectralMultiplier_apply_basis,
    map_smul, LinearMap.coe_toContinuousLinearMap', hT.apply_eigenvectorBasis,
    smul_smul]
  rw [mul_comm]

/-- Strict positivity and injectivity suffice for the genuine exponential/logarithm identity. -/
theorem exp_realLog (T : Module.End ℝ E) (hT : T.IsPositive)
    (hinj : Function.Injective T) :
    NormedSpace.exp (realLog T hT.isSymmetric) = (LinearMap.toContinuousLinearMap T) := by
  let b := hT.isSymmetric.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let μ := hT.isSymmetric.eigenvalues (n := Module.finrank ℝ E) rfl
  have hb : ∀ i, T (b i) = μ i • b i :=
    hT.isSymmetric.apply_eigenvectorBasis rfl
  have hμ : ∀ i, 0 < μ i := by
    intro i
    apply lt_of_le_of_ne (hT.nonneg_eigenvalues rfl i)
    intro hz
    change 0 = μ i at hz
    have hi : T (b i) = 0 := by rw [hb, ← hz, zero_smul]
    have : b i = 0 := hinj (hi.trans T.map_zero.symm)
    exact (b.toBasis.ne_zero i) this
  change NormedSpace.exp (spectralMultiplier b (fun i => Real.log (μ i))) = _
  rw [exp_spectralMultiplier]
  apply eq_of_basis b
  intro i
  simp only [spectralMultiplier_apply_basis, Real.exp_log (hμ i)]
  exact (hb i).symm

end SpectralCalculus

section Intertwining

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [CompleteSpace E] [CompleteSpace F]

/-- A bounded intertwiner intertwines power-series exponentials, including
maps between different carriers. -/
theorem exp_intertwines (A : E →L[ℝ] E) (B : F →L[ℝ] F) (j : E →L[ℝ] F)
    (h : ∀ x, j (A x) = B (j x)) (x : E) :
    j (NormedSpace.exp A x) = NormedSpace.exp B (j x) := by
  have hp : ∀ n : ℕ, j ((A ^ n) x) = (B ^ n) (j x) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', mul_apply_eq_comp, h, ih]
  have hleft :
      j ((∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ • A ^ n) x) =
        ∑' n : ℕ, j (((Nat.factorial n : ℝ)⁻¹ • A ^ n) x) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using
      (j.comp (ContinuousLinearMap.apply ℝ E x)).map_tsum
        (NormedSpace.expSeries_summable' (𝕂 := ℝ) A)
  have hBeval :
      (∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ • B ^ n) (j x) =
        ∑' n : ℕ, ((Nat.factorial n : ℝ)⁻¹ • B ^ n) (j x) :=
    (ContinuousLinearMap.apply ℝ F (j x)).map_tsum
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) B)
  rw [NormedSpace.exp_eq_tsum ℝ, NormedSpace.exp_eq_tsum ℝ, hleft, hBeval]
  apply tsum_congr
  intro n
  simp only [smul_apply, map_smul, hp n]

end Intertwining

section Support

variable [FiniteDimensional ℝ E]

/-- The actual retained carrier; no ambient invertibility is required. -/
abbrev Support (T : Module.End ℝ E) := T.kerᗮ

/-- Explicit native operator-norm ring structure for the support subtype. -/
local instance supportEndTopologicalRing (T : Module.End ℝ E) :
    IsTopologicalRing (Support T →L[ℝ] Support T) := by
  letI : NormedRing (Support T →L[ℝ] Support T) := ContinuousLinearMap.toNormedRing
  infer_instance

private theorem maps_support (T : Module.End ℝ E) (hT : T.IsSymmetric) (x : E) :
    T x ∈ T.kerᗮ := by
  apply (T.ker.mem_orthogonal (T x)).mpr
  intro y hy
  rw [← hT y x, show T y = 0 from hy, inner_zero_left]

/-- Restriction of the original operator to its true support. -/
def supportOperator (T : Module.End ℝ E) (hT : T.IsSymmetric) :
    Module.End ℝ (Support T) :=
  (T.domRestrict (Support T)).codRestrict (Support T)
    (fun x => maps_support T hT x)

@[simp] theorem supportOperator_coe (T : Module.End ℝ E) (hT : T.IsSymmetric)
    (x : Support T) : (supportOperator T hT x : E) = T x := rfl

/-- Positivity descends to the actual support carrier. -/
theorem supportOperator_isPositive (T : Module.End ℝ E) (hT : T.IsPositive) :
    (supportOperator T hT.isSymmetric).IsPositive := by
  apply (LinearMap.isPositive_iff _).mpr
  constructor
  · intro x y
    exact hT.isSymmetric x y
  · intro x
    exact hT.inner_nonneg_left x

/-- There are no zero modes on the support itself. -/
theorem supportOperator_injective (T : Module.End ℝ E) (hT : T.IsSymmetric) :
    Function.Injective (supportOperator T hT) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  apply Subtype.ext
  have hxker : (x : E) ∈ T.ker := by
    change T x = 0
    exact congrArg Subtype.val hx
  exact inner_self_eq_zero.mp (T.ker.inner_right_of_mem_orthogonal hxker x.property)

/-- The quadratic form is strictly positive on every nonzero support vector. -/
theorem supportOperator_inner_pos (T : Module.End ℝ E) (hT : T.IsPositive)
    (x : Support T) (hx : x ≠ 0) :
    0 < inner ℝ x (supportOperator T hT.isSymmetric x) := by
  exact RealPositiveOperatorGap.inner_pos_of_mem_ker_orthogonal T hT x.property
    (fun hzero => hx (Subtype.ext hzero))

/-- The restricted operator has a genuine inverse in its endomorphism algebra. -/
theorem supportOperator_isUnit (T : Module.End ℝ E) (hT : T.IsSymmetric) :
    IsUnit (supportOperator T hT) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact supportOperator_injective T hT

/-- Strict spectral positivity holds on the support carrier, including when
zero is present in the ambient spectrum. -/
theorem supportOperator_spectrum_positive (T : Module.End ℝ E) (hT : T.IsPositive) :
    spectrum ℝ (supportOperator T hT.isSymmetric) ⊆ Set.Ioi (0 : ℝ) := by
  obtain ⟨δ, hδ, hgap⟩ := RealPositiveOperatorGap.exists_positive_spectral_gap
    (supportOperator T hT.isSymmetric) (supportOperator_isPositive T hT)
  intro μ hμ
  rcases hgap μ hμ with hz | hge
  · subst μ
    exact (spectrum.zero_notMem ℝ (supportOperator_isUnit T hT.isSymmetric) hμ).elim
  · exact hδ.trans_le hge

/-- The native real spectral logarithm, constructed on the restricted carrier. -/
def supportLog (T : Module.End ℝ E) (hT : T.IsPositive) :
    Support T →L[ℝ] Support T :=
  realLog (supportOperator T hT.isSymmetric) (supportOperator_isPositive T hT).isSymmetric

/-- The support logarithm is symmetric in the induced real inner product. -/
theorem supportLog_isSymmetric (T : Module.End ℝ E) (hT : T.IsPositive) :
    (supportLog T hT).IsSymmetric := realLog_isSymmetric _ _

theorem supportLog_isSelfAdjoint (T : Module.End ℝ E) (hT : T.IsPositive) :
    IsSelfAdjoint (supportLog T hT) := (supportLog_isSymmetric T hT).isSelfAdjoint

/-- Exponentiation recovers the original operator on its support. -/
theorem exp_supportLog (T : Module.End ℝ E) (hT : T.IsPositive) :
    NormedSpace.exp (supportLog T hT) =
      LinearMap.toContinuousLinearMap (supportOperator T hT.isSymmetric) :=
  exp_realLog _ (supportOperator_isPositive T hT) (supportOperator_injective T _)

/-- Extension by zero from the actual orthogonal support. -/
def supportExtend (T : Module.End ℝ E) (A : Support T →L[ℝ] Support T) : E →L[ℝ] E :=
  (Support T).subtypeL.comp (A.comp (Support T).orthogonalProjectionOnto)

@[simp] theorem supportExtend_apply_coe (T : Module.End ℝ E)
    (A : Support T →L[ℝ] Support T) (x : Support T) :
    supportExtend T A (x : E) = (A x : E) := by
  simp [supportExtend]

/-- Extension by zero is supported by the same orthogonal projection on both sides. -/
theorem supportExtend_supported (T : Module.End ℝ E)
    (A : Support T →L[ℝ] Support T) :
    (Support T).starProjection * supportExtend T A = supportExtend T A ∧
      supportExtend T A * (Support T).starProjection = supportExtend T A := by
  constructor
  · ext x
    exact Submodule.starProjection_eq_self_iff.mpr
      (A ((Support T).orthogonalProjectionOnto x)).property
  · ext x
    change (A ((Support T).orthogonalProjectionOnto ((Support T).starProjection x)) : E) =
      (A ((Support T).orthogonalProjectionOnto x) : E)
    rw [Submodule.orthogonalProjectionOnto_starProjection_of_le le_rfl]

/-- Orthogonal extension by zero preserves Hilbert symmetry. -/
theorem supportExtend_isSymmetric (T : Module.End ℝ E)
    (A : Support T →L[ℝ] Support T) (hA : A.IsSymmetric) :
    (supportExtend T A).IsSymmetric := by
  intro x y
  change inner ℝ (A ((Support T).orthogonalProjectionOnto x) : E) y =
    inner ℝ x (A ((Support T).orthogonalProjectionOnto y) : E)
  have hs := hA ((Support T).orthogonalProjectionOnto x)
    ((Support T).orthogonalProjectionOnto y)
  change inner ℝ (A ((Support T).orthogonalProjectionOnto x))
      ((Support T).orthogonalProjectionOnto y) =
    inner ℝ ((Support T).orthogonalProjectionOnto x)
      (A ((Support T).orthogonalProjectionOnto y)) at hs
  simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using hs

/-- The support Hamiltonian extended by zero, as a full ambient operator. -/
def modularHamiltonian (T : Module.End ℝ E) (hT : T.IsPositive) : E →L[ℝ] E :=
  supportExtend T (-supportLog T hT)

/-- The constructed full Hamiltonian is symmetric in the ambient Hilbert metric. -/
theorem modularHamiltonian_isSymmetric (T : Module.End ℝ E) (hT : T.IsPositive) :
    (modularHamiltonian T hT).IsSymmetric := by
  apply supportExtend_isSymmetric
  intro x y
  change inner ℝ (-(supportLog T hT x)) y = inner ℝ x (-(supportLog T hT y))
  rw [inner_neg_left, inner_neg_right]
  exact congrArg Neg.neg (supportLog_isSymmetric T hT x y)

theorem modularHamiltonian_isSelfAdjoint (T : Module.End ℝ E) (hT : T.IsPositive) :
    IsSelfAdjoint (modularHamiltonian T hT) :=
  (modularHamiltonian_isSymmetric T hT).isSelfAdjoint

@[simp] theorem neg_modularHamiltonian (T : Module.End ℝ E) (hT : T.IsPositive) :
    -modularHamiltonian T hT = supportExtend T (supportLog T hT) := by
  ext x
  simp [modularHamiltonian, supportExtend]

/-- The exponential of the ambient extension agrees with the restricted
exponential on retained vectors. -/
theorem exp_extend_apply_coe (T : Module.End ℝ E)
    (A : Support T →L[ℝ] Support T) (x : Support T) :
    NormedSpace.exp (supportExtend T A) (x : E) =
      (NormedSpace.exp A x : E) := by
  exact (exp_intertwines A (supportExtend T A) (Support T).subtypeL
    (fun y => (supportExtend_apply_coe T A y).symm) x).symm

/-- The correct ambient reconstruction for a possibly singular positive
operator: the exponential must be compressed to the support. -/
theorem compressed_exp_neg_modularHamiltonian (T : Module.End ℝ E) (hT : T.IsPositive) :
    (Support T).starProjection * NormedSpace.exp (-modularHamiltonian T hT) *
      (Support T).starProjection = (LinearMap.toContinuousLinearMap T) := by
  ext x
  rw [neg_modularHamiltonian]
  change (Support T).starProjection
    (NormedSpace.exp (supportExtend T (supportLog T hT))
      ((Support T).orthogonalProjectionOnto x : E)) = T x
  rw [exp_extend_apply_coe, exp_supportLog]
  change (Support T).starProjection (T ((Support T).starProjection x)) = T x
  have hPT := congrArg (fun f : Module.End ℝ E => f x)
    (supportProjection_mul T hT.isSymmetric)
  have hTP : T ((Support T).starProjection x) = T x := by
    have hker : x - (Support T).starProjection x ∈ T.ker := by
      have ho := (Support T).sub_starProjection_mem_orthogonal x
      simpa [Support, Submodule.orthogonal_orthogonal] using ho
    have hz : T (x - (Support T).starProjection x) = 0 := hker
    exact (sub_eq_zero.mp (by simpa only [map_sub] using hz)).symm
  rw [hTP]
  exact hPT

/-- Extension by zero annihilates the discarded kernel. -/
theorem supportExtend_apply_kernel (T : Module.End ℝ E)
    (A : Support T →L[ℝ] Support T) (x : E) (hx : T x = 0) :
    supportExtend T A x = 0 := by
  have hp : (Support T).orthogonalProjectionOnto x = 0 := by
    apply Subtype.ext
    change (Support T).starProjection x = 0
    apply (Support T).starProjection_apply_eq_zero_iff.mpr
    exact T.ker.le_orthogonal_orthogonal hx
  simp [supportExtend, hp]

/-- The exponential acts as identity on the discarded kernel, which explains
why an uncompressed ambient reconstruction is false for singular operators. -/
theorem exp_neg_modularHamiltonian_apply_kernel (T : Module.End ℝ E) (hT : T.IsPositive)
    (x : E) (hx : T x = 0) :
    NormedSpace.exp (-modularHamiltonian T hT) x = x := by
  rw [neg_modularHamiltonian]
  have h := exp_intertwines (0 : T.ker →L[ℝ] T.ker)
    (supportExtend T (supportLog T hT)) T.ker.subtypeL
    (fun y => by
      simpa using (supportExtend_apply_kernel T (supportLog T hT) y y.property).symm)
    (⟨x, hx⟩ : T.ker)
  simpa using h.symm

/-- The precise uncompressed ambient exponential includes the identity on the
discarded kernel. Compression removes exactly this additional projection. -/
theorem exp_neg_modularHamiltonian_eq (T : Module.End ℝ E) (hT : T.IsPositive) :
    NormedSpace.exp (-modularHamiltonian T hT) =
      (LinearMap.toContinuousLinearMap T) + (1 - (Support T).starProjection) := by
  ext x
  have hker : T (x - (Support T).starProjection x) = 0 := by
    have ho := (Support T).sub_starProjection_mem_orthogonal x
    have hm : x - (Support T).starProjection x ∈ T.ker := by
      simpa [Support, Submodule.orthogonal_orthogonal] using ho
    exact hm
  have hTP : T ((Support T).starProjection x) = T x :=
    (sub_eq_zero.mp (by simpa only [map_sub] using hker)).symm
  have hs : NormedSpace.exp (-modularHamiltonian T hT)
      ((Support T).starProjection x) = T ((Support T).starProjection x) := by
    rw [neg_modularHamiltonian]
    change NormedSpace.exp (supportExtend T (supportLog T hT))
      ((Support T).orthogonalProjectionOnto x : E) = _
    rw [exp_extend_apply_coe, exp_supportLog]
    rfl
  calc
    NormedSpace.exp (-modularHamiltonian T hT) x =
        NormedSpace.exp (-modularHamiltonian T hT)
          ((Support T).starProjection x + (x - (Support T).starProjection x)) := by
      congr 1
      abel
    _ = T x + (x - (Support T).starProjection x) := by
      rw [map_add, hs, hTP, exp_neg_modularHamiltonian_apply_kernel T hT _ hker]
    _ = _ := rfl

/-- A nonzero zero mode obstructs the tempting uncompressed exponential identity. -/
theorem exp_neg_modularHamiltonian_ne_of_kernel (T : Module.End ℝ E) (hT : T.IsPositive)
    (x : E) (hx : T x = 0) (hx0 : x ≠ 0) :
    NormedSpace.exp (-modularHamiltonian T hT) ≠ (LinearMap.toContinuousLinearMap T) := by
  intro heq
  have h := congrArg (fun A : E →L[ℝ] E => A x) heq
  rw [exp_neg_modularHamiltonian_apply_kernel T hT x hx] at h
  exact hx0 (h.trans hx)

end Support

end InfoGeometry.Analysis.RealSupportLogarithm
