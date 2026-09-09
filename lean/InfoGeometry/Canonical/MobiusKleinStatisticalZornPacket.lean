import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import InfoGeometry.Canonical.KleinBottleBoundaryActionPacket
import InfoGeometry.Canonical.TwoSheetComplexPolarization
import InfoGeometry.Geometry.MobiusDual2x2

/-!
# Möbius--Klein--statistical--Zorn finite packet

This module formalizes only the finite algebraic content of the proposed
consolidation.

Closed results include:

* normalization of three distinct affine points by a complex fractional-linear
  map, together with projective uniqueness of its representing matrix;
* the failure of determinant sign to descend through complex projective matrix
  scaling;
* exact determinants of the Gaussian and Poisson second-moment matrices;
* the distinction between symmetric Fisher/Wasserstein pairings and a separately
  defined skew form on the doubled carrier;
* the Klein relation obtained by conjugating a paired flow with sheet exchange;
* the exact additive and norm-one multiplicative associators of the Zorn
  generators `S₁`, `S₂`, and `U₃` in the existing coordinate Zorn model;
* elementary finite matrix certificates for the parabolic/elliptic modular
  generators.

This file does not assert a global Klein-bottle quotient, a Kähler or
super-Kähler manifold structure, an orbifold theorem, a statistical
interpretation of Zorn congruence indices, or a topological descent theorem for
the Zorn associator.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace InfoGeometry.Canonical.MobiusKleinStatisticalZornPacket

/-! ## Complex Möbius normalization -/

abbrev ComplexMat2 : Type :=
  Matrix (Fin 2) (Fin 2) ℂ

/-- Explicit `2 × 2` complex matrix constructor. -/
def complexMat2 (a b c d : ℂ) : ComplexMat2 :=
  !![a, b; c, d]

/-- Fractional-linear action on the affine chart. -/
def fractionalLinear (A : ComplexMat2) (z : ℂ) : ℂ :=
  (A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)

/--
The normalized affine formula taking `z₁` to `0` and `z₂` to `1`, with a pole
at `z₃`.
-/
def normalizedMobius (z₁ z₂ z₃ z : ℂ) : ℂ :=
  ((z - z₁) * (z₂ - z₃)) / ((z - z₃) * (z₂ - z₁))

/-- Denominator of `normalizedMobius` before division. -/
def normalizedMobiusDenominator (z₁ z₂ z₃ z : ℂ) : ℂ :=
  (z - z₃) * (z₂ - z₁)

/-- A matrix representative of the normalized Möbius transformation. -/
def normalizedMobiusMatrix (z₁ z₂ z₃ : ℂ) : ComplexMat2 :=
  complexMat2
    (z₂ - z₃)
    (-z₁ * (z₂ - z₃))
    (z₂ - z₁)
    (-z₃ * (z₂ - z₁))

@[simp] theorem normalizedMobius_at_first (z₁ z₂ z₃ : ℂ) :
    normalizedMobius z₁ z₂ z₃ z₁ = 0 := by
  simp [normalizedMobius]

@[simp] theorem normalizedMobiusDenominator_at_third (z₁ z₂ z₃ : ℂ) :
    normalizedMobiusDenominator z₁ z₂ z₃ z₃ = 0 := by
  simp [normalizedMobiusDenominator]

@[simp] theorem normalizedMobius_at_second
    (z₁ z₂ z₃ : ℂ)
    (h₁₂ : z₁ ≠ z₂)
    (h₂₃ : z₂ ≠ z₃) :
    normalizedMobius z₁ z₂ z₃ z₂ = 1 := by
  have h₂₁ : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
  have h₂₃' : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h₂₃
  simp [normalizedMobius]
  field_simp [h₂₁, h₂₃']

/-- The displayed matrix induces the normalized affine formula. -/
theorem fractionalLinear_normalizedMobiusMatrix
    (z₁ z₂ z₃ z : ℂ) :
    fractionalLinear (normalizedMobiusMatrix z₁ z₂ z₃) z =
      normalizedMobius z₁ z₂ z₃ z := by
  simp [fractionalLinear, normalizedMobiusMatrix, normalizedMobius, complexMat2]
  congr 1 <;> ring

/-- Determinant of the normalized representative. -/
theorem normalizedMobiusMatrix_det
    (z₁ z₂ z₃ : ℂ) :
    (normalizedMobiusMatrix z₁ z₂ z₃).det =
      (z₂ - z₃) * (z₂ - z₁) * (z₁ - z₃) := by
  simp [normalizedMobiusMatrix, complexMat2, Matrix.det_fin_two]
  ring

/-- Distinct marked points give an invertible matrix representative. -/
theorem normalizedMobiusMatrix_det_ne_zero
    (z₁ z₂ z₃ : ℂ)
    (h₁₂ : z₁ ≠ z₂)
    (h₁₃ : z₁ ≠ z₃)
    (h₂₃ : z₂ ≠ z₃) :
    (normalizedMobiusMatrix z₁ z₂ z₃).det ≠ 0 := by
  rw [normalizedMobiusMatrix_det]
  exact mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr h₂₃) (sub_ne_zero.mpr h₁₂.symm))
    (sub_ne_zero.mpr h₁₃)

/--
Projective uniqueness of the matrix normalizing the ordered triple.

The three equations encode respectively the zero at `z₁`, the pole at `z₃`,
and the value `1` at `z₂`. Every coefficient quadruple satisfying them is a
scalar multiple of `normalizedMobiusMatrix`.
-/
theorem normalizedMobiusMatrix_unique_up_to_scalar
    (a b c d z₁ z₂ z₃ : ℂ)
    (h₁₂ : z₁ ≠ z₂)
    (h₂₃ : z₂ ≠ z₃)
    (hzero : a * z₁ + b = 0)
    (hpole : c * z₃ + d = 0)
    (hone : a * z₂ + b = c * z₂ + d) :
    ∃ s : ℂ,
      complexMat2 a b c d = s • normalizedMobiusMatrix z₁ z₂ z₃ := by
  let s : ℂ := a / (z₂ - z₃)
  have h₂₃' : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h₂₃
  have hb : b = -a * z₁ := by
    linear_combination hzero
  have hd : d = -c * z₃ := by
    linear_combination hpole
  have hrel : a * (z₂ - z₁) = c * (z₂ - z₃) := by
    linear_combination hone - hzero + hpole
  have ha : a = s * (z₂ - z₃) := by
    dsimp [s]
    field_simp [h₂₃']
  have hc : c = s * (z₂ - z₁) := by
    dsimp [s]
    field_simp [h₂₃']
    exact hrel.symm
  refine ⟨s, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexMat2, normalizedMobiusMatrix, ha, hb, hc, hd] <;>
    ring

/-! ## Complex projective scaling and determinant sign -/

/-- Two matrix representatives differ by a nonzero complex scalar. -/
def ProjectivelyEquivalent (A B : ComplexMat2) : Prop :=
  ∃ r : ℂ, r ≠ 0 ∧ B = r • A

@[refl] theorem projectivelyEquivalent_refl (A : ComplexMat2) :
    ProjectivelyEquivalent A A := by
  exact ⟨1, one_ne_zero, by simp⟩

@[symm] theorem projectivelyEquivalent_symm
    {A B : ComplexMat2}
    (h : ProjectivelyEquivalent A B) :
    ProjectivelyEquivalent B A := by
  rcases h with ⟨r, hr, rfl⟩
  refine ⟨r⁻¹, inv_ne_zero hr, ?_⟩
  ext i j
  simp [smul_smul, hr]

@[trans] theorem projectivelyEquivalent_trans
    {A B C : ComplexMat2}
    (hAB : ProjectivelyEquivalent A B)
    (hBC : ProjectivelyEquivalent B C) :
    ProjectivelyEquivalent A C := by
  rcases hAB with ⟨r, hr, hB⟩
  rcases hBC with ⟨s, hs, hC⟩
  refine ⟨s * r, mul_ne_zero hs hr, ?_⟩
  rw [hC, hB]
  simp [smul_smul]

/-- The scalar `i` gives a projectively equivalent matrix representative. -/
theorem projectivelyEquivalent_I_smul (A : ComplexMat2) :
    ProjectivelyEquivalent A (Complex.I • A) := by
  refine ⟨Complex.I, ?_, rfl⟩
  norm_num

/-- Coordinate determinant for a `2 × 2` matrix. -/
def det2 (A : ComplexMat2) : ℂ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

@[simp] theorem det2_eq_det (A : ComplexMat2) :
    det2 A = A.det := by
  simp [det2, Matrix.det_fin_two]

/-- Multiplication of a representative by `i` reverses its determinant. -/
theorem det2_I_smul (A : ComplexMat2) :
    det2 (Complex.I • A) = -det2 A := by
  calc
    det2 (Complex.I • A) =
        Complex.I * Complex.I * (A 0 0 * A 1 1) -
          Complex.I * Complex.I * (A 0 1 * A 1 0) := by
      simp [det2]
      ring_nf
      rw [Complex.I_sq]
      ring
    _ = -det2 A := by
      simp [det2]
      ring

/-- Therefore determinant sign cannot descend to complex projective classes. -/
theorem projectivelyEquivalent_with_negated_det (A : ComplexMat2) :
    ProjectivelyEquivalent A (Complex.I • A) ∧
      det2 (Complex.I • A) = -det2 A := by
  exact ⟨projectivelyEquivalent_I_smul A, det2_I_smul A⟩

/-! ## Second-moment matrices and statistical pairings -/

abbrev RealMat2 : Type :=
  Matrix (Fin 2) (Fin 2) ℝ

/-- Matrix of the moments `1`, `E[X]`, and `E[X²] = m² + v`. -/
def secondMomentMatrix (m v : ℝ) : RealMat2 :=
  !![(1 : ℝ), m; m, m ^ 2 + v]

/-- Gaussian moment matrix with variance `σ²`. -/
def gaussianMomentMatrix (μ σ : ℝ) : RealMat2 :=
  secondMomentMatrix μ (σ ^ 2)

/-- Poisson moment matrix with mean and variance both equal to `λ`. -/
def poissonMomentMatrix (lam : ℝ) : RealMat2 :=
  secondMomentMatrix lam lam

@[simp] theorem secondMomentMatrix_det (m v : ℝ) :
    (secondMomentMatrix m v).det = v := by
  simp [secondMomentMatrix, Matrix.det_fin_two]
  ring

@[simp] theorem gaussianMomentMatrix_det (μ σ : ℝ) :
    (gaussianMomentMatrix μ σ).det = σ ^ 2 := by
  simp [gaussianMomentMatrix]

@[simp] theorem poissonMomentMatrix_det (lam : ℝ) :
    (poissonMomentMatrix lam).det = lam := by
  simp [poissonMomentMatrix]

abbrev StatisticalTangent2 : Type :=
  ℝ × ℝ

/-- Fisher pairing for the univariate Gaussian `(μ, σ)` chart. -/
def gaussianFisherPair (σ : ℝ)
    (u v : StatisticalTangent2) : ℝ :=
  (u.1 * v.1 + 2 * u.2 * v.2) / σ ^ 2

/-- Wasserstein pairing for the univariate Gaussian `(μ, σ)` chart. -/
def gaussianWassersteinPair
    (u v : StatisticalTangent2) : ℝ :=
  u.1 * v.1 + u.2 * v.2

@[simp] theorem gaussianFisherPair_symm
    (σ : ℝ) (u v : StatisticalTangent2) :
    gaussianFisherPair σ u v = gaussianFisherPair σ v u := by
  unfold gaussianFisherPair
  ring

@[simp] theorem gaussianWassersteinPair_symm
    (u v : StatisticalTangent2) :
    gaussianWassersteinPair u v = gaussianWassersteinPair v u := by
  unfold gaussianWassersteinPair
  ring

/-- Canonical skew form obtained from a symmetric pairing on a doubled carrier. -/
def doubledOmega {V : Type*}
    (B : V → V → ℝ) (p q : V × V) : ℝ :=
  B p.1 q.2 - B p.2 q.1

/-- A symmetric pairing induces a skew form on the doubled carrier. -/
theorem doubledOmega_skew
    {V : Type*}
    (B : V → V → ℝ)
    (hB : ∀ u v, B u v = B v u)
    (p q : V × V) :
    doubledOmega B p q = -doubledOmega B q p := by
  unfold doubledOmega
  rw [hB p.1 q.2, hB p.2 q.1]
  ring

/-- The induced skew form vanishes on the diagonal. -/
@[simp] theorem doubledOmega_self
    {V : Type*}
    (B : V → V → ℝ)
    (hB : ∀ u v, B u v = B v u)
    (p : V × V) :
    doubledOmega B p p = 0 := by
  unfold doubledOmega
  rw [hB p.1 p.2]
  ring

/-- Arithmetic mean of two scalar-valued connection coefficients. -/
def connectionMean {X : Type*}
    (e m : X → X → ℝ) (x y : X) : ℝ :=
  (e x y + m x y) / 2

/-- Difference of two scalar-valued connection coefficients. -/
def connectionDifference {X : Type*}
    (e m : X → X → ℝ) (x y : X) : ℝ :=
  m x y - e x y

/-- Recover the first connection from its mean and difference. -/
theorem connection_first_reconstruction
    {X : Type*}
    (e m : X → X → ℝ) (x y : X) :
    connectionMean e m x y - connectionDifference e m x y / 2 = e x y := by
  simp [connectionMean, connectionDifference]
  ring

/-- Recover the second connection from its mean and difference. -/
theorem connection_second_reconstruction
    {X : Type*}
    (e m : X → X → ℝ) (x y : X) :
    connectionMean e m x y + connectionDifference e m x y / 2 = m x y := by
  simp [connectionMean, connectionDifference]
  ring

/-! ## Exact Klein relation on the doubled carrier -/

/-- Exchange the two components of a doubled carrier. -/
def swapSheets {X : Type*} (p : X × X) : X × X :=
  (p.2, p.1)

/-- Pair an equivalence with its inverse on the opposite sheet. -/
def pairedFlow {X : Type*} (f : X ≃ X) (p : X × X) : X × X :=
  (f p.1, f.symm p.2)

@[simp] theorem swapSheets_involutive
    {X : Type*} (p : X × X) :
    swapSheets (swapSheets p) = p := by
  rfl

/--
The sheet exchange conjugates a paired flow to its inverse: the abstract Klein
relation `a b a⁻¹ = b⁻¹`, with `a² = 1`.
-/
theorem klein_relation
    {X : Type*} (f : X ≃ X) (p : X × X) :
    swapSheets (pairedFlow f (swapSheets p)) = pairedFlow f.symm p := by
  rfl

/-- Function-level form of the Klein relation. -/
theorem klein_relation_function
    {X : Type*} (f : X ≃ X) :
    swapSheets ∘ pairedFlow f ∘ swapSheets = pairedFlow f.symm := by
  funext p
  rfl

/-! ## Ordinary `2 × 2` generator certificates -/

abbrev IntMat2 : Type :=
  Matrix (Fin 2) (Fin 2) ℤ

/-- Standard order-two elliptic modular representative. -/
def modularT : IntMat2 :=
  !![(0 : ℤ), 1; -1, 0]

/-- Standard parabolic modular representative. -/
def modularS : IntMat2 :=
  !![(1 : ℤ), 1; 0, 1]

/-- Standard order-three elliptic modular representative. -/
def modularU : IntMat2 :=
  !![(0 : ℤ), 1; -1, 1]

/-- Coordinate trace of an integral `2 × 2` matrix. -/
def intTrace2 (A : IntMat2) : ℤ :=
  A 0 0 + A 1 1

@[simp] theorem modularT_det : modularT.det = 1 := by
  norm_num [modularT, Matrix.det_fin_two]

@[simp] theorem modularS_det : modularS.det = 1 := by
  norm_num [modularS, Matrix.det_fin_two]

@[simp] theorem modularU_det : modularU.det = 1 := by
  norm_num [modularU, Matrix.det_fin_two]

@[simp] theorem modularT_trace : intTrace2 modularT = 0 := by
  norm_num [intTrace2, modularT]

@[simp] theorem modularS_trace : intTrace2 modularS = 2 := by
  norm_num [intTrace2, modularS]

@[simp] theorem modularU_trace : intTrace2 modularU = 1 := by
  norm_num [intTrace2, modularU]

/-- `T² = -I`, hence `T` has order two projectively. -/
theorem modularT_sq :
    modularT * modularT = -(1 : IntMat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularT, Matrix.mul_apply, Fin.sum_univ_two]

/-- `U³ = -I`, hence `U` has order three projectively. -/
theorem modularU_cube :
    (modularU * modularU) * modularU = -(1 : IntMat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularU, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Explicit Zorn generator associators -/

set_option maxHeartbeats 1000000

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-- First standard coordinate vector. -/
def zornE1 : Vec3 :=
  ![(1 : ℝ), 0, 0]

/-- Second standard coordinate vector. -/
def zornE2 : Vec3 :=
  ![(0 : ℝ), 1, 0]

/-- Third standard coordinate vector. -/
def zornE3 : Vec3 :=
  ![(0 : ℝ), 0, 1]

/-- Upper-unipotent Zorn generator in direction `e₁`. -/
def zornS1 : ZornCoord :=
  zornMk 1 1 zornE1 0

/-- Upper-unipotent Zorn generator in direction `e₂`. -/
def zornS2 : ZornCoord :=
  zornMk 1 1 zornE2 0

/-- Mixed Zorn generator `[[0,e₃],[-e₃,1]]`. -/
def zornU3 : ZornCoord :=
  zornMk 0 1 zornE3 (-zornE3)

/-- Additive associator in the existing coordinate Zorn algebra. -/
def zornAdditiveAssociator
    (p q r : ZornCoord) : ZornCoord :=
  zornMul (zornMul p q) r - zornMul p (zornMul q r)

/-- Norm-one multiplicative associator, using conjugation for the inverse. -/
def zornMultiplicativeAssociator
    (p q r : ZornCoord) : ZornCoord :=
  zornMul
    (zornMul (zornMul p q) r)
    (zornConj (zornMul p (zornMul q r)))

@[simp] theorem zornS1_norm : zornNorm zornS1 = 1 := by
  norm_num [zornS1, zornE1, zornNorm, zornMk, zornA, zornB, zornX, zornY, dot3]

@[simp] theorem zornS2_norm : zornNorm zornS2 = 1 := by
  norm_num [zornS2, zornE2, zornNorm, zornMk, zornA, zornB, zornX, zornY, dot3]

@[simp] theorem zornU3_norm : zornNorm zornU3 = 1 := by
  norm_num [zornU3, zornE3, zornNorm, zornMk, zornA, zornB, zornX, zornY, dot3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Left bracketing of the three explicit generators. -/
theorem zorn_left_bracketing :
    zornMul (zornMul zornS1 zornS2) zornU3 =
      zornMk 0 2
        (zornE1 + zornE2 + zornE3)
        (zornE1 - zornE2 - zornE3) := by
  ext i <;>
    simp [zornS1, zornS2, zornU3, zornE1, zornE2, zornE3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try fin_cases i <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring <;> omega <;>
    simp [Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    <;> decide
  all_goals first
    | (change (1 : ℝ) + 1 = 2; norm_num)
    | (change (2 : ℝ) - 1 = 1; norm_num)
    | (change (2 : ℝ) + 1 = 3; norm_num)

/-- Right bracketing of the three explicit generators. -/
theorem zorn_right_bracketing :
    zornMul zornS1 (zornMul zornS2 zornU3) =
      zornMk 1 1
        (zornE1 + zornE2 + zornE3)
        (zornE1 - zornE2) := by
  ext i <;>
    simp [zornS1, zornS2, zornU3, zornE1, zornE2, zornE3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try fin_cases i <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring <;> omega <;>
    simp [Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    <;> decide
  all_goals first
    | (change (1 : ℝ) + 1 = 2; norm_num)
    | (change (2 : ℝ) - 1 = 1; norm_num)
    | (change (2 : ℝ) + 1 = 3; norm_num)

/-- The exact nonzero additive associator of `S₁`, `S₂`, and `U₃`. -/
theorem zorn_additive_associator_exact :
    zornAdditiveAssociator zornS1 zornS2 zornU3 =
      zornMk (-1) 1 0 (-zornE3) := by
  rw [zornAdditiveAssociator, zorn_left_bracketing, zorn_right_bracketing]
  ext i <;>
    simp [zornMk, zornE1, zornE2, zornE3] <;>
    try fin_cases i <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring <;> omega <;>
    simp [Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    <;> decide
  all_goals first
    | (change (1 : ℝ) + 1 = 2; norm_num)
    | (change (2 : ℝ) - 1 = 1; norm_num)
    | (change (2 : ℝ) + 1 = 3; norm_num)

/-- The explicit additive associator is nonzero. -/
theorem zorn_additive_associator_ne_zero :
    zornAdditiveAssociator zornS1 zornS2 zornU3 ≠ 0 := by
  rw [zorn_additive_associator_exact]
  intro h
  have ha := congrArg zornA h
  norm_num [zornA, zornMk] at ha

/- The multiplicative associator readout remains a definition; its exact
   coordinate normalization is the next frontier for the current vector API. -/

@[simp] theorem zorn_multiplicative_associator_norm :
    zornNorm (zornMultiplicativeAssociator zornS1 zornS2 zornU3) = 1 := by
  simp [zornMultiplicativeAssociator, zornNorm_mul, zornNorm_conj]
