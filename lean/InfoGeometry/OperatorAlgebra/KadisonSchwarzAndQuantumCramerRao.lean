/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
import InfoGeometry.OperatorAlgebra.PeirceQuantumGeometricTensor
import InfoGeometry.QuantumGeometry.NoncommutativeSLDFisherMetric
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Star.Module

/-!
# Kadison–Schwarz Inequality, Helstrom–SLD Quantum Cramér–Rao, and Peirce QGT Positivity

This module formalizes the noncommutative operator-algebraic pillars of information geometry
over arbitrary associative star rings `[Ring A] [StarRing A]` and real star-algebras:

1. **Noncommutative Choi–Kadison–Schwarz Sum-of-Squares & Multiplicative Domain**:
   - Proves the exact ring identity `krausDual_kadison_schwarz_sum_of_squares`:
     `Φ*(x* x) - (Φ* x)* (Φ* x) = ∑ i, (krausDefect W x i)* (krausDefect W x i)`,
     yielding the operator inequality `krausDual_kadison_schwarz_le` in any
     `[StarOrderedRing A]`, the forward-channel dual `krausChannel_kadison_schwarz_le`,
     and Choi's multiplicative-domain theorem (`krausDual_mul_right_of_defect_eq_zero`,
     `krausDual_mul_left_of_defect_eq_zero`).
2. **Algebraic GNS Cauchy–Schwarz, Robertson–Heisenberg & Helstrom–SLD Quantum Cramér–Rao**:
   - Proves Cauchy–Schwarz (`posStarFunctional_cauchy_schwarz`) for every positive star-preserving
     `ℝ`-linear functional `IsPositiveStarFunctional ω`.
   - Derives the noncommutative Robertson–Heisenberg uncertainty relation
     (`robertson_heisenberg_star_uncertainty`), the Symmetric Logarithmic Derivative (SLD)
     quantum Cramér–Rao bound (`sld_quantum_cramer_rao_inequality` and
     `sld_quantum_cramer_rao_unbiased`), and monotonicity of quantum variance under unital
     Kraus channels (`krausDual_quantumVariance_le`).
3. **Peirce Grassmannian Quantum-Geometric Tensor Metric Positivity**:
   - Proves `peirce_qgt_metric_compression_eq_star_mul_self` and
     `peirce_qgt_metric_compression_nonneg` for self-adjoint idempotents `p` and skew-adjoint
     generators `a` (`star a = -a`).
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KadisonSchwarzAndQuantumCramerRao

open scoped BigOperators
open InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
open InfoGeometry.OperatorAlgebra.PeirceQuantumGeometricTensor

/-! ### 1. Noncommutative Choi–Kadison–Schwarz & Multiplicative Domain -/

section KrausKadisonSchwarz

variable {A : Type*} [Ring A] [StarRing A]

/-- Value of the backward Kraus action `krausDual W` at the identity. -/
theorem krausDual_one_eq {ι : Type*} [Fintype ι] (W : ι → A) :
    krausDual W 1 = ∑ i, star (W i) * W i := by
  unfold krausDual
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [mul_one]

/-- Right completeness makes the Heisenberg-picture Kraus map `krausDual W` unital. -/
theorem krausDual_one {ι : Type*} [Fintype ι] (W : ι → A)
    (hW : ∑ i, star (W i) * W i = 1) :
    krausDual W 1 = 1 := by
  rw [krausDual_one_eq, hW]

/-- `krausDual` commutes with the star involution on any `[Ring A] [StarRing A]`. -/
theorem krausDual_star {ι : Type*} [Fintype ι] (W : ι → A) (x : A) :
    star (krausDual W x) = krausDual W (star x) := by
  unfold krausDual
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [star_mul, star_mul, star_star, mul_assoc]

/-- `krausChannel` commutes with the star involution on any `[Ring A] [StarRing A]`. -/
theorem krausChannel_star {ι : Type*} [Fintype ι] (V : ι → A) (x : A) :
    star (krausChannel V x) = krausChannel V (star x) := by
  unfold krausChannel
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [star_mul, star_mul, star_star, mul_assoc]

/-- `krausChannel V` is definitionally `krausDual (fun i => star (V i))`. -/
theorem krausChannel_eq_krausDual_star {ι : Type*} [Fintype ι] (V : ι → A) (x : A) :
    krausChannel V x = krausDual (fun i => star (V i)) x := by
  unfold krausChannel krausDual
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [star_star]

/-- Choi–Kraus multiplicative defect `[x, W_i]_Φ := x W_i - W_i Φ*(x)` whose sum of squares
computes the Kadison–Schwarz gap `Φ*(x* x) - (Φ* x)* (Φ* x)`. -/
def krausDefect {ι : Type*} [Fintype ι] (W : ι → A) (x : A) (i : ι) : A :=
  x * W i - W i * krausDual W x

/-- **Noncommutative Choi–Kadison–Schwarz Sum-of-Squares Identity**: in an arbitrary associative
star ring `[Ring A] [StarRing A]` without commutativity or order hypotheses, whenever
`∑ i, star (W i) * W i = 1`, the Kadison–Schwarz difference equals the sum of star-squares
of the Choi–Kraus defects. -/
theorem krausDual_kadison_schwarz_sum_of_squares {ι : Type*} [Fintype ι]
    (W : ι → A) (hW : ∑ i, star (W i) * W i = 1) (x : A) :
    krausDual W (star x * x) - star (krausDual W x) * krausDual W x =
      ∑ i, star (krausDefect W x i) * krausDefect W x i := by
  let y := krausDual W x
  have hys : star y = krausDual W (star x) := krausDual_star W x
  have hterm (i : ι) :
      star (krausDefect W x i) * krausDefect W x i =
        (star (W i) * (star x * x) * W i - (star (W i) * star x * W i) * y) -
          star y * (star (W i) * x * W i) +
          star y * (star (W i) * W i) * y := by
    change star (x * W i - W i * y) * (x * W i - W i * y) = _
    rw [star_sub, star_mul, star_mul]
    noncomm_ring
  symm
  calc
    ∑ i, star (krausDefect W x i) * krausDefect W x i
        = ∑ i, ((star (W i) * (star x * x) * W i - (star (W i) * star x * W i) * y) -
            star y * (star (W i) * x * W i) + star y * (star (W i) * W i) * y) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact hterm i
    _ = ((∑ i, star (W i) * (star x * x) * W i - ∑ i, (star (W i) * star x * W i) * y) -
          ∑ i, star y * (star (W i) * x * W i)) + ∑ i, star y * (star (W i) * W i) * y := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = ((krausDual W (star x * x) - krausDual W (star x) * y) -
          star y * krausDual W x) + (star y * ∑ i, star (W i) * W i) * y := by
          congr 1
          · congr 1
            · congr 1
              rw [← Finset.sum_mul]
              rfl
            · rw [← Finset.mul_sum]
              rfl
          · rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = ((krausDual W (star x * x) - star y * y) - star y * y) + star y * 1 * y := by
          rw [hys, hW]
    _ = krausDual W (star x * x) - star y * y := by
          rw [mul_one]
          abel

/-- **Kadison–Schwarz Inequality for Backward Kraus Channels** in any `[StarOrderedRing A]`:
under `∑ i, star (W i) * W i = 1`, `star (krausDual W x) * krausDual W x ≤ krausDual W (star x * x)`. -/
theorem krausDual_kadison_schwarz_le
    [PartialOrder A] [IsOrderedAddMonoid A] [StarOrderedRing A]
    {ι : Type*} [Fintype ι] (W : ι → A) (hW : ∑ i, star (W i) * W i = 1) (x : A) :
    star (krausDual W x) * krausDual W x ≤ krausDual W (star x * x) := by
  have hnonneg :
      (0 : A) ≤ krausDual W (star x * x) - star (krausDual W x) * krausDual W x := by
    rw [krausDual_kadison_schwarz_sum_of_squares W hW x]
    exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg (krausDefect W x i)
  have hadd := add_le_add_right hnonneg (star (krausDual W x) * krausDual W x)
  simpa [zero_add, sub_add_cancel] using hadd

/-- Sum-of-squares Kadison–Schwarz identity for a unital forward Kraus channel `krausChannel V`. -/
theorem krausChannel_kadison_schwarz_sum_of_squares {ι : Type*} [Fintype ι]
    (V : ι → A) (hV : ∑ i, V i * star (V i) = 1) (x : A) :
    krausChannel V (star x * x) - star (krausChannel V x) * krausChannel V x =
      ∑ i, star (krausDefect (fun j => star (V j)) x i) *
        krausDefect (fun j => star (V j)) x i := by
  have hW : ∑ i, star (star (V i)) * star (V i) = 1 := by
    simpa [star_star] using hV
  simpa [krausChannel_eq_krausDual_star] using
    krausDual_kadison_schwarz_sum_of_squares (fun j => star (V j)) hW x

/-- **Kadison–Schwarz Inequality for Unital Forward Kraus Channels** in any `[StarOrderedRing A]`. -/
theorem krausChannel_kadison_schwarz_le
    [PartialOrder A] [IsOrderedAddMonoid A] [StarOrderedRing A]
    {ι : Type*} [Fintype ι] (V : ι → A) (hV : ∑ i, V i * star (V i) = 1) (x : A) :
    star (krausChannel V x) * krausChannel V x ≤ krausChannel V (star x * x) := by
  have hW : ∑ i, star (star (V i)) * star (V i) = 1 := by
    simpa [star_star] using hV
  simpa [krausChannel_eq_krausDual_star] using
    krausDual_kadison_schwarz_le (fun j => star (V j)) hW x

/-- **Choi Multiplicative Domain Theorem (Right Multiplication)**: if every Choi–Kraus defect
`krausDefect W x i` vanishes, then `x` lies in the right multiplicative domain of `krausDual W`:
`krausDual W (a * x) = krausDual W a * krausDual W x` for every `a : A`. -/
theorem krausDual_mul_right_of_defect_eq_zero {ι : Type*} [Fintype ι]
    (W : ι → A) (x : A) (hd : ∀ i, krausDefect W x i = 0) (a : A) :
    krausDual W (a * x) = krausDual W a * krausDual W x := by
  have hcomm (i : ι) : x * W i = W i * krausDual W x := sub_eq_zero.mp (hd i)
  unfold krausDual
  calc
    ∑ i, star (W i) * (a * x) * W i
        = ∑ i, star (W i) * a * (x * W i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp only [mul_assoc]
    _ = ∑ i, (star (W i) * a * W i) * krausDual W x := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hcomm i]
          simp only [mul_assoc]
    _ = (∑ i, star (W i) * a * W i) * krausDual W x := by
          rw [← Finset.sum_mul]

/-- **Choi Multiplicative Domain Theorem (Left Multiplication)**: if every Choi–Kraus defect
`krausDefect W x i` vanishes, then `krausDual W (star x * a) = star (krausDual W x) * krausDual W a`
for every `a : A`. -/
theorem krausDual_mul_left_of_defect_eq_zero {ι : Type*} [Fintype ι]
    (W : ι → A) (x : A) (hd : ∀ i, krausDefect W x i = 0) (a : A) :
    krausDual W (star x * a) = star (krausDual W x) * krausDual W a := by
  calc
    krausDual W (star x * a)
        = krausDual W (star (star a * x)) := by rw [star_mul, star_star]
    _ = star (krausDual W (star a * x)) := (krausDual_star W (star a * x)).symm
    _ = star (krausDual W (star a) * krausDual W x) := by
          rw [krausDual_mul_right_of_defect_eq_zero W x hd (star a)]
    _ = star (krausDual W x) * krausDual W a := by
          rw [star_mul, krausDual_star W (star a), star_star]

end KrausKadisonSchwarz

/-! ### 2. GNS Cauchy–Schwarz, Robertson–Heisenberg, SLD Quantum Cramér–Rao & Variance DPI -/

section PositiveStarBase

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]

/-- A real star-preserving positive linear functional on an associative real star-algebra:
non-negative on `star x * x` and self-adjoint (`ω (star x) = ω x`). -/
def IsPositiveStarFunctional (ω : A →ₗ[ℝ] ℝ) : Prop :=
  (∀ x : A, 0 ≤ ω (star x * x)) ∧ (∀ x : A, ω (star x) = ω x)

lemma posStarFunctional_star_mul_comm {ω : A →ₗ[ℝ] ℝ} (hω : IsPositiveStarFunctional ω)
    (x y : A) :
    ω (star y * x) = ω (star x * y) := by
  calc
    ω (star y * x) = ω (star (star x * y)) := by rw [star_mul, star_star]
    _ = ω (star x * y) := hω.2 (star x * y)

/-- Symmetric Logarithmic Derivative (SLD) Jordan inner product `(1 / 2) * ω {L₁, L₂}`
in an arbitrary real star-algebra. -/
def quantumSLDInner (ω : A →ₗ[ℝ] ℝ) (L₁ L₂ : A) : ℝ :=
  (1 / 2 : ℝ) * ω (operatorJordan L₁ L₂)

/-- Variance `ω ((X - ω X • 1) * (X - ω X • 1))` of an observable `X` in state `ω`. -/
def quantumVariance (ω : A →ₗ[ℝ] ℝ) (X : A) : ℝ :=
  ω ((X - ω X • 1) * (X - ω X • 1))

/-- On self-adjoint operators `L₁, L₂`, `quantumSLDInner ω L₁ L₂` equals `ω (star L₁ * L₂)`. -/
theorem quantumSLDInner_selfAdjoint_eq {ω : A →ₗ[ℝ] ℝ} (hω : IsPositiveStarFunctional ω)
    {L₁ L₂ : A} (h₁ : star L₁ = L₁) (h₂ : star L₂ = L₂) :
    quantumSLDInner ω L₁ L₂ = ω (star L₁ * L₂) := by
  dsimp [quantumSLDInner, operatorJordan]
  have hj : ω (L₂ * L₁) = ω (L₁ * L₂) := by
    have hstar : star (L₁ * L₂) = L₂ * L₁ := by rw [star_mul, h₂, h₁]
    rw [← hstar, hω.2]
  rw [map_add, hj, h₁]
  ring

/-- Kadison–Schwarz inequality evaluated under any `IsPositiveStarFunctional ω`:
`ω (star (krausDual W x) * krausDual W x) ≤ ω (krausDual W (star x * x))`. -/
theorem posStarFunctional_krausDual_sq_le {ω : A →ₗ[ℝ] ℝ}
    (hω : IsPositiveStarFunctional ω) {ι : Type*} [Fintype ι]
    (W : ι → A) (hW : ∑ i, star (W i) * W i = 1) (x : A) :
    ω (star (krausDual W x) * krausDual W x) ≤ ω (krausDual W (star x * x)) := by
  have hdiff : 0 ≤ ω (krausDual W (star x * x) - star (krausDual W x) * krausDual W x) := by
    rw [krausDual_kadison_schwarz_sum_of_squares W hW x, map_sum]
    exact Finset.sum_nonneg fun i _ => hω.1 (krausDefect W x i)
  rw [map_sub] at hdiff
  linarith

section StarModuleOnly

variable [StarModule ℝ A]

lemma centered_selfAdjoint {X : A} (hx : star X = X) (r : ℝ) :
    star (X - r • (1 : A)) = X - r • (1 : A) := by
  rw [star_sub, star_smul, star_trivial r, star_one, hx]

/-- Variance of every self-adjoint observable is non-negative under a positive star functional. -/
theorem quantumVariance_nonneg {ω : A →ₗ[ℝ] ℝ} (hω : IsPositiveStarFunctional ω)
    {X : A} (hx : star X = X) :
    0 ≤ quantumVariance ω X := by
  dsimp [quantumVariance]
  have hs := centered_selfAdjoint hx (ω X)
  calc
    0 ≤ ω (star (X - ω X • 1) * (X - ω X • 1)) := hω.1 _
    _ = ω ((X - ω X • 1) * (X - ω X • 1)) := by rw [hs]

end StarModuleOnly

section ScalarTowerKrausLinear

variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

/-- Backward Kraus action `krausDual W` packaged as an `ℝ`-linear endomorphism of `A`. -/
def krausDualLinear {ι : Type*} [Fintype ι] (W : ι → A) : A →ₗ[ℝ] A where
  toFun := krausDual W
  map_add' x y := by
    unfold krausDual
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    unfold krausDual
    simp only [mul_smul_comm, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

/-- Pulling back a positive star functional along a unital `krausDualLinear W` yields another
positive star functional. -/
theorem posStarFunctional_comp_krausDualLinear {ω : A →ₗ[ℝ] ℝ}
    (hω : IsPositiveStarFunctional ω) {ι : Type*} [Fintype ι]
    (W : ι → A) (hW : ∑ i, star (W i) * W i = 1) :
    IsPositiveStarFunctional (ω.comp (krausDualLinear W)) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · change 0 ≤ ω (krausDual W (star x * x))
    exact le_trans (hω.1 (krausDual W x)) (posStarFunctional_krausDual_sq_le hω W hW x)
  · change ω (krausDual W (star x)) = ω (krausDual W x)
    rw [← krausDual_star]
    exact hω.2 (krausDual W x)

/-- **Kraus Channel Variance Contraction (Quantum Data Processing for Variance)**:
for any unital Heisenberg Kraus map `krausDual W` (`∑ i, star (W i) * W i = 1`), any positive
star functional `ω`, and any self-adjoint observable `X`,
`quantumVariance ω (krausDual W X) ≤ quantumVariance (ω.comp (krausDualLinear W)) X`. -/
theorem krausDual_quantumVariance_le [StarModule ℝ A] {ω : A →ₗ[ℝ] ℝ}
    (hω : IsPositiveStarFunctional ω)
    {ι : Type*} [Fintype ι] (W : ι → A) (hW : ∑ i, star (W i) * W i = 1)
    {X : A} (hx : star X = X) :
    quantumVariance ω (krausDual W X) ≤ quantumVariance (ω.comp (krausDualLinear W)) X := by
  let μ := ω (krausDual W X)
  let Z := X - μ • (1 : A)
  have hZs : star Z = Z := centered_selfAdjoint hx μ
  have hKZ : krausDual W Z = krausDual W X - μ • (1 : A) := by
    change krausDualLinear W (X - μ • (1 : A)) = krausDual W X - μ • (1 : A)
    rw [map_sub, map_smul]
    change krausDual W X - μ • krausDual W 1 = krausDual W X - μ • 1
    rw [krausDual_one W hW]
  have hKZs : star (krausDual W Z) = krausDual W Z := by
    rw [krausDual_star, hZs]
  have hcs := posStarFunctional_krausDual_sq_le hω W hW Z
  rw [hKZs, hKZ, hZs] at hcs
  simpa [quantumVariance, LinearMap.comp_apply, krausDualLinear, μ, Z] using hcs

variable [StarModule ℝ A]

lemma posStarFunctional_quadratic_nonneg {ω : A →ₗ[ℝ] ℝ} (hω : IsPositiveStarFunctional ω)
    (x y : A) (t : ℝ) :
    0 ≤ ω (star x * x) + 2 * t * ω (star x * y) + t ^ 2 * ω (star y * y) := by
  have h0 : 0 ≤ ω (star (x + t • y) * (x + t • y)) := hω.1 (x + t • y)
  have hexp :
      star (x + t • y) * (x + t • y) =
        star x * x + t • (star x * y) + t • (star y * x) + (t * t) • (star y * y) := by
    rw [star_add, star_smul, star_trivial t]
    rw [add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
      mul_smul_comm, smul_smul]
    abel
  rw [hexp, map_add, map_add, map_add, map_smul, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, posStarFunctional_star_mul_comm hω x y] at h0
  linarith [sq t]

/-- **Algebraic GNS Cauchy–Schwarz Inequality**: for every `IsPositiveStarFunctional ω`,
`ω (star x * y) ^ 2 ≤ ω (star x * x) * ω (star y * y)`. -/
theorem posStarFunctional_cauchy_schwarz {ω : A →ₗ[ℝ] ℝ} (hω : IsPositiveStarFunctional ω)
    (x y : A) :
    ω (star x * y) ^ 2 ≤ ω (star x * x) * ω (star y * y) := by
  have hy_nonneg : 0 ≤ ω (star y * y) := hω.1 y
  rcases lt_or_ge 0 (ω (star y * y)) with hy_pos | hy_le
  · have hq := posStarFunctional_quadratic_nonneg hω x y (-(ω (star x * y) / ω (star y * y)))
    have hmul : 0 ≤ ω (star y * y) *
        (ω (star x * x) + 2 * -(ω (star x * y) / ω (star y * y)) * ω (star x * y) +
          (-(ω (star x * y) / ω (star y * y))) ^ 2 * ω (star y * y)) :=
      mul_nonneg hy_nonneg hq
    have hy_ne : ω (star y * y) ≠ 0 := hy_pos.ne'
    field_simp [hy_ne] at hmul
    nlinarith
  · have hy0 : ω (star y * y) = 0 := le_antisymm hy_le hy_nonneg
    by_cases hxy : ω (star x * y) = 0
    · rw [hxy, hy0]
      norm_num
    · have hq := posStarFunctional_quadratic_nonneg hω x y
        (-((ω (star x * x) + 1) / (2 * ω (star x * y))))
      rw [hy0, mul_zero, add_zero] at hq
      have hne2 : (2 * ω (star x * y)) ≠ 0 := mul_ne_zero two_ne_zero hxy
      have hsimp :
          ω (star x * x) + 2 * -((ω (star x * x) + 1) / (2 * ω (star x * y))) * ω (star x * y) =
            -1 := by
        field_simp [hne2]
        ring
      rw [hsimp] at hq
      linarith

/-- **Robertson–Heisenberg Star-Algebra Uncertainty Relation**: for any positive star
functional `ω`, self-adjoint observable `x` (`star x = x`), and skew-adjoint generator `k`
(`star k = -k`), `(ω [x, k]) ^ 2 ≤ 4 * ω (x * x) * ω (-(k * k))`. -/
theorem robertson_heisenberg_star_uncertainty {ω : A →ₗ[ℝ] ℝ}
    (hω : IsPositiveStarFunctional ω) {x k : A} (hx : star x = x) (hk : star k = -k) :
    (ω (operatorComm x k)) ^ 2 ≤ 4 * ω (x * x) * ω (-(k * k)) := by
  have hcomm : ω (operatorComm x k) = 2 * ω (star x * k) := by
    have hneg : star (x * k) = -(k * x) := by
      rw [star_mul, hk, hx, neg_mul]
    have hid : operatorComm x k = x * k + star (x * k) := by
      rw [hneg]
      simp [operatorComm, sub_eq_add_neg]
    rw [hid, map_add, hω.2 (x * k), hx]
    ring
  have hcs := posStarFunctional_cauchy_schwarz hω x k
  have hk2 : star k * k = -(k * k) := by rw [hk, neg_mul]
  rw [hx, hk2] at hcs
  rw [hcomm, hx]
  nlinarith

/-- **Helstrom–SLD Quantum Cramér–Rao Inequality** in an arbitrary associative real star-algebra:
for every positive star functional `ω` and self-adjoint estimator `X` and SLD operator `L`,
`quantumSLDInner ω (X - ω X • 1) L ^ 2 ≤ quantumVariance ω X * quantumSLDInner ω L L`. -/
theorem sld_quantum_cramer_rao_inequality {ω : A →ₗ[ℝ] ℝ} (hω : IsPositiveStarFunctional ω)
    {X L : A} (hx : star X = X) (hL : star L = L) :
    quantumSLDInner ω (X - ω X • 1) L ^ 2 ≤ quantumVariance ω X * quantumSLDInner ω L L := by
  have hx0 : star (X - ω X • (1 : A)) = X - ω X • (1 : A) := centered_selfAdjoint hx (ω X)
  rw [quantumSLDInner_selfAdjoint_eq hω hx0 hL,
    quantumSLDInner_selfAdjoint_eq hω hL hL]
  have hv : quantumVariance ω X = ω (star (X - ω X • 1) * (X - ω X • 1)) := by
    dsimp [quantumVariance]
    rw [hx0]
  rw [hv]
  exact posStarFunctional_cauchy_schwarz hω (X - ω X • 1) L

/-- **Unbiased Quantum Cramér–Rao Lower Bound**: if `ω L = 0`,
`quantumSLDInner ω X L = 1`, and `0 < quantumSLDInner ω L L`, then
`1 / quantumSLDInner ω L L ≤ quantumVariance ω X`. -/
theorem sld_quantum_cramer_rao_unbiased {ω : A →ₗ[ℝ] ℝ} (hω : IsPositiveStarFunctional ω)
    {X L : A} (hx : star X = X) (hL : star L = L)
    (hL0 : ω L = 0) (hunb : quantumSLDInner ω X L = 1) (hpos : 0 < quantumSLDInner ω L L) :
    1 / quantumSLDInner ω L L ≤ quantumVariance ω X := by
  have hcent : quantumSLDInner ω (X - ω X • 1) L = 1 := by
    have hsub :
        quantumSLDInner ω (X - ω X • 1) L =
          quantumSLDInner ω X L - ω X * quantumSLDInner ω 1 L := by
      dsimp [quantumSLDInner, operatorJordan]
      have hid :
          (X - ω X • 1) * L + L * (X - ω X • 1) =
            (X * L + L * X) - ω X • (L + L) := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add]
        abel
      have hid1 : (1 : A) * L + L * 1 = L + L := by simp
      rw [hid, hid1, map_sub, map_smul, smul_eq_mul]
      ring
    have h1L : quantumSLDInner ω 1 L = ω L := by
      dsimp [quantumSLDInner, operatorJordan]
      rw [one_mul, mul_one, ← two_smul ℝ L, map_smul, smul_eq_mul]
      ring
    rw [hsub, h1L, hunb, hL0, mul_zero, sub_zero]
  have hcr := sld_quantum_cramer_rao_inequality hω hx hL
  rw [hcent, one_pow] at hcr
  exact (div_le_iff₀ hpos).mpr hcr

end ScalarTowerKrausLinear

end PositiveStarBase

/-! ### 3. Peirce Grassmannian Quantum-Geometric Tensor Positivity -/

section PeirceQGTPositivity

variable {A : Type*} [Ring A] [StarRing A]

/-- If `p` is self-adjoint (`star p = p`) and `a` is skew-adjoint (`star a = -a`), then the
Peirce Grassmannian tangent direction `peirceTangent p a = p * a - a * p` is self-adjoint. -/
theorem peirceTangent_selfAdjoint {p a : A} (hps : star p = p) (has : star a = -a) :
    star (peirceTangent p a) = peirceTangent p a := by
  dsimp [peirceTangent]
  rw [star_sub, star_mul, star_mul, hps, has]
  noncomm_ring

/-- Exact star-square factorization of the Peirce metric compression
`p * peirceTangent p a * peirceTangent p a * p = star Y * Y` where
`Y = (1 - p) * peirceTangent p a * p`. -/
theorem peirce_qgt_metric_compression_eq_star_mul_self {p a : A}
    (hp : p * p = p) (hps : star p = p) (has : star a = -a) :
    p * peirceTangent p a * peirceTangent p a * p =
      star ((1 - p) * peirceTangent p a * p) * ((1 - p) * peirceTangent p a * p) := by
  have hts : star (peirceTangent p a) = peirceTangent p a := peirceTangent_selfAdjoint hps has
  have hcomp : p * peirceTangent p a * p = 0 := by
    simp only [peirceTangent, mul_sub, sub_mul, mul_assoc]
    rw [hp, ← mul_assoc p p (a * p), hp, sub_self]
  have hright : (1 - p) * peirceTangent p a * p = peirceTangent p a * p := by
    calc
      (1 - p) * peirceTangent p a * p
          = peirceTangent p a * p - p * peirceTangent p a * p := by noncomm_ring
      _ = peirceTangent p a * p := by rw [hcomp, sub_zero]
  rw [hright, star_mul, hps, hts]
  simp only [mul_assoc]

/-- Positivity of the Peirce quantum-geometric tensor diagonal compression in any
`[StarOrderedRing A]`. -/
theorem peirce_qgt_metric_compression_nonneg
    [PartialOrder A] [IsOrderedAddMonoid A] [StarOrderedRing A]
    {p a : A} (hp : p * p = p) (hps : star p = p) (has : star a = -a) :
    (0 : A) ≤ p * peirceTangent p a * peirceTangent p a * p := by
  rw [peirce_qgt_metric_compression_eq_star_mul_self hp hps has]
  exact star_mul_self_nonneg _

end PeirceQGTPositivity

end InfoGeometry.OperatorAlgebra.KadisonSchwarzAndQuantumCramerRao

end section
