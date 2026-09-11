import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesRealModularRealizationBridge
import InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge

/-!
# Finite Hestenes--Dirichlet operator bridge

This owner is the finite algebraic shadow of substituting the real logarithmic
flow for the Mellin variable.  It records finite sums of the operators
`realFlow (log n)` and their exact rectangular composition law.  No unbounded
operator, functional calculus, convergence, or inverse is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteHestenesDirichletOperatorBridge

open InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge
open InfoGeometry.Canonical.HestenesRealModularRealizationBridge
open ArithmeticFunction
open scoped BigOperators

/-- A finite Dirichlet operator with coefficients in `ℝ`. -/
def finiteHestenesDirichletOperator
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (N : ℕ) (f : ℕ → ℝ) : M →ₗ[ℝ] M :=
  ∑ n ∈ Finset.Icc 1 N, f n • D.realFlow (Real.log n)

theorem finiteHestenesDirichletOperator_apply
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (N : ℕ) (f : ℕ → ℝ) (v : M) :
    finiteHestenesDirichletOperator D N f v =
      ∑ n ∈ Finset.Icc 1 N, f n • D.realFlow (Real.log n) v := by
  simp [finiteHestenesDirichletOperator]

/-- The coefficient of the finite rectangular product, over `ℝ`. -/
def rectangularHestenesDirichletConvolution
    (N : ℕ) (f g : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun p => p.1 * p.2 = k), f p.1 * g p.2

/-- Composition is the exact finite rectangular Dirichlet product. -/
theorem finiteHestenesDirichletOperator_comp_rectangular
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (N : ℕ) (f g : ℕ → ℝ) :
    finiteHestenesDirichletOperator D N f ∘ₗ
        finiteHestenesDirichletOperator D N g =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (f m * g n) • D.realFlow (Real.log (m * n)) := by
  ext v
  simp only [finiteHestenesDirichletOperator, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
  have hlog : Real.log (m : ℝ) + Real.log (n : ℝ) =
      Real.log (m * n : ℕ) := by
    simpa [Nat.cast_mul] using
      (Real.log_mul (by positivity : (m : ℝ) ≠ 0)
        (by positivity : (n : ℝ) ≠ 0)).symm
  have hflow := congrArg (fun T : M →ₗ[ℝ] M => T v)
    (D.realFlow_add (Real.log (m : ℝ)) (Real.log (n : ℝ)))
  rw [hlog] at hflow
  have hflow' : (D.realFlow (Real.log (m : ℝ)))
      ((D.realFlow (Real.log (n : ℝ))) v) =
      (D.realFlow (Real.log (m * n : ℕ))) v := by
    simpa [LinearMap.comp_apply] using hflow.symm
  rw [hflow']
  simp [smul_smul]

/-- The same rectangular composition, regrouped by the product index. -/
theorem finiteHestenesDirichletOperator_comp_grouped
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (N : ℕ) (f g : ℕ → ℝ) :
    finiteHestenesDirichletOperator D N f ∘ₗ
        finiteHestenesDirichletOperator D N g =
      ∑ k ∈ Finset.Icc 1 (N * N),
        rectangularHestenesDirichletConvolution N f g k •
          D.realFlow (Real.log k) := by
  rw [finiteHestenesDirichletOperator_comp_rectangular]
  classical
  let S := Finset.Icc 1 N ×ˢ Finset.Icc 1 N
  let T := Finset.Icc 1 (N * N)
  have hleft :
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (f m * g n) • D.realFlow (Real.log (m * n))) =
      ∑ p ∈ S, (f p.1 * g p.2) •
        D.realFlow (Real.log ((p.1 * p.2 : ℕ) : ℝ)) := by
    rw [Finset.sum_product]
    simp [Nat.cast_mul]
  rw [hleft]
  let hmap : ∀ p ∈ S, p.1 * p.2 ∈ T := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    rcases hp' with ⟨hpm, hpn⟩
    rw [Finset.mem_Icc] at hpm hpn ⊢
    constructor
    · exact Nat.mul_pos hpm.1 hpn.1
    · exact Nat.mul_le_mul hpm.2 hpn.2
  have hfib := Finset.sum_fiberwise_of_maps_to (s := S) (t := T)
    (g := fun p : ℕ × ℕ => p.1 * p.2) (hmap)
    (fun p => (f p.1 * g p.2) •
      D.realFlow (Real.log (p.1 * p.2)))
  simp only [Nat.cast_mul] at hfib ⊢
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro k hk
  have hsum :
      (∑ p ∈ S with p.1 * p.2 = k,
        (f p.1 * g p.2) • D.realFlow (Real.log (p.1 * p.2))) =
        ∑ p ∈ S with p.1 * p.2 = k,
          (f p.1 * g p.2) • D.realFlow (Real.log k) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hcast : (p.1 : ℝ) * (p.2 : ℝ) = (k : ℝ) := by
      exact_mod_cast hp.2
    rw [hcast]
  rw [hsum]
  rw [← Finset.sum_smul]
  rfl

/-- The finite logarithmic coefficient operator. -/
def finiteHestenesLogOperator
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (N : ℕ) : M →ₗ[ℝ] M :=
  finiteHestenesDirichletOperator D N logCoefficients

/-- The finite von Mangoldt coefficient operator. -/
def finiteHestenesMangoldtOperator
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (N : ℕ) : M →ₗ[ℝ] M :=
  finiteHestenesDirichletOperator D N mangoldtCoefficients

theorem finiteHestenesLogOperator_apply
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (N : ℕ) (v : M) :
    finiteHestenesLogOperator D N v =
      ∑ n ∈ Finset.Icc 1 N, Real.log n • D.realFlow (Real.log n) v := by
  simp [finiteHestenesLogOperator, finiteHestenesDirichletOperator,
    logCoefficients]

theorem finiteHestenesMangoldtOperator_apply
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (N : ℕ) (v : M) :
    finiteHestenesMangoldtOperator D N v =
      ∑ n ∈ Finset.Icc 1 N, mangoldtCoefficients n •
        D.realFlow (Real.log n) v := by
  simp [finiteHestenesMangoldtOperator, finiteHestenesDirichletOperator]

theorem rectangularHestenesConvolution_eq_divisorConvolution_of_le
    (N : ℕ) (f g : ℕ → ℝ) (k : ℕ) (hk : k ≤ N) (hk0 : 0 < k) :
    rectangularHestenesDirichletConvolution N f g k =
      ∑ d ∈ Nat.divisors k, f d * g (k / d) := by
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  unfold rectangularHestenesDirichletConvolution
  rw [hset]
  rw [← Nat.divisorsAntidiagonal_eq_prod_filter_of_le (Nat.ne_of_gt hk0) hk]
  exact Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)

/-- Finite Möbius inversion on the stable coefficient range of the Hestenes
operator product. -/
theorem hestenes_mobius_convolution_stableRange
    (N k : ℕ) (hk : k ≤ N) (hk0 : 0 < k) :
    rectangularHestenesDirichletConvolution N
        (fun _ => (1 : ℝ)) (fun n => (ArithmeticFunction.moebius n : ℝ)) k =
      if k = 1 then 1 else 0 := by
  rw [rectangularHestenesConvolution_eq_divisorConvolution_of_le N
    (fun _ => (1 : ℝ)) (fun n => (ArithmeticFunction.moebius n : ℝ)) k hk hk0]
  rw [← Nat.sum_divisorsAntidiagonal
    (fun a b => (1 : ℝ) * (ArithmeticFunction.moebius b : ℝ))]
  have h :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) = 1 :=
    ArithmeticFunction.coe_zeta_mul_coe_moebius
  have hk' := congrArg (fun F : ArithmeticFunction ℝ => F k) h
  dsimp at hk'
  have hzero :
      (∑ x ∈ k.divisorsAntidiagonal,
        ((if x.1 = 0 then 0 else 1 : ℕ) : ℝ) *
          (ArithmeticFunction.moebius x.2 : ℝ)) =
        ∑ x ∈ k.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
    simp [hx0]
  rw [hzero] at hk'
  simpa [hk0.ne'] using hk'

theorem hestenes_zeta_mangoldt_eq_log
    (N k : ℕ) (hk : k ≤ N) (hk0 : 0 < k) :
    rectangularHestenesDirichletConvolution N
        (fun _ => (1 : ℝ)) mangoldtCoefficients k = Real.log k := by
  rw [rectangularHestenesConvolution_eq_divisorConvolution_of_le N
    (fun _ => (1 : ℝ)) mangoldtCoefficients k hk hk0]
  rw [← Nat.sum_divisorsAntidiagonal
    (fun a b => (1 : ℝ) * mangoldtCoefficients b)]
  have hfun :
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        ArithmeticFunction.vonMangoldt = ArithmeticFunction.log :=
    ArithmeticFunction.zeta_mul_vonMangoldt
  have h := congrArg (fun F : ArithmeticFunction ℝ => F k) hfun
  dsimp at h
  have hzero :
      (∑ x ∈ k.divisorsAntidiagonal,
        ((if x.1 = 0 then 0 else 1 : ℕ) : ℝ) * vonMangoldt x.2) =
        ∑ x ∈ k.divisorsAntidiagonal, vonMangoldt x.2 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
    simp [hx0]
  rw [hzero] at h
  simpa [mangoldtCoefficients] using h

theorem hestenes_mobius_log_eq_mangoldt
    (N k : ℕ) (hk : k ≤ N) (hk0 : 0 < k) :
    rectangularHestenesDirichletConvolution N
        (fun n => (ArithmeticFunction.moebius n : ℝ)) logCoefficients k =
      mangoldtCoefficients k := by
  rw [rectangularHestenesConvolution_eq_divisorConvolution_of_le N
    (fun n => (ArithmeticFunction.moebius n : ℝ)) logCoefficients k hk hk0]
  simp only [logCoefficients, mangoldtCoefficients]
  rw [← Nat.sum_divisorsAntidiagonal
    (fun a b => (ArithmeticFunction.moebius a : ℝ) * Real.log b)]
  have hfun :
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        ArithmeticFunction.log = ArithmeticFunction.vonMangoldt :=
    ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  have h := congrArg (fun F : ArithmeticFunction ℝ => F k) hfun
  dsimp at h
  simpa [logCoefficients, mangoldtCoefficients] using h

end InfoGeometry.Canonical.FiniteHestenesDirichletOperatorBridge
