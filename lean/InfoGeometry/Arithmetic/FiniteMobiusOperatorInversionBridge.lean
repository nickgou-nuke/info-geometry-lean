import Mathlib.NumberTheory.Divisors
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge

/-!
# Finite Möbius Operator Inversion Bridge
-/

namespace InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge

open InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge
open ArithmeticFunction
open scoped BigOperators

noncomputable def dirichletOperator (N : ℕ) (f : ℕ → ℂ) : TestFun →ₗ[ℂ] TestFun :=
  ∑ n ∈ Finset.Icc 1 N, f n • logShiftOp n

theorem dirichletOperator_expTestFun (N : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    dirichletOperator N f (expTestFun s) =
      (∑ n ∈ Finset.Icc 1 N,
        f n * Complex.exp (-(s * (Real.log (n : ℝ) : ℂ)))) • expTestFun s := by
  unfold dirichletOperator
  simp [LinearMap.sum_apply, logNatShift_expTestFun, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro n hn
  ext t
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem dirichletOperator_expTestFun_cpow
    (N : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    dirichletOperator N f (expTestFun s) =
      (∑ n ∈ Finset.Icc 1 N, f n * (n : ℂ) ^ (-s)) • expTestFun s := by
  rw [dirichletOperator_expTestFun]
  apply congrArg (fun z : ℂ => z • expTestFun s)
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [← complexPow_nat_eq_exp_neg_log n hnpos s]

theorem dirichletOperator_comp_exact (N : ℕ) (f g : ℕ → ℂ) :
    dirichletOperator N f ∘ₗ dirichletOperator N g =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        (f a * g b) • logShiftOp (a * b) := by
  classical
  ext h t
  simp only [dirichletOperator, LinearMap.comp_apply, LinearMap.sum_apply,
    Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    logShiftOp, shiftOp]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.sum_apply]
  change
    (∑ x ∈ Finset.Icc 1 N,
      f x * (∑ y ∈ Finset.Icc 1 N,
        (g y • (fun u : ℝ => h (u - Real.log (y : ℝ))))
          (t - Real.log (x : ℝ)))) =
      ∑ x ∈ Finset.Icc 1 N, ∑ y ∈ Finset.Icc 1 N,
        f x * g y * h (t - Real.log ((x * y : ℕ) : ℝ))
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [Nat.cast_mul]
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr (Finset.mem_Icc.mp hx).1
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (Finset.mem_Icc.mp hy).1
  rw [Real.log_mul (ne_of_gt hxpos) (ne_of_gt hypos)]
  ring_nf

theorem logShiftOp_comp_eq_mul (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    logShiftOp n ∘ₗ logShiftOp m = logShiftOp (n * m) := by
  unfold logShiftOp
  rw [shiftOp_comp]
  congr 1
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  simpa [Nat.cast_mul] using
    (Real.log_mul (ne_of_gt hn_pos) (ne_of_gt hm_pos)).symm

/-- The exact rectangular Dirichlet convolution $f *_{N}^{\square} g$. -/
noncomputable def rectangularDirichletConvolution (N : ℕ) (f g : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 = k), f p.1 * g p.2

theorem rectangularConvolution_eq_dirichletConvolution_of_le (N : ℕ) (f g : ℕ → ℂ) (k : ℕ) (hk : k ≤ N) (hk0 : 0 < k) :
    rectangularDirichletConvolution N f g k = ∑ d ∈ Nat.divisors k, f d * g (k / d) := by
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  unfold rectangularDirichletConvolution
  rw [hset]
  rw [← Nat.divisorsAntidiagonal_eq_prod_filter_of_le (Nat.ne_of_gt hk0) hk]
  exact Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)

noncomputable def zetaCoefficients : ℕ → ℂ := fun _ => 1
noncomputable def mobiusCoefficients : ℕ → ℂ := fun n => (moebius n : ℂ)

noncomputable def zetaDirichletOperator (N : ℕ) : TestFun →ₗ[ℂ] TestFun :=
  dirichletOperator N zetaCoefficients

noncomputable def mobiusDirichletOperator (N : ℕ) : TestFun →ₗ[ℂ] TestFun :=
  dirichletOperator N mobiusCoefficients

theorem zetaDirichletOperator_expTestFun (N : ℕ) (s : ℂ) :
    zetaDirichletOperator N (expTestFun s) =
      (∑ n ∈ Finset.Icc 1 N,
        Complex.exp (-(s * (Real.log (n : ℝ) : ℂ)))) • expTestFun s := by
  unfold zetaDirichletOperator
  simpa [zetaCoefficients] using dirichletOperator_expTestFun N zetaCoefficients s

theorem mobiusDirichletOperator_expTestFun (N : ℕ) (s : ℂ) :
    mobiusDirichletOperator N (expTestFun s) =
      (∑ n ∈ Finset.Icc 1 N,
        mobiusCoefficients n *
          Complex.exp (-(s * (Real.log (n : ℝ) : ℂ)))) • expTestFun s := by
  unfold mobiusDirichletOperator
  exact dirichletOperator_expTestFun N mobiusCoefficients s

theorem mobius_convolution_stableRange (N k : ℕ) (hk : k ≤ N) (hk0 : 0 < k) :
    rectangularDirichletConvolution N zetaCoefficients mobiusCoefficients k =
      if k = 1 then 1 else 0 := by
  rw [rectangularConvolution_eq_dirichletConvolution_of_le N zetaCoefficients
    mobiusCoefficients k hk hk0]
  rw [← Nat.sum_divisorsAntidiagonal
    (fun a b => zetaCoefficients a * mobiusCoefficients b)]
  have h :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) = 1 :=
    ArithmeticFunction.coe_zeta_mul_coe_moebius
  have hk' := congrArg (fun F : ArithmeticFunction ℂ => F k) h
  dsimp at hk'
  have hzero :
      (∑ x ∈ k.divisorsAntidiagonal,
        ((if x.1 = 0 then 0 else 1 : ℕ) : ℂ) * (moebius x.2 : ℂ)) =
        ∑ x ∈ k.divisorsAntidiagonal, (moebius x.2 : ℂ) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
    simp [hx0]
  rw [hzero] at hk'
  simpa [zetaCoefficients, mobiusCoefficients, hk0.ne'] using hk'

theorem finiteZetaMobius_boundary_support (N k : ℕ) (hk : k ≤ N) :
    k ∈ Finset.Ioc N (N ^ 2) ↔ False := by
  constructor
  · intro h
    exact (Nat.not_lt_of_ge hk) (Finset.mem_Ioc.mp h).1
  · intro h
    exact False.elim h

end InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge
