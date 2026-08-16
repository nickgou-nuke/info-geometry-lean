import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import InfoGeometry.Topology.ConformalSpin

/-!
# N-Potent Cyclotomic Spin Hull and Hadjiivanov--Georgiev Fibonacci Bridge

This module formalizes the algebraic connection between:
1. $n$-potent hull operators: $T^n = T$ with polynomial $p_n(z) = z^n - z = z(z^{n-1} - 1)$
2. Cyclotomic phase spectra $\mu_{n-1} = \{\zeta \in \mathbb{C} \mid \zeta^{n-1} = 1\}$
3. Rational fractional spins $s = m / (n-1) \pmod 1$ via $\lambda = e^{2\pi i s}$
4. The Hadjiivanov--Georgiev (arXiv:2404.01778) Fibonacci anyon sector at $h_\varepsilon = 2/5$,
   whose topological twist $\theta_\tau = e^{4\pi i / 5}$ is a primitive 5th root of unity and a root of the 6-potent hull $z^6 - z = 0$.

## Key Theorems:
- `n_potent_root_iff_succ`: $z^{m+1} = z \iff z^m = 1$ for $z \neq 0$.
- `fibonacci_twist_is_primitive_root_five`: $\theta_\tau$ is a primitive 5th root of unity (`IsPrimitiveRoot θ_τ 5`).
- `fibonacci_twist_pow_five`: $(\theta_\tau)^5 = 1$.
- `fibonacci_twist_pow_ne_one_of_lt`: $(\theta_\tau)^k \neq 1$ for all $1 \le k < 5$.
- `fibonacci_twist_minimal_nPotency`: $6$ is the minimal potency degree $n > 1$ such that $(\theta_\tau)^n = \theta_\tau$.
- `fibonacci_spin_mem_six_potent_hull`: $\theta_\tau$ is a root of the 6-potent hull polynomial $p_6(z) = 0$.
- `mem_fibonacciEigenspace_iff`: Eigenspace $\ker(T - \theta_\tau I)$ of an endomorphism $T$.
-/

set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Physics.Algebra.NPotentCyclotomicSpinHullBridge

open Complex

/-- The $n$-potent hull polynomial $p_n(z) = z^n - z$. -/
def hullPoly (n : ℕ) (z : ℂ) : ℂ := z ^ n - z

/-- A nonzero complex number is an $(m+1)$-potent root iff it is an $m$-th root of unity. -/
theorem n_potent_root_iff_succ (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (hz : z ≠ 0) :
    hullPoly (m + 1) z = 0 ↔ z ^ m = 1 := by
  dsimp [hullPoly]
  have h_split : z ^ (m + 1) - z = z * (z ^ m - 1) := by
    rw [pow_succ, mul_sub, mul_one, mul_comm (z ^ m) z]
  rw [h_split, mul_eq_zero]
  simp [hz, sub_eq_zero]

/-- A nonzero complex number is an $n$-potent root iff it is an $(n-1)$-th root of unity (for $n \ge 2$). -/
theorem n_potent_root_iff (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ≠ 0) :
    hullPoly n z = 0 ↔ z ^ (n - 1) = 1 := by
  have hn_eq : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn_eq]
  exact n_potent_root_iff_succ (n - 1) (by omega) z hz

/-- The topological twist associated to a rational conformal spin $s$. -/
def topologicalTwist (s : ℚ) : ℂ :=
  Complex.exp (2 * Real.pi * I * (s : ℂ))

/-- The Georgiev--Hadjiivanov conformal weight of the Fibonacci anyon field ε. -/
def fibonacciConformalWeight : ℚ := 2 / 5

/-- The Fibonacci topological twist θ_τ = e^{4π i / 5}. -/
def fibonacciTopologicalTwist : ℂ :=
  topologicalTwist fibonacciConformalWeight

/-- 🏆 THEOREM: The Fibonacci topological twist is a PRIMITIVE 5th root of unity in ℂ. -/
theorem fibonacci_twist_is_primitive_root_five :
    IsPrimitiveRoot fibonacciTopologicalTwist 5 := by
  dsimp [fibonacciTopologicalTwist, topologicalTwist, fibonacciConformalWeight]
  have hcop : Nat.Coprime 2 5 := by decide
  have h := Complex.isPrimitiveRoot_exp_of_coprime 2 5 (by decide) hcop
  have heq : ((2 : ℕ) : ℂ) / ((5 : ℕ) : ℂ) = ((2 / 5 : ℚ) : ℂ) := by
    push_cast
    ring
  rw [heq] at h
  exact h

/-- The sixth-potent polynomial splits into the zero factor and the
primitive-fifth-root cyclotomic sector.  This is a polynomial identity, not
an assertion about a particular boundary operator. -/
theorem six_potent_polynomial_factorization :
    (Polynomial.X ^ 6 - Polynomial.X : Polynomial ℂ) =
      Polynomial.X * Polynomial.cyclotomic 1 ℂ * Polynomial.cyclotomic 5 ℂ := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [Polynomial.cyclotomic_one, Polynomial.cyclotomic_prime]
  simp [Finset.sum_range_succ]
  ring

/-- The Fibonacci twist lies in the named `Φ₅` cyclotomic root sector. -/
theorem fibonacci_twist_is_cyclotomic_five_root :
    (Polynomial.cyclotomic 5 ℂ).IsRoot fibonacciTopologicalTwist :=
  fibonacci_twist_is_primitive_root_five.isRoot_cyclotomic (by norm_num)

/-- 🏆 THEOREM: The Fibonacci topological twist satisfies (θ_τ)^5 = 1. -/
theorem fibonacci_twist_pow_five :
    fibonacciTopologicalTwist ^ 5 = 1 :=
  fibonacci_twist_is_primitive_root_five.pow_eq_one

/-- 🏆 THEOREM: No smaller positive power of θ_τ equals 1. -/
theorem fibonacci_twist_pow_ne_one_of_lt (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < 5) :
    fibonacciTopologicalTwist ^ k ≠ 1 := by
  intro h
  have hdvd := fibonacci_twist_is_primitive_root_five.dvd_of_pow_eq_one k h
  have : 5 ≤ k := Nat.le_of_dvd hk_pos hdvd
  omega

/-- 🏆 THEOREM: 6 is the MINIMAL integer n > 1 such that (θ_τ)^n = θ_τ. -/
theorem fibonacci_twist_minimal_nPotency :
    fibonacciTopologicalTwist ^ 6 = fibonacciTopologicalTwist ∧
      ∀ n : ℕ, 1 < n → n < 6 → fibonacciTopologicalTwist ^ n ≠ fibonacciTopologicalTwist := by
  have h6 : fibonacciTopologicalTwist ^ 6 = fibonacciTopologicalTwist := by
    have h_pow5 := fibonacci_twist_pow_five
    calc
      fibonacciTopologicalTwist ^ 6 = fibonacciTopologicalTwist ^ (5 + 1) := rfl
      _ = fibonacciTopologicalTwist ^ 5 * fibonacciTopologicalTwist := by rw [pow_succ]
      _ = 1 * fibonacciTopologicalTwist := by rw [h_pow5]
      _ = fibonacciTopologicalTwist := by rw [one_mul]
  refine ⟨h6, ?_⟩
  intro n hn_gt1 hn_lt6
  have hz_ne : fibonacciTopologicalTwist ≠ 0 := Complex.exp_ne_zero _
  intro h_eq
  have hn_sub_pos : 0 < n - 1 := by omega
  have hn_sub_lt : n - 1 < 5 := by omega
  have h_split : fibonacciTopologicalTwist ^ (n - 1) = 1 := by
    have h_decomp : fibonacciTopologicalTwist ^ n = fibonacciTopologicalTwist * fibonacciTopologicalTwist ^ (n - 1) := by
      have hn_eq : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn_eq]
      rw [pow_succ, mul_comm]
    rw [h_decomp] at h_eq
    have h_div := mul_left_cancel₀ hz_ne (h_eq.trans (mul_one fibonacciTopologicalTwist).symm)
    exact h_div
  exact fibonacci_twist_pow_ne_one_of_lt (n - 1) hn_sub_pos hn_sub_lt h_split

/-- 🏆 THEOREM: The Fibonacci anyon twist is an exact root of the 6-potent hull polynomial:
    p₆(θ_τ) = (θ_τ)⁶ - θ_τ = 0. -/
theorem fibonacci_spin_mem_six_potent_hull :
    hullPoly 6 fibonacciTopologicalTwist = 0 := by
  have hz_ne : fibonacciTopologicalTwist ≠ 0 := Complex.exp_ne_zero _
  have h6 : (6 : ℕ) - 1 = 5 := rfl
  have h_root := (n_potent_root_iff 6 (by norm_num) fibonacciTopologicalTwist hz_ne).mpr
  rw [h6] at h_root
  exact h_root fibonacci_twist_pow_five

/-- 🏆 THEOREM: 6-potency equality (θ_τ)⁶ = θ_τ on the scalar twist level. -/
theorem fibonacci_twist_six_potent :
    fibonacciTopologicalTwist ^ 6 = fibonacciTopologicalTwist :=
  fibonacci_twist_minimal_nPotency.1

/-- Eigenspace sector of an operator T for the Fibonacci twist eigenvalue θ_τ. -/
def fibonacciEigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) : Submodule ℂ V :=
  LinearMap.ker (T - (fibonacciTopologicalTwist • (1 : Module.End ℂ V)))

/-- Any vector in the Fibonacci eigenspace is scaled by θ_τ. -/
theorem mem_fibonacciEigenspace_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (v : V) :
    v ∈ fibonacciEigenspace T ↔ T v = fibonacciTopologicalTwist • v := by
  dsimp [fibonacciEigenspace]
  rw [LinearMap.mem_ker]
  simp [sub_eq_zero]

/-- Endomorphisms commuting with `T` preserve its Fibonacci eigenspace.

This is the algebraic restriction prerequisite for transporting braid or
modular operators to the cyclotomic Fibonacci sector; no boundary or fusion
identification is assumed here.
-/
theorem commuting_endomorphism_preserves_fibonacciEigenspace
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T A : Module.End ℂ V) (hcomm : A * T = T * A) (v : V)
    (hv : v ∈ fibonacciEigenspace T) :
    A v ∈ fibonacciEigenspace T := by
  rw [mem_fibonacciEigenspace_iff] at hv ⊢
  have hcomm_v := congrArg (fun F : Module.End ℂ V => F v) hcomm
  have hcomm_apply : A (T v) = T (A v) := by
    simpa only [Module.End.mul_apply] using hcomm_v
  rw [← hcomm_apply, hv, map_smul]

private theorem pow_apply_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (n : ℕ) {z : ℂ} {v : V}
    (heig : T v = z • v) : (T ^ n) v = z ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, heig, map_smul, ih, smul_smul]
      ring_nf

/-- A nonzero eigenvector of an `n`-potent endomorphism has an `n`-potent
eigenvalue.  This is the operator-level direction from the polynomial hull to
the cyclotomic spectrum; no converse or diagonalizability claim is made. -/
theorem eigenvector_n_potent_root {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (n : ℕ) (hT : T ^ n = T)
    {z : ℂ} {v : V} (hv : v ≠ 0) (heig : T v = z • v) :
    hullPoly n z = 0 := by
  have hpow : (T ^ n) v = z ^ n • v := pow_apply_eigenvector T n heig
  have hTv : (T ^ n) v = T v := by rw [hT]
  have hscalar : z ^ n • v = z • v := by
    calc
      z ^ n • v = (T ^ n) v := hpow.symm
      _ = T v := hTv
      _ = z • v := heig
  have hz : z ^ n = z := (smul_left_injective ℂ hv) hscalar
  exact sub_eq_zero.mpr hz

theorem nonzero_eigenvector_cyclotomic_root {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (n : ℕ) (hn : 2 ≤ n) (hT : T ^ n = T)
    {z : ℂ} {v : V} (hv : v ≠ 0) (hz : z ≠ 0)
    (heig : T v = z • v) : z ^ (n - 1) = 1 := by
  exact (n_potent_root_iff n hn z hz).mp
    (eigenvector_n_potent_root T n hT hv heig)

/-! The finite-dimensional spectrum statement is downstream of the
eigenvector theorem: over `ℂ`, Mathlib identifies spectrum with eigenvalues
only after finite-dimensionality is supplied. -/

theorem operator_spectrum_subset_npotent_hull
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V]
    (T : Module.End ℂ V) (n : ℕ) (hn : 2 ≤ n) (hT : T ^ n = T) :
    spectrum ℂ T ⊆ {0} ∪ {z : ℂ | z ^ (n - 1) = 1} := by
  intro z hz
  have hEigen : T.HasEigenvalue z :=
    (Module.End.hasEigenvalue_iff_mem_spectrum).mpr hz
  obtain ⟨v, hv⟩ := hEigen.exists_hasEigenvector
  by_cases hz0 : z = 0
  · exact Set.mem_union_left _ hz0
  · exact Set.mem_union_right _
      (nonzero_eigenvector_cyclotomic_root T n hn hT
        (Module.End.hasEigenvector_iff.mp hv).2 hz0 hv.apply_eq_smul)

/-! A square-free hypothesis is the exact missing ingredient for the
semisimplicity conclusion.  Keeping it explicit prevents the scalar root
classification from being mistaken for a diagonalizability proof. -/

theorem operator_semisimple_of_squarefree_npotent_polynomial
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (n : ℕ) (hT : T ^ n = T)
    (hsq : Squarefree (Polynomial.X ^ n - Polynomial.X : Polynomial ℂ)) :
    T.IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq
  change (Polynomial.aeval T) (Polynomial.X ^ n - Polynomial.X) = 0
  simp [Polynomial.aeval_sub, Polynomial.aeval_X_pow, hT]

/-- The polynomial `X^n - X` is square-free over `ℂ` for `n ≥ 2`. -/
theorem n_potent_polynomial_squarefree (n : ℕ) (hn : 2 ≤ n) :
    Squarefree (Polynomial.X ^ n - Polynomial.X : Polynomial ℂ) := by
  let m := n - 1
  have hm : 1 ≤ m := by
    dsimp [m]
    omega
  have hsepX : (Polynomial.X : Polynomial ℂ).Separable := by
    simpa using (Polynomial.separable_X_sub_C (R := ℂ) (x := 0))
  have hsepM : (Polynomial.X ^ m - Polynomial.C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (by norm_num [Nat.ne_of_gt hm]) (by norm_num)
  have hcopBase : IsCoprime (1 : Polynomial ℂ) Polynomial.X := isCoprime_one_left
  have hcop' :
      IsCoprime (1 + Polynomial.X * (-Polynomial.X ^ (m - 1))) Polynomial.X :=
    hcopBase.add_mul_left_left (-Polynomial.X ^ (m - 1))
  have hcop : IsCoprime (Polynomial.X ^ m - Polynomial.C (1 : ℂ)) Polynomial.X := by
    have hm_eq : m = (m - 1) + 1 := by omega
    have hidx : m - 1 + 1 - 1 = m - 1 := by omega
    have hpow : (Polynomial.X : Polynomial ℂ) ^ m =
        Polynomial.X * Polynomial.X ^ (m - 1) := by
      rw [hm_eq, pow_succ, mul_comm, hidx]
    have hneg := hcop'.neg_left
    rw [hpow]
    convert hneg using 1 <;> simp <;> ring
  have hprod :
      (Polynomial.X * (Polynomial.X ^ m - Polynomial.C (1 : ℂ))).Separable :=
    hsepX.mul hsepM hcop.symm
  have hfactor : Polynomial.X ^ n - Polynomial.X =
      Polynomial.X * (Polynomial.X ^ m - Polynomial.C (1 : ℂ)) := by
    have hn_m : n = m + 1 := by
      dsimp [m]
      omega
    rw [hn_m, pow_succ]
    simp
    ring
  rw [hfactor]
  exact hprod.squarefree

/-- An `n`-potent complex finite-dimensional endomorphism is semisimple. -/
theorem operator_n_potent_is_semisimple
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (n : ℕ) (hn : 2 ≤ n) (hT : T ^ n = T) :
    T.IsSemisimple :=
  operator_semisimple_of_squarefree_npotent_polynomial T n hT
    (n_potent_polynomial_squarefree n hn)

/-! ### A concrete operator witness

The following one-dimensional model is deliberately explicit.  It proves
that the scalar twist is realised by an actual endomorphism and a nonzero
eigenvector; it does not claim to be the conformal-block or boundary braid
carrier.
-/

/-- Scalar Fibonacci operator on the one-dimensional complex carrier. -/
def fibonacciScalarOperator : Module.End ℂ ℂ :=
  fibonacciTopologicalTwist • (1 : Module.End ℂ ℂ)

theorem fibonacciScalarOperator_apply (z : ℂ) :
    fibonacciScalarOperator z = fibonacciTopologicalTwist * z := by
  simp [fibonacciScalarOperator]

/-- The vector `1` is a nonzero Fibonacci eigenvector. -/
theorem fibonacciScalarOperator_has_eigenvalue :
    fibonacciScalarOperator 1 = fibonacciTopologicalTwist • (1 : ℂ) := by
  simp [fibonacciScalarOperator]

theorem fibonacciScalarOperator_has_nonzero_fibonacci_eigenvector :
    (1 : ℂ) ∈ fibonacciEigenspace fibonacciScalarOperator ∧
      (1 : ℂ) ≠ 0 := by
  refine ⟨(mem_fibonacciEigenspace_iff fibonacciScalarOperator 1).2 ?_, one_ne_zero⟩
  exact fibonacciScalarOperator_has_eigenvalue

/-- The explicit scalar model has a genuinely nontrivial Fibonacci eigenspace.

This is a witness theorem for the chosen one-dimensional carrier only.  It does
not promote an arbitrary operator satisfying the six-potent equation to having
the Fibonacci eigenvalue.
-/
theorem fibonacciScalarOperator_fibonacciEigenspace_nontrivial :
    fibonacciEigenspace fibonacciScalarOperator ≠ ⊥ := by
  intro hbot
  have hmem : (1 : ℂ) ∈ (⊥ : Submodule ℂ ℂ) := by
    rw [← hbot]
    exact fibonacciScalarOperator_has_nonzero_fibonacci_eigenvector.1
  have hzero : (1 : ℂ) = 0 := by
    simpa only [Submodule.mem_bot] using hmem
  exact one_ne_zero hzero

/-- The concrete scalar operator satisfies the 6-potent operator equation. -/
theorem fibonacciScalarOperator_six_potent :
    fibonacciScalarOperator ^ 6 = fibonacciScalarOperator := by
  dsimp [fibonacciScalarOperator]
  have hpow (n : ℕ) :
      (fibonacciTopologicalTwist • (1 : Module.End ℂ ℂ)) ^ n =
        fibonacciTopologicalTwist ^ n • (1 : Module.End ℂ ℂ) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, pow_succ]
        rw [smul_mul_assoc, mul_smul_comm]
        rw [smul_smul, one_mul]
  rw [hpow, fibonacci_twist_six_potent]

end InfoGeometry.Physics.Algebra.NPotentCyclotomicSpinHullBridge
