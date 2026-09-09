import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeMajoranaCAR

/-!
# InfoGeometry.Arithmetic.CantorDiracOperator

Native finite Cantor/Dirac layer over the prime-indexed Boolean hypercube.

This module keeps the finite operator boundary explicit:

* the Dirac operator is the finite weighted sum
  `∑_{p ∈ P.primes} √(log p) • γ p`;
* the local Clifford surface is recorded by the Majorana CAR relations;
* self-adjointness follows from self-adjoint Majorana generators;
* the finite Lichnerowicz square law is proved directly from the local
  Clifford anticommutator.

No infinite tensor products, analytic continuation, or RH claim is asserted
here.
-/

noncomputable section

open scoped BigOperators
open scoped Real

namespace InfoGeometry.Arithmetic.CantorDiracOperator

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeMajoranaCAR

/-! ## 1. The Cantor Dirac operator -/

/--
The master Cantor Dirac operator on the finite prime register.

The coefficient attached to each prime mode is `√(log p)`.
-/
@[rep_depth thermo]
def cantorDiracOperator
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (P : PrimeRegister)
    (γ : ℕ → Op) : Op :=
  Finset.sum P.primes (fun p => (Real.sqrt (Real.log p) : ℝ) • γ p)

/--
The finite operator-valued Hamiltonian readout attached to the prime register.

This is the finite `log p` boundary operator that the Lichnerowicz square law
is supposed to recover.
-/
@[rep_depth thermo]
def cantorDiracHamiltonian
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (P : PrimeRegister) : Op :=
  Finset.sum P.primes (fun p => (Real.log p : ℝ) • (1 : Op))

/-! ## 2. Local Clifford surface -/

/--
The local Majorana Clifford relations on the prime register.

`{γ_p, γ_q} = 2 δ_{pq}`.
-/
@[rep_depth thermo]
def IsMajoranaCliffordRepresentation
    {Op : Type*} [Ring Op]
    (P : PrimeRegister)
    (γ : ℕ → Op) : Prop :=
  ∀ p q, p ∈ P.primes → q ∈ P.primes →
    γ p * γ q + γ q * γ p = if p = q then 2 else 0

/-! ## 3. Finite Lichnerowicz square law -/

/--
From the Clifford anticommutator relation, each generator squares to `1`.

This is the diagonal part of `{γ_p, γ_p} = 2`.
-/
@[rep_depth thermo]
theorem majorana_sq_one_of_clifford
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    {P : PrimeRegister} {γ : ℕ → Op}
    (hγ : IsMajoranaCliffordRepresentation P γ)
    {p : ℕ} (hp : p ∈ P.primes) :
    γ p * γ p = 1 := by
  have hdiag :
      γ p * γ p + γ p * γ p = (2 : Op) := by
    simpa using hγ p p hp hp

  have hhalf :=
    congrArg (fun x : Op => (1 / 2 : ℝ) • x) hdiag

  have hleft :
      (1 / 2 : ℝ) • (γ p * γ p + γ p * γ p) =
        γ p * γ p := by
    calc
      (1 / 2 : ℝ) • (γ p * γ p + γ p * γ p)
          = (1 / 2 : ℝ) • (γ p * γ p) + (1 / 2 : ℝ) • (γ p * γ p) := by
              rw [smul_add]
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • (γ p * γ p) := by
              rw [← add_smul]
      _ = γ p * γ p := by
              norm_num

  have hright :
      (1 / 2 : ℝ) • (2 : Op) = (1 : Op) := by
    have htwo : (2 : Op) = (2 : ℝ) • (1 : Op) := by
      calc
        (2 : Op) = algebraMap ℝ Op (2 : ℝ) := by
          simpa using (map_natCast (algebraMap ℝ Op) 2).symm
        _ = (2 : ℝ) • (1 : Op) := by
            simpa [Algebra.smul_def]
    rw [htwo, smul_smul]
    norm_num

  change (1 / 2 : ℝ) • (γ p * γ p + γ p * γ p) = (1 / 2 : ℝ) • (2 : Op) at hhalf
  rw [hleft, hright] at hhalf
  exact hhalf

/--
From the Clifford anticommutator relation, distinct generators anticommute.
-/
@[rep_depth thermo]
theorem majorana_anticomm_zero_of_ne
    {Op : Type*} [Ring Op]
    {P : PrimeRegister} {γ : ℕ → Op}
    (hγ : IsMajoranaCliffordRepresentation P γ)
    {p q : ℕ}
    (hp : p ∈ P.primes) (hq : q ∈ P.primes)
    (hpq : p ≠ q) :
    γ p * γ q + γ q * γ p = 0 := by
  simpa [hpq] using hγ p q hp hq

/-- Operator anticommutator. -/
private def anticomm {Op : Type*} [Ring Op] (x y : Op) : Op := x * y + y * x

/--
Finite left-linearity of anticommutator over a `Finset` sum.
-/
private theorem anticomm_sum_left
    {Op : Type*} [Ring Op]
    (S : Finset ℕ) (f : ℕ → Op) (y : Op) :
    anticomm (S.sum f) y = S.sum (fun i => anticomm (f i) y) := by
  classical
  refine Finset.induction_on S ?base ?step
  · simp [anticomm]
  · intro a s ha ih
    have ih' :
        (Finset.sum s f) * y + y * (Finset.sum s f) =
          Finset.sum s (fun x => anticomm (f x) y) := by
      simpa [anticomm] using ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, anticomm, add_mul, mul_add]
    calc
      f a * y + (Finset.sum s f) * y + (y * f a + y * (Finset.sum s f))
          = anticomm (f a) y + ((Finset.sum s f) * y + y * (Finset.sum s f)) := by
              simp [anticomm, add_assoc, add_left_comm, add_comm]
      _ = anticomm (f a) y + Finset.sum s (fun x => anticomm (f x) y) := by
              rw [ih']

/--
Finite right-linearity of anticommutator over a `Finset` sum.
-/
private theorem anticomm_sum_right
    {Op : Type*} [Ring Op]
    (x : Op) (S : Finset ℕ) (f : ℕ → Op) :
    anticomm x (S.sum f) = S.sum (fun i => anticomm x (f i)) := by
  classical
  refine Finset.induction_on S ?base ?step
  · simp [anticomm]
  · intro a s ha ih
    have ih' :
        x * (Finset.sum s f) + (Finset.sum s f) * x =
          Finset.sum s (fun i => anticomm x (f i)) := by
      simpa [anticomm] using ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, anticomm, mul_add, add_mul]
    calc
      x * f a + x * (Finset.sum s f) + (f a * x + (Finset.sum s f) * x)
          = anticomm x (f a) + (x * (Finset.sum s f) + (Finset.sum s f) * x) := by
              simp [anticomm, add_assoc, add_left_comm, add_comm]
      _ = anticomm x (f a) + Finset.sum s (fun i => anticomm x (f i)) := by
              rw [ih']

/--
Scalar bilinearity of the anticommutator over `ℝ`.
-/
private theorem anticomm_smul_smul
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (a b : ℝ) (x y : Op) :
    anticomm (a • x) (b • y) = (a * b) • anticomm x y := by
  simp [anticomm, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, mul_comm, mul_left_comm, mul_assoc]

/--
A weighted square-sum lemma for finite Majorana systems.

If `γ_p γ_q + γ_q γ_p = 2δ_pq` on a finite set `S`, then

`(Σ p∈S, a_p γ_p)^2 = Σ p∈S, a_p^2`.

This is the algebraic core of the finite Lichnerowicz law.
-/
@[rep_depth thermo]
theorem weighted_majorana_sum_sq
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    {P : PrimeRegister} {γ : ℕ → Op}
    (hγ : IsMajoranaCliffordRepresentation P γ)
    (a : ℕ → ℝ)
    (S : Finset ℕ)
    (hS : S ⊆ P.primes) :
    (Finset.sum S (fun p => a p • γ p)) ^ 2 =
      Finset.sum S (fun p => (a p * a p) • (1 : Op)) := by
  classical
  revert hS
  refine Finset.induction_on S ?empty ?insert
  · intro _hS
    simp
  · intro p S hpS ih hsub
    have hpP : p ∈ P.primes := hsub (by simp)
    have hSsub : S ⊆ P.primes := by
      intro q hq
      exact hsub (by simp [hq])
    have ihS :
        (Finset.sum S (fun q => a q • γ q)) ^ 2 =
          Finset.sum S (fun q => (a q * a q) • (1 : Op)) :=
      ih hSsub
    have hdiag :
        (a p • γ p) * (a p • γ p) =
          (a p * a p) • (1 : Op) := by
      calc
        (a p • γ p) * (a p • γ p)
            = a p • (γ p * (a p • γ p)) := by
                rw [smul_mul_assoc]
        _ = a p • (a p • (γ p * γ p)) := by
                rw [mul_smul_comm]
        _ = (a p * a p) • (γ p * γ p) := by
                rw [smul_smul]
        _ = (a p * a p) • (1 : Op) := by
                rw [majorana_sq_one_of_clifford hγ hpP]
    have hcross :
        (a p • γ p) * (Finset.sum S (fun q => a q • γ q)) +
          (Finset.sum S (fun q => a q • γ q)) * (a p • γ p) = 0 := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero ?_
      intro q hq
      have hqP : q ∈ P.primes := hSsub hq
      have hpq : p ≠ q := by
        intro hpq
        subst q
        exact hpS hq
      have hanti :
          γ p * γ q + γ q * γ p = 0 :=
        majorana_anticomm_zero_of_ne hγ hpP hqP hpq
      have hmul₁ :
          (a p • γ p) * (a q • γ q) =
            (a p * a q) • (γ p * γ q) := by
        calc
          (a p • γ p) * (a q • γ q)
              = a p • (γ p * (a q • γ q)) := by
                  rw [smul_mul_assoc]
          _ = a p • (a q • (γ p * γ q)) := by
                  rw [mul_smul_comm]
          _ = (a p * a q) • (γ p * γ q) := by
                  rw [smul_smul]
      have hmul₂ :
          (a q • γ q) * (a p • γ p) =
            (a q * a p) • (γ q * γ p) := by
        calc
          (a q • γ q) * (a p • γ p)
              = a q • (γ q * (a p • γ p)) := by
                  rw [smul_mul_assoc]
          _ = a q • (a p • (γ q * γ p)) := by
                  rw [mul_smul_comm]
          _ = (a q * a p) • (γ q * γ p) := by
                  rw [smul_smul]
      calc
        (a p • γ p) * (a q • γ q) +
            (a q • γ q) * (a p • γ p)
            =
            (a p * a q) • (γ p * γ q) +
              (a q * a p) • (γ q * γ p) := by
                rw [hmul₁, hmul₂]
        _ =
            (a p * a q) • (γ p * γ q) +
              (a p * a q) • (γ q * γ p) := by
                rw [mul_comm (a q) (a p)]
        _ =
            (a p * a q) • (γ p * γ q + γ q * γ p) := by
                rw [← smul_add]
        _ = 0 := by
                rw [hanti, smul_zero]
    calc
      (Finset.sum (insert p S) (fun q => a q • γ q)) ^ 2
          =
          ((a p • γ p) + Finset.sum S (fun q => a q • γ q)) ^ 2 := by
            rw [Finset.sum_insert hpS]
      _ =
          (a p • γ p) * (a p • γ p) +
            (Finset.sum S (fun q => a q • γ q)) ^ 2 +
            ((a p • γ p) * (Finset.sum S (fun q => a q • γ q)) +
              (Finset.sum S (fun q => a q • γ q)) * (a p • γ p)) := by
            simp [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
      _ =
          (a p * a p) • (1 : Op) +
            Finset.sum S (fun q => (a q * a q) • (1 : Op)) + 0 := by
            rw [hdiag, ihS, hcross]
      _ =
          Finset.sum (insert p S) (fun q => (a q * a q) • (1 : Op)) := by
            rw [Finset.sum_insert hpS]
            abel

/--
Finite Cantor-Dirac Lichnerowicz square law.

If the finite prime-register generators satisfy the Majorana Clifford
relations

`γ_p γ_q + γ_q γ_p = 2 δ_pq`,

then the prime-weighted Cantor Dirac operator

`D = Σ_{p∈P} sqrt(log p) • γ_p`

satisfies

`D² = Σ_{p∈P} log p • 1`.
-/
@[rep_depth thermo]
theorem cantorDirac_sq_eq_hamiltonian_of_clifford
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (P : PrimeRegister)
    (γ : ℕ → Op)
    (hγ : IsMajoranaCliffordRepresentation P γ) :
    cantorDiracOperator P γ ^ 2 =
      cantorDiracHamiltonian (Op := Op) P := by
  classical

  let a : ℕ → ℝ := fun p => Real.sqrt (Real.log (p : ℝ))

  have hmain :
      cantorDiracOperator P γ ^ 2 =
        Finset.sum P.primes (fun p => (a p * a p) • (1 : Op)) := by
    simpa [cantorDiracOperator, a] using
      weighted_majorana_sum_sq
        (P := P) (γ := γ) hγ a P.primes
        (by intro p hp; exact hp)

  calc
    cantorDiracOperator P γ ^ 2
        = Finset.sum P.primes (fun p => (a p * a p) • (1 : Op)) := hmain
    _ = cantorDiracHamiltonian (Op := Op) P := by
        unfold cantorDiracHamiltonian
        refine Finset.sum_congr rfl ?_
        intro p hp

        have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.Prime.one_lt (P.prime_mem p hp)).le

        have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
          Real.log_nonneg hp_one

        have hsqrt :
            a p * a p = Real.log (p : ℝ) := by
          simpa [a, pow_two] using Real.sq_sqrt hlog_nonneg

        rw [hsqrt]

/--
The finite Cantor Dirac operator is self-adjoint when the Majorana generators
are self-adjoint.
-/
@[rep_depth thermo]
theorem cantorDirac_is_selfAdjoint
    {Op : Type*} [Ring Op] [Algebra ℝ Op] [StarRing Op] [StarModule ℝ Op]
    (P : PrimeRegister)
    (γ : ℕ → Op)
    (h_self : ∀ p ∈ P.primes, star (γ p) = γ p) :
    star (cantorDiracOperator P γ) = cantorDiracOperator P γ := by
  unfold cantorDiracOperator
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [StarModule.star_smul]
  simpa [h_self p hp]

/--
Predicate form of finite self-adjointness for the implemented Cantor Dirac
operator.
-/
@[rep_depth thermo]
theorem cantorDirac_isSelfAdjoint
    {Op : Type*} [Ring Op] [Algebra ℝ Op] [StarRing Op] [StarModule ℝ Op]
    (P : PrimeRegister)
    (γ : ℕ → Op)
    (h_self : ∀ p ∈ P.primes, star (γ p) = γ p) :
    IsSelfAdjoint (cantorDiracOperator P γ) := by
  exact cantorDirac_is_selfAdjoint P γ h_self

/--
Alias with explicit hypothesis naming:
self-adjoint Majorana generators imply self-adjoint finite Cantor Dirac.
-/
@[rep_depth thermo]
theorem cantorDirac_selfAdjoint_of_generator_selfAdjoint
    {Op : Type*} [Ring Op] [Algebra ℝ Op] [StarRing Op] [StarModule ℝ Op]
    (P : PrimeRegister)
    (γ : ℕ → Op)
    (h_self : ∀ p ∈ P.primes, star (γ p) = γ p) :
    IsSelfAdjoint (cantorDiracOperator P γ) :=
  cantorDirac_isSelfAdjoint P γ h_self

/--
Equation-form alias:
`star D = D` for the finite Cantor Dirac operator under generator
self-adjointness.
-/
@[rep_depth thermo]
theorem star_cantorDirac_eq_cantorDirac_of_generator_selfAdjoint
    {Op : Type*} [Ring Op] [Algebra ℝ Op] [StarRing Op] [StarModule ℝ Op]
    (P : PrimeRegister)
    (γ : ℕ → Op)
    (h_self : ∀ p ∈ P.primes, star (γ p) = γ p) :
    star (cantorDiracOperator P γ) = cantorDiracOperator P γ :=
  cantorDirac_is_selfAdjoint P γ h_self

end InfoGeometry.Arithmetic.CantorDiracOperator
