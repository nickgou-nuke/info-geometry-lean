import Mathlib
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
* the Lichnerowicz square law is kept as an explicit socket, not as a fake
  theorem.

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
