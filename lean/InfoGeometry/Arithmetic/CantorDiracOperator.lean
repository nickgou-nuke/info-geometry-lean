import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget
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
@[rep_depth thermo, owner_target_tag]
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

/-- Owner target for the finite Cantor Dirac layer. -/
@[owner_target_tag]
def CantorDiracOperatorOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℝ Op] [StarRing Op] [StarModule ℝ Op] :
    Prop :=
  ∀ (P : PrimeRegister) (γ : ℕ → Op),
    (∀ p ∈ P.primes, star (γ p) = γ p) →
      star (cantorDiracOperator P γ) = cantorDiracOperator P γ

/-- The owner target is closed by the direct self-adjointness theorem. -/
theorem cantorDiracOperatorOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℝ Op] [StarRing Op] [StarModule ℝ Op] :
    CantorDiracOperatorOwnerTarget Op := by
  intro P γ h_self
  exact cantorDirac_is_selfAdjoint (P := P) (γ := γ) h_self

/-! ## 3. Lichnerowicz square law socket -/

/--
The finite Lichnerowicz-type square law is kept as explicit socket debt.

The operator square should recover the Hamiltonian readout, but that identity
is not proven here.
-/
@[socket_debt_tag, rep_depth thermo]
structure CantorDiracLichnerowiczSocket
    (Op : Type*) [Ring Op] [Algebra ℝ Op] where
  P : PrimeRegister
  γ : ℕ → Op
  clifford : IsMajoranaCliffordRepresentation P γ
  squareLaw : Prop
  squareLaw_shape :
    squareLaw =
      (cantorDiracOperator P γ ^ 2 = cantorDiracHamiltonian (Op := Op) P)
  squareLaw_certificate : squareLaw

namespace CantorDiracLichnerowiczSocket

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

/-- Reexport of the supplied square-law bridge. -/
@[bridge_target_tag, rep_depth thermo]
theorem squareLaw_valid (S : CantorDiracLichnerowiczSocket Op) :
    S.squareLaw := S.squareLaw_certificate

/-- Reexport of the square-law as an equality statement. -/
@[bridge_target_tag, rep_depth thermo]
theorem cantorDirac_sq_eq_hamiltonian
    (S : CantorDiracLichnerowiczSocket Op) :
    cantorDiracOperator S.P S.γ ^ 2 =
      cantorDiracHamiltonian (Op := Op) S.P := by
  simpa [S.squareLaw_shape] using S.squareLaw_certificate

/--
If the Dirac operator annihilates a state, then the Hamiltonian readout does
too, assuming the square law.
-/
@[bridge_target_tag, rep_depth thermo]
theorem zeroMode_annihilates_hamiltonian
    (S : CantorDiracLichnerowiczSocket Op)
    (ψ : Op)
    (h_zero : cantorDiracOperator S.P S.γ * ψ = 0) :
    cantorDiracHamiltonian (Op := Op) S.P * ψ = 0 := by
  rw [← cantorDirac_sq_eq_hamiltonian S]
  rw [pow_two, mul_assoc, h_zero, mul_zero]

end CantorDiracLichnerowiczSocket

end InfoGeometry.Arithmetic.CantorDiracOperator
