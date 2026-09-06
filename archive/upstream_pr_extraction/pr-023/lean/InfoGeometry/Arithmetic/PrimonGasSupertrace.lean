import Mathlib
import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
# InfoGeometry.Arithmetic.PrimonGasSupertrace

Finite primon gas and Möbius supertrace owner surface.

This module formalizes the conservative arithmetic layer of the primon gas:

* energy `E n = log n`;
* bosonic finite partition sums;
* square-free finite partition sums;
* Möbius signed finite supertrace;
* parity/projector distinction.

It does not assert Bost--Connes KMS phases, Type III factors, the Riemann
Hypothesis, or an analytic continuation theorem.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonGasSupertrace

open scoped BigOperators

/-- Primon gas energy level: `E(n) = log n`. -/
def primonEnergy (n : ℕ) : ℝ :=
  Real.log (n : ℝ)

/-- Boltzmann weight `e^{-β log n}` with zero convention at `n = 0`. -/
def primonBoltzmannWeight (β : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.exp (-β * primonEnergy n)

/-- Finite bosonic primon-gas partition sum over a finite support. -/
def finiteBosonicPartition
    (A : Finset ℕ)
    (β : ℝ) : ℝ :=
  ∑ n ∈ A, primonBoltzmannWeight β n

/--
Square-free support predicate.

This is the fermionic occupancy lane: each prime may occur at most once.
-/
def IsSquarefreeState (n : ℕ) : Prop :=
  Squarefree n

/-- Square-free state membership is used as a finite filter predicate. -/
noncomputable instance decidablePredIsSquarefreeState :
    DecidablePred IsSquarefreeState :=
  Classical.decPred IsSquarefreeState

/-- Finite square-free partition sum. -/
def finiteSquarefreePartition
    (A : Finset ℕ)
    (β : ℝ) : ℝ :=
  by
    classical
    exact ∑ n ∈ A.filter IsSquarefreeState, primonBoltzmannWeight β n

/--
A supplied Möbius coefficient.

This is kept as a parameter rather than hard-coding a Mathlib API choice.
The intended value is `μ(n)`.
-/
structure MobiusCoefficient where
  coeff : ℕ → ℝ

  /-- Non-square-free states are killed. -/
  coeff_eq_zero_of_not_squarefree :
    ∀ n : ℕ, ¬ IsSquarefreeState n → coeff n = 0

  /-- Square-free states have parity value `±1`. -/
  coeff_sq_eq_one_of_squarefree :
    ∀ n : ℕ, IsSquarefreeState n → coeff n ^ 2 = 1

namespace MobiusCoefficient

variable (μ : MobiusCoefficient)

/-- Finite Möbius/signed supertrace. -/
def finiteSupertrace
    (A : Finset ℕ)
    (β : ℝ) : ℝ :=
  ∑ n ∈ A, μ.coeff n * primonBoltzmannWeight β n

/--
The Möbius finite supertrace only sees square-free states.
-/
theorem finiteSupertrace_eq_squarefree_filter
    (A : Finset ℕ)
    (β : ℝ) :
    μ.finiteSupertrace A β =
      ∑ n ∈ A.filter IsSquarefreeState,
        μ.coeff n * primonBoltzmannWeight β n := by
  classical
  unfold finiteSupertrace
  have hkill :
      ∑ x ∈ A.filter (fun a => ¬ IsSquarefreeState a),
          μ.coeff x * primonBoltzmannWeight β x = 0 := by
    refine Finset.sum_eq_zero ?_
    intro n hn
    have hnot : ¬ IsSquarefreeState n :=
      (Finset.mem_filter.mp hn).2
    rw [μ.coeff_eq_zero_of_not_squarefree n hnot]
    simp
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := A)
      (p := IsSquarefreeState)
      (f := fun n => μ.coeff n * primonBoltzmannWeight β n)
  calc
    (∑ n ∈ A, μ.coeff n * primonBoltzmannWeight β n)
        =
      (∑ n ∈ A.filter IsSquarefreeState,
        μ.coeff n * primonBoltzmannWeight β n)
        +
      (∑ n ∈ A.filter (fun a => ¬ IsSquarefreeState a),
        μ.coeff n * primonBoltzmannWeight β n) := by
        simpa using hsplit.symm
    _ =
      (∑ n ∈ A.filter IsSquarefreeState,
        μ.coeff n * primonBoltzmannWeight β n) + 0 := by
        rw [hkill]
    _ =
      ∑ n ∈ A.filter IsSquarefreeState,
        μ.coeff n * primonBoltzmannWeight β n := by
        simp

end MobiusCoefficient

/--
Finite arithmetic thermal packet.

This packages the three finite readouts without claiming an infinite analytic
identity.
-/
structure FinitePrimonThermalPacket where
  support : Finset ℕ
  beta : ℝ
  mobius : MobiusCoefficient

namespace FinitePrimonThermalPacket

variable (P : FinitePrimonThermalPacket)

/-- Bosonic finite partition readout. -/
def bosonicPartition : ℝ :=
  finiteBosonicPartition P.support P.beta

/-- Square-free finite partition readout. -/
def squarefreePartition : ℝ :=
  finiteSquarefreePartition P.support P.beta

/-- Möbius signed finite supertrace readout. -/
def supertrace : ℝ :=
  P.mobius.finiteSupertrace P.support P.beta

/-- Supertrace is supported on the square-free lane. -/
theorem supertrace_eq_squarefree_filter :
    P.supertrace =
      ∑ n ∈ P.support.filter IsSquarefreeState,
        P.mobius.coeff n * primonBoltzmannWeight P.beta n := by
  classical
  exact P.mobius.finiteSupertrace_eq_squarefree_filter P.support P.beta

end FinitePrimonThermalPacket

end InfoGeometry.Arithmetic.PrimonGasSupertrace
