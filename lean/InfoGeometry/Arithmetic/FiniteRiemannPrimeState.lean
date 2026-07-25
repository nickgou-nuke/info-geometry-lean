import Mathlib.Tactic

/-!
# InfoGeometry.Arithmetic.FiniteRiemannPrimeState

Finite Riemann/prime-state owner surface.

This module keeps the Latorre--Sierra style quantum-register state separate
from the bosonic/fermionic primon Fock gas:

* a finite state is a normalized weighted superposition over a finite support;
* the finite probability weights sum to `1`;

No infinite Hilbert-space state, analytic continuation theorem, BRST anomaly
cancellation theorem, Riemann Hypothesis statement, or CFT/bosonization theorem
is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.FiniteRiemannPrimeState

/-! ## 1. Finite Riemann-state normalization -/

/--
Finite squared norm of a weighted register state.

For a truncated Riemann state one later reads `w n` as a finite stand-in for
`|n^{-s}|`.
-/
def finiteRiemannNormSq
    {α : Type*}
    (A : Finset α)
    (w : α → ℝ) : ℝ :=
  ∑ a ∈ A, w a ^ 2

/--
Finite normalized probability attached to a weighted register state.

This is a probability readout, not a signed/Krein supertrace.
-/
def finiteRiemannProbability
    {α : Type*}
    (A : Finset α)
    (w : α → ℝ)
    (a : α) : ℝ :=
  w a ^ 2 / finiteRiemannNormSq A w

/--
The finite normalized probabilities sum to `1` when the finite norm is nonzero.
-/
theorem finiteRiemannProbability_sum_eq_one
    {α : Type*}
    (A : Finset α)
    (w : α → ℝ)
    (h : finiteRiemannNormSq A w ≠ 0) :
    ∑ a ∈ A, finiteRiemannProbability A w a = 1 := by
  unfold finiteRiemannProbability finiteRiemannNormSq
  rw [← Finset.sum_div]
  exact div_self h

/--
Finite prime-state packet.

The support can be all integers in a cutoff, or only primes in a cutoff.
Primality of the support is a predicate field, not built into the normalization
theorem.
-/
structure FiniteRiemannStatePacket where
  support : Finset ℕ
  weight : ℕ → ℝ
  normSq_nonzero : finiteRiemannNormSq support weight ≠ 0
  support_is_prime_lane : Prop

namespace FiniteRiemannStatePacket

variable (P : FiniteRiemannStatePacket)

/-- Finite squared norm of the packet. -/
def normSq : ℝ :=
  finiteRiemannNormSq P.support P.weight

/-- Finite probability weight of one register basis element. -/
def probability (n : ℕ) : ℝ :=
  finiteRiemannProbability P.support P.weight n

/-- The finite packet probabilities sum to `1`. -/
theorem probability_sum_eq_one :
    ∑ n ∈ P.support, P.probability n = 1 := by
  exact finiteRiemannProbability_sum_eq_one P.support P.weight P.normSq_nonzero

end FiniteRiemannStatePacket

end InfoGeometry.Arithmetic.FiniteRiemannPrimeState
