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
Finite prime-state packet.  Membership in the prime lane is the concrete
Mathlib primality law on every supported natural number.
-/
def FiniteRiemannStatePacket : Type _ :=
  {p : Finset Nat.Primes × (Nat.Primes → ℝ) //
    finiteRiemannNormSq p.1 p.2 ≠ 0}

namespace FiniteRiemannStatePacket

/-- Native product projection for the finite prime support. -/
abbrev support (P : FiniteRiemannStatePacket) : Finset Nat.Primes :=
  P.1.1

/-- Native product projection for the register weight. -/
abbrev weight (P : FiniteRiemannStatePacket) : Nat.Primes → ℝ :=
  P.1.2

/-- Native subtype proof of nonzero finite norm. -/
theorem normSq_nonzero (P : FiniteRiemannStatePacket) :
    finiteRiemannNormSq P.support P.weight ≠ 0 :=
  P.2

end FiniteRiemannStatePacket

namespace FiniteRiemannStatePacket

variable (P : FiniteRiemannStatePacket)

/-- Natural-number projection of the intrinsically prime support. -/
def natSupport : Finset ℕ :=
  P.support.image (fun p : Nat.Primes => p.1)

/-- Finite squared norm of the packet. -/
def normSq : ℝ :=
  finiteRiemannNormSq P.support P.weight

/-- Finite probability weight of one register basis element. -/
def probability (p : Nat.Primes) : ℝ :=
  finiteRiemannProbability P.support P.weight p

/-- Primality is intrinsic to every supported mode. -/
theorem support_is_prime_lane
    (p : Nat.Primes) (_hp : p ∈ P.support) :
    Nat.Prime p.1 :=
  p.2

/-- The finite support lies in Mathlib's subtype of prime natural numbers. -/
theorem support_subset_primes :
    (P.natSupport : Set ℕ) ⊆ Set.range (fun p : Nat.Primes => p.1) := by
  intro p hp
  rcases Finset.mem_image.mp (by simpa [natSupport] using hp) with ⟨q, hq, hq'⟩
  exact ⟨q, hq'⟩

/-- The finite packet probabilities sum to `1`. -/
theorem probability_sum_eq_one :
    ∑ n ∈ P.support, P.probability n = 1 := by
  exact finiteRiemannProbability_sum_eq_one P.support P.weight P.normSq_nonzero

end FiniteRiemannStatePacket

end InfoGeometry.Arithmetic.FiniteRiemannPrimeState
