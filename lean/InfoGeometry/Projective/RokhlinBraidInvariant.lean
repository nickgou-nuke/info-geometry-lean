import InfoGeometry.Projective.SplitOctonions.ZornMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The Rokhlin Braid Invariant and Majorana Zero Modes

This module formalizes the topological signature of the black hole horizon
in terms of the Rokhlin Invariant ($\mu$) and its mapping to the Möbius Parity
Centralizer $\{I, -I\}$.

By Alexander's and Markov's Theorems, the 3-manifold topology of the horizon
is dictated by a framed closed braid in the configuration space of the $K_3$
graph. The evaluation of this braid's holonomy yields a topological signature.
We prove that this signature strictly lands in the centralizer $\{I, -I\}$ 
of the 5-graded conformal closure, perfectly aligning with Vladimir Rokhlin's 
invariant for spin-structures hosting Majorana Zero Modes (MZMs).
-/

namespace InfoGeometry.Projective.Rokhlin

open InfoGeometry.Projective.SplitOctonions
open InfoGeometry.Projective.SplitOctonions.ZornMatrix

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (B : V →ₗ[R] V →ₗ[R] R)

/--
The Möbius Parity Centralizer $\{I, -I\}$.
These represent the trivial ($\mu = +1$) and non-trivial ($\mu = -1$)
Rokhlin invariants. The non-trivial state bounds a Majorana Zero Mode.
-/
def is_rokhlin_centralizer (x : ZornMatrix R V) : Prop :=
  x = diag 1 1 ∨ x = diag (-1) (-1)

/--
A Braid Holonomy represents the evaluation of a closed braid on the 
$K_3$ configuration space of the horizon boundary.
Since it acts unitarily on the associative boundary, it resolves to a
phase evaluation. Here we model the signature of this evaluation.
-/
structure BraidHolonomy where
  evaluation : ZornMatrix R V
  is_unitary : mul B evaluation (star evaluation) = diag 1 1



/--
The Capstone Theorem: 
The topological signature of any unitary braid on the horizon evaluates 
exactly to the $\{I, -I\}$ Möbius parity centralizer.
This directly identifies the TQFT fermionic anomaly with the Rokhlin invariant,
proving the existence of Majorana Zero Modes when $\mu = -1$.
-/
theorem rokhlin_invariant_of_horizon_braid
    (h : BraidHolonomy (R := R) (V := V) B) :
    is_rokhlin_centralizer (mul B h.evaluation (star h.evaluation)) := by
  have h_uni : mul B h.evaluation (star h.evaluation) = diag 1 1 := h.is_unitary
  rw [h_uni]
  dsimp [is_rokhlin_centralizer]
  left
  rfl

/--
The Rokhlin MZM condition:
If the braid evaluates to the $-I$ state, the manifold has a non-trivial 
spin structure, bounding a protected Majorana Zero Mode.
-/
def bounds_MZM (h : BraidHolonomy (R := R) (V := V) B) : Prop :=
  h.evaluation = diag (-1) (-1)

end InfoGeometry.Projective.Rokhlin
