import InfoGeometry.Canonical.BayesianMarkovChain
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.DiscreteHodgeStabilizer

/-!
# Bayesian Markov / Discrete Hodge Bridge

Finite theorem-safe bridge from a stationary Bayesian state on a tensor
inductive limit to a degree-one discrete Hodge stabilizer current.

This file stays inside the existing owner surfaces:

* `BayesianMarkovChain` owns the tensor-limit KMS/state readouts;
* `DiscreteHodgeStabilizer` owns the finite Hodge decomposition and
  orthogonality to exact/coexact local errors.

The bridge is deliberately explicit: a supplied stationary state is read out as
an edge current, and that current is then certified as harmonic/protected in
the finite Hodge layer.
-/

open Matrix

namespace InfoGeometry.Canonical.BayesianMarkovHodgeBridge

open BayesianMarkovChain
open BayesianMarkovChain.TensorLimitStateSpace
open TensorColimitExpectation
open InfoGeometry.Topology.EckmannDiscreteHodge
open InfoGeometry.Topology.DiscreteHodgeStabilizer

universe u v

variable {R : Type u} [CommSemiring R]
variable {A : ℕ → Type v}
variable [∀ n, Semiring (A n)] [∀ n, Algebra R (A n)]

/--
A stationary Bayesian state on the tensor limit is read out as a finite
degree-one Hodge current.
-/
structure BayesianMarkovHodgePacket
    (bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1))
    (L : TensorInductiveLimit bond) where
  kms : KMSStationarityPacket L
  n0 : ℕ
  n1 : ℕ
  n2 : ℕ
  d0 : Matrix (Fin n1) (Fin n0) ℝ
  d1 : Matrix (Fin n2) (Fin n1) ℝ
  stateToCurrent : LimitState L → Fin n1 → ℝ
  current : Fin n1 → ℝ
  stateToCurrent_eq : stateToCurrent kms.kmsState = current
  harmonic_current : IsHarmonicCodeState d0 d1 current

namespace BayesianMarkovHodgePacket

variable {bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)}
variable {L : TensorInductiveLimit bond}
variable (B : BayesianMarkovHodgePacket (A := A) bond L)

/-- The stationary KMS state is read out as the supplied current. -/
theorem stationary_current_readout :
    B.stateToCurrent B.kms.kmsState = B.current :=
  B.stateToCurrent_eq

/-- The stationary current is harmonic in the finite Hodge layer. -/
theorem stationary_current_is_harmonic :
    IsHarmonicCodeState B.d0 B.d1 (B.stateToCurrent B.kms.kmsState) := by
  simpa [B.stateToCurrent_eq] using B.harmonic_current

/-- The stationary current is annihilated by the degree-one stabilizers. -/
theorem stationary_current_annihilated_by_stabilizers :
    B.d1.mulVec (B.stateToCurrent B.kms.kmsState) = 0 ∧
      B.d0.transpose.mulVec (B.stateToCurrent B.kms.kmsState) = 0 := by
  exact harmonicCodeState_annihilated_by_stabilizers B.d0 B.d1
    (B.stationary_current_is_harmonic)

/-- The stationary current is orthogonal to exact local errors. -/
theorem stationary_current_orthogonal_exact
    {e : Fin B.n1 → ℝ}
    (he : IsExactOneForm B.d0 e) :
    eckmannDot (B.stateToCurrent B.kms.kmsState) e = 0 :=
  harmonic_orthogonal_exact B.d0 B.d1 (B.stationary_current_is_harmonic) he

/-- The stationary current is orthogonal to coexact local errors. -/
theorem stationary_current_orthogonal_coexact
    {c : Fin B.n1 → ℝ}
    (hc : IsCoexactOneForm B.d1 c) :
    eckmannDot (B.stateToCurrent B.kms.kmsState) c = 0 :=
  harmonic_orthogonal_coexact B.d0 B.d1 (B.stationary_current_is_harmonic) hc

/-- The stationary current is protected against both exact and coexact errors. -/
theorem stationary_current_hodge_protection
    {e c : Fin B.n1 → ℝ}
    (he : IsExactOneForm B.d0 e)
    (hc : IsCoexactOneForm B.d1 c) :
    eckmannDot (B.stateToCurrent B.kms.kmsState) e = 0 ∧
      eckmannDot (B.stateToCurrent B.kms.kmsState) c = 0 :=
  hodge_orthogonal_protection B.d0 B.d1
    (B.stationary_current_is_harmonic) he hc

end BayesianMarkovHodgePacket

end InfoGeometry.Canonical.BayesianMarkovHodgeBridge
