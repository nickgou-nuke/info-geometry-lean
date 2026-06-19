import Mathlib
import InfoGeometry.Canonical.TensorColimitExpectation

/-!
# Bayesian Markov Chain on a Tensor Colimit

This module packages the tensor-colimit expectation layer into a conservative
Bayesian state-dynamics bridge.

The checked content is intentionally theorem-safe:

* a compatible family of finite-stage functionals;
* a supplied global limit functional on the colimit carrier;
* supplied local conditional expectations as superoperators on the algebra;
* a supplied Markov superoperator on the colimit algebra with stationary
  readback for the global functional.

No uniqueness theorem, CP-map construction, KMS theorem, or analytic convergence
claim is asserted here.
-/

namespace InfoGeometry.Canonical.BayesianMarkovChain

open InfoGeometry.Canonical.TensorColimitExpectation

universe u v

variable {R : Type u} [CommSemiring R]
variable {A : ℕ → Type v}
variable [∀ n, Semiring (A n)] [∀ n, Algebra R (A n)]

/--
Bayesian state dynamics over a tensor inductive limit.

The structure collects the finite tower, the compatible functional family, the
global readout, the local conditional expectations, and the Bayesian
superoperator acting on the colimit algebra.
-/
structure BayesianTensorSystem
    (bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)) where
  limit : TensorInductiveLimit bond
  family : CompatibleFunctionalFamily bond
  global : limit.LimitFunctional
  extendsFamily : limit.ExtendsFamily family global
  expectations : ∀ n : ℕ, TensorInductiveLimit.ConditionalExpectation limit n
  markov : limit.AInf →ₗ[R] limit.AInf
  stationary : global.comp markov = global

namespace BayesianTensorSystem

variable {bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)}
variable (S : BayesianTensorSystem bond)

/-- The Bayesian update on the limit functional is the dual action of the Markov superoperator. -/
def bayesianUpdate : S.limit.LimitFunctional := S.global.comp S.markov

@[simp]
theorem bayesianUpdate_eq_global : S.bayesianUpdate = S.global :=
  S.stationary

/-- Read back the global functional on a finite embedded stage. -/
theorem stage_readback (n : ℕ) (x : A n) :
    S.global (S.limit.inj n x) = S.family.omega n x :=
  S.limit.limit_functional_recovers_stage S.family S.global S.extendsFamily n x

/-- Compatibility of the finite family is recovered from the global extension. -/
theorem compatibility (n : ℕ) (x : A n) :
    S.family.omega (n + 1) (bond n x) = S.family.omega n x :=
  S.limit.extending_limit_functional_implies_compatible S.family S.global S.extendsFamily n x

/-- State compatibility through the local conditional expectation. -/
theorem local_expectation_state_compatibility
    (n : ℕ)
    (x : S.limit.AInf) :
    S.global x = S.family.omega n ((S.expectations n).E x) :=
  TensorInductiveLimit.ConditionalExpectation.state_compatibility
    (S.expectations n) S.family S.global S.extendsFamily x

/-- On the embedded finite stage, the conditional expectation is the identity. -/
theorem expectation_projection
    (n : ℕ) (x : A n) :
    (S.expectations n).E (S.limit.inj n x) = x :=
  TensorInductiveLimit.ConditionalExpectation.projection_apply (S.expectations n) x

/-- The local conditional expectation satisfies the bimodule law. -/
theorem expectation_bimodule
    (n : ℕ) (a b : A n) (x : S.limit.AInf) :
    (S.expectations n).E (S.limit.inj n a * x * S.limit.inj n b) =
      a * (S.expectations n).E x * b :=
  TensorInductiveLimit.ConditionalExpectation.bimodule_property (S.expectations n) a b x

end BayesianTensorSystem

end InfoGeometry.Canonical.BayesianMarkovChain
