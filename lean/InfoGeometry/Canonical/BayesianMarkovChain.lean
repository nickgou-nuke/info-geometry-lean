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

namespace BayesianMarkovChain

open TensorColimitExpectation

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

/-- KMS-style stationarity readback for the global limit state. -/
theorem kms_stationarity :
    S.global.comp S.markov = S.global :=
  S.stationary

/--
Stationarity for an explicitly supplied KMS/reference functional.

The analytic assertion that `kms_state` is the KMS state is represented by the
identification hypothesis `h_kms`; this theorem only transports the installed
Markov stationarity law through that identification.
-/
theorem kms_reference_stationarity
    (kms_state : S.limit.LimitFunctional)
    (h_kms : kms_state = S.global) :
    kms_state.comp S.markov = kms_state := by
  subst kms_state
  exact S.kms_stationarity

/-- Read back the global functional on a finite embedded stage. -/
theorem stage_readback (n : ℕ) (x : A n) :
    S.global (S.limit.inj n x) = S.family.omega n x :=
  S.limit.limit_functional_recovers_stage S.family S.global S.extendsFamily n x

/-- The stationary Bayesian update has the same finite-stage readback. -/
theorem bayesianUpdate_stage_readback (n : ℕ) (x : A n) :
    S.bayesianUpdate (S.limit.inj n x) = S.family.omega n x := by
  rw [S.bayesianUpdate_eq_global]
  exact S.stage_readback n x

/-- A supplied KMS/reference functional reads back the same finite-stage data. -/
theorem kms_stage_readback
    (kms_state : S.limit.LimitFunctional)
    (h_kms : kms_state = S.global)
    (n : ℕ) (x : A n) :
    kms_state (S.limit.inj n x) = S.family.omega n x := by
  subst kms_state
  exact S.stage_readback n x

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

/-! ## Dual Markov/state-space interface -/

namespace TensorLimitStateSpace

variable {bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)}
variable (L : TensorInductiveLimit bond)

/-- A normalized state-functional on the supplied tensor colimit. -/
structure LimitState where
  functional : L.LimitFunctional
  normalized : functional 1 = 1
  positivityCondition : Prop

/--
A Markov superoperator on observables together with its dual action on supplied
normalized states.

Complete positivity and normality remain explicit propositions owned by the
analytic layer; this file only checks the finite algebraic consequences.
-/
structure MarkovDualOperator where
  T : L.AInf →ₗ[R] L.AInf
  Tstar : LimitState L → LimitState L
  unital : T 1 = 1
  duality : ∀ (s : LimitState L) (x : L.AInf),
    (Tstar s).functional x = s.functional (T x)
  completelyPositiveCondition : Prop

namespace MarkovDualOperator

variable {L}
variable (M : MarkovDualOperator L)

/-- Readback: the dual state update preserves normalization. -/
theorem preserves_normalization (s : LimitState L) :
    (M.Tstar s).functional 1 = 1 :=
  (M.Tstar s).normalized

/-- A fixed state has stationary expectations under the observable Markov operator. -/
theorem expectation_stationary_of_fixed
    {s : LimitState L} (hs : M.Tstar s = s) (x : L.AInf) :
    s.functional (M.T x) = s.functional x := by
  rw [← M.duality s x, hs]

/-- Iterating the dual Markov update. -/
def iterateState : ℕ → LimitState L → LimitState L
  | 0, s => s
  | n + 1, s => M.Tstar (iterateState n s)

@[simp]
theorem iterateState_zero (s : LimitState L) :
    M.iterateState 0 s = s :=
  rfl

@[simp]
theorem iterateState_succ (n : ℕ) (s : LimitState L) :
    M.iterateState (n + 1) s = M.Tstar (M.iterateState n s) :=
  rfl

/-- A fixed state remains fixed under every finite Markov iterate. -/
theorem iterateState_fixed
    {s : LimitState L} (hs : M.Tstar s = s) :
    ∀ n : ℕ, M.iterateState n s = s
  | 0 => rfl
  | n + 1 => by
      rw [iterateState_succ, iterateState_fixed hs n, hs]

end MarkovDualOperator

/--
KMS stationarity packet for a supplied Markov dual operator.

The KMS property, detailed balance, and uniqueness are propositions supplied by
an owner module.  This file exposes only the readbacks that follow from the
stored fixed-point equation.
-/
structure KMSStationarityPacket where
  markov : MarkovDualOperator L
  kmsState : LimitState L
  isKMS : Prop
  detailedBalance : Prop
  uniqueInvariant : Prop
  stationary : markov.Tstar kmsState = kmsState

namespace KMSStationarityPacket

variable {L}
variable (K : KMSStationarityPacket L)

/-- Readback: the supplied KMS state is stationary for the Markov dual update. -/
theorem kms_stationary : K.markov.Tstar K.kmsState = K.kmsState :=
  K.stationary

/-- Stationarity gives invariant expectation values. -/
theorem kms_expectation_stationary (x : L.AInf) :
    K.kmsState.functional (K.markov.T x) = K.kmsState.functional x :=
  K.markov.expectation_stationary_of_fixed K.stationary x

/-- Every finite Markov iterate fixes the supplied stationary KMS state. -/
theorem kms_iterate_stationary (n : ℕ) :
    K.markov.iterateState n K.kmsState = K.kmsState :=
  K.markov.iterateState_fixed K.stationary n

/-- Readback of a supplied KMS proof. -/
theorem kms_holds (h : K.isKMS) : K.isKMS :=
  h

/-- Readback of a supplied detailed-balance proof. -/
theorem detailed_balance_holds (h : K.detailedBalance) : K.detailedBalance :=
  h

/-- Readback of a supplied uniqueness proof. -/
theorem unique_invariant_holds (h : K.uniqueInvariant) : K.uniqueInvariant :=
  h

/-- If uniqueness is given as an explicit eliminator, every fixed state is the KMS state. -/
theorem fixed_state_eq_kms_of_unique
    (uniqueFixed : ∀ s : LimitState L, K.markov.Tstar s = s → s = K.kmsState)
    (s : LimitState L)
    (hs : K.markov.Tstar s = s) :
    s = K.kmsState :=
  uniqueFixed s hs

end KMSStationarityPacket

/-! ## Bayesian projection as an explicit minimizer -/

section BayesianProjection

variable {State : Type u}

/--
The posterior is a constrained minimizer of the divergence from the prior.

For an information-geometric model this is the m-projection/Bayes update.  The
existence and uniqueness of the minimizer are supplied by the concrete model.
-/
def IsBayesianProjection
    (divergence : State → State → ℝ)
    (constraint : State → Prop)
    (prior posterior : State) : Prop :=
  constraint posterior ∧
    ∀ candidate : State,
      constraint candidate → divergence posterior prior ≤ divergence candidate prior

/-- The selected Bayesian update satisfies the supplied minimizer law. -/
theorem bayesian_projection_minimizes
    (divergence : State → State → ℝ)
    (constraint : State → Prop)
    (prior posterior : State)
    (hmin : IsBayesianProjection divergence constraint prior posterior) :
    ∀ candidate : State,
      constraint candidate → divergence posterior prior ≤ divergence candidate prior :=
  hmin.2

/-- The selected Bayesian update lies in the supplied constraint set. -/
theorem bayesian_projection_mem
    (divergence : State → State → ℝ)
    (constraint : State → Prop)
    (prior posterior : State)
    (hmin : IsBayesianProjection divergence constraint prior posterior) :
    constraint posterior :=
  hmin.1

/--
If a Markov update is identified with a Bayesian projection, the Markov step
inherits the constrained minimizer property.
-/
theorem markov_step_is_bayesian_projection
    (M : State → State)
    (divergence : State → State → ℝ)
    (constraint : State → Prop)
    (prior posterior : State)
    (hstep : M prior = posterior)
    (hmin : IsBayesianProjection divergence constraint prior posterior) :
    IsBayesianProjection divergence constraint prior (M prior) := by
  rw [hstep]
  exact hmin

end BayesianProjection

end TensorLimitStateSpace

end BayesianMarkovChain
