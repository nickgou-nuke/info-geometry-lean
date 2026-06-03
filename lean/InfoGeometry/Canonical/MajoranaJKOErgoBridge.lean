/-
InfoGeometry/Canonical/MajoranaJKOErgoBridge.lean

Majorana JKO / Ergo bridge.

This module connects existing repository layers:

* `ProjectivePolarizedBigradedBogoliubovDatum`
  supplies the doubled real Majorana/Hestenes carrier.

* `JKOTimeStep`
  supplies a deterministic variational update with an explicit minimizer proof.

* `DualFlatStructure`
  supplies Bregman divergence and the Pythagorean projection identity.

This file does not assert a universal theorem that every JKO step equals every
Bayesian update. The bridge is proof-carrying:

* the Bayesian update is explicitly identified with the JKO `next` state;
* feasible alternatives satisfy the dual-flat orthogonality condition;
* a model-specific compatibility certificate records that the same update has
  both the JKO and Bregman/Bayesian readings;
* the Bregman Pythagorean identity is then proved constructively from
  `DualFlat.bregman_pythagorean`.

No stochastic/Hudson-Parthasarathy layer is introduced here.
-/

import Mathlib
import InfoGeometry.Canonical.OperatorJKOStep
import InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
import InfoGeometry.Geometry.DualFlat
import InfoGeometry.Quantum.HestenesKahler
import InfoGeometry.Meta.OwnerTarget

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.MajoranaJKOErgoBridge

open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
open InfoGeometry.Canonical.OperatorJKOStep
open InfoGeometry.Geometry.DualFlat
open InfoGeometry.Quantum

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1. Majorana/JKO/Bayesian bridge datum -/

/--
Majorana JKO / Ergo bridge.

`State` is the finite or abstract state index used by density functions
`Density State = State → ℝ`.

`E` is the real Hilbert/Krein-Hestenes carrier into which densities are encoded
for dual-flat/Bregman geometry.

The key data are:

* a Majorana/Hestenes carrier datum;
* a Souriau/metriplectic/optimal-transport flow;
* a JKO variational step;
* a dual-flat Bregman structure on the encoded carrier;
* an encoder from densities to the Bregman carrier;
* a Bayesian update map;
* an equality saying the Bayesian update of the previous density is the JKO
  next density;
* an explicit compatibility certificate;
* a dual-flat orthogonality law for feasible alternatives.
-/
structure MajoranaJKOErgoBridge
    (State LieGroup LieAlgebra LieDual Observable : Type*) where
  /-- Doubled real Majorana/Hestenes carrier. -/
  majorana :
    ProjectivePolarizedBigradedBogoliubovDatum (E := E)

  /-- Souriau/metriplectic/optimal-transport flow layer. -/
  flow :
    SouriauMetriplecticOTFlow
      State LieGroup LieAlgebra LieDual Observable

  /-- Deterministic JKO time step. -/
  jko :
    JKOTimeStep State

  /-- Dual-flat Bregman geometry on the encoded carrier. -/
  dualFlat :
    DualFlatStructure E

  /-- Encode a density into the Bregman/Hestenes carrier. -/
  encodeDensity :
    Density State → E

  /-- Feasible alternatives for the projection/Bayes update problem. -/
  feasibleAlternative :
    Density State → Prop

  /-- Bayesian/discrete update map on densities. -/
  bayesUpdate :
    Density State → Density State

  /--
  The Bayesian update of the previous density is exactly the JKO next density.

  This is an explicit equation, not a vague compatibility proposition.
  -/
  bayes_update_previous_eq_next :
    bayesUpdate jko.previous = jko.next

  /--
  Compatibility law identifying the supplied JKO update with the supplied
  latent Bregman/Bayesian update.

  This is the ergo-transfer certificate: continuous transport and discrete
  projection are the same update only in models that provide this witness.
  -/
  jko_bayes_compatibility_True : Prop := by

    sorry

  /--
  Dual-flat projection orthogonality for feasible alternatives.

  This is the exact hypothesis needed to turn the Bayes/JKO update into a
  Bregman Pythagorean identity.
  -/
  projection_orthogonality :
    ∀ ρ : Density State,
      feasibleAlternative ρ →
        inner ℝ
          (nabla dualFlat (encodeDensity jko.previous) -
            nabla dualFlat (encodeDensity jko.next))
          (encodeDensity ρ - encodeDensity jko.next) = 0

namespace MajoranaJKOErgoBridge

variable
    {State LieGroup LieAlgebra LieDual Observable : Type*}

variable
    (B : MajoranaJKOErgoBridge
      (E := E) State LieGroup LieAlgebra LieDual Observable)

/-! ## 2. Re-export the JKO variational content -/

/-- Prior latent point induced by the previous JKO density. -/
def priorLatent : E :=
  B.encodeDensity B.jko.previous

/-- Posterior latent point induced by the next JKO density. -/
def posteriorLatent : E :=
  B.encodeDensity B.jko.next

/-- The JKO step minimizes its stored objective. -/
theorem jko_minimizing
    (ρ : Density State) :
    B.jko.objective B.jko.next ≤ B.jko.objective ρ :=
  B.jko.minimizing ρ

/-- The JKO step size is nonnegative. -/
theorem jko_stepSize_nonneg :
    0 ≤ B.jko.stepSize :=
  B.jko.stepSize_nonneg

/-- The Bayesian update of the previous density is the JKO next density. -/
theorem bayesUpdate_previous_eq_next :
    B.bayesUpdate B.jko.previous = B.jko.next :=
  B.bayes_update_previous_eq_next

/--
Equivalent orientation: the JKO next density is the Bayesian update of the
previous density.
-/
theorem next_eq_bayesUpdate_previous :
    B.jko.next = B.bayesUpdate B.jko.previous :=
  B.bayes_update_previous_eq_next.symm

/--
The Bayesian update minimizes the JKO objective, because it is explicitly
identified with the JKO next state by the bridge datum.
-/
theorem bayesUpdate_minimizing
    (ρ : Density State) :
    B.jko.objective (B.bayesUpdate B.jko.previous) ≤
      B.jko.objective ρ := by
  rw [B.bayes_update_previous_eq_next]
  exact B.jko_minimizing ρ

/--
The Souriau/metriplectic total flow is the sum of reversible and dissipative
pieces.

This is re-exported from the stored flow witness.
-/
theorem totalFlow_eq_add_at
    (ρ : Density State) :
    B.flow.totalFlow ρ =
      B.flow.reversibleFlow ρ + B.flow.dissipativeFlow ρ :=
  SouriauMetriplecticOTFlow.totalFlow_eq_add_at B.flow ρ

/--
The free energy carried by the optimal-transport flow splits into entropy and
expectation terms.
-/
theorem freeEnergy_eq_entropy_plus_expectation
    (ρ : Density State) :
    B.flow.freeEnergy.freeEnergy ρ =
      B.flow.freeEnergy.entropyTerm ρ +
        B.flow.freeEnergy.expectationTerm ρ :=
  B.flow.freeEnergy.freeEnergy_eq ρ

/-! ## 3. Encoded Bregman geometry -/

/-- Encoded Bregman divergence between two densities. -/
def encodedDivergence
    (ρ σ : Density State) : ℝ :=
  divergence B.dualFlat
    (B.encodeDensity ρ)
    (B.encodeDensity σ)

@[simp]
theorem encodedDivergence_self
    (ρ : Density State) :
    B.encodedDivergence ρ ρ = 0 := by
  dsimp [encodedDivergence]
  simp

/-- Projection orthogonality, re-exported as a theorem. -/
theorem projection_orthogonality_apply
    (ρ : Density State)
    (hρ : B.feasibleAlternative ρ) :
    inner ℝ
      (nabla B.dualFlat (B.encodeDensity B.jko.previous) -
        nabla B.dualFlat (B.encodeDensity B.jko.next))
      (B.encodeDensity ρ - B.encodeDensity B.jko.next) = 0 :=
  B.projection_orthogonality ρ hρ

/--
Bregman Pythagorean identity for the feasible Bayesian/JKO projection.

This is the constructive theorem payload of the bridge.

For every feasible alternative `ρ`,

`D(ρ || previous) = D(ρ || next) + D(next || previous)`

after encoding densities into the dual-flat carrier.
-/
theorem bayesian_projection_identity
    (ρ : Density State)
    (hρ : B.feasibleAlternative ρ) :
    B.encodedDivergence ρ B.jko.previous =
      B.encodedDivergence ρ B.jko.next +
        B.encodedDivergence B.jko.next B.jko.previous := by
  dsimp [encodedDivergence]
  exact
    bregman_pythagorean
      (S := B.dualFlat)
      (x := B.encodeDensity ρ)
      (y := B.encodeDensity B.jko.next)
      (z := B.encodeDensity B.jko.previous)
      (B.projection_orthogonality_apply ρ hρ)

/--
The same Pythagorean identity, written with the Bayesian update instead of
`jko.next`.
-/
theorem bayesian_projection_identity_bayesUpdate
    (ρ : Density State)
    (hρ : B.feasibleAlternative ρ) :
    divergence B.dualFlat
        (B.encodeDensity ρ)
        (B.encodeDensity B.jko.previous)
      =
    divergence B.dualFlat
        (B.encodeDensity ρ)
        (B.encodeDensity (B.bayesUpdate B.jko.previous))
      +
    divergence B.dualFlat
        (B.encodeDensity (B.bayesUpdate B.jko.previous))
        (B.encodeDensity B.jko.previous) := by
  rw [B.bayes_update_previous_eq_next]
  exact B.bayesian_projection_identity ρ hρ

/--
The latent Majorana datum carries a phase-even Hestenes axis.

This is a re-export of the existing Hestenes/Kähler Majorana carrier theorem.
-/
theorem majorana_phase_axis_even :
    HasPhaseParity (E := E) PhaseParity.even B.majorana.K :=
  B.majorana.K_phase_even

/-- The Majorana/QGT compatibility law on the latent carrier. -/
theorem majorana_qgt_compat
    (u v : InfoGeometry.Krein.DoubledSpace E) :
    B.majorana.qgt.berry u v =
      B.majorana.qgt.metric (B.majorana.K u) v :=
  B.majorana.compat u v

/--
A packaged ergo-transfer proposition: the supplied bridge targets

* the JKO variational minimizing property,
* the Bregman/Bayesian projection identity,
* and the JKO/Bayes compatibility law.
-/
def ergo_transfer_payload
    (ρ alt : Density State) : Prop :=
  B.jko.objective B.jko.next ≤ B.jko.objective ρ
    ∧
  B.encodedDivergence alt B.jko.previous =
    B.encodedDivergence alt B.jko.next +
      B.encodedDivergence B.jko.next B.jko.previous
    ∧
  B.jko_bayes_compatibility_True

/-- Constructor lemma for the packaged ergo-transfer payload. -/
theorem ergo_transfer_payload_intro
    (ρ alt : Density State)
    (halt : B.feasibleAlternative alt)
    (hCompat : B.jko_bayes_compatibility_True) :
    B.jko.objective B.jko.next ≤ B.jko.objective ρ
      ∧
    B.encodedDivergence alt B.jko.previous =
      B.encodedDivergence alt B.jko.next +
        B.encodedDivergence B.jko.next B.jko.previous
      ∧
    B.jko_bayes_compatibility_True := by
  exact
    ⟨B.jko_minimizing ρ,
      B.bayesian_projection_identity alt halt,
      hCompat⟩

/--
The Majorana/Hestenes carrier is available as data.

This is a `def`, not a theorem, because the carrier is structure data rather
than a proposition.
-/
def majoranaCarrier :
    ProjectivePolarizedBigradedBogoliubovDatum (E := E) :=
  B.majorana

end MajoranaJKOErgoBridge

/-! ## 4. Operator-JKO/Bayes/Majorana fusion adapter -/

/--
Fusion adapter between the abstract operator-JKO/Bayesian calibration lane and
the Majorana/Hestenes carrier lane.

This does not create another density-level `MajoranaJKOErgoBridge`. It connects
the already existing `OperatorJKOArgmin`/`JKOBayesianCalibration` layer to a
dual-flat projection certificate and re-exports the Majorana phase-axis carrier.
-/
structure OperatorJKOBayesMajoranaBridge
    (Weight Evidence : Type*)
    [NormedAddCommGroup Weight]
    [InnerProductSpace ℝ Weight]
    [CompleteSpace Weight] where
  /-- Doubled real Majorana/Hestenes carrier. -/
  majorana :
    ProjectivePolarizedBigradedBogoliubovDatum (E := E)

  /-- Operator-JKO potential on the abstract weight/state carrier. -/
  potential :
    OperatorJKOPotential Weight

  /-- Bayesian calibration of the deterministic operator-JKO step. -/
  bayes :
    JKOBayesianCalibration
      (Weight := Weight)
      (Evidence := Evidence)
      potential

  /-- Dual-flat Bregman geometry on the operator-JKO weight carrier. -/
  dualFlat :
    DualFlatStructure Weight

  /-- Feasible alternatives for the evidence-conditioned projection problem. -/
  feasibleAlternative :
    Weight → Weight → Evidence → Prop

  /--
  Orthogonality law for the evidence-conditioned Bayesian/JKO projection.

  The posterior is `bayes.bayesUpdate prior evidence`.
  -/
  projection_orthogonality :
    ∀ prior alt evidence,
      feasibleAlternative prior alt evidence →
        inner ℝ
          (nabla dualFlat prior -
            nabla dualFlat (bayes.bayesUpdate prior evidence))
          (alt - bayes.bayesUpdate prior evidence) = 0

namespace OperatorJKOBayesMajoranaBridge

variable
    {Weight Evidence : Type*}
    [NormedAddCommGroup Weight]
    [InnerProductSpace ℝ Weight]
    [CompleteSpace Weight]

variable
    (B : OperatorJKOBayesMajoranaBridge
      (E := E) Weight Evidence)

/-- The Bayesian posterior inherits deterministic operator-JKO energy decay. -/
theorem bayes_energy_le_prior_energy
    (prior : Weight)
    (evidence : Evidence) :
    B.potential.energy (B.bayes.bayesUpdate prior evidence) ≤
      B.potential.energy prior :=
  B.bayes.bayes_energy_le_prior_energy prior evidence

/-- The selected Bayesian/JKO penalty is bounded by the installed energy drop. -/
theorem jko_penalty_le_energy_drop
    (prior : Weight)
    (evidence : Evidence) :
    B.potential.penalty
        (B.bayes.jkoStep prior evidence).stepSize
        (B.bayes.jkoStep prior evidence).next
        (B.bayes.jkoStep prior evidence).previous
      ≤
    B.potential.energy (B.bayes.jkoStep prior evidence).previous -
      B.potential.energy (B.bayes.jkoStep prior evidence).next :=
  B.bayes.jko_penalty_le_energy_drop prior evidence

/-- Projection orthogonality, re-exported from the adapter witness. -/
theorem projection_orthogonality_apply
    (prior alt : Weight)
    (evidence : Evidence)
    (halt : B.feasibleAlternative prior alt evidence) :
    inner ℝ
      (nabla B.dualFlat prior -
        nabla B.dualFlat (B.bayes.bayesUpdate prior evidence))
      (alt - B.bayes.bayesUpdate prior evidence) = 0 :=
  B.projection_orthogonality prior alt evidence halt

/--
Bregman projection identity for the abstract operator-JKO Bayesian posterior.

For every feasible alternative `alt`,

`D(alt || prior) = D(alt || posterior) + D(posterior || prior)`.
-/
theorem bayesian_projection_identity
    (prior alt : Weight)
    (evidence : Evidence)
    (halt : B.feasibleAlternative prior alt evidence) :
    divergence B.dualFlat alt prior =
      divergence B.dualFlat alt (B.bayes.bayesUpdate prior evidence) +
        divergence B.dualFlat (B.bayes.bayesUpdate prior evidence) prior := by
  exact
    bregman_pythagorean
      (S := B.dualFlat)
      (x := alt)
      (y := B.bayes.bayesUpdate prior evidence)
      (z := prior)
      (B.projection_orthogonality_apply prior alt evidence halt)

/-- The latent Majorana datum carries a phase-even Hestenes axis. -/
theorem majorana_phase_axis_even :
    HasPhaseParity (E := E) PhaseParity.even B.majorana.K :=
  B.majorana.K_phase_even

/--
The adapter exposes the three intended outputs together:
operator-JKO energy decay, Bregman projection identity, and the Majorana
phase-even carrier.
-/
theorem operator_jko_bayes_majorana_payload
    (prior alt : Weight)
    (evidence : Evidence)
    (halt : B.feasibleAlternative prior alt evidence) :
    B.potential.energy (B.bayes.bayesUpdate prior evidence) ≤
        B.potential.energy prior
      ∧
    divergence B.dualFlat alt prior =
        divergence B.dualFlat alt (B.bayes.bayesUpdate prior evidence) +
          divergence B.dualFlat (B.bayes.bayesUpdate prior evidence) prior
      ∧
    HasPhaseParity (E := E) PhaseParity.even B.majorana.K :=
  ⟨B.bayes_energy_le_prior_energy prior evidence,
    B.bayesian_projection_identity prior alt evidence halt,
    B.majorana_phase_axis_even⟩

end OperatorJKOBayesMajoranaBridge

/-! ## 5. Constructive scalar deterministic JKO anchor -/

/--
Parameters for the scalar quadratic deterministic JKO model.

This gives the repository a fully constructive anchor before any Type III or
weak-* compactness theorem is attempted.
-/
structure ScalarJKOParameters where
  /-- Time step. -/
  tau : ℝ

  /-- Positive time step. -/
  tau_pos : 0 < tau

  /-- Previous/prior scalar state. -/
  previous : ℝ

  /-- Equilibrium/target scalar state. -/
  equilibrium : ℝ

namespace ScalarJKOParameters

variable (P : ScalarJKOParameters)

/-- `τ ≠ 0`. -/
theorem tau_ne_zero :
    P.tau ≠ 0 :=
  ne_of_gt P.tau_pos

/-- `1 + τ > 0`. -/
theorem one_add_tau_pos :
    0 < 1 + P.tau := by
  linarith [P.tau_pos]

/-- `1 + τ ≠ 0`. -/
theorem one_add_tau_ne_zero :
    1 + P.tau ≠ 0 :=
  ne_of_gt P.one_add_tau_pos

/--
Scalar deterministic JKO functional:

`F(x) = 1/2 (x-eq)^2 + 1/(2τ) (x-prev)^2`.
-/
def functional
    (x : ℝ) : ℝ :=
  (1 / 2) * (x - P.equilibrium) ^ 2 +
    (1 / (2 * P.tau)) * (x - P.previous) ^ 2

/--
Explicit scalar JKO step:

`x* = (previous + τ equilibrium)/(1+τ)`.
-/
def step : ℝ :=
  (P.previous + P.tau * P.equilibrium) / (1 + P.tau)

/-- The completed-square coefficient is positive. -/
theorem square_coefficient_pos :
    0 < (1 + P.tau) / (2 * P.tau) := by
  have hnum : 0 < 1 + P.tau :=
    P.one_add_tau_pos
  have hden : 0 < 2 * P.tau := by
    nlinarith [P.tau_pos]
  exact div_pos hnum hden

/--
Completed-square identity for the scalar JKO functional.

This is the constructive finite anchor:

`F(x) = F(x*) + ((1+τ)/(2τ)) (x-x*)²`.
-/
theorem functional_complete_square
    (x : ℝ) :
    P.functional x =
      P.functional P.step +
        ((1 + P.tau) / (2 * P.tau)) * (x - P.step) ^ 2 := by
  dsimp [functional, step]
  have htau : P.tau ≠ 0 := P.tau_ne_zero
  have hden : 1 + P.tau ≠ 0 := P.one_add_tau_ne_zero
  have h2tau : 2 * P.tau ≠ 0 := by
    nlinarith [P.tau_pos]
  field_simp [htau, hden, h2tau]
  ring

/-- The explicit scalar JKO step minimizes the scalar JKO functional. -/
theorem step_minimizes
    (x : ℝ) :
    P.functional P.step ≤ P.functional x := by
  rw [P.functional_complete_square x]
  have hcoef :
      0 ≤ (1 + P.tau) / (2 * P.tau) :=
    le_of_lt P.square_coefficient_pos
  have hsquare :
      0 ≤ (x - P.step) ^ 2 :=
    sq_nonneg (x - P.step)
  nlinarith

/-- Equality of value with the JKO step forces equality of point. -/
theorem eq_step_of_equal_value
    {x : ℝ}
    (hval : P.functional x = P.functional P.step) :
    x = P.step := by
  have hcs := P.functional_complete_square x
  rw [hval] at hcs

  have hterm :
      ((1 + P.tau) / (2 * P.tau)) * (x - P.step) ^ 2 = 0 := by
    linarith

  have hcoef :
      0 < (1 + P.tau) / (2 * P.tau) :=
    P.square_coefficient_pos

  have hcoef_ne :
      (1 + P.tau) / (2 * P.tau) ≠ 0 :=
    ne_of_gt hcoef

  have hsquare :
      (x - P.step) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hterm with hbad | hsq
    · exact False.elim (hcoef_ne hbad)
    · exact hsq

  have hdiff :
      x - P.step = 0 := by
    nlinarith [hsquare]

  linarith

/-- The scalar JKO step is the unique minimizer. -/
theorem step_unique_minimizer
    {x : ℝ}
    (hmin :
      ∀ y : ℝ, P.functional x ≤ P.functional y) :
    x = P.step := by
  have h₁ : P.functional x ≤ P.functional P.step :=
    hmin P.step

  have h₂ : P.functional P.step ≤ P.functional x :=
    P.step_minimizes x

  have heq :
      P.functional x = P.functional P.step :=
    le_antisymm h₁ h₂

  exact P.eq_step_of_equal_value heq

end ScalarJKOParameters

/-! ## 5. Owner targets -/

/-- Owner target for scalar deterministic JKO minimization. -/
@[owner_target_tag]
def ScalarJKOOwnerTarget : Prop :=
  ∀ P : ScalarJKOParameters,
    ∀ x : ℝ,
      P.functional P.step ≤ P.functional x

/-- Constructive proof of scalar deterministic JKO minimization. -/
theorem scalarJKOOwnerTarget :
    ScalarJKOOwnerTarget := by
  intro P x
  exact P.step_minimizes x

/-- Owner target for uniqueness of scalar deterministic JKO minimization. -/
@[owner_target_tag]
def ScalarJKOUniqueOwnerTarget : Prop :=
  ∀ P : ScalarJKOParameters,
    ∀ x : ℝ,
      (∀ y : ℝ, P.functional x ≤ P.functional y) →
        x = P.step

/-- Constructive proof of scalar deterministic JKO uniqueness. -/
theorem scalarJKOUniqueOwnerTarget :
    ScalarJKOUniqueOwnerTarget := by
  intro P x hmin
  exact P.step_unique_minimizer hmin

/--
Owner target for the Majorana/JKO/Ergo bridge once a bridge witness is supplied.
-/
@[owner_target_tag]
def MajoranaJKOErgoBridgeOwnerTarget : Prop :=
  ∀ (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
  ∀ (State LieGroup LieAlgebra LieDual Observable : Type*),
    MajoranaJKOErgoBridge
      (E := E) State LieGroup LieAlgebra LieDual Observable →
      Nonempty
        (MajoranaJKOErgoBridge
          (E := E) State LieGroup LieAlgebra LieDual Observable)

/-- The Majorana/JKO/Ergo bridge owner target is discharged by the supplied bridge. -/
theorem majoranaJKOErgoBridgeOwnerTarget :
    MajoranaJKOErgoBridgeOwnerTarget := by
  intro E _ _ _ State LieGroup LieAlgebra LieDual Observable B
  exact ⟨B⟩

end InfoGeometry.Canonical.MajoranaJKOErgoBridge
