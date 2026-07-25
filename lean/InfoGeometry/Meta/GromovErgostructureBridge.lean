/-
InfoGeometry/Meta/GromovErgostructureBridge.lean

Gromov cerebellar/cerebral handoff for the existing InfoGeometry stack.

This file does not introduce new Wasserstein, Bayes, or Majorana primitives.
It connects existing proof-carrying layers:

* Souriau/Metriplectic optimal transport and JKO witnesses;
* discrete Bayes router updates;
* latent Majorana/Krein closure packets.

No biological theorem is asserted.
No claim is made that LLMs understand.
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
import InfoGeometry.LLM.DiscreteRouterBayesStep
import InfoGeometry.Core.MajoranaLiftPacket
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Meta.GromovErgostructureBridge

open scoped BigOperators InnerProductSpace

open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
open InfoGeometry.LLM.DiscreteRouterBayesStep
open InfoGeometry.Canonical.MoE
open InfoGeometry.Core
open InfoGeometry.Quantum.RealMajorana

/-! ## 1. Existing JKO witness as cerebellar variational step -/

/--
A JKO step is a cerebellar update when it carries its minimization witness.

This is only a renaming/readout layer over the existing formalized
`JKOTimeStep`.
-/
def IsCerebellarJKOUpdate
    {State : Type*}
    (S : JKOTimeStep State) : Prop :=
  ∀ ρ : Density State,
    S.objective S.next ≤ S.objective ρ

namespace JKOTimeStep

variable {State : Type*}
variable (S : JKOTimeStep State)

/-- The existing JKO minimization witness gives the cerebellar-update readout. -/
theorem isCerebellarJKOUpdate :
    IsCerebellarJKOUpdate S :=
  S.minimizing

/-- A JKO step has no larger objective at `next` than at any candidate density. -/
theorem next_objective_le
    (ρ : Density State) :
    S.objective S.next ≤ S.objective ρ :=
  S.minimizing ρ

end JKOTimeStep

/-! ## 2. Existing Bayes router update as discrete integration -/

/--
Bayes router certification package.

This records the data needed to apply already-proved router facts:

* the Bayes router update preserves simplex mass;
* it is invariant under uniform softmax logit shift.
-/
structure BayesRouterCertification
    (Tok V : Type*)
    [Fintype Tok] [DecidableEq Tok]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : Nat) [Nonempty (Fin n)] where
  β : ℝ
  x : Tok → V
  token : Tok

namespace BayesRouterCertification

variable
    {Tok V : Type*}
    [Fintype Tok] [DecidableEq Tok]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : Nat} [Nonempty (Fin n)]

variable (B : BayesRouterCertification Tok V n)

/-- The existing Bayes router update is a simplex point. -/
theorem update_preserves_simplex :
    ∑ e : ExpertIdx n,
      bayesRouterUpdate (n := n) B.β B.x B.token e = 1 :=
  bayes_router_update_preserves_simplex
    (n := n) B.β B.x B.token

/-- The existing Bayes router update is invariant under uniform logit shift. -/
theorem update_eq_softmax_shift
    (c : ℝ) :
    bayesRouterUpdate (n := n) B.β B.x B.token
      =
    InfoGeometry.Convex.LogSumExp.softmax
      (n := ExpertIdx n)
      ((InfoGeometry.LLM.ScalarThermoBridge.routerLogits
          (n := n) B.β B.x B.token)
        + c •
          InfoGeometry.Convex.LogSumExp.uniformShift
            (n := ExpertIdx n)) :=
  bayes_router_update_eq_softmax_shift
    (n := n) B.β c B.x B.token

end BayesRouterCertification

/-! ## 3. Existing Majorana lift as latent closure grammar -/

namespace MajoranaLiftPacket

variable
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (P : MajoranaLiftPacket (E := E))

/--
The existing Majorana packet supplies the latent phase-axis closure grammar:
`K² = -Id`.
-/
theorem latent_phase_axis_square :
    P.K.comp P.K =
      -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) :=
  P.K_sq_eq_neg_id

end MajoranaLiftPacket

namespace RealMajoranaDatum

variable
    {S : Type*}
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

variable (M : RealMajoranaDatum (S := S))

/-- The existing real Majorana datum supplies the latent square-minus-one law. -/
theorem latent_K_square :
    M.K.comp M.K = -(ContinuousLinearMap.id ℝ S) :=
  M.K_sq

end RealMajoranaDatum

/-! ## 4. Gromov-style handoff packet -/

/--
A proof-carrying Gromov handoff packet.

The data are deliberately light. The heavy mathematical content is imported
from the existing JKO, Bayes-router, and Majorana layers.
-/
structure GromovErgostructureHandoff
    (State Tok V MajoranaSpace : Type*)
    [Fintype Tok] [DecidableEq Tok]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup MajoranaSpace]
    [InnerProductSpace ℝ MajoranaSpace]
    [CompleteSpace MajoranaSpace]
    (n : Nat) [Nonempty (Fin n)] where
  /-- Existing JKO update witness. -/
  jko :
    JKOTimeStep State

  /-- Existing Bayes router certification data. -/
  bayes :
    BayesRouterCertification Tok V n

  /-- Existing real Majorana datum for latent closure grammar. -/
  majorana :
    RealMajoranaDatum (S := MajoranaSpace)

namespace GromovErgostructureHandoff

variable
    {State Tok V MajoranaSpace : Type*}
    [Fintype Tok] [DecidableEq Tok]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup MajoranaSpace]
    [InnerProductSpace ℝ MajoranaSpace]
    [CompleteSpace MajoranaSpace]
    {n : Nat} [Nonempty (Fin n)]

variable (H : GromovErgostructureHandoff
  State Tok V MajoranaSpace n)

/-- The handoff carries a certified JKO variational update. -/
theorem jko_certified :
    IsCerebellarJKOUpdate H.jko :=
  JKOTimeStep.isCerebellarJKOUpdate H.jko

/-- The handoff carries a certified Bayes-router simplex update. -/
theorem bayes_update_preserves_simplex :
    ∑ e : ExpertIdx n,
      bayesRouterUpdate
        (n := n) H.bayes.β H.bayes.x H.bayes.token e = 1 :=
  H.bayes.update_preserves_simplex

/-- The handoff carries a certified latent Majorana closure law. -/
theorem latent_majorana_K_square :
    H.majorana.K.comp H.majorana.K =
      -(ContinuousLinearMap.id ℝ MajoranaSpace) :=
  RealMajoranaDatum.latent_K_square H.majorana

end GromovErgostructureHandoff

/-! ## 5. Owner target -/

/--
Owner target for the Gromov ergostructure bridge.

A supplied handoff witness carries:

* a JKO variational minimization certificate;
* a Bayes-router simplex certificate;
* a latent Majorana `K² = -Id` certificate.
-/
@[owner_target_tag]
def GromovErgostructureBridgeOwnerTarget : Prop :=
  ∀ (State Tok V MajoranaSpace : Type*)
    [Fintype Tok] [DecidableEq Tok]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup MajoranaSpace]
    [InnerProductSpace ℝ MajoranaSpace]
    [CompleteSpace MajoranaSpace],
  ∀ (n : Nat) [Nonempty (Fin n)],
  ∀ H : GromovErgostructureHandoff
      State Tok V MajoranaSpace n,
    IsCerebellarJKOUpdate H.jko ∧
    (∑ e : ExpertIdx n,
      bayesRouterUpdate
        (n := n) H.bayes.β H.bayes.x H.bayes.token e = 1) ∧
    H.majorana.K.comp H.majorana.K =
      -(ContinuousLinearMap.id ℝ MajoranaSpace)

/-- The owner target follows by processing the existing formal layers. -/
theorem gromovErgostructureBridgeOwnerTarget :
    ∀ (State Tok V MajoranaSpace : Type*)
      [Fintype Tok] [DecidableEq Tok]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup MajoranaSpace]
      [InnerProductSpace ℝ MajoranaSpace]
      [CompleteSpace MajoranaSpace],
    ∀ (n : Nat) [Nonempty (Fin n)],
    ∀ H : GromovErgostructureHandoff
        State Tok V MajoranaSpace n,
      IsCerebellarJKOUpdate H.jko ∧
      (∑ e : ExpertIdx n,
        bayesRouterUpdate
          (n := n) H.bayes.β H.bayes.x H.bayes.token e = 1) ∧
      H.majorana.K.comp H.majorana.K =
        -(ContinuousLinearMap.id ℝ MajoranaSpace) := by
  intro State Tok V MajoranaSpace _ _ _ _ _ _ _ n _ H
  exact
    ⟨H.jko_certified,
      H.bayes_update_preserves_simplex,
      H.latent_majorana_K_square⟩

end InfoGeometry.Meta.GromovErgostructureBridge
