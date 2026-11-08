/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
import InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
import InfoGeometry.Krein.DoubledKreinMobiusTwist

/-!
# Constructive Current-to-Heisenberg Colimit Bridge and Krein Bogoliubov Orthogonality

This module connects the completed normal-ordered CAR current central class to
the filtered Heisenberg colimit Lie bracket, proves the linear representation
intertwining on `ChargedFockSpace 𝕜 α` and the Sugawara mode-shift identity, and
establishes the orthogonality of the forward and backward Krein Bogoliubov blocks.

- BUCKET 1 (Real Math in This File):
  - `completedCurrentCentralReadout`,
    `completedCurrentCentralReadout_centralCurrentClass`,
    `completedCurrentBracket_readout_eq_heisenbergBracket`,
    `completedCurrentBracket_readout_eq_colimitBracket`
  - `canonicalExteriorFockRawCAR`,
    `canonicalExteriorFock_completedCurrent_heisenberg`,
    `exteriorFock_to_heisenbergColimit_summary`
  - `completedModeRepresentation`, `completedModeRepresentation_bracket`,
    `completedModeRepresentation_sugawara_shift`,
    `colimitHeisenbergToChargedFock`, `colimitHeisenbergToChargedFock_mode`
  - `externalInfiniteJ_sugawara_shift`, `externalInfiniteJ_hasModeShift`
  - `currentForward`, `currentBackward`,
    `forward_backward_orthogonal`, `backward_forward_orthogonal`,
    `heisenberg_current_commutator`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.BosonizationConstructiveCurrent`
  - `InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge`
  - `InfoGeometry.Krein.DoubledKreinMobiusTwist`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge

attribute [local instance 100] LieRing.ofAssociativeRing

open VirasoroProject
open ContinuousLinearMap
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SugawaraFiveGradingObstruction
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
open InfoGeometry.OperatorAlgebra

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Readout of a `CompletedCurrentCentralClass` into the central line of
`HeisenbergAlgebra 𝕜`. -/
noncomputable def completedCurrentCentralReadout
    (X : CompletedCurrentCentralClass) : HeisenbergAlgebra 𝕜 :=
  (X.centralCoeff : 𝕜) • HeisenbergAlgebra.kgen 𝕜

/-- Evaluation of `completedCurrentCentralReadout` on `centralCurrentClass k`. -/
@[simp] theorem completedCurrentCentralReadout_centralCurrentClass (k : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (centralCurrentClass k) =
      (k : 𝕜) • HeisenbergAlgebra.kgen 𝕜 := by
  unfold completedCurrentCentralReadout centralCurrentClass
  rfl

/-- The central readout of `completedCurrentModeBracket m n` equals the Lie
bracket `⁅HeisenbergAlgebra.jgen 𝕜 m, HeisenbergAlgebra.jgen 𝕜 n⁆`. -/
theorem completedCurrentBracket_readout_eq_heisenbergBracket (m n : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (completedCurrentModeBracket m n) =
      ⁅HeisenbergAlgebra.jgen 𝕜 m, HeisenbergAlgebra.jgen 𝕜 n⁆ := by
  rw [completedCurrentCentralReadout,
    completedCurrentModeBracket_centralCoeff_eq_heisenberg,
    HeisenbergAlgebra.lie_jgen]
  by_cases h : m + n = 0 <;> simp [h]

/-- The central readout of `completedCurrentModeBracket m n` equals the Lie
bracket of the transported colimit modes `heisenbergColimitMode m` and
`heisenbergColimitMode n`. -/
theorem completedCurrentBracket_readout_eq_colimitBracket (m n : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (completedCurrentModeBracket m n) =
      ⁅heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode m),
        heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode n)⁆ := by
  rw [heisenbergFiniteModeColimitEquiv_mode,
    heisenbergFiniteModeColimitEquiv_mode]
  exact completedCurrentBracket_readout_eq_heisenbergBracket (𝕜 := 𝕜) m n

/-- Canonical direct-sum exterior-Fock raw CAR completion over `𝕜`. -/
abbrev canonicalExteriorFockRawCAR := directSumExteriorFockRawCAR 𝕜

/-- Completed normal-ordered CAR current commutator on the canonical
exterior-Fock completion. -/
theorem canonicalExteriorFock_completedCurrent_heisenberg (m n : ℤ) :
    CCRBracketCompleted (canonicalExteriorFockRawCAR (𝕜 := 𝕜))
      (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m)
      (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) n) =
      if m + n = 0 then m • (1 :
        InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock (R := 𝕜)
          (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      else 0 := by
  unfold canonicalExteriorFockRawCAR
  exact directSumExteriorFock_constructiveHeisenbergCurrent 𝕜 m n

/-- Joint stabilization and colimit-bracket theorem for the completed exterior-Fock
current modes `m` and `n`. -/
theorem exteriorFock_to_heisenbergColimit_summary (m n : ℤ) :
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j) ∧
    (∀ i j : ℤ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (cutoffDiagonalCurrent N n).coeff i j = (completedCurrent n).coeff i j) ∧
    completedCurrentCentralReadout (𝕜 := 𝕜) (completedCurrentModeBracket m n) =
      ⁅heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode m),
        heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode n)⁆ := by
  rcases constructiveHeisenbergCurrent_from_completedCurrent
      (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m n with ⟨hm, hn, _, _, _⟩
  exact ⟨hm, hn, completedCurrentBracket_readout_eq_colimitBracket m n⟩

/-- Represented current mode `(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n` on
`ChargedFockSpace 𝕜 α`. -/
noncomputable def completedModeRepresentation (α : 𝕜) (n : ℤ) :=
  (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n

/-- Linear endomorphism space of `ChargedFockSpace 𝕜 α` viewed as a UEA module. -/
abbrev FockEnd (α : 𝕜) :=
  ModuleOfModuleAlgebra 𝕜
    (UniversalEnvelopingAlgebra 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
    (VirasoroProject.ChargedFockSpace 𝕜 α) →ₗ[𝕜]
  ModuleOfModuleAlgebra 𝕜
    (UniversalEnvelopingAlgebra 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
    (VirasoroProject.ChargedFockSpace 𝕜 α)

/-- Unfolding identity for `completedModeRepresentation`. -/
@[simp] theorem completedModeRepresentation_eq_current (α : 𝕜) (n : ℤ) :
    completedModeRepresentation (𝕜 := 𝕜) α n =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n := by
  unfold completedModeRepresentation
  rfl

/-- Heisenberg mode commutator of `completedModeRepresentation α m` and
`completedModeRepresentation α n`. -/
theorem completedModeRepresentation_bracket (α : 𝕜) (m n : ℤ) :
    (completedModeRepresentation (𝕜 := 𝕜) α m).commutator
        (completedModeRepresentation (𝕜 := 𝕜) α n) =
      if m + n = 0 then (m : 𝕜) • (1 : _) else 0 := by
  unfold completedModeRepresentation
  exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

/-- Sugawara Virasoro mode-shift identity `[L_r, J_m] = -m J_{r+m}` for
`completedModeRepresentation`. -/
theorem completedModeRepresentation_sugawara_shift
    (α : 𝕜) (r m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 r)).commutator
      (completedModeRepresentation (𝕜 := 𝕜) α m) =
        (-m : 𝕜) • completedModeRepresentation (𝕜 := 𝕜) α (r + m) := by
  unfold completedModeRepresentation
  exact chargedFock_vira_mode_shift α r m

/-- Joint definition and commutator summary for `completedModeRepresentation`. -/
theorem completedModeRepresentation_summary (α : 𝕜) (m n : ℤ) :
    completedModeRepresentation (𝕜 := 𝕜) α m =
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m ∧
    (completedModeRepresentation (𝕜 := 𝕜) α m).commutator
        (completedModeRepresentation (𝕜 := 𝕜) α n) =
      if m + n = 0 then (m : 𝕜) • (1 : _) else 0 := by
  constructor
  · exact completedModeRepresentation_eq_current α m
  · exact completedModeRepresentation_bracket α m n

/-- Linear map from the filtered Heisenberg colimit `heisenbergFiniteModeColimit`
into `FockEnd α`. -/
noncomputable def colimitHeisenbergToChargedFock
    (α : 𝕜) :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) →ₗ[𝕜] FockEnd α :=
  (UniversalEnvelopingAlgebra.representation
      (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
      (V := VirasoroProject.ChargedFockSpace 𝕜 α)).toLinearMap.comp
    (heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)).toLinearMap

/-- `colimitHeisenbergToChargedFock` maps `heisenbergColimitMode m` to the
represented charged-Fock current `(chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m`. -/
theorem colimitHeisenbergToChargedFock_mode (α : 𝕜) (m : ℤ) :
    colimitHeisenbergToChargedFock (𝕜 := 𝕜) α
        (heisenbergColimitMode (𝕜 := 𝕜) m) =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  change
    (UniversalEnvelopingAlgebra.representation
        (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
        (V := VirasoroProject.ChargedFockSpace 𝕜 α))
        (heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
          (heisenbergColimitMode (𝕜 := 𝕜) m)) =
      (UniversalEnvelopingAlgebra.representation
        (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
        (V := VirasoroProject.ChargedFockSpace 𝕜 α))
        (HeisenbergAlgebra.jgen 𝕜 m)
  rw [heisenbergFiniteModeColimitEquiv_mode]

/-- Sugawara Virasoro mode-shift identity for `externalInfiniteJ_currentHeisenbergRep`. -/
theorem externalInfiniteJ_sugawara_shift
    (α : 𝕜) (r m : ℤ) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 r)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J m) =
        (-m : 𝕜) • (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J (r + m) := by
  rw [CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply]
  exact sugawara_LJ_comm (𝕜 := 𝕜) α r m

/-- `HasModeShift` witness for `externalInfiniteJ_currentHeisenbergRep`. -/
theorem externalInfiniteJ_hasModeShift
    (α : 𝕜) :
    HasModeShift
      (fun n X =>
        ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator X)
      (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J
      (fun n m => n + m)
      (fun _ m => (-m : 𝕜)) := by
  intro n m
  exact externalInfiniteJ_sugawara_shift α n m

section BogoliubovCrossTerms

open InfoGeometry.Krein

/-- Transmission block `kp.Phi T` of a Bogoliubov transformation relative to
Krein projections `kp`. -/
def currentForward
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (kp : KreinProjections (𝕜 := 𝕜) E) (T : E →L[𝕜] E) : E →L[𝕜] E :=
  kp.Phi T

/-- Leakage block `kp.Psi T` of a Bogoliubov transformation relative to Krein
projections `kp`. -/
def currentBackward
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (kp : KreinProjections (𝕜 := 𝕜) E) (T : E →L[𝕜] E) : E →L[𝕜] E :=
  kp.Psi T

/-- The forward-backward cross term `adjoint (currentForward kp T) ∘L currentBackward kp T`
vanishes by orthogonality of `P_plus` and `P_minus`. -/
theorem forward_backward_orthogonal
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (kp : KreinProjections (𝕜 := 𝕜) E) (T : E →L[𝕜] E) :
    ContinuousLinearMap.adjoint (currentForward kp T) ∘L currentBackward kp T = 0 := by
  dsimp [currentForward, currentBackward, KreinProjections.Phi, KreinProjections.Psi]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    kp.p_plus_selfadj]
  calc
    (kp.P_plus.comp (ContinuousLinearMap.adjoint T)).comp kp.P_plus ∘L
        (kp.P_minus.comp (T.comp kp.P_plus)) =
      (kp.P_plus.comp (ContinuousLinearMap.adjoint T)).comp
        (kp.P_plus.comp (kp.P_minus.comp (T.comp kp.P_plus))) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = (kp.P_plus.comp (ContinuousLinearMap.adjoint T)).comp
        ((kp.P_plus.comp kp.P_minus).comp (T.comp kp.P_plus)) := by
          dsimp; simp only [ContinuousLinearMap.comp_assoc]
    _ = 0 := by rw [kp.orthog_symm]; simp

/-- The backward-forward cross term `adjoint (currentBackward kp T) ∘L currentForward kp T`
vanishes by orthogonality `P_minus ∘ P_plus = 0`. -/
theorem backward_forward_orthogonal
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (kp : KreinProjections (𝕜 := 𝕜) E) (T : E →L[𝕜] E) :
    ContinuousLinearMap.adjoint (currentBackward kp T) ∘L currentForward kp T = 0 := by
  dsimp [currentForward, currentBackward, KreinProjections.Phi, KreinProjections.Psi]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    kp.p_plus_selfadj, kp.p_minus_selfadj]
  calc
    (kp.P_plus.comp (ContinuousLinearMap.adjoint T)).comp kp.P_minus ∘L
        (kp.P_plus.comp (T.comp kp.P_plus)) =
      (kp.P_plus.comp (ContinuousLinearMap.adjoint T)).comp
        (kp.P_minus.comp (kp.P_plus.comp (T.comp kp.P_plus))) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = (kp.P_plus.comp (ContinuousLinearMap.adjoint T)).comp
        ((kp.P_minus.comp kp.P_plus).comp (T.comp kp.P_plus)) := by
          dsimp; simp only [ContinuousLinearMap.comp_assoc]
    _ = 0 := by rw [kp.orthog]; simp

/-- Bogoliubov subspace split: when `T` is a Krein isometry on the positive cone,
`adjoint (kp.Phi T) ∘L kp.Phi T - adjoint (kp.Psi T) ∘L kp.Psi T = kp.P_plus`. -/
theorem heisenberg_current_commutator
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (kp : KreinProjections (𝕜 := 𝕜) E) (T : E →L[𝕜] E)
    (hT : kp.P_plus.comp ((kp.kreinAdjoint T).comp (T.comp kp.P_plus)) = kp.P_plus) :
    ContinuousLinearMap.adjoint (kp.Phi T) ∘L kp.Phi T -
       ContinuousLinearMap.adjoint (kp.Psi T) ∘L kp.Psi T = kp.P_plus := by
  apply kp.bogoliubov_subspace_split T
  exact hT

end BogoliubovCrossTerms

end InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
