import Mathlib.Tactic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
import InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
import InfoGeometry.Krein.DoubledKreinMobiusTwist

/-! The constructive exterior-current bracket is read into the genuine
Heisenberg central line and compared with the canonical singleton-stage
representatives.  The completed-current coefficient carrier itself is not
declared to be a Lie algebra. -/
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

noncomputable def completedCurrentCentralReadout
    (X : CompletedCurrentCentralClass) : HeisenbergAlgebra 𝕜 :=
  (X.centralCoeff : 𝕜) • HeisenbergAlgebra.kgen 𝕜

@[simp] theorem completedCurrentCentralReadout_centralCurrentClass (k : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (centralCurrentClass k) =
      (k : 𝕜) • HeisenbergAlgebra.kgen 𝕜 := by
  rfl

theorem completedCurrentBracket_readout_eq_heisenbergBracket (m n : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (completedCurrentModeBracket m n) =
      ⁅HeisenbergAlgebra.jgen 𝕜 m, HeisenbergAlgebra.jgen 𝕜 n⁆ := by
  rw [completedCurrentCentralReadout,
    completedCurrentModeBracket_centralCoeff_eq_heisenberg,
    HeisenbergAlgebra.lie_jgen]
  by_cases h : m + n = 0 <;> simp [h]

theorem completedCurrentBracket_readout_eq_colimitBracket (m n : ℤ) :
    completedCurrentCentralReadout (𝕜 := 𝕜) (completedCurrentModeBracket m n) =
      ⁅heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode m),
        heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) (heisenbergColimitMode n)⁆ := by
  rw [heisenbergFiniteModeColimitEquiv_mode,
    heisenbergFiniteModeColimitEquiv_mode]
  exact completedCurrentBracket_readout_eq_heisenbergBracket (𝕜 := 𝕜) m n

abbrev canonicalExteriorFockRawCAR := directSumExteriorFockRawCAR 𝕜

theorem canonicalExteriorFock_completedCurrent_heisenberg (m n : ℤ) :
    CCRBracketCompleted (canonicalExteriorFockRawCAR (𝕜 := 𝕜))
      (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) m)
      (normalOrderedCurrent (canonicalExteriorFockRawCAR (𝕜 := 𝕜)) n) =
      if m + n = 0 then m • (1 :
        InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock (R := 𝕜)
          (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace 𝕜))
      else 0 := by
  exact directSumExteriorFock_constructiveHeisenbergCurrent 𝕜 m n

theorem exteriorFock_to_heisenbergColimit_packet (m n : ℤ) :
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

/-! The represented endpoint is the existing charged-Fock current owner. -/
noncomputable def completedModeRepresentation (α : 𝕜) (n : ℤ) :=
  (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n

abbrev FockEnd (α : 𝕜) :=
  ModuleOfModuleAlgebra 𝕜
    (UniversalEnvelopingAlgebra 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
    (VirasoroProject.ChargedFockSpace 𝕜 α) →ₗ[𝕜]
  ModuleOfModuleAlgebra 𝕜
    (UniversalEnvelopingAlgebra 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
    (VirasoroProject.ChargedFockSpace 𝕜 α)

@[simp] theorem completedModeRepresentation_eq_current (α : 𝕜) (n : ℤ) :
    completedModeRepresentation (𝕜 := 𝕜) α n =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J n :=
  rfl

theorem completedModeRepresentation_bracket (α : 𝕜) (m n : ℤ) :
    (completedModeRepresentation (𝕜 := 𝕜) α m).commutator
        (completedModeRepresentation (𝕜 := 𝕜) α n) =
      if m + n = 0 then (m : 𝕜) • (1 : _) else 0 := by
  exact (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm m n

theorem completedModeRepresentation_sugawara_shift
    (α : 𝕜) (r m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 r)).commutator
      (completedModeRepresentation (𝕜 := 𝕜) α m) =
        (-m : 𝕜) • completedModeRepresentation (𝕜 := 𝕜) α (r + m) := by
  exact chargedFock_vira_mode_shift α r m

theorem completedModeRepresentation_packet (α : 𝕜) (m n : ℤ) :
    completedModeRepresentation (𝕜 := 𝕜) α m =
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m ∧
    (completedModeRepresentation (𝕜 := 𝕜) α m).commutator
        (completedModeRepresentation (𝕜 := 𝕜) α n) =
      if m + n = 0 then (m : 𝕜) • (1 : _) else 0 := by
  exact ⟨completedModeRepresentation_eq_current α m,
    completedModeRepresentation_bracket α m n⟩

noncomputable def colimitHeisenbergToChargedFock
    (α : 𝕜) :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) →ₗ[𝕜] FockEnd α :=
  (UniversalEnvelopingAlgebra.representation
      (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
      (V := VirasoroProject.ChargedFockSpace 𝕜 α)).toLinearMap.comp
    (heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)).toLinearMap

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

theorem externalInfiniteJ_sugawara_shift
    (α : 𝕜) (r m : ℤ) :
    ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 r)).commutator
      ((externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J m) =
        (-m : 𝕜) • (externalInfiniteJ_currentHeisenbergRep (𝕜 := 𝕜) α).J (r + m) := by
  rw [CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply]
  exact sugawara_LJ_comm (𝕜 := 𝕜) α r m

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

/-! ### Bogoliubov forward/backward cross terms -/

section BogoliubovCrossTerms

open InfoGeometry.Krein

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (kp : KreinProjections (𝕜 := 𝕜) E)

/-- The transmission block of the Bogoliubov transformation. -/
def currentForward (T : E →L[𝕜] E) : E →L[𝕜] E := kp.Phi T

/-- The leakage block of the Bogoliubov transformation. -/
def currentBackward (T : E →L[𝕜] E) : E →L[𝕜] E := kp.Psi T

/-- The forward-backward cross term vanishes because the adjacent projectors
    are orthogonal: `Phi T` and `Psi T` have no mixed contribution. -/
theorem forward_backward_orthogonal (T : E →L[𝕜] E) :
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
          simp only [ContinuousLinearMap.comp_assoc]
    _ = 0 := by rw [kp.orthog_symm]; simp

/-- The backward-forward cross term vanishes by `P₋ P₊ = 0`. -/
theorem backward_forward_orthogonal (T : E →L[𝕜] E) :
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
          simp only [ContinuousLinearMap.comp_assoc]
    _ = 0 := by rw [kp.orthog]; simp

/-- The Heisenberg current commutator reduces to the positive projector `P+`
    whenever `T` is a Krein isometry on the positive cone.

    This is a direct restatement of `KreinProjections.bogoliubov_subspace_split`,
    interpreted as the canonical commutation relation for the current field. -/
theorem heisenberg_current_commutator (T : E →L[𝕜] E)
    (hT : kp.P_plus.comp ((kp.kreinAdjoint T).comp (T.comp kp.P_plus)) = kp.P_plus) :
    ContinuousLinearMap.adjoint (kp.Phi T) ∘L kp.Phi T -
       ContinuousLinearMap.adjoint (kp.Psi T) ∘L kp.Psi T = kp.P_plus :=
  kp.bogoliubov_subspace_split T hT

end BogoliubovCrossTerms

end InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
