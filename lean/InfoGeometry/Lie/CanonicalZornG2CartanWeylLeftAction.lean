import InfoGeometry.Lie.CanonicalZornG2CartanWeylNormalizedObservables
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Left-action convention for finite Weyl ensembles

The canonical ensemble datum stores parameter transport as a monoid-valued
contragredient map.  This owner exposes the corresponding genuine left action
by precomposing with inversion, while retaining the state action supplied by
the canonical datum.  No second action law or duplicate parameter datum is
introduced here.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanWeylLeftAction

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariantEnsemble
open InfoGeometry.Lie.CanonicalZornG2CartanWeylNormalizedObservables

open scoped BigOperators

variable {State W Y : Type*} [Fintype State] [Nonempty State] [Group W]

abbrev LeftActionEnsembleDatum (State W : Type*) [Fintype State]
    [Nonempty State] [Group W] :=
  WeylEquivariantEnsembleDatum State W

variable [D : LeftActionEnsembleDatum State W]

def leftParameterAction (w : W) (beta : Fin 2 → ℝ) : Fin 2 → ℝ :=
  parameterLeftAction (D := D) w beta

theorem leftParameterAction_one (beta : Fin 2 → ℝ) :
    leftParameterAction (D := D) (1 : W) beta = beta := by
  simp [leftParameterAction, parameterLeftAction]

theorem leftParameterAction_mul_reverse (g h : W) (beta : Fin 2 → ℝ) :
    leftParameterAction (D := D) (g * h) beta =
      leftParameterAction (D := D) h
        (leftParameterAction (D := D) g beta) := by
  simp [leftParameterAction, parameterLeftAction, mul_inv_rev]

theorem stateAction_inverse_cancel (w : W) (m : State) :
    w⁻¹ • (w • m) = m := by
  exact inv_smul_smul w m

theorem diagonal_energy_invariant (w : W) (beta : Fin 2 → ℝ)
    (m : State) :
    realPairingEnergy D.base
        (leftParameterAction (D := D) w beta) (w • m) =
      realPairingEnergy D.base beta m := by
  exact energy_diagonal_invariant (D := D) w beta m

theorem diagonal_weight_invariant (w : W) (beta : Fin 2 → ℝ)
    (m : State) :
    realGibbsWeight D.base
        (leftParameterAction (D := D) w beta) (w • m) =
      realGibbsWeight D.base beta m := by
  exact probability_diagonal_invariant (D := D) w beta m

theorem diagonal_partition_invariant (w : W) (beta : Fin 2 → ℝ) :
    realGibbsPartition D.base
        (leftParameterAction (D := D) w beta) =
      realGibbsPartition D.base beta := by
  exact partition_invariance (D := D) w beta

theorem diagonal_massieu_invariant (w : W) (beta : Fin 2 → ℝ) :
    souriauMassieu D.base
        (leftParameterAction (D := D) w beta) =
      souriauMassieu D.base beta := by
  exact massieu_invariance (D := D) w beta

theorem diagonal_kernel_invariant (w : W) (beta : Fin 2 → ℝ)
    (m : State) :
    realGibbsKernel D.base
        (leftParameterAction (D := D) w beta) (w • m) =
      realGibbsKernel D.base beta m := by
  exact unnormalizedWeight_diagonal_invariant (D := D) w beta m

theorem left_action_gibbsExpectation_transport
    (w : W) (beta : Fin 2 → ℝ) (f : State → Y) (g : Y → ℝ) :
    gibbsExpectation D (leftParameterAction (D := D) w beta) f g =
      gibbsExpectation D beta (fun m => f (w • m)) g := by
  exact gibbsExpectation_parameterLeftAction (D := D) w beta f g

end InfoGeometry.Lie.CanonicalZornG2CartanWeylLeftAction
