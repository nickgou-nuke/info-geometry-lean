import InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
import InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
import proofs.BraidProject.BraidGroup

/-!
# Arbitrary finite braid-group actions on logarithmic tensor powers

For every `n`, the existing `Braid.braid_group (n+2)` acts on the right-associated
`(n+2)`-fold tensor power of the standard rank-two logarithmic Jordan object.
The only inputs are the adjacent checked-R slices and the Artin/far relations
proved in `LogJordanTensorPowerBraidRelations`.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation

open Braid
open InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
open InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge

/-- All defining relations of `B_{n+2}` are satisfied by the adjacent checked-R
slices on the `(n+2)`-fold standard logarithmic tensor power. -/
theorem standardTensorPower_braidRelations (n : ℕ) :
    ∀ r ∈ braid_rels (n + 1),
      FreeGroup.lift (standardTensorPowerGenerator n) r =
        (1 : tensorPowerObj standardJordanObject (n + 2) ≃ₗ[ℂ]
          tensorPowerObj standardJordanObject (n + 2)) := by
  intro r hr
  cases n with
  | zero =>
      simpa [braid_rels] using hr
  | succ k =>
      change
        (∃ i : Fin (k + 1), r = braid_rel i.castSucc i.succ) ∨
          (∃ i j : Fin k, i ≤ j ∧
            r = comm_rel i.castSucc.castSucc j.succ.succ) at hr
      rcases hr with hAdj | hFar
      · rcases hAdj with ⟨i, rfl⟩
        have hArtin := standardTensorPower_artin k i
        simp [braid_rel, FreeGroup.lift_apply_of, mul_assoc]
        group
        rw [hArtin]
        group
      · rcases hFar with ⟨i, j, hij, rfl⟩
        cases k with
        | zero => exact i.elim0
        | succ l =>
            have hComm := standardTensorPower_far l i j hij
            simp [comm_rel, FreeGroup.lift_apply_of, mul_assoc]
            group
            rw [hComm]
            group

/-- Group-level action of `B_{n+2}` on the `(n+2)`-fold logarithmic tensor
carrier. -/
def standardHadjiivanovBraidProjectHom (n : ℕ) :
    braid_group (n + 2) →*
      (tensorPowerObj standardJordanObject (n + 2) ≃ₗ[ℂ]
        tensorPowerObj standardJordanObject (n + 2)) :=
  PresentedGroup.toGroup (standardTensorPower_braidRelations n)

/-- Native Mathlib representation of every finite braid stage. -/
def standardHadjiivanovBraidProjectRepresentation (n : ℕ) :
    Representation ℂ (braid_group (n + 2))
      (tensorPowerObj standardJordanObject (n + 2)) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (standardHadjiivanovBraidProjectHom n)

/-- Generator readback: the `i`th Artin generator is exactly the `i`th
checked-R slice. -/
@[simp]
theorem standardHadjiivanovBraidProject_sigma
    (n : ℕ) (i : Fin (n + 1)) :
    standardHadjiivanovBraidProjectHom n (σ' (n + 1) i) =
      standardTensorPowerGenerator n i := by
  exact PresentedGroup.toGroup.of (standardTensorPower_braidRelations n)

/-- Under the canonical finite-to-infinite group map, every stage generator
keeps its index. -/
theorem standardTensorPower_generator_to_infinite
    (n : ℕ) (i : Fin (n + 1)) :
    finiteToInfiniteGroupHom (n + 1) (σ' (n + 1) i) = σi i.1 := by
  exact finiteToInfiniteGroupHom_sigma (n + 1) i

/-- The stage-3 representation recovered from the uniform finite-stage family
has the expected first two checked-R generators. -/
theorem standardTensorPower_stage3_packet :
    standardHadjiivanovBraidProjectHom 1 (σ' 2 (0 : Fin 2)) =
        standardTensorPowerGenerator 1 (0 : Fin 2) ∧
      standardHadjiivanovBraidProjectHom 1 (σ' 2 (1 : Fin 2)) =
        standardTensorPowerGenerator 1 (1 : Fin 2) := by
  constructor
  · exact PresentedGroup.toGroup.of (standardTensorPower_braidRelations 1)
  · exact PresentedGroup.toGroup.of (standardTensorPower_braidRelations 1)

/-- Stage four simultaneously exhibits adjacent Artin and far commutation via
the uniform family. -/
theorem standardTensorPower_stage4_relation_packet :
    standardHadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) *
        standardHadjiivanovBraidProjectHom 2 (σ' 3 (1 : Fin 3)) *
        standardHadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) =
      standardHadjiivanovBraidProjectHom 2 (σ' 3 (1 : Fin 3)) *
        standardHadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) *
        standardHadjiivanovBraidProjectHom 2 (σ' 3 (1 : Fin 3)) ∧
    standardHadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) *
        standardHadjiivanovBraidProjectHom 2 (σ' 3 (2 : Fin 3)) =
      standardHadjiivanovBraidProjectHom 2 (σ' 3 (2 : Fin 3)) *
        standardHadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) := by
  constructor
  · simpa using standardTensorPower_artin 1 (0 : Fin 2)
  · simpa using standardTensorPower_far 0 (0 : Fin 1) (0 : Fin 1) (by simp)

end InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
