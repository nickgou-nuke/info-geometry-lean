import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import proofs.BraidProject.BraidGroup
import InfoGeometry.Categorical.FibonacciBraidGroup3Representation
import InfoGeometry.Categorical.HadjiivanovBraidGroupColimit

/-!
# Canonical equivalence of the repository's two B₃ presentations

The repository contains two theorem-honest presentations of the three-strand
braid group:

* `InfoGeometry.Categorical.FibonacciBraidGroup3Representation.BraidGroup3`,
  presented by an inductive two-generator type;
* `Braid.braid_group 3`, the `n = 3` stage of the general finite braid-group
  tower in `proofs/BraidProject/BraidGroup`.

This file proves they are canonically isomorphic by matching their two Artin
generators.  No new presentation is introduced.
-/

noncomputable section

namespace InfoGeometry.Categorical.BraidGroup3PresentationBridge

open Braid
open InfoGeometry.Categorical.FibonacciBraidGroup3Representation

/-- The two standard generators of `Braid.braid_group 3` form Artin data for
the generic two-generator `BraidGroup3` owner. -/
def braidProjectB3Generators :
    BraidThreeGenerators (braid_group 3) where
  sigmaOne := σ' 2 (0 : Fin 2)
  sigmaTwo := σ' 2 (1 : Fin 2)
  artin := by
    have h := braid_group.braid (n := 0) (i := (0 : Fin 1))
    simpa [σ, σ'] using h

/-- Canonical homomorphism from the newer two-generator presentation to the
`BraidProject` stage `B₃`. -/
def presentedB3ToBraidProject : BraidGroup3 →* braid_group 3 :=
  braidProjectB3Generators.toGroupHom

@[simp]
theorem presentedB3ToBraidProject_sigmaOne :
    presentedB3ToBraidProject sigmaOne = σ' 2 (0 : Fin 2) := by
  simp [presentedB3ToBraidProject, braidProjectB3Generators]

@[simp]
theorem presentedB3ToBraidProject_sigmaTwo :
    presentedB3ToBraidProject sigmaTwo = σ' 2 (1 : Fin 2) := by
  simp [presentedB3ToBraidProject, braidProjectB3Generators]

/-- Generator map in the reverse direction. -/
def braidProjectGeneratorToPresented : Fin 2 → BraidGroup3 := fun i =>
  if i = 0 then sigmaOne else sigmaTwo

@[simp]
theorem braidProjectGeneratorToPresented_zero :
    braidProjectGeneratorToPresented (0 : Fin 2) = sigmaOne := by
  simp [braidProjectGeneratorToPresented]

@[simp]
theorem braidProjectGeneratorToPresented_one :
    braidProjectGeneratorToPresented (1 : Fin 2) = sigmaTwo := by
  simp [braidProjectGeneratorToPresented]

/-- The two `BraidGroup3` generators satisfy every relation in the
`BraidProject` stage presentation `braid_rels 2`. -/
theorem presentedGenerators_satisfy_braidProject_relations :
    ∀ r ∈ braid_rels 2,
      FreeGroup.lift braidProjectGeneratorToPresented r = (1 : BraidGroup3) := by
  intro r hr
  change
    (∃ i : Fin 1, r = braid_rel i.castSucc i.succ) ∨
      (∃ i j : Fin 0, i ≤ j ∧
        r = comm_rel i.castSucc.castSucc j.succ.succ) at hr
  rcases hr with hAdj | hFar
  · rcases hAdj with ⟨i, rfl⟩
    fin_cases i
    have hArtin := braidGroup3_artin
    exact InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.freeGroup_lift_braid_relator
      braidProjectGeneratorToPresented (0 : Fin 2) (1 : Fin 2) hArtin
  · rcases hFar with ⟨i, j, hij, hr⟩
    exact i.elim0

/-- Canonical homomorphism from `BraidProject`'s `B₃` stage to the newer
`BraidGroup3` owner. -/
def braidProjectToPresentedB3 : braid_group 3 →* BraidGroup3 :=
  PresentedGroup.toGroup
    (f := braidProjectGeneratorToPresented)
    (rels := braid_rels 2)
    presentedGenerators_satisfy_braidProject_relations

@[simp]
theorem braidProjectToPresentedB3_sigmaZero :
    braidProjectToPresentedB3 (σ' 2 (0 : Fin 2)) = sigmaOne := by
  change PresentedGroup.toGroup
      (f := braidProjectGeneratorToPresented)
      (rels := braid_rels 2)
      presentedGenerators_satisfy_braidProject_relations
      (PresentedGroup.of (0 : Fin 2)) = sigmaOne
  exact PresentedGroup.toGroup.of
    (x := (0 : Fin 2)) presentedGenerators_satisfy_braidProject_relations

@[simp]
theorem braidProjectToPresentedB3_sigmaOneIndex :
    braidProjectToPresentedB3 (σ' 2 (1 : Fin 2)) = sigmaTwo := by
  change PresentedGroup.toGroup
      (f := braidProjectGeneratorToPresented)
      (rels := braid_rels 2)
      presentedGenerators_satisfy_braidProject_relations
      (PresentedGroup.of (1 : Fin 2)) = sigmaTwo
  exact PresentedGroup.toGroup.of
    (x := (1 : Fin 2)) presentedGenerators_satisfy_braidProject_relations

/-- Reverse-after-forward is the identity on the newer `BraidGroup3`. -/
theorem braidProjectToPresented_comp_presentedToBraidProject :
    braidProjectToPresentedB3.comp presentedB3ToBraidProject =
      MonoidHom.id BraidGroup3 := by
  apply PresentedGroup.ext
  intro g
  cases g
  · change braidProjectToPresentedB3
      (presentedB3ToBraidProject sigmaOne) = sigmaOne
    rw [presentedB3ToBraidProject_sigmaOne,
      braidProjectToPresentedB3_sigmaZero]
  · change braidProjectToPresentedB3
      (presentedB3ToBraidProject sigmaTwo) = sigmaTwo
    rw [presentedB3ToBraidProject_sigmaTwo,
      braidProjectToPresentedB3_sigmaOneIndex]

/-- Forward-after-reverse is the identity on `BraidProject`'s `B₃`. -/
theorem presentedToBraidProject_comp_braidProjectToPresented :
    presentedB3ToBraidProject.comp braidProjectToPresentedB3 =
      MonoidHom.id (braid_group 3) := by
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · change presentedB3ToBraidProject
      (braidProjectToPresentedB3 (σ' 2 (0 : Fin 2))) = σ' 2 (0 : Fin 2)
    rw [braidProjectToPresentedB3_sigmaZero,
      presentedB3ToBraidProject_sigmaOne]
  · change presentedB3ToBraidProject
      (braidProjectToPresentedB3 (σ' 2 (1 : Fin 2))) = σ' 2 (1 : Fin 2)
    rw [braidProjectToPresentedB3_sigmaOneIndex,
      presentedB3ToBraidProject_sigmaTwo]

/-- Canonical multiplicative equivalence between the two repository `B₃`
presentations. -/
def braidGroup3MulEquiv : BraidGroup3 ≃* braid_group 3 where
  toFun := presentedB3ToBraidProject
  invFun := braidProjectToPresentedB3
  left_inv := by
    intro g
    exact congrArg (fun f => f g)
      braidProjectToPresented_comp_presentedToBraidProject
  right_inv := by
    intro g
    exact congrArg (fun f => f g)
      presentedToBraidProject_comp_braidProjectToPresented
  map_mul' := by
    intro a b
    exact presentedB3ToBraidProject.map_mul a b

end InfoGeometry.Categorical.BraidGroup3PresentationBridge
