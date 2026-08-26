/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2ArtinPresentation
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2

/-!
# G₂ Artin-to-Weyl quotient bridge

The native presentation owner already supplies the quotient action
`coordinateAction : ArtinG2 →* Equiv.Perm G2CoordinateRoot`.  This owner
exposes its longest-element readback without introducing a second Weyl
carrier or a duplicate presentation.
-/

namespace InfoGeometry.Exceptional.G2ArtinWeylBridge

open InfoGeometry.Exceptional.G2ArtinPresentation
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

noncomputable section

theorem artinToWeyl_garside :
    coordinateAction G2ArtinPresentation.garside =
      dihedralToPerm
        InfoGeometry.Algebra.Zorn.G2LongestElementBridge.g2LongestNF := by
  exact G2ArtinPresentation.garsideWord_is_longest_readback

theorem artinToWeyl_garside_sq :
    coordinateAction
        (G2ArtinPresentation.garside * G2ArtinPresentation.garside) = 1 := by
  rw [map_mul, artinToWeyl_garside]
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

/-! ## Concrete automorphism target

The coordinate-root action above is the finite normal-form readback.  The
following homomorphism is the corresponding map into the existing concrete
split-octonion automorphism group; it does not introduce a second Weyl
carrier.
-/

theorem concrete_simple_reflections_relation :
    s * t * s * t * s * t = t * s * t * s * t * s := by
  exact st_artin_braid_relation

private def concreteAssignment :
    G2ArtinPresentation.Generator →
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut
  | 0 => s
  | 1 => t

private theorem concreteRelationRespected :
    ∀ r ∈ G2ArtinPresentation.relations,
      FreeGroup.lift concreteAssignment r = 1 := by
  intro r hr
  have hr' : r = G2ArtinPresentation.relation := by
    simpa [G2ArtinPresentation.relations] using hr
  subst r
  simpa only [G2ArtinPresentation.relation, map_mul, map_inv,
    FreeGroup.lift_apply_of] using
    (show s * t * s * t * s * t *
        (t * s * t * s * t * s)⁻¹ =
      (1 : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) by
      exact mul_inv_eq_one.mpr concrete_simple_reflections_relation)

noncomputable def concreteAction :
    G2ArtinPresentation.ArtinG2 →*
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut :=
  PresentedGroup.toGroup (f := concreteAssignment)
    (rels := G2ArtinPresentation.relations) concreteRelationRespected

@[simp] theorem concreteAction_sigmaZero :
    concreteAction G2ArtinPresentation.sigmaZero = s := by
  change PresentedGroup.toGroup (f := concreteAssignment)
    (rels := G2ArtinPresentation.relations) concreteRelationRespected
      (PresentedGroup.of 0) = s
  rw [PresentedGroup.toGroup.of]
  rfl

@[simp] theorem concreteAction_sigmaOne :
    concreteAction G2ArtinPresentation.sigmaOne = t := by
  change PresentedGroup.toGroup (f := concreteAssignment)
    (rels := G2ArtinPresentation.relations) concreteRelationRespected
      (PresentedGroup.of 1) = t
  rw [PresentedGroup.toGroup.of]
  rfl

theorem concreteAction_garside :
    concreteAction G2ArtinPresentation.garside = c ^ 3 := by
  have h0 : concreteAction (PresentedGroup.of 0) = s := by
    simpa [G2ArtinPresentation.sigmaZero] using concreteAction_sigmaZero
  have h1 : concreteAction (PresentedGroup.of 1) = t := by
    simpa [G2ArtinPresentation.sigmaOne] using concreteAction_sigmaOne
  change concreteAction (PresentedGroup.of 0 * PresentedGroup.of 1 *
    PresentedGroup.of 0 * PresentedGroup.of 1 * PresentedGroup.of 0 *
    PresentedGroup.of 1) = c ^ 3
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, h0, h1]
  have hst : s * t = c := by
    dsimp [t]
    rw [← mul_assoc, s_sq, one_mul]
  calc
    s * t * s * t * s * t = (s * t) ^ 3 := by
      simp [pow_succ, mul_assoc]
    _ = c ^ 3 := by rw [hst]

theorem concreteAction_garside_eq_swapCartan :
    concreteAction G2ArtinPresentation.garside = swapCartanAut := by
  rw [concreteAction_garside, c_pow_three_eq_swapCartan]

theorem concreteAction_garside_sq :
    concreteAction
        (G2ArtinPresentation.garside * G2ArtinPresentation.garside) = 1 := by
  rw [map_mul, concreteAction_garside_eq_swapCartan, swapCartanAut_sq]

theorem concreteAction_garside_up0 :
    (concreteAction G2ArtinPresentation.garside).1
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.up0 =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.down0 := by
  rw [concreteAction_garside]
  exact c_cube_up0

end

end InfoGeometry.Exceptional.G2ArtinWeylBridge
