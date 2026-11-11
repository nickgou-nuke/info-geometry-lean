/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.PluckerLinearComplexGeometry
import InfoGeometry.Projective.PluckerComplexPencil
import InfoGeometry.Projective.PluckerQuadraticComplex
import InfoGeometry.Projective.PluckerPeirceBracket

/-!
# Axiom audit for the Plücker complex and Peirce development

Every public definition and theorem in the five new mathematical owners is
listed below. The concrete final examples check the zero-complex boundary
and characteristic two, and exhibit a real pencil with no real special member.
-/

#print axioms InfoGeometry.Projective.PluckerLinearComplex.complexMatrix
#print axioms InfoGeometry.Projective.PluckerLinearComplex.complexForm
#print axioms InfoGeometry.Projective.PluckerLinearComplex.complexMatrix_det
#print axioms InfoGeometry.Projective.PluckerLinearComplex.complexForm_isAlt
#print axioms InfoGeometry.Projective.PluckerLinearComplex.complexForm_zero_iff_swap
#print axioms InfoGeometry.Projective.PluckerLinearComplex.complexForm_scale
#print axioms InfoGeometry.Projective.PluckerLinearComplex.polarSubmodule
#print axioms InfoGeometry.Projective.PluckerLinearComplex.mem_polarSubmodule_self
#print axioms InfoGeometry.Projective.PluckerLinearComplex.polarSubmodule_smul_point
#print axioms InfoGeometry.Projective.PluckerLinearComplex.polarSubmodule_scale
#print axioms InfoGeometry.Projective.PluckerLinearComplex.complexForm_nondegenerate_iff
#print axioms InfoGeometry.Projective.PluckerLinearComplex.complexForm_apply_ne_zero
#print axioms InfoGeometry.Projective.PluckerLinearComplex.finrank_polarSubmodule

#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.nativeCoordinates
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.nativeComplexForm
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.nativeComplexForm_apply
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.nativeComplexForm_isAlt
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.lineComplex
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.mem_lineComplex_frameSpan_iff
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.mem_lineComplex_linePlucker_iff
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.forall_det_rows_eq_zero_iff_mem_frameSpan
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.ker_nativeComplexForm_linePlucker
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.finrank_ker_nativeComplexForm_linePlucker
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.polar_ker_eq_top_iff_mem_directrix
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.exists_frame_of_special
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.special_complex_exists_directrix
#print axioms InfoGeometry.Projective.PluckerLinearComplexGeometry.finrank_ker_of_special

#print axioms InfoGeometry.Projective.PluckerComplexPencil.complexForm_add
#print axioms InfoGeometry.Projective.PluckerComplexPencil.kleinQ_homogeneous_pencil
#print axioms InfoGeometry.Projective.PluckerComplexPencil.pencil_nondegenerate_iff
#print axioms InfoGeometry.Projective.PluckerComplexPencil.nativeComplexForm_pencil
#print axioms InfoGeometry.Projective.PluckerComplexPencil.mem_lineComplex_pencil_of_mem
#print axioms InfoGeometry.Projective.PluckerComplexPencil.lineComplex_inter_pencil
#print axioms InfoGeometry.Projective.PluckerComplexPencil.special_pencil_exists_directrix

#print axioms InfoGeometry.Projective.PluckerQuadraticComplex.quadraticComplex
#print axioms InfoGeometry.Projective.PluckerQuadraticComplex.quadraticComplex_add_klein
#print axioms InfoGeometry.Projective.PluckerQuadraticComplex.polarComplexForm
#print axioms InfoGeometry.Projective.PluckerQuadraticComplex.polarComplexForm_symm
#print axioms InfoGeometry.Projective.PluckerQuadraticComplex.polarComplexForm_self
#print axioms InfoGeometry.Projective.PluckerQuadraticComplex.polarComplexForm_self_eq_zero_iff
#print axioms InfoGeometry.Projective.PluckerQuadraticComplex.polarComplexForm_zero_iff_swap

#print axioms InfoGeometry.Projective.PluckerPeirceBracket.peirce_two_step_product
#print axioms InfoGeometry.Projective.PluckerPeirceBracket.peirce_two_step_commutator
#print axioms InfoGeometry.Projective.PluckerPeirceBracket.step
#print axioms InfoGeometry.Projective.PluckerPeirceBracket.step_mul
#print axioms InfoGeometry.Projective.PluckerPeirceBracket.step_commutator
#print axioms InfoGeometry.Projective.PluckerPeirceBracket.step_commutator_of_klein

open InfoGeometry.Projective.PluckerLinearComplex
open InfoGeometry.Projective.PluckerLinearComplexGeometry

example :
    (complexForm (⟨1, 0, 0, 0, 0, 1⟩ :
      InfoGeometry.Projective.KleinQuadric.Plucker6 (ZMod 2))).Nondegenerate := by
  rw [complexForm_nondegenerate_iff]
  norm_num [InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ]

example :
    nativeComplexForm (⟨0, 0, 0, 0, 0, 0⟩ :
      InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ) = 0 := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  rw [nativeComplexForm_apply]
  simp [InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm]

open InfoGeometry.Projective.KleinQuadric

/-- The finite members have Klein value `1 + μ²`, so the unconditional
claim of two real directrices would be false. The member at infinity also
has Klein value one, as checked by the following example. -/
example (μ : ℝ) :
    (complexForm (Plucker6.add (⟨1, 0, 0, 0, 0, 1⟩ : Plucker6 ℝ)
      (Plucker6.scale μ ⟨0, 1, 0, 0, -1, 0⟩))).Nondegenerate := by
  rw [complexForm_nondegenerate_iff, Plucker6.kleinQ_add_scale]
  norm_num [Plucker6.kleinQ, Plucker6.polar_formula]
  positivity

example : (complexForm (⟨0, 1, 0, 0, -1, 0⟩ : Plucker6 ℝ)).Nondegenerate := by
  rw [complexForm_nondegenerate_iff]
  norm_num [Plucker6.kleinQ]
