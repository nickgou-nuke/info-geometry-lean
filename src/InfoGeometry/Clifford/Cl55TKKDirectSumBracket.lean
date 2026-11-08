/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Lie.TransferInstance
import InfoGeometry.Clifford.Cl55TKKGradeReversalDirectSum

set_option autoImplicit false

/-!
# The commutator bracket on the external five-grade carrier

The bracket is transported across the established reconstruction equivalence.
The component theorem records its exact value on homogeneous direct-sum
inclusions, using the ambient TKK grade-closure theorem.
-/

namespace InfoGeometry.Clifford.Cl55SuperTKK

open scoped DirectSum

private theorem tkkFiveGradeSubmodule_eq_grade_local (i : Fin 5) :
    tkkFiveGradeSubmodule i = tkkGrade (tkkFiveGradeValue i) := by
  ext X
  simp only [tkkFiveGradeSubmodule, tkkGrade, Module.End.mem_eigenspace_iff]
  rfl

/-- Transport the concrete `EndV` commutator to the external five-grade
direct sum. -/
noncomputable def tkkFiveGradeDirectSumBracket
    (x y : TkkFiveGradeSum) : TkkFiveGradeSum :=
  tkkFiveGradeDirectSumEquiv.symm
    (tkkBracket (tkkFiveGradeDirectSumEquiv x)
      (tkkFiveGradeDirectSumEquiv y))

/-- On homogeneous `lof` inputs, the transported bracket is exactly the
`lof` inclusion of the ambient bracket in the specified target grade. -/
theorem tkkFiveGradeDirectSumBracket_lof
    {i j k : Fin 5} (x : TkkFiveGradeCarrier i)
    (y : TkkFiveGradeCarrier j)
    (hbr : tkkBracket (x : EndV) (y : EndV) ∈ tkkFiveGradeSubmodule k) :
    tkkFiveGradeDirectSumBracket
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier i x)
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier j y) =
      DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier k
        ⟨tkkBracket (x : EndV) (y : EndV), hbr⟩ := by
  apply tkkFiveGradeDirectSumEquiv.injective
  simp only [tkkFiveGradeDirectSumBracket,
    LinearEquiv.apply_symm_apply]
  change tkkBracket
      (DirectSum.coeLinearMap tkkFiveGradeSubmodule
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier i x))
      (DirectSum.coeLinearMap tkkFiveGradeSubmodule
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier j y)) =
    DirectSum.coeLinearMap tkkFiveGradeSubmodule
      (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier k
        ⟨tkkBracket (x : EndV) (y : EndV), hbr⟩)
  rw [DirectSum.coeLinearMap_lof, DirectSum.coeLinearMap_lof,
    DirectSum.coeLinearMap_lof]

/-- Ambient grade closure supplies the membership proof required by the
homogeneous external bracket readout whenever the five-grade labels add. -/
theorem tkkFiveGradeDirectSumBracket_lof_grade
    {i j k : Fin 5}
    (hij : tkkFiveGradeValue i + tkkFiveGradeValue j =
      tkkFiveGradeValue k)
    (x : TkkFiveGradeCarrier i) (y : TkkFiveGradeCarrier j) :
    tkkBracket (x : EndV) (y : EndV) ∈ tkkFiveGradeSubmodule k := by
  rw [tkkFiveGradeSubmodule_eq_grade_local]
  apply tkk_bracket_grade_add hij
  · simpa only [tkkFiveGradeSubmodule_eq_grade_local] using x.property
  · simpa only [tkkFiveGradeSubmodule_eq_grade_local] using y.property

/-- The external bracket closes in the grade indexed by the sum of the
input grades, provided that sum is one of the five represented grades. -/
theorem tkkFiveGradeDirectSumBracket_lof_grade_add
    {i j k : Fin 5}
    (hij : tkkFiveGradeValue i + tkkFiveGradeValue j =
      tkkFiveGradeValue k)
    (x : TkkFiveGradeCarrier i) (y : TkkFiveGradeCarrier j) :
    tkkFiveGradeDirectSumBracket
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier i x)
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier j y) =
      DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier k
        ⟨tkkBracket (x : EndV) (y : EndV),
          tkkFiveGradeDirectSumBracket_lof_grade hij x y⟩ := by
  exact tkkFiveGradeDirectSumBracket_lof x y
    (tkkFiveGradeDirectSumBracket_lof_grade hij x y)

/-- A homogeneous external bracket vanishes when the summed grade lies
outside the five grades represented by `Fin 5`. -/
theorem tkkFiveGradeDirectSumBracket_lof_eq_zero_of_grade_sum_outside
    {i j : Fin 5} (x : TkkFiveGradeCarrier i)
    (y : TkkFiveGradeCarrier j)
    (hOut : tkkFiveGradeValue i + tkkFiveGradeValue j < -2 ∨
      2 < tkkFiveGradeValue i + tkkFiveGradeValue j) :
    tkkFiveGradeDirectSumBracket
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier i x)
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier j y) = 0 := by
  apply tkkFiveGradeDirectSumEquiv.injective
  simp only [tkkFiveGradeDirectSumBracket,
    LinearEquiv.apply_symm_apply]
  change tkkBracket
      (DirectSum.coeLinearMap tkkFiveGradeSubmodule
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier i x))
      (DirectSum.coeLinearMap tkkFiveGradeSubmodule
        (DirectSum.lof ℝ (Fin 5) TkkFiveGradeCarrier j y)) = 0
  rw [DirectSum.coeLinearMap_lof, DirectSum.coeLinearMap_lof]
  apply tkkBracket_eq_zero_of_grade_sum_outside
  · simpa only [tkkFiveGradeSubmodule_eq_grade_local] using x.property
  · simpa only [tkkFiveGradeSubmodule_eq_grade_local] using y.property
  · exact hOut

/-- The direct-sum grade-reversal action preserves the binary bracket
transported from the concrete `EndV` commutator. This compatibility theorem
is stated directly for the named operation; it does not itself choose one of
the named Lie structures introduced below. -/
theorem tkkFiveGradeDirectSumReverseAction_preserves_bracket
    (x y : TkkFiveGradeSum) :
    tkkFiveGradeDirectSumReverseAction
        (tkkFiveGradeDirectSumBracket x y) =
      tkkFiveGradeDirectSumBracket
        (tkkFiveGradeDirectSumReverseAction x)
        (tkkFiveGradeDirectSumReverseAction y) := by
  apply tkkFiveGradeDirectSumEquiv.injective
  have hintertwines (z : TkkFiveGradeSum) :
      tkkFiveGradeDirectSumEquiv.toLinearMap
          (tkkFiveGradeDirectSumReverseAction z) =
        idealModularConjugationAction
          (tkkFiveGradeDirectSumEquiv.toLinearMap z) := by
    have h := congrArg
      (fun f : TkkFiveGradeSum →ₗ[ℝ] EndV => f z)
      tkkFiveGradeDirectSumReverseAction_intertwines_reconstruction
    simpa only [LinearMap.comp_apply] using h
  have hbracket (a b : TkkFiveGradeSum) :
      tkkFiveGradeDirectSumEquiv.toLinearMap
          (tkkFiveGradeDirectSumBracket a b) =
        tkkBracket (tkkFiveGradeDirectSumEquiv.toLinearMap a)
          (tkkFiveGradeDirectSumEquiv.toLinearMap b) := by
    change tkkFiveGradeDirectSumEquiv
        (tkkFiveGradeDirectSumEquiv.symm
          (tkkBracket (tkkFiveGradeDirectSumEquiv a)
            (tkkFiveGradeDirectSumEquiv b))) = _
    exact tkkFiveGradeDirectSumEquiv.apply_symm_apply _
  change tkkFiveGradeDirectSumEquiv.toLinearMap
        (tkkFiveGradeDirectSumReverseAction
          (tkkFiveGradeDirectSumBracket x y)) =
      tkkFiveGradeDirectSumEquiv.toLinearMap
        (tkkFiveGradeDirectSumBracket
          (tkkFiveGradeDirectSumReverseAction x)
          (tkkFiveGradeDirectSumReverseAction y))
  calc
    tkkFiveGradeDirectSumEquiv.toLinearMap
        (tkkFiveGradeDirectSumReverseAction
          (tkkFiveGradeDirectSumBracket x y))
        = idealModularConjugationAction
            (tkkFiveGradeDirectSumEquiv.toLinearMap
              (tkkFiveGradeDirectSumBracket x y)) :=
          hintertwines (tkkFiveGradeDirectSumBracket x y)
    _ = tkkBracket
          (idealModularConjugationAction
            (tkkFiveGradeDirectSumEquiv.toLinearMap x))
          (idealModularConjugationAction
            (tkkFiveGradeDirectSumEquiv.toLinearMap y)) := by
          rw [hbracket]
          exact idealModularConjugationAction_preserves_tkkBracket
            (tkkFiveGradeDirectSumEquiv.toLinearMap x)
            (tkkFiveGradeDirectSumEquiv.toLinearMap y)
    _ = tkkBracket
          (tkkFiveGradeDirectSumEquiv.toLinearMap
            (tkkFiveGradeDirectSumReverseAction x))
          (tkkFiveGradeDirectSumEquiv.toLinearMap
            (tkkFiveGradeDirectSumReverseAction y)) := by
          rw [← hintertwines x, ← hintertwines y]
    _ = tkkFiveGradeDirectSumEquiv.toLinearMap
          (tkkFiveGradeDirectSumBracket
            (tkkFiveGradeDirectSumReverseAction x)
            (tkkFiveGradeDirectSumReverseAction y)) := by
          exact (hbracket
            (tkkFiveGradeDirectSumReverseAction x)
            (tkkFiveGradeDirectSumReverseAction y)).symm

/-- The transported commutator on the external five-grade direct sum
satisfies the cyclic Jacobi identity. This theorem is proved directly from
the reconstruction equivalence, independently of the named Lie-ring
structure introduced below. -/
theorem tkkFiveGradeDirectSumBracket_jacobi
    (x y z : TkkFiveGradeSum) :
    tkkFiveGradeDirectSumBracket x
        (tkkFiveGradeDirectSumBracket y z) +
      tkkFiveGradeDirectSumBracket y
        (tkkFiveGradeDirectSumBracket z x) +
      tkkFiveGradeDirectSumBracket z
        (tkkFiveGradeDirectSumBracket x y) = 0 := by
  letI : LieRing EndV := LieRing.ofAssociativeRing
  have ambientJacobi (X Y Z : EndV) :
      tkkBracket X (tkkBracket Y Z) +
        tkkBracket Y (tkkBracket Z X) +
        tkkBracket Z (tkkBracket X Y) = 0 := by
    simpa only [tkkBracket, LieRing.of_associative_ring_bracket] using
      (lie_jacobi X Y Z)
  apply tkkFiveGradeDirectSumEquiv.injective
  simp only [map_zero]
  have hbracket (a b : TkkFiveGradeSum) :
      tkkFiveGradeDirectSumEquiv
          (tkkFiveGradeDirectSumBracket a b) =
        tkkBracket (tkkFiveGradeDirectSumEquiv a)
          (tkkFiveGradeDirectSumEquiv b) := by
    change tkkFiveGradeDirectSumEquiv
          (tkkFiveGradeDirectSumEquiv.symm
            (tkkBracket (tkkFiveGradeDirectSumEquiv a)
              (tkkFiveGradeDirectSumEquiv b))) = _
    exact tkkFiveGradeDirectSumEquiv.apply_symm_apply _
  calc
    tkkFiveGradeDirectSumEquiv
        (tkkFiveGradeDirectSumBracket x
            (tkkFiveGradeDirectSumBracket y z) +
          tkkFiveGradeDirectSumBracket y
            (tkkFiveGradeDirectSumBracket z x) +
          tkkFiveGradeDirectSumBracket z
            (tkkFiveGradeDirectSumBracket x y))
        = tkkBracket (tkkFiveGradeDirectSumEquiv x)
            (tkkBracket (tkkFiveGradeDirectSumEquiv y)
              (tkkFiveGradeDirectSumEquiv z)) +
          tkkBracket (tkkFiveGradeDirectSumEquiv y)
            (tkkBracket (tkkFiveGradeDirectSumEquiv z)
              (tkkFiveGradeDirectSumEquiv x)) +
          tkkBracket (tkkFiveGradeDirectSumEquiv z)
            (tkkBracket (tkkFiveGradeDirectSumEquiv x)
              (tkkFiveGradeDirectSumEquiv y)) := by
          simp only [map_add, hbracket]
    _ = 0 := by
          exact ambientJacobi (tkkFiveGradeDirectSumEquiv x)
            (tkkFiveGradeDirectSumEquiv y)
            (tkkFiveGradeDirectSumEquiv z)

/-- A named Lie-ring structure for the external five-grade carrier, using
the bracket transported from `EndV`. This is deliberately not registered as
a global instance, so downstream code opts into its notation locally. -/
@[instance_reducible]
noncomputable def tkkFiveGradeDirectSumLieRing :
    LieRing TkkFiveGradeSum := by
  letI : LieRing EndV := LieRing.ofAssociativeRing
  exact tkkFiveGradeDirectSumEquiv.toAddEquiv.lieRing

/-- The explicitly transported `LieRing` uses the same binary operation as
the independently named external bracket. -/
theorem tkkFiveGradeDirectSumLieRing_bracket
    (x y : TkkFiveGradeSum) :
    letI := tkkFiveGradeDirectSumLieRing
    ⁅x, y⁆ = tkkFiveGradeDirectSumBracket x y := by
  letI : LieRing TkkFiveGradeSum := tkkFiveGradeDirectSumLieRing
  letI : LieRing EndV := LieRing.ofAssociativeRing
  change ⁅x, y⁆ = _
  rw [AddEquiv.bracket_def]
  rfl

/-- The real Lie-algebra structure transported to the external five-grade
direct sum. It uses the named transported `LieRing` above and is deliberately
not installed as a global instance. -/
@[instance_reducible]
noncomputable def tkkFiveGradeDirectSumLieAlgebra :
    letI := tkkFiveGradeDirectSumLieRing
    LieAlgebra ℝ TkkFiveGradeSum := by
  letI : LieRing TkkFiveGradeSum := tkkFiveGradeDirectSumLieRing
  refine { toModule := inferInstance, lie_smul := ?_ }
  intro r x y
  letI : LieRing EndV := LieRing.ofAssociativeRing
  change tkkFiveGradeDirectSumEquiv.symm
      ⁅tkkFiveGradeDirectSumEquiv x,
        tkkFiveGradeDirectSumEquiv (r • y)⁆ =
    r • tkkFiveGradeDirectSumEquiv.symm
      ⁅tkkFiveGradeDirectSumEquiv x,
        tkkFiveGradeDirectSumEquiv y⁆
  rw [map_smul, lie_smul, map_smul]

/-- Reconstruction preserves the transported bracket as a real linear
equivalence. This is the bracket-compatibility content of a Lie equivalence,
stated without changing the external direct-sum's existing module instance. -/
theorem tkkFiveGradeDirectSumEquiv_map_bracket
    (x y : TkkFiveGradeSum) :
    letI := tkkFiveGradeDirectSumLieRing
    tkkFiveGradeDirectSumEquiv ⁅x, y⁆ =
      ⁅tkkFiveGradeDirectSumEquiv x,
        tkkFiveGradeDirectSumEquiv y⁆ := by
  letI : LieRing EndV := LieRing.ofAssociativeRing
  letI := tkkFiveGradeDirectSumLieRing
  change tkkFiveGradeDirectSumEquiv
      (tkkFiveGradeDirectSumEquiv.symm
        ⁅tkkFiveGradeDirectSumEquiv x,
          tkkFiveGradeDirectSumEquiv y⁆) = _
  exact tkkFiveGradeDirectSumEquiv.apply_symm_apply _

end InfoGeometry.Clifford.Cl55SuperTKK
