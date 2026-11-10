/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PositiveGrassmannianExteriorCantor
import InfoGeometry.Analysis.L2CantorCommutation
import InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport
import InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading

/-!
# Cantor triple associator and five-grade Zorn defect profile

This module records the two relevant defect readouts on their actual
carriers. The represented Cantor product has zero associator. A nonzero
operator-Zorn multiplication defect has a nonzero component in one of its
five grades. These statements are intentionally not identified: this module
does not postulate a map between the Cantor and operator-Zorn carriers.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.CantorZornDefectProfile

/-- The signed associator residual of the homogeneous triple Cantor product.
Its two terms are the two Koszul parenthesizations. -/
def cantorTripleAssociatorResidual {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Topology.CuntzO2Carrier Op)
    (p q r : Bool) (u v w : List InfoGeometry.OperatorAlgebra.ErlangenNet.BinarySector) : Op :=
  InfoGeometry.Canonical.PositiveGrassmannianExteriorCantor.cantorGradedTripleProduct
      C p q r u v w -
    InfoGeometry.Canonical.PositiveGrassmannianExteriorCantor.gradedProduct p
      (InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge.parityAdd q r)
      (InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge.cylinderOperator C u)
      (InfoGeometry.Canonical.PositiveGrassmannianExteriorCantor.cantorGradedProduct C q r v w)

/-- The Cantor triple associator residual vanishes by the existing graded
associator law. This says nothing about the distinct nonassociative Zorn
carrier. -/
theorem cantorTripleAssociatorResidual_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Topology.CuntzO2Carrier Op)
    (p q r : Bool) (u v w : List InfoGeometry.OperatorAlgebra.ErlangenNet.BinarySector) :
    cantorTripleAssociatorResidual C p q r u v w = 0 := by
  simp [cantorTripleAssociatorResidual,
    InfoGeometry.Canonical.PositiveGrassmannianExteriorCantor.cantorGradedProduct_associator]

/-- A left-multiplication defect is nonzero exactly when one of its five
native grade projections is nonzero. The forward direction uses exhaustive
five-grade support; the reverse direction follows because each projection
sends the zero endomorphism to zero. -/
theorem zornDefect_has_fiveGrade_support
    {A : Type*} [Ring A]
    (X Y : InfoGeometry.Canonical.OperatorZornMatrix A)
    : InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y ≠ 0 ↔
      ∃ d : Fin 5,
        InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
          (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d ≠ 0 := by
  constructor
  · exact InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport.ncZornMulDefect_has_nonzero_five_grade_component X Y
  · rintro ⟨d, hd⟩ hZero
    have hComponent := congrArg
      (fun K : Module.End ℤ (InfoGeometry.Canonical.OperatorZornMatrix A) =>
        InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent K d)
      hZero
    have hComponentZero :
        InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
          (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d = 0 := by
      have hZeroComponent :
          InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
              (0 : Module.End ℤ (InfoGeometry.Canonical.OperatorZornMatrix A)) d = 0 := by
        simp [InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent,
          InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornBlock]
        fin_cases d <;> rfl
      rw [hZeroComponent] at hComponent
      exact hComponent
    exact hd hComponentZero

/-- A nonzero operator-valued Zorn defect has an input at which one of its
five evaluated grade contributions is nonzero. This strengthens the
operator-level support theorem by exhibiting a witness in the carrier. -/
theorem cantor_triple_and_zorn_fiveGrade_defects
    {Op A : Type*} [Ring Op] [StarRing Op] [Ring A]
    (C : InfoGeometry.Topology.CuntzO2Carrier Op)
    (p q r : Bool)
    (u v w : List InfoGeometry.OperatorAlgebra.ErlangenNet.BinarySector)
    (X Y : InfoGeometry.Canonical.OperatorZornMatrix A)
    (hD : InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y ≠ 0) :
    cantorTripleAssociatorResidual C p q r u v w = 0 ∧
      ∃ Z : InfoGeometry.Canonical.OperatorZornMatrix A,
        ∃ d : Fin 5,
          InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
            (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d Z ≠ 0 := by
  have hInput : ∃ Z : InfoGeometry.Canonical.OperatorZornMatrix A,
      InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y Z ≠ 0 := by
    by_contra hNoInput
    apply hD
    apply LinearMap.ext
    intro Z
    by_contra hNZ
    exact hNoInput ⟨Z, hNZ⟩
  rcases hInput with ⟨Z, hZ⟩
  exact ⟨cantorTripleAssociatorResidual_eq_zero C p q r u v w, Z,
    (InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport.ncZornMulDefect_apply_has_nonzero_five_grade_component
      X Y Z hZ)⟩

/-- Full carrier-separated readout: the Cantor associator vanishes, while
the Zorn associator itself (not merely its nonvanishing support) is exactly
the sum of its five graded operator contributions. A supplied nonzero defect
also has at least one nonzero grade. -/
theorem cantor_and_full_zorn_defect_profile
    {Op A : Type*} [Ring Op] [StarRing Op] [Ring A]
    (C : InfoGeometry.Topology.CuntzO2Carrier Op)
    (p q r : Bool)
    (u v w : List InfoGeometry.OperatorAlgebra.ErlangenNet.BinarySector)
    (X Y Z : InfoGeometry.Canonical.OperatorZornMatrix A) :
    cantorTripleAssociatorResidual C p q r u v w = 0 ∧
      InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y Z =
        ∑ d : Fin 5,
          InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
            (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d Z ∧
      (∀ d : Fin 5,
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm
            (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornTripotent)
            (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
              (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d) =
          ((d.val : ℤ) - 2) •
            InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
              (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d) ∧
      (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y ≠ 0 →
        ∃ d : Fin 5,
          InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
            (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d ≠ 0) := by
  refine ⟨cantorTripleAssociatorResidual_eq_zero C p q r u v w, ?_, ?_, ?_⟩
  · exact InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport.ncZornMulDefect_associator_five_grade_expansion
      X Y Z
  · intro d
    exact InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent_comm_tripotent
      (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d
  · intro hD
    exact (zornDefect_has_fiveGrade_support X Y).mp hD

/-- At a fixed third input, the defect value is the sum of its five evaluated
grade contributions; if that value is nonzero, one contribution is nonzero.
Each endomorphism grade has its exact tripotent charge. -/
theorem cantor_and_evaluated_zorn_defect_profile
    {A : Type*} [Ring A]
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Topology.CuntzO2Carrier Op)
    (p q r : Bool)
    (u v w : List InfoGeometry.OperatorAlgebra.ErlangenNet.BinarySector)
    (X Y Z : InfoGeometry.Canonical.OperatorZornMatrix A)
    (hD : InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y Z ≠ 0) :
    cantorTripleAssociatorResidual C p q r u v w = 0 ∧
      InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y Z =
        ∑ d : Fin 5,
          InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
            (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d Z ∧
      (∃ d : Fin 5,
        InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
          (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d Z ≠ 0) ∧
      (∀ d : Fin 5,
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm
            (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornTripotent)
            (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
              (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d) =
          ((d.val : ℤ) - 2) •
            InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
              (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d) := by
  refine ⟨cantorTripleAssociatorResidual_eq_zero C p q r u v w, ?_, ?_, ?_⟩
  · exact InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport.ncZornMulDefect_associator_five_grade_expansion
      X Y Z
  · exact InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport.ncZornMulDefect_apply_has_nonzero_five_grade_component
      X Y Z hD
  · intro d
    exact InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent_comm_tripotent
      (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d

end InfoGeometry.OperatorAlgebra.PeirceSpine.CantorZornDefectProfile
