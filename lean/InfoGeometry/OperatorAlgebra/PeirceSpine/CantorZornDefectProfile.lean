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

/-- On the operator-Zorn carrier, every nonzero left-multiplication defect
has a nonzero component in the native five-grade decomposition. -/
theorem zornDefect_has_fiveGrade_support
    {A : Type*} [Ring A]
    (X Y : InfoGeometry.Canonical.OperatorZornMatrix A)
    (hD : InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y ≠ 0) :
    ∃ d : Fin 5,
      InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
        (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d ≠ 0 :=
  InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport.ncZornMulDefect_has_nonzero_five_grade_component X Y hD

/-- Carrier-separated defect profile: the represented Cantor triple
associator vanishes, while any supplied nonzero Zorn multiplication defect
is detected by its five-grade components. No cross-carrier equality is
asserted. -/
theorem cantor_triple_and_zorn_fiveGrade_defects
    {Op A : Type*} [Ring Op] [StarRing Op] [Ring A]
    (C : InfoGeometry.Topology.CuntzO2Carrier Op)
    (p q r : Bool)
    (u v w : List InfoGeometry.OperatorAlgebra.ErlangenNet.BinarySector)
    (X Y : InfoGeometry.Canonical.OperatorZornMatrix A)
    (hD : InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y ≠ 0) :
    cantorTripleAssociatorResidual C p q r u v w = 0 ∧
      ∃ d : Fin 5,
        InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornFiveComponent
          (InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading.ncZornMulDefect X Y) d ≠ 0 :=
  ⟨cantorTripleAssociatorResidual_eq_zero C p q r u v w,
    zornDefect_has_fiveGrade_support X Y hD⟩

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
    exact zornDefect_has_fiveGrade_support X Y hD

/-- Evaluation-level carrier-separated profile: the represented Cantor
associator vanishes, while a nonzero operator-Zorn associator value at the
specified third input has a nonzero evaluated grade contribution. -/
theorem cantor_and_evaluated_zorn_defect_profile
    {Op A : Type*} [Ring Op] [StarRing Op] [Ring A]
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
