import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

set_option linter.unusedSectionVars false

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RealDoubledChiralKreinBridge

Thin canonical bridge from the real doubled chiral Krein owner file.

This file only re-exports closed finite block/off-block facts from the real
doubled Krein surface. It does not introduce any complex-analytic language or
any flow-level claims.
-/

namespace InfoGeometry.Canonical.RealDoubledChiralKreinBridge

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- The chiral grading is block-diagonal with respect to itself. -/
theorem gamma5_isBlockDiagonal :
    IsBlockDiagonal (gamma5 (E := E)) :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.gamma5_isBlockDiagonal (E := E)

/-- The chiral/off-block metric exchanges chiral sectors. -/
theorem etaChiral_isOffBlockDiagonal :
    IsOffBlockDiagonal (etaChiral (E := E)) :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.etaChiral_isOffBlockDiagonal (E := E)

/-- The split metric is block-diagonal with respect to the chiral grading. -/
theorem etaSplit_isBlockDiagonal [CompleteSpace E] :
    IsBlockDiagonal (etaSplit (E := E)) :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.etaSplit_isBlockDiagonal (E := E)

/-- The chiral grading is an involution. -/
theorem gamma5_involution :
    (gamma5 (E := E)).comp (gamma5 (E := E)) =
      ContinuousLinearMap.id ℝ H₂ :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.gamma5_involution (E := E)

/-- The off-block chiral Liouvillean squares to a block-diagonal operator. -/
theorem RealChiralLiouvillean.square_isBlock [CompleteSpace E]
    (L : RealChiralLiouvillean (E := E)) :
    L.L.comp L.L ∈ blockDiagonalSubmodule (E := E) :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.RealChiralLiouvillean.square_isBlock (E := E) L

/-- The left chiral projector keeps the first doubled component. -/
theorem leftChiralProjector_to_doubled
    (x ξ : E) :
    leftChiralProjector (E := E) (to_doubled x ξ : H₂) =
      to_doubled x 0 :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.leftChiralProjector_to_doubled (E := E) x ξ

/-- The right chiral projector keeps the second doubled component. -/
theorem rightChiralProjector_to_doubled
    (x ξ : E) :
    rightChiralProjector (E := E) (to_doubled x ξ : H₂) =
      to_doubled 0 ξ :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.rightChiralProjector_to_doubled (E := E) x ξ

/-- The off-block chiral metric intertwines the left projector with the right one. -/
theorem etaChiral_comp_left_projector :
    (etaChiral (E := E)).comp (leftChiralProjector (E := E)) =
      (rightChiralProjector (E := E)).comp (etaChiral (E := E)) :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.etaChiral_comp_left_projector (E := E)

/-- The off-block chiral metric intertwines the right projector with the left one. -/
theorem etaChiral_comp_right_projector :
    (etaChiral (E := E)).comp (rightChiralProjector (E := E)) =
      (leftChiralProjector (E := E)).comp (etaChiral (E := E)) :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.etaChiral_comp_right_projector (E := E)

end Core

end InfoGeometry.Canonical.RealDoubledChiralKreinBridge
