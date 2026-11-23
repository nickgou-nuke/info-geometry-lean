/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
import InfoGeometry.Canonical.PeirceBoundaryComplex
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
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements

section Core

attribute [local instance 100] LieRing.ofAssociativeRing

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

set_option linter.overlappingInstances false in
/-- The split metric is block-diagonal with respect to the chiral grading. -/
theorem etaSplit_isBlockDiagonal [CompleteSpace E] :
    IsBlockDiagonal (etaSplit (E := E)) :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.etaSplit_isBlockDiagonal (E := E)

/-- The chiral grading is an involution. -/
theorem gamma5_involution :
    (gamma5 (E := E)).comp (gamma5 (E := E)) =
      ContinuousLinearMap.id ℝ H₂ :=
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.gamma5_involution (E := E)

set_option linter.overlappingInstances false in
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

/-! ## Graded differential on the actual real chiral endomorphism algebra

The generic Peirce differential is now tied to the actual `DoubledSpace E`
carrier: its reflection is exactly `gamma5`, and its square is the inner
action of the square of an odd continuous endomorphism. -/

/-- The Peirce reflection of the real chiral projector is the existing
`gamma5` operator on `DoubledSpace E`. -/
theorem peirceReflection_leftChiralProjector_eq_gamma5 :
    InfoGeometry.Core.PeirceGrading.reflection
        (leftChiralProjector (E := E)) =
      gamma5 (E := E) := by
  change (2 : DoubledSpace E →L[ℝ] DoubledSpace E) *
      leftChiralProjector (E := E) - 1 = gamma5 (E := E)
  apply ContinuousLinearMap.ext
  intro u
  simp [leftChiralProjector, gamma5]
  module

/-- On the actual real doubled carrier, the Peirce differential uses `gamma5`
as its grading conjugation. -/
theorem realChiralDifferential_apply
    (u A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    InfoGeometry.Canonical.PeirceBoundaryComplex.differential
        (R := ℝ) (leftChiralProjector (E := E)) u A =
      u * A - ((gamma5 (E := E)) * A * gamma5 (E := E)) * u := by
  rw [InfoGeometry.Canonical.PeirceBoundaryComplex.differential_apply,
    InfoGeometry.Core.PeirceGrading.conjugation_apply,
    peirceReflection_leftChiralProjector_eq_gamma5]

/-- For an odd continuous endomorphism of the real doubled carrier, the square
of the chiral graded differential is commutation by `u²` on the full algebra
of continuous endomorphisms. -/
theorem realChiralDifferential_sq
    (u : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hu : u ∈ LinearMap.range
      (InfoGeometry.Core.PeirceGrading.odd
        (leftChiralProjector (E := E)))) :
    (InfoGeometry.Canonical.PeirceBoundaryComplex.differential
      (R := ℝ) (leftChiralProjector (E := E)) u) ^ 2 =
        LieAlgebra.ad ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) (u * u) := by
  have hp : IsIdempotentElem (leftChiralProjector (E := E)) := by
    change (leftChiralProjector (E := E)).comp
      (leftChiralProjector (E := E)) = leftChiralProjector (E := E)
    exact leftChiralProjector_idempotent
  exact InfoGeometry.Canonical.PeirceBoundaryComplex.differential_sq hp hu

end Core

end InfoGeometry.Canonical.RealDoubledChiralKreinBridge
