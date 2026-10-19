/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.RealDoubledHilbertBridge
import InfoGeometry.Krein.StarHomAdjointTransport
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Operator-level real doubled/Krein transport

This owner records the operator soldering theorem missing from the carrier
transport: conjugation by the canonical real linear isometry from
`DoubledSpace E` to `HilbertDoubled E` preserves the Krein adjoint.
-/

namespace InfoGeometry.Krein.RealDoubledOperatorAdjointTransport

open InfoGeometry.Krein
open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

noncomputable abbrev doubledHilbertIsometry :
    DoubledSpace E ≃ₗᵢ[ℝ] HilbertDoubled E :=
  HilbertDoubled.ofDoubledLIE (E := E)

/- The existing star-algebra transport and the carrier-level conjugation are
   the same operator map.  This is the soldering equation between the two
   APIs. -/
theorem conjStarAlgEquiv_eq_conjugateDoubledEnd
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    (doubledHilbertIsometry (E := E)).conjStarAlgEquiv A =
      conjugateDoubledEnd (E := E) A := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem metric_conjugation_eq
    : (doubledHilbertIsometry (E := E)).conjStarAlgEquiv
        (KreinSpace.jCLM (H := DoubledSpace E)) =
      KreinSpace.jCLM (H := HilbertDoubled E) := by
  apply ContinuousLinearMap.ext
  intro x
  apply HilbertDoubled.ext
  rfl

theorem kreinAdjoint_conjugation (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    (doubledHilbertIsometry (E := E)).conjStarAlgEquiv
        (KreinSpace.kreinAdjoint A) =
      KreinSpace.kreinAdjoint
        ((doubledHilbertIsometry (E := E)).conjStarAlgEquiv A) := by
  exact StarHomAdjointTransport.map_bounded_kreinAdjoint
    (doubledHilbertIsometry (E := E)).conjStarAlgEquiv.toStarAlgHom
    (Or.inl (metric_conjugation_eq (E := E))) A

theorem kreinAdjoint_conjugateDoubledEnd
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    KreinSpace.kreinAdjoint (conjugateDoubledEnd (E := E) A) =
      conjugateDoubledEnd (E := E) (KreinSpace.kreinAdjoint A) := by
  rw [← conjStarAlgEquiv_eq_conjugateDoubledEnd (E := E) A]
  rw [← conjStarAlgEquiv_eq_conjugateDoubledEnd (E := E)
    (KreinSpace.kreinAdjoint A)]
  exact (kreinAdjoint_conjugation (E := E) A).symm

theorem kreinSelfAdjoint_conjugation
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : KreinSpace.IsKreinSelfAdjoint A) :
    KreinSpace.IsKreinSelfAdjoint
      ((doubledHilbertIsometry (E := E)).conjStarAlgEquiv A) := by
  exact StarHomAdjointTransport.map_bounded_krein_selfAdjoint
    (doubledHilbertIsometry (E := E)).conjStarAlgEquiv.toStarAlgHom
    (Or.inl (metric_conjugation_eq (E := E))) A hA

theorem kreinSkewAdjoint_conjugation
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : KreinSpace.IsKreinSkewAdjoint A) :
    KreinSpace.IsKreinSkewAdjoint
      ((doubledHilbertIsometry (E := E)).conjStarAlgEquiv A) := by
  change KreinSpace.kreinAdjoint
      ((doubledHilbertIsometry (E := E)).conjStarAlgEquiv A) =
    -((doubledHilbertIsometry (E := E)).conjStarAlgEquiv A)
  rw [← kreinAdjoint_conjugation (E := E) A]
  exact congrArg (doubledHilbertIsometry (E := E)).conjStarAlgEquiv hA

end InfoGeometry.Krein.RealDoubledOperatorAdjointTransport
