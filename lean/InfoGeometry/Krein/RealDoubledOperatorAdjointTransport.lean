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

theorem kreinSelfAdjoint_conjugation
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : KreinSpace.IsKreinSelfAdjoint A) :
    KreinSpace.IsKreinSelfAdjoint
      ((doubledHilbertIsometry (E := E)).conjStarAlgEquiv A) := by
  exact StarHomAdjointTransport.map_bounded_krein_selfAdjoint
    (doubledHilbertIsometry (E := E)).conjStarAlgEquiv.toStarAlgHom
    (Or.inl (metric_conjugation_eq (E := E))) A hA

end InfoGeometry.Krein.RealDoubledOperatorAdjointTransport
