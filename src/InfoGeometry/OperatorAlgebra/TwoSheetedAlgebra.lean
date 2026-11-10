/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

open MulOpposite

namespace InfoGeometry.OperatorAlgebra

/-- Two-sheeted operator algebra with commutant structure.
    Represents the (M, M') pair from Tomita-Takesaki theory,
    or the (Cl⁺, Cl⁻) pair in chiral setups.
-/
structure TwoSheetedAlgebra (K : Type*) [Ring K] where
  L : Type*
  R_alg : Type*
  [instL : Ring L]
  [instR : Ring R_alg]
  [instModL : Module K L]
  [instModR : Module K R_alg]
  /-- Commutant embedding (Tomita J-action mapping M to M')
      Modeled here as an equivalence between L and the opposite ring of R_alg -/
  commutant : L ≃+* R_algᵐᵒᵖ

instance (K : Type*) [Ring K] : Inhabited (TwoSheetedAlgebra K) :=
  ⟨{ L := Kᵐᵒᵖ
     R_alg := K
     commutant := RingEquiv.refl Kᵐᵒᵖ }⟩

end InfoGeometry.OperatorAlgebra
