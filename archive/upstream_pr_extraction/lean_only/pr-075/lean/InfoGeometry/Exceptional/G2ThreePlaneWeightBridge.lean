/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.QuantumAlgebra.ThreePlaneChiralCarrier
import InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords

/-!
# Finite three-plane labels inside the existing `G₂` signed-root carrier

This owner records only an explicit finite index correspondence.  It does not
assert a Lie-module decomposition, a braid interpretation, or a physical
identification of the two signs.
-/

namespace InfoGeometry.Exceptional.G2ThreePlaneWeightBridge

open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2SignedRootReflections

/-! The three short positive roots selected for the chiral packet. -/

def shortRoot : Fin 3 → G2PositiveRoot
  | 0 => .alpha
  | 1 => .alpha_add_beta
  | 2 => .two_alpha_beta

def upperWeightLabel (i : Fin 3) : SignedPositiveRoot :=
  (true, shortRoot i)

def lowerWeightLabel (i : Fin 3) : SignedPositiveRoot :=
  (false, shortRoot i)

theorem shortRoot_injective : Function.Injective shortRoot := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [shortRoot] at h ⊢

theorem upperWeightLabel_injective : Function.Injective upperWeightLabel := by
  intro i j h
  exact shortRoot_injective (congrArg Prod.snd h)

theorem lowerWeightLabel_injective : Function.Injective lowerWeightLabel := by
  intro i j h
  exact shortRoot_injective (congrArg Prod.snd h)

theorem canonical_w0_upperWeightLabel (i : Fin 3) :
    canonicalWeylAction G2WeylElement.w0 (upperWeightLabel i) =
      lowerWeightLabel i := by
  fin_cases i <;> native_decide

theorem canonical_w0_lowerWeightLabel (i : Fin 3) :
    canonicalWeylAction G2WeylElement.w0 (lowerWeightLabel i) =
      upperWeightLabel i := by
  fin_cases i <;> native_decide

end InfoGeometry.Exceptional.G2ThreePlaneWeightBridge
