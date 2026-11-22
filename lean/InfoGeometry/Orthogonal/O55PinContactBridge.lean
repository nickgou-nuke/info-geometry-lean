/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Orthogonal.O55WittNullFrame
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55RealSplitPinNullPairProjective
import InfoGeometry.Orthogonal.O55ExistingPinGlideBridge

/-!
# Native contact/Pin readouts

This owner deliberately uses the native `InfoGeometry` carriers.  The former
version imported `proofs.PinO55GlideReflection`, which is not a Lake target and
therefore could not be part of the verified source graph.  The affine Klein
glide is a separate frontier; the theorems below retain the proved finite
content: dimension counts, projective null-sheet exchange, and involutive
contact/sheet opposition.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence

theorem matrix_clifford_count_agreement :
    Fintype.card (Fin 10) = 10 ∧ Nat.choose 10 2 = 45 := by
  decide

theorem pin_crosscap_projective_null_swap :
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nPairProjective crosscapIndex) =
      nbarPairProjective crosscapIndex ∧
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nbarPairProjective crosscapIndex) =
      nPairProjective crosscapIndex := by
  exact ⟨realSplitPinNullAction_fNegRealPin_nPairProjective crosscapIndex,
    realSplitPinNullAction_fNegRealPin_nbarPairProjective crosscapIndex⟩



theorem pin_crosscap_n_to_neg_nbar :
    twisted_adj PinO55GlideReflection.crosscapReflectionPin55
        (n_pair PinO55GlideReflection.crosscapIndex) =
      -ι55 (nbar_pair PinO55GlideReflection.crosscapIndex) :=
  PinO55GlideReflection.crosscap_pin_twisted_adj_n_to_neg_nbar

theorem pin_crosscap_nbar_to_neg_n :
    twisted_adj PinO55GlideReflection.crosscapReflectionPin55
        (nbar_pair PinO55GlideReflection.crosscapIndex) =
      -ι55 (n_pair PinO55GlideReflection.crosscapIndex) :=
  PinO55GlideReflection.crosscap_pin_twisted_adj_nbar_to_neg_n

/-- The internal Pin crosscap reverses orientation. -/
theorem pin_crosscap_orientation_sign :
    PinO55GlideReflection.crosscapOrientationSign = -1 :=
  PinO55GlideReflection.crosscap_orientation_reversing

end InfoGeometry.Orthogonal.O55Contact

end noncomputable section
