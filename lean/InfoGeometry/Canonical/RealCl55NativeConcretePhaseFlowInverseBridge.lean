/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowBridge

/-!
# Inverses for the native concrete phase flow

The existing phase-flow group law is an operator identity on the actual
Hestenes image.  This file exposes its two inverse identities without adding
an analytic exponential or any physical interpretation.
-/

namespace InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowInverseBridge

open InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowBridge
open InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit

theorem nativeConcretePhaseFlowOnImage_neg_add (t : ℝ) :
    (nativeConcretePhaseFlowOnImage (-t)).comp
        (nativeConcretePhaseFlowOnImage t) =
      LinearMap.id := by
  calc
    (nativeConcretePhaseFlowOnImage (-t)).comp
        (nativeConcretePhaseFlowOnImage t) =
      nativeConcretePhaseFlowOnImage (-t + t) :=
        (nativeConcretePhaseFlowOnImage_add (-t) t).symm
    _ = nativeConcretePhaseFlowOnImage 0 := by rw [neg_add_cancel]
    _ = LinearMap.id :=
      nativeConcretePhaseFlowOnImage_zero

theorem nativeConcretePhaseFlowOnImage_add_neg (t : ℝ) :
    (nativeConcretePhaseFlowOnImage t).comp
        (nativeConcretePhaseFlowOnImage (-t)) =
      LinearMap.id := by
  calc
    (nativeConcretePhaseFlowOnImage t).comp
        (nativeConcretePhaseFlowOnImage (-t)) =
      nativeConcretePhaseFlowOnImage (t + -t) :=
        (nativeConcretePhaseFlowOnImage_add t (-t)).symm
    _ = nativeConcretePhaseFlowOnImage 0 := by rw [add_neg_cancel]
    _ = LinearMap.id :=
      nativeConcretePhaseFlowOnImage_zero

end InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowInverseBridge
