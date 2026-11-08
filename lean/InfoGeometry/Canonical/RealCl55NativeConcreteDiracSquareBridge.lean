/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge

/-!
# Square identity for the concrete native Dirac operator

This owner stays on the proved Hestenes image.  It does not identify the
image with the full fixed master carrier, so no basis-compatibility axiom is
hidden in the statement.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge

open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit

theorem nativeConcreteDiracOnImage_sq
    (v : SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ SplitOctonionExterior3HodgeDiracBridge.V3) :
    (nativeConcreteDiracOnImage v φ).comp
        (nativeConcreteDiracOnImage v φ) =
      nativeConcreteLaplacianOnImage v φ := by
  apply LinearMap.ext
  intro z
  rw [← nativeConcreteHestenesEmbeddingEquiv.apply_symm_apply z]
  simp only [LinearMap.comp_apply]
  rw [nativeConcreteDiracOnImage_intertwines_embeddingEquiv,
    nativeConcreteDiracOnImage_intertwines_embeddingEquiv,
    nativeConcreteLaplacianOnImage_intertwines_embeddingEquiv]
  exact congrArg nativeConcreteHestenesEmbeddingEquiv
    (congrArg (fun T : DoubledExterior3End => T
      (nativeConcreteHestenesEmbeddingEquiv.symm z))
      (concreteDirac3_sq v φ))

end InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
