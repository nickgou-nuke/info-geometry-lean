/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwelveFoldAdditiveCharacter
import InfoGeometry.Canonical.TwelveFoldCyclotomicNative

/-!
# Exact twelvefold arithmetic alongside the `G₂` Artin owner

The `I₂(6)` presentation and its longest-element readback are owned by
`G2ArtinPresentation`.  The native C12 owners provide the cyclotomic and
Galois infrastructure.  This owner records the concrete `ζ₁₂` root fact at
the exceptional namespace boundary; it does not introduce a second Weyl
carrier or claim a cyclotomic matrix representation of the Artin group.
-/

namespace InfoGeometry.Exceptional.G2ArtinCyclotomicBridge

open InfoGeometry.Canonical.TwelveFoldAdditiveCharacter
open InfoGeometry.Canonical.TwelveFoldCyclotomicNative
open Polynomial

noncomputable section

theorem zeta12_is_cyclotomic_root :
    (cyclotomic 12 ℂ).IsRoot zeta12 :=
  primitive_twelfth_root_is_cyclotomic_root zeta12_primitive

end
end InfoGeometry.Exceptional.G2ArtinCyclotomicBridge
