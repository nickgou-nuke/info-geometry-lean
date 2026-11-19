/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicLatentQuotientTopological
import InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological

/-!
# Product Readout for the Cyclotomic Latent Quotient and Charged-Fock Sugawara Bundle

The input uses the quotient owner's actual carrier `SixthRootParameter × (ℕ × ℕ)`,
paired with a field parameter.  The readout combines that owner's finite latent
chart with the represented charged-Fock Sugawara section.
-/

namespace InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological

open InfoGeometry.Topology.CyclotomicLatentQuotientTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Actual finite-label carrier paired with the field parameter. -/
abbrev CyclotomicHeisenbergSugawaraInput (𝕜 : Type*) :=
  (SixthRootParameter × (ℕ × ℕ)) × 𝕜

/-- Product output of a latent quotient point and a represented Sugawara bundle. -/
abbrev CyclotomicHeisenbergSugawaraOutput
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :=
  LatentQuotient × ChargedFockSugawaraBundle 𝕜

/-- Product readout of the cyclotomic labels and field parameter. -/
def cyclotomicHeisenbergSugawaraReadout
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    CyclotomicHeisenbergSugawaraOutput 𝕜 :=
  (cyclotomicLatentQuotientReadout p.1, representedChargedFockSugawaraBundle p.2)

@[simp] theorem cyclotomicHeisenbergSugawaraReadout_fst
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) p).1 =
      cyclotomicLatentQuotientReadout p.1 := rfl

@[simp] theorem cyclotomicHeisenbergSugawaraReadout_snd
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) p).2 =
      representedChargedFockSugawaraBundle p.2 := rfl

/-- Continuity of the product readout. -/
theorem continuous_cyclotomicHeisenbergSugawaraReadout :
    Continuous (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜)) := by
  unfold cyclotomicHeisenbergSugawaraReadout
  exact Continuous.prodMk
    (continuous_cyclotomicLatentQuotientReadout.comp continuous_fst)
    (continuous_representedChargedFockSugawaraBundle.comp continuous_snd)

/-- Local constancy for the discrete product parameter space. -/
theorem isLocallyConstant_cyclotomicHeisenbergSugawaraReadout :
    IsLocallyConstant (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜)) := by
  exact IsLocallyConstant.of_discrete _

/-- The readout is precisely the product of its two owner maps. -/
theorem cyclotomicHeisenbergSugawaraReadout_latent_and_sugawara
    (q : SixthRootParameter) (m : ℕ × ℕ) (a : 𝕜) :
    cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) ((q, m), a) =
      (cyclotomicLatentQuotientReadout (q, m),
       representedChargedFockSugawaraBundle a) := rfl

end
end InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological
