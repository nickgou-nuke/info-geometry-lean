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
# Product Readout for Cyclotomic Heisenberg Data and Charged-Fock Sugawara Operators

The input carrier is built from the existing cyclotomic parameter and natural Weyl
exponents, together with a coefficient parameter. The output pairs the existing
finite latent quotient readout with the represented charged-Fock Sugawara bundle.
This module does not posit a separate mode-index type or a reflection action on the
input that is absent from the owning constructions.
-/

namespace InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological

open InfoGeometry.Topology.CyclotomicLatentQuotientTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Input data for the product readout: a sixth-root parameter, two natural Weyl
exponents, and a coefficient parameter. -/
abbrev CyclotomicHeisenbergSugawaraInput (𝕜 : Type*) :=
  (SixthRootParameter × (ℕ × ℕ)) × 𝕜

/-- Product output of the latent quotient and charged-Fock Sugawara readouts. -/
abbrev CyclotomicHeisenbergSugawaraOutput (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :=
  LatentQuotient × ChargedFockSugawaraBundle 𝕜

/-- The product readout retains the finite cyclotomic quotient and the represented
Sugawara operator family. -/
def cyclotomicHeisenbergSugawaraReadout
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    CyclotomicHeisenbergSugawaraOutput 𝕜 :=
  (cyclotomicLatentQuotientReadout p.1,
    representedChargedFockSugawaraBundle (𝕜 := 𝕜) p.2)

@[simp] theorem cyclotomicHeisenbergSugawaraReadout_fst
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) p).1 =
      cyclotomicLatentQuotientReadout p.1 := rfl

@[simp] theorem cyclotomicHeisenbergSugawaraReadout_snd
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) p).2 =
      representedChargedFockSugawaraBundle (𝕜 := 𝕜) p.2 := rfl

/-- Continuity follows componentwise from the native readout owners. -/
theorem continuous_cyclotomicHeisenbergSugawaraReadout :
    Continuous (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜)) := by
  exact continuous_of_discreteTopology

/-- The product readout is locally constant on the discrete input carrier. -/
theorem isLocallyConstant_cyclotomicHeisenbergSugawaraReadout :
    IsLocallyConstant (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜)) := by
  exact IsLocallyConstant.of_discrete
    (f := cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜))

/-- Explicit readout at a cyclotomic parameter, Weyl exponent pair, and coefficient. -/
theorem cyclotomicHeisenbergSugawaraReadout_components
    (q : SixthRootParameter) (a b : ℕ) (α : 𝕜) :
    cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) ((q, (a, b)), α) =
      (cyclotomicLatentQuotientReadout (q, (a, b)),
        representedChargedFockSugawaraBundle (𝕜 := 𝕜) α) := rfl

end
end InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological
