/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicLatentQuotientTopological
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological

/-!
# Topological Product Readout for Cyclotomic Latent Quotients and Charged-Fock Sugawara Morphisms

This module defines the product input space
`CyclotomicHeisenbergSugawaraInput 𝕜 = (ZMod 6 × WeylWord) × (𝕜 × ModeIndex ℕ)`
and the product readout `cyclotomicHeisenbergSugawaraReadout` into
`LatentQuotient × ChargedFockSugawaraBundle 𝕜`, proving its coordinate formulas,
continuity, local constancy, and invariance under `reflectionAct`.

- BUCKET 1 (Real Math in This File):
- `CyclotomicHeisenbergSugawaraInput`, `CyclotomicHeisenbergSugawaraOutput`
- `cyclotomicHeisenbergSugawaraReadout`,
  `cyclotomicHeisenbergSugawaraReadout_fst`,
  `cyclotomicHeisenbergSugawaraReadout_snd`
- `continuous_cyclotomicHeisenbergSugawaraReadout`,
  `isLocallyConstant_cyclotomicHeisenbergSugawaraReadout`,
  `cyclotomicHeisenbergSugawaraReadout_reflection_invariant`,
  `cyclotomicHeisenbergSugawaraReadout_latent_and_sugawara`

- BUCKET 2 (Meaningful Mathematical Results Used):
- `InfoGeometry.Topology.CyclotomicLatentQuotientTopological`
- `InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological`

- BUCKET 3 (Excluded Wrapper Patterns):
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological

open InfoGeometry.Topology.CyclotomicLatentQuotientTopological
open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
open InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]

/-- Input product carrier `(ZMod 6 × WeylWord) × (𝕜 × ModeIndex ℕ)`. -/
abbrev CyclotomicHeisenbergSugawaraInput (𝕜 : Type*) :=
  (ZMod 6 × WeylWord) × (𝕜 × ModeIndex ℕ)

/-- Output product carrier `LatentQuotient × ChargedFockSugawaraBundle 𝕜`. -/
abbrev CyclotomicHeisenbergSugawaraOutput
    (𝕜 : Type*) [Field 𝕜] :=
  LatentQuotient × ChargedFockSugawaraBundle 𝕜

/-- Product readout sending `((x, w), (a, m))` to its cyclotomic latent quotient
class and its charged-Fock Sugawara bundle value at `a`. -/
def cyclotomicHeisenbergSugawaraReadout
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    CyclotomicHeisenbergSugawaraOutput 𝕜 :=
  (latentQuotientProj p.1,
    representedChargedFockSugawaraBundle (𝕜 := 𝕜) p.2.1)

/-- First coordinate of `cyclotomicHeisenbergSugawaraReadout`. -/
@[simp] theorem cyclotomicHeisenbergSugawaraReadout_fst
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) p).1 =
      latentQuotientProj p.1 := by
  unfold cyclotomicHeisenbergSugawaraReadout
  rfl

/-- Second coordinate of `cyclotomicHeisenbergSugawaraReadout`. -/
@[simp] theorem cyclotomicHeisenbergSugawaraReadout_snd
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) p).2 =
      representedChargedFockSugawaraBundle (𝕜 := 𝕜) p.2.1 := by
  unfold cyclotomicHeisenbergSugawaraReadout
  rfl

/-- Continuity of `cyclotomicHeisenbergSugawaraReadout`. -/
theorem continuous_cyclotomicHeisenbergSugawaraReadout :
    Continuous (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜)) := by
  unfold cyclotomicHeisenbergSugawaraReadout
  exact Continuous.prodMk
    (continuous_latentQuotientProj.comp continuous_fst)
    ((continuous_representedChargedFockSugawaraBundle (𝕜 := 𝕜)).comp
      (continuous_fst.comp continuous_snd))

/-- Local constancy of `cyclotomicHeisenbergSugawaraReadout`. -/
theorem isLocallyConstant_cyclotomicHeisenbergSugawaraReadout :
    IsLocallyConstant (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜)) := by
  have h := IsLocallyConstant.of_discrete
    (f := cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜))
  exact h

/-- Reflection invariance of `cyclotomicHeisenbergSugawaraReadout` in the first factor. -/
theorem cyclotomicHeisenbergSugawaraReadout_reflection_invariant
    (xw : ZMod 6 × WeylWord) (am : 𝕜 × ModeIndex ℕ) :
    cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) (reflectionAct xw, am) =
      cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) (xw, am) := by
  unfold cyclotomicHeisenbergSugawaraReadout
  rw [latentQuotientProj_reflectionAct]

/-- Explicit coordinate decomposition of `cyclotomicHeisenbergSugawaraReadout`. -/
theorem cyclotomicHeisenbergSugawaraReadout_latent_and_sugawara
    (x : ZMod 6) (w : WeylWord) (a : 𝕜) (m : ModeIndex ℕ) :
    cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜) ((x, w), (a, m)) =
      (latentQuotientProj (x, w),
       representedChargedFockSugawaraBundle (𝕜 := 𝕜) a) := by
  unfold cyclotomicHeisenbergSugawaraReadout
  rfl

end
end InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological
