/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Conformal.BesselHagenGenerators
import InfoGeometry.Conformal.MaxwellStressConservation

/-!
# From real Maxwell equations to Bessel--Hagen conformal currents

This module combines the field equations, Bianchi identity, stress conservation,
four-dimensional metric trace and conformal Killing equation. Stress
conservation is derived. For a potential with commuting derivations, Bianchi
and gauge invariance are also derived; the vacuum Maxwell equation remains the
field-equation hypothesis.
-/

noncomputable section

namespace InfoGeometry.Conformal.BesselHagenMaxwell

open scoped BigOperators
open InfoGeometry.Canonical.BesselHagenNoether
open InfoGeometry.Conformal.BesselHagenCurrent
open InfoGeometry.Conformal.BesselHagenGenerators
open InfoGeometry.Conformal.MaxwellStressTensor

variable {A ι : Type*} [CommRing A] [Algebra ℝ A]

/-- Abelian field strength on a real differential algebra. -/
def abelianFieldStrength (D : ι → Derivation ℝ A A) (potential : ι → A) : Matrix ι ι A :=
  fun i j => D i (potential j) - D j (potential i)

theorem abelianFieldStrength_skew (D : ι → Derivation ℝ A A) (potential : ι → A)
    (i j : ι) :
    abelianFieldStrength D potential i j = -abelianFieldStrength D potential j i := by
  simp only [abelianFieldStrength, neg_sub]

/-- Commuting derivations supply the homogeneous Maxwell equation for a potential. -/
theorem abelianFieldStrength_bianchi (D : ι → Derivation ℝ A A) (potential : ι → A)
    (hcomm : ∀ i j a, D i (D j a) = D j (D i a)) (i j k : ι) :
    D i (abelianFieldStrength D potential j k) +
      D j (abelianFieldStrength D potential k i) +
      D k (abelianFieldStrength D potential i j) = 0 := by
  simp only [abelianFieldStrength, map_sub]
  rw [hcomm i j, hcomm i k, hcomm j k]
  abel

/-- Adding an exact potential leaves the field strength unchanged. -/
theorem abelianFieldStrength_gauge_invariant (D : ι → Derivation ℝ A A)
    (potential : ι → A) (χ : A)
    (hcomm : ∀ i j a, D i (D j a) = D j (D i a)) :
    abelianFieldStrength D (fun i => potential i + D i χ) = abelianFieldStrength D potential := by
  funext i j
  simp only [abelianFieldStrength, map_add]
  rw [hcomm i j]
  abel

/-- Vacuum Maxwell and Bianchi imply every four-dimensional conformal stress-current law. -/
theorem vacuum_conformalCurrent_conserved
    (D : Fin 4 → Derivation ℝ A A) (ε : Fin 4 → A)
    (F : Matrix (Fin 4) (Fin 4) A)
    (hε : ∀ i, ε i * ε i = 1) (hεconst : ∀ i j, D i (ε j) = 0)
    (hskew : ∀ i j, F i j = -F j i)
    (hBianchi : ∀ i j k, D i (F j k) + D j (F k i) + D k (F i j) = 0)
    (hMaxwell : ∀ j, ∑ i, ε i * D i (F i j) = 0)
    (ξ : Fin 4 → A) (σ : A) (hξ : IsConformalKilling D (metricEntry ε) ξ σ) :
    divergence D (stressCurrent (raisedTensor ε F) ξ) = 0 := by
  exact maxwell_conformalCurrent_conserved D ε hε F ξ σ hξ
    (raisedTensor_stressDivergence_zero D ε F hε hεconst hskew hBianchi hMaxwell)

/-- Potential formulation: gauge and homogeneous equations are constructed, not supplied. -/
theorem potential_conformalCurrent_conserved
    (D : Fin 4 → Derivation ℝ A A) (ε potential : Fin 4 → A)
    (hε : ∀ i, ε i * ε i = 1) (hεconst : ∀ i j, D i (ε j) = 0)
    (hcomm : ∀ i j a, D i (D j a) = D j (D i a))
    (hMaxwell : ∀ j, ∑ i, ε i * D i (abelianFieldStrength D potential i j) = 0)
    (ξ : Fin 4 → A) (σ : A) (hξ : IsConformalKilling D (metricEntry ε) ξ σ) :
    divergence D (stressCurrent (raisedTensor ε (abelianFieldStrength D potential)) ξ) = 0 := by
  exact vacuum_conformalCurrent_conserved D ε (abelianFieldStrength D potential) hε hεconst
    (abelianFieldStrength_skew D potential) (abelianFieldStrength_bianchi D potential hcomm)
    hMaxwell ξ σ hξ

/-- The special-conformal current directly follows from the potential's Maxwell equation. -/
theorem potential_specialConformalCurrent_conserved
    (D : Fin 4 → Derivation ℝ A A) (ε potential x b : Fin 4 → A)
    (hε : ∀ i, ε i * ε i = 1) (hεconst : ∀ i j, D i (ε j) = 0)
    (hcomm : ∀ i j a, D i (D j a) = D j (D i a))
    (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hb : ∀ i j, D i (b j) = 0)
    (hMaxwell : ∀ j, ∑ i, ε i * D i (abelianFieldStrength D potential i j) = 0) :
    divergence D (stressCurrent (raisedTensor ε (abelianFieldStrength D potential))
      (specialConformalCovector ε b x)) = 0 := by
  exact potential_conformalCurrent_conserved D ε potential hε hεconst hcomm hMaxwell
    (specialConformalCovector ε b x) (2 * parameterPairing ε b x)
    (specialConformal_isConformalKilling D ε x hεconst hx b hb)

end InfoGeometry.Conformal.BesselHagenMaxwell
