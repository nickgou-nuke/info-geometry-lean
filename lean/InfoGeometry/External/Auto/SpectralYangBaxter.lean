import Mathlib.Tactic

/-!
# Spectral Yang-Baxter Stitching

Finite spectral-parameter model for the local braid regulator.

The file proves:

* adjacent braid generators on a three-component vector field satisfy
  `σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂`;
* each generator is involutive, the finite version of `R(u) R(-u) = I`;
* spectral parameters are carried by differences `u - v`, and CPT/log
  inversion flips the sign of the spectral parameter.

This is a concrete algebraic braid/spectral skeleton.  It does not assert any
global statement about zeta zeros or spectral torsion.
-/

noncomputable section

abbrev HestenesField := Fin 3 → ℝ

def sigma₁ (v : HestenesField) : HestenesField :=
  fun i =>
    match i with
    | 0 => v 1
    | 1 => v 0
    | 2 => v 2

def sigma₂ (v : HestenesField) : HestenesField :=
  fun i =>
    match i with
    | 0 => v 0
    | 1 => v 2
    | 2 => v 1

def spectralParameter (u v : ℝ) : ℝ :=
  u - v

def cptInvertScale (u : ℝ) : ℝ :=
  -u

theorem sigma₁_involutive (v : HestenesField) :
    sigma₁ (sigma₁ v) = v := by
  funext i
  fin_cases i <;> simp [sigma₁]

theorem sigma₂_involutive (v : HestenesField) :
    sigma₂ (sigma₂ v) = v := by
  funext i
  fin_cases i <;> simp [sigma₂]

theorem spectral_yang_baxter (v : HestenesField) :
    sigma₁ (sigma₂ (sigma₁ v)) = sigma₂ (sigma₁ (sigma₂ v)) := by
  funext i
  fin_cases i <;> simp [sigma₁, sigma₂]

theorem spectralParameter_swap (u v : ℝ) :
    spectralParameter v u = -spectralParameter u v := by
  unfold spectralParameter
  ring

theorem spectralParameter_cpt (u v : ℝ) :
    spectralParameter (cptInvertScale u) (cptInvertScale v) =
      -spectralParameter u v := by
  unfold spectralParameter cptInvertScale
  ring

theorem spectralParameter_additive (u v w : ℝ) :
    spectralParameter u w = spectralParameter u v + spectralParameter v w := by
  unfold spectralParameter
  ring

def braidTorsion (v : HestenesField) : HestenesField :=
  fun i => sigma₁ (sigma₂ (sigma₁ v)) i - sigma₂ (sigma₁ (sigma₂ v)) i

theorem braidTorsion_zero (v : HestenesField) :
    braidTorsion v = 0 := by
  funext i
  unfold braidTorsion
  rw [spectral_yang_baxter v]
  simp

/-- Consolidated finite spectral-YBE package. -/
theorem spectral_yang_baxter_synthesis :
    (∀ v : HestenesField, sigma₁ (sigma₁ v) = v) ∧
    (∀ v : HestenesField, sigma₂ (sigma₂ v) = v) ∧
    (∀ v : HestenesField,
      sigma₁ (sigma₂ (sigma₁ v)) = sigma₂ (sigma₁ (sigma₂ v))) ∧
    (∀ u v, spectralParameter v u = -spectralParameter u v) ∧
    (∀ u v, spectralParameter (cptInvertScale u) (cptInvertScale v) =
      -spectralParameter u v) ∧
    (∀ u v w, spectralParameter u w =
      spectralParameter u v + spectralParameter v w) ∧
    (∀ v : HestenesField, braidTorsion v = 0) := by
  exact ⟨sigma₁_involutive, sigma₂_involutive, spectral_yang_baxter,
    spectralParameter_swap, spectralParameter_cpt, spectralParameter_additive,
    braidTorsion_zero⟩

end noncomputable section
