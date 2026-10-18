/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Section 122: Sorkin Parameter `κ₃` for Triple-Slit Interferometry and Superposed Aharonov–Bohm Flux Qubits
Target: `InfoGeometry/QuantumContext/SorkinBornRuleSuperposedABFluxQubit.lean`

Formalizes the multipath and superposed-flux extensions referenced in Sections 2 and 4 of Assafrão et al. (2019):
1. Superposed macroscopic magnetic flux in a superconducting ring (Flux Qubit,
   Bradonjić & Swain [27], Mooij et al. [48]) with weights `w₊ + w₋ = 1`.
2. Interferometric readout of a flux qubit (`superposed_ab_flux_qubit_readout`):
   `P_superposed = w₊ P_AB(c, s) + w₋ P_AB(c, -s)`
   `             = I_+ + (c² + s²)I_- + 2c G_{(+,-)} + 2(w₊ - w₋)s H_{(+,-)}`.
   The Yang term (`2c G`) is invariant, while the Yin term measures the qubit polarization `Δw = w₊ - w₋`.
3. Symmetric Schrödinger cat state (`w₊ = w₋`):
   In a balanced superposition (`w₊ = w₋`), the odd Yin asymmetry `H_{(+,-)}` cancels identically,
   while the even Yang shift `2c G_{(+,-)}` remains active.
4. Sorkin third-order multipath parameter `κ₃ ≡ 0` for the defined quadratic intensity
   under unphased additive superposition:
   `κ₃ = I₁₂₃ - (I₁₂ + I₂₃ + I₃₁) + (I₁ + I₂ + I₃) = 0`.
   The triple-slit definitions use coordinate-pair addition and do not encode
   slit-dependent magnetic phases.
-/

namespace InfoGeometry.QuantumContext.SorkinFluxQubit

variable {R : Type*} [CommRing R]

/-! ### 1. Fresnel Quadratures and Multi-Slit Wave Superposition -/

@[ext]
structure FresnelWave (R : Type*) where
  cQuad : R
  sQuad : R
  deriving DecidableEq, Repr, Inhabited

namespace FresnelWave

variable {R : Type*} [CommRing R]

def zeroWave : FresnelWave R := ⟨0, 0⟩

def sampleFresnelWaveInt : FresnelWave ℤ := ⟨3, 4⟩

theorem sampleFresnelWaveInt_ne_zero :
    sampleFresnelWaveInt ≠ zeroWave := by
  decide

/-- Two-wave superposition (double slit). -/
def add (ψ₁ ψ₂ : FresnelWave R) : FresnelWave R :=
  ⟨ψ₁.cQuad + ψ₂.cQuad, ψ₁.sQuad + ψ₂.sQuad⟩

/-- Three-wave superposition (triple slit `A + B + C`). -/
def add3 (ψ₁ ψ₂ ψ₃ : FresnelWave R) : FresnelWave R :=
  add (add ψ₁ ψ₂) ψ₃

/-- Born-rule intensity: `I(ψ) = C² + S²`. -/
def intensity (ψ : FresnelWave R) : R :=
  ψ.cQuad * ψ.cQuad + ψ.sQuad * ψ.sQuad

/-- Symmetric Yang correlator `G_{(1,2)} = C₁ C₂ + S₁ S₂`. -/
def yangG (ψ₁ ψ₂ : FresnelWave R) : R :=
  ψ₁.cQuad * ψ₂.cQuad + ψ₁.sQuad * ψ₂.sQuad

/-- Skew-symmetric Yin correlator `H_{(1,2)} = C₁ S₂ - S₁ C₂`. -/
def yinH (ψ₁ ψ₂ : FresnelWave R) : R :=
  ψ₁.cQuad * ψ₂.sQuad - ψ₁.sQuad * ψ₂.cQuad

/-- Transition probability under flux holonomy orientation `(c, s)`. -/
def abProb (ψ₁ ψ₂ : FresnelWave R) (c s : R) : R :=
  intensity ψ₁ + (c * c + s * s) * intensity ψ₂ +
    2 * c * yangG ψ₁ ψ₂ + 2 * s * yinH ψ₁ ψ₂

/-! ### 2. Superposed Aharonov–Bohm Effect and Superconducting Flux Qubit -/

/--
Effective screen probability when the solenoid is in a superposition of opposite currents:
`P_qubit = w₊ P_AB(c, +s) + w₋ P_AB(c, -s)`.
-/
def superposedFluxProb (ψ₁ ψ₂ : FresnelWave R) (c s w_plus w_minus : R) : R :=
  w_plus * abProb ψ₁ ψ₂ c s + w_minus * abProb ψ₁ ψ₂ c (-s)

/--
Exact formula for interferometric readout of a flux qubit (Bradonjić–Swain [27]):
For normalized qubit weights (`w₊ + w₋ = 1`), the superposed diffraction pattern separates
the even topological shift from the qubit polarization (`w₊ - w₋`):
`P_qubit = I₁ + (c² + s²)I₂ + 2c G_{(1,2)} + 2(w₊ - w₋)s H_{(1,2)}`.
-/
theorem superposed_ab_flux_qubit_readout
    (ψ₁ ψ₂ : FresnelWave R) (c s w_plus w_minus : R)
    (h_norm : w_plus + w_minus = 1) :
    superposedFluxProb ψ₁ ψ₂ c s w_plus w_minus =
      intensity ψ₁ + (c * c + s * s) * intensity ψ₂ +
      2 * c * yangG ψ₁ ψ₂ + 2 * (w_plus - w_minus) * s * yinH ψ₁ ψ₂ := by
  dsimp [superposedFluxProb, abProb]
  linear_combination
    (intensity ψ₁ + (c * c + s * s) * intensity ψ₂ + 2 * c * yangG ψ₁ ψ₂) * h_norm

/--
Symmetric Schrödinger cat state of the flux qubit (`w₊ = w₋`):
When the macroscopic flux in the ring is in a balanced superposition (`w₊ = w₋` and `w₊ + w₋ = 1`),
the odd Yin term `H_{(1,2)}` cancels completely, restoring spatial symmetry `x ↔ -x`,
while the even Yang term `2c G_{(1,2)}` remains active.
-/
theorem balanced_flux_cat_state_cancels_yin_asymmetry
    (ψ₁ ψ₂ : FresnelWave R) (c s w : R)
    (h_norm : w + w = 1) :
    superposedFluxProb ψ₁ ψ₂ c s w w =
      intensity ψ₁ + (c * c + s * s) * intensity ψ₂ + 2 * c * yangG ψ₁ ψ₂ := by
  rw [superposed_ab_flux_qubit_readout ψ₁ ψ₂ c s w w h_norm]
  ring

/-! ### 3. Triple Slit and Exact Vanishing of the Sorkin Parameter `κ₃` (Sorkin [31]) -/

/-- Double-slit intensity `I_{ij} = |ψ_i + ψ_j|²`. -/
def doubleSlitIntensity (ψ_i ψ_j : FresnelWave R) : R :=
  intensity (add ψ_i ψ_j)

/-- Triple-slit intensity `I_{123} = |ψ₁ + ψ₂ + ψ₃|²`. -/
def tripleSlitIntensity (ψ₁ ψ₂ ψ₃ : FresnelWave R) : R :=
  intensity (add3 ψ₁ ψ₂ ψ₃)

/--
Third-order Sorkin parameter `κ₃` (Sorkin 1994, Sinha et al. 2010, Quach 2017):
`κ₃ = I₁₂₃ - (I₁₂ + I₂₃ + I₃₁) + (I₁ + I₂ + I₃)`.
Measures deviation from the quadratic Born rule in multipath quantum interference.
-/
def sorkinKappa3 (ψ₁ ψ₂ ψ₃ : FresnelWave R) : R :=
  tripleSlitIntensity ψ₁ ψ₂ ψ₃ -
    (doubleSlitIntensity ψ₁ ψ₂ + doubleSlitIntensity ψ₂ ψ₃ + doubleSlitIntensity ψ₃ ψ₁) +
    (intensity ψ₁ + intensity ψ₂ + intensity ψ₃)

/-- Double-slit intensity expansion: `I_{12} = I₁ + I₂ + 2 G_{(1,2)}`. -/
theorem double_slit_expansion (ψ₁ ψ₂ : FresnelWave R) :
    doubleSlitIntensity ψ₁ ψ₂ = intensity ψ₁ + intensity ψ₂ + 2 * yangG ψ₁ ψ₂ := by
  dsimp [doubleSlitIntensity, intensity, add, yangG]
  ring

/-- Triple-slit intensity expansion: `I_{123} = I₁ + I₂ + I₃ + 2(G₁₂ + G₂₃ + G₃₁)`. -/
theorem triple_slit_expansion (ψ₁ ψ₂ ψ₃ : FresnelWave R) :
    tripleSlitIntensity ψ₁ ψ₂ ψ₃ =
      intensity ψ₁ + intensity ψ₂ + intensity ψ₃ +
      2 * (yangG ψ₁ ψ₂ + yangG ψ₂ ψ₃ + yangG ψ₃ ψ₁) := by
  dsimp [tripleSlitIntensity, intensity, add3, add, yangG]
  ring

/--
Exact vanishing of the Sorkin parameter `κ₃ ≡ 0`:
Every triple of Fresnel waves has identically zero third-order Sorkin parameter:
`κ₃(ψ₁, ψ₂, ψ₃) = 0`.
-/
theorem sorkin_kappa3_identically_zero (ψ₁ ψ₂ ψ₃ : FresnelWave R) :
    sorkinKappa3 ψ₁ ψ₂ ψ₃ = 0 := by
  dsimp [sorkinKappa3, tripleSlitIntensity, doubleSlitIntensity, intensity, add3, add]
  ring

end FresnelWave

end InfoGeometry.QuantumContext.SorkinFluxQubit
