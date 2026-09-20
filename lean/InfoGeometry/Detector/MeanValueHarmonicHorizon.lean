import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.MeanValueHarmonicHorizon

section MeanValue

def harmonicMeanValue (V center : ℝ) : ℝ := V * center

theorem mean_value_factorization (V center : ℝ) :
    harmonicMeanValue V center = V * center := rfl

end MeanValue

section FocalSingularity

noncomputable def singleFlux (C d z : ℝ) : ℝ := C / (d + z) ^ 2

noncomputable def coincidenceFlux (C d z : ℝ) : ℝ := C / (d + z) ^ 4

theorem sqrt_coincidence_flux (C d z : ℝ) (hC : 0 ≤ C)
    (hd : 0 < d + z) :
    Real.sqrt (coincidenceFlux C d z) = Real.sqrt C / (d + z) ^ 2 := by
  simp only [coincidenceFlux]
  have hsq : 0 < (d + z) ^ 2 := sq_pos_of_pos hd
  have hfour : (d + z) ^ 4 = ((d + z) ^ 2) ^ 2 := by ring
  rw [hfour, Real.sqrt_div hC, Real.sqrt_sq (le_of_lt hsq)]

end FocalSingularity

section RoomAnnihilation

noncomputable def harmonicQuotient (C₁ C₂ d z : ℝ) : ℝ :=
  singleFlux C₁ d z / Real.sqrt (coincidenceFlux C₂ d z)

theorem room_annihilation (C₁ C₂ d z : ℝ) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hd : 0 < d + z) :
    harmonicQuotient C₁ C₂ d z = C₁ / Real.sqrt C₂ := by
  simp only [harmonicQuotient, singleFlux]
  rw [sqrt_coincidence_flux C₂ d z (le_of_lt hC₂) hd]
  have hsq : (d + z) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hd)
  have hroot : Real.sqrt C₂ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hC₂)
  field_simp [hsq, hroot]

theorem gauge_invariance (C₁ C₂ d₁ d₂ z₁ z₂ : ℝ) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (h₁ : 0 < d₁ + z₁) (h₂ : 0 < d₂ + z₂) :
    harmonicQuotient C₁ C₂ d₁ z₁ = harmonicQuotient C₁ C₂ d₂ z₂ := by
  rw [room_annihilation C₁ C₂ d₁ z₁ hC₁ hC₂ h₁,
    room_annihilation C₁ C₂ d₂ z₂ hC₁ hC₂ h₂]

end RoomAnnihilation

section OriginClamping

theorem origin_clamped (C₁ C₂ m b : ℝ)
    (h_ray : ∀ x : ℝ, 0 ≤ x → m * x + b =
      (C₁ / Real.sqrt C₂) * x) : b = 0 := by
  simpa using h_ray 0 (le_refl 0)

theorem linear_ray (C₁ C₂ m b : ℝ)
    (h_ray : ∀ x : ℝ, 0 ≤ x → m * x + b =
      (C₁ / Real.sqrt C₂) * x) (x : ℝ) (hx : 0 ≤ x) :
    m * x + b = (C₁ / Real.sqrt C₂) * x := h_ray x hx

end OriginClamping

section CausalPoset

inductive Archetype
  | meanValue
  | focalSingularity
  | roomAnnihilation
  | gaugeInvariant
  | originClamping
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .meanValue => 142
  | .focalSingularity => 143
  | .roomAnnihilation => 144
  | .gaugeInvariant => 145
  | .originClamping => 146

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := by
  exact Nat.le_trans

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

theorem canonical_chain :
    causallyPrecedes .meanValue .focalSingularity ∧
    causallyPrecedes .focalSingularity .roomAnnihilation ∧
    causallyPrecedes .roomAnnihilation .gaugeInvariant ∧
    causallyPrecedes .gaugeInvariant .originClamping := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

end DetectorGeometry.MeanValueHarmonicHorizon
