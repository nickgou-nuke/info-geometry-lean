import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.QuantumProjectorField

section FieldProjectorSector

def singlesSector (ε k : ℝ) : ℝ := ε * (1 - k * ε)

def coincidenceSector (ε k : ℝ) : ℝ := k * ε ^ 2

theorem field_sector_conservation (ε k : ℝ) :
    singlesSector ε k + 2 * coincidenceSector ε k = ε * (1 + k * ε) := by
  simp [singlesSector, coincidenceSector]
  ring

end FieldProjectorSector

section SqrtCoordinateInversion

noncomputable def sqrtCoincidenceCoordinate (N : ℝ) : ℝ := Real.sqrt N

theorem square_root_inversion_parabola (N₀ ε k : ℝ) (hN₀ : 0 ≤ N₀)
    (hk : 0 ≤ k) :
    sqrtCoincidenceCoordinate (N₀ * k * ε ^ 2) ^ 2 = N₀ * k * ε ^ 2 := by
  simp only [sqrtCoincidenceCoordinate]
  apply Real.sq_sqrt
  positivity

end SqrtCoordinateInversion

section RankOneSVDStructure

def rankOneElement (spaceFactor energyFactor : ℝ) : ℝ :=
  spaceFactor * energyFactor

theorem rank_one_factorization_identity (a b c d : ℝ) :
    rankOneElement a c * rankOneElement b d =
      rankOneElement b c * rankOneElement a d := by
  simp [rankOneElement]
  ring

def rankOneMatrix (u v : ℝ → ℝ) (i j : ℝ) : ℝ := u i * v j

theorem rank_one_matrix_minor (u v : ℝ → ℝ) (i₁ i₂ j₁ j₂ : ℝ) :
    rankOneMatrix u v i₁ j₁ * rankOneMatrix u v i₂ j₂ -
      rankOneMatrix u v i₁ j₂ * rankOneMatrix u v i₂ j₁ = 0 := by
  simp only [rankOneMatrix]
  ring

end RankOneSVDStructure

section FluxCorrelatorInvariance

noncomputable def fluxCorrelator (a V : ℝ) : ℝ := a * Real.sqrt V

theorem flux_correlator_invariant (s a V : ℝ) (hs : 0 < s) (hV : 0 < V) :
    fluxCorrelator ((Real.sqrt s)⁻¹ * a) (s * V) =
      fluxCorrelator a V := by
  simp only [fluxCorrelator]
  rw [Real.sqrt_mul (le_of_lt hs)]
  have hsqrt : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  calc
    (Real.sqrt s)⁻¹ * a * (Real.sqrt s * Real.sqrt V) =
        ((Real.sqrt s)⁻¹ * Real.sqrt s) * (a * Real.sqrt V) := by ring
    _ = a * Real.sqrt V := by rw [inv_mul_cancel₀ hsqrt]; ring

end FluxCorrelatorInvariance

section CausalPoset

inductive Archetype
  | fieldProjector
  | sqrtInversion
  | rankOneSVD
  | fluxMeter
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .fieldProjector => 200
  | .sqrtInversion => 201
  | .rankOneSVD => 202
  | .fluxMeter => 203

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
    causallyPrecedes .fieldProjector .sqrtInversion ∧
    causallyPrecedes .sqrtInversion .rankOneSVD ∧
    causallyPrecedes .rankOneSVD .fluxMeter := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

end DetectorGeometry.QuantumProjectorField
