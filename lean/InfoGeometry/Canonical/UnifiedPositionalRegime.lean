import InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RoPERepresentationBridge
import InfoGeometry.Canonical.FourierCharacterRepresentationBridge
import InfoGeometry.LLM.ALiBi

namespace InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

open InfoGeometry.LLM

/-! Unified interface for every positional action whose parameter composes
additively.  The relative action is derived, not an additional axiom. -/

structure PositionalRegime (M : Type*) (G : Type*)
    [Zero G] [Add G] [Neg G] extends AdditivePositionRepresentation M G where
  relativeValue : G → G → M
  relativeValue_def : ∀ t s, relativeValue t s = mul (value (-s)) (value t)

def AdditivePositionRepresentation.toPositionalRegime
    {M G : Type*} [AddCommGroup G]
    (ρ : AdditivePositionRepresentation M G) : PositionalRegime M G where
  toAdditivePositionRepresentation := ρ
  relativeValue := fun t s => ρ.mul (ρ.value (-s)) (ρ.value t)
  relativeValue_def := by intro t s; rfl

theorem PositionalRegime.relativeValue_eq_value_sub
    {M G : Type*} [AddCommGroup G]
    (ρ : PositionalRegime M G) (t s : G) :
    ρ.relativeValue t s = ρ.value (t - s) := by
  rw [ρ.relativeValue_def, ← ρ.value_add]
  have h : -s + t = t - s := by simp [sub_eq_add_neg, add_comm]
  rw [h]

theorem PositionalRegime.relativeValue_add
    {M G : Type*} [AddCommGroup G]
    (ρ : PositionalRegime M G) (t s u : G) :
    ρ.relativeValue (t + u) s =
      ρ.mul (ρ.value u) (ρ.relativeValue t s) := by
  rw [ρ.relativeValue_eq_value_sub, ρ.relativeValue_eq_value_sub]
  rw [show t + u - s = u + (t - s) by abel, ρ.value_add]

noncomputable def ropeRotorPositionalRegime (θ : ℝ) :
    PositionalRegime (Matrix (Fin 2) (Fin 2) ℝ) ℤ :=
  (ropeRotorRepresentation θ).toPositionalRegime

noncomputable def ellipticRotorPositionalRegime (θ : ℝ) :
    PositionalRegime (Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) ℝ :=
  (ellipticRotor_functionRepresentation θ).toPositionalRegime

noncomputable def hyperbolicRotorPositionalRegime (θ : ℝ) :
    PositionalRegime (Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) ℝ :=
  (hyperbolicRotor_functionRepresentation θ).toPositionalRegime

noncomputable def jordanPositionalRegime (Δ : ℝ) :
    PositionalRegime (Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) ℝ :=
  (expJordanCell_functionRepresentation Δ).toPositionalRegime

noncomputable def fourierCharacterPositionalRegime
    {G : Type*} [AddCommGroup G] (χ : FourierCharacter G) :
    PositionalRegime (ℂ → ℂ) G :=
  (FourierCharacter.toPositionRepresentation χ).toPositionalRegime

/-! Score-level regimes cover encodings such as ALiBi, whose positional effect
is added to the query-key score rather than applied to the carrier. -/

structure ScorePositionalRegime (Q G : Type*) [Zero G] [Add G] where
  score : Q → Q → G → G → ℝ
  translation_invariant : ∀ q k t s a,
    score q k (t + a) (s + a) = score q k t s

def alibiScorePositionalRegime {Q : Type*}
    (dot : Q → Q → ℝ) (p : ℝ) : ScorePositionalRegime Q ℝ where
  score := alibiScore dot p
  translation_invariant := by
    intro q k t s a
    exact alibiScore_translation_invariant dot p q k t s a

theorem alibiScorePositionalRegime_score {Q : Type*}
    (dot : Q → Q → ℝ) (p : ℝ) (q k : Q) (t s : ℝ) :
    (alibiScorePositionalRegime dot p).score q k t s =
      dot q k - p * (t - s) := rfl

end InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
