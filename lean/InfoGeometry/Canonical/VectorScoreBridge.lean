import InfoGeometry.Canonical.UnifiedPositionalRegime
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.PositionalDynamicsRegimeBridge

/-! Pairing-level bridge from a vector action to an attention score. -/

structure PairingCompatibleRegime (Q G : Type*)
    [Zero G] [Add G] [Neg G] extends PositionalRegime (Q → Q) G where
  pairing : Q → Q → ℝ
  action_add : ∀ s t q, value (s + t) q = value t (value s q)
  pairing_invariant : ∀ a q k,
    pairing (value a q) (value a k) = pairing q k

def PairingCompatibleRegime.score
    {Q G : Type*} [Zero G] [Add G] [Neg G]
    (ρ : PairingCompatibleRegime Q G) (q k : Q) (t s : G) : ℝ :=
  ρ.pairing (ρ.value t q) (ρ.value s k)

theorem PairingCompatibleRegime.score_translation_invariant
    {Q G : Type*} [AddCommGroup G]
    (ρ : PairingCompatibleRegime Q G) (q k : Q) (t s a : G) :
    PairingCompatibleRegime.score ρ q k (t + a) (s + a) =
      PairingCompatibleRegime.score ρ q k t s := by
  simp only [PairingCompatibleRegime.score]
  rw [ρ.action_add t a q, ρ.action_add s a k]
  exact ρ.pairing_invariant a (ρ.value t q) (ρ.value s k)

theorem PairingCompatibleRegime.score_relative_form
    {Q G : Type*} [AddCommGroup G]
    (ρ : PairingCompatibleRegime Q G) (q k : Q) (t s : G) :
    PairingCompatibleRegime.score ρ q k t s =
      ρ.pairing (ρ.value s (ρ.value (t - s) q)) (ρ.value s k) := by
  simp only [PairingCompatibleRegime.score]
  rw [show t = (t - s) + s by abel, ρ.action_add]
  congr 1
  abel

def PairingCompatibleRegime.toScorePositionalRegime
    {Q G : Type*} [AddCommGroup G]
    (ρ : PairingCompatibleRegime Q G) : ScorePositionalRegime Q G where
  score := PairingCompatibleRegime.score ρ
  translation_invariant := ρ.score_translation_invariant

end InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
