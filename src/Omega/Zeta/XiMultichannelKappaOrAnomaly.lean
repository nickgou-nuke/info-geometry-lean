import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-multichannel-witness-kappa-or-anom`. A genuine visible-channel
negative-square resonance produces the finite witness, while failure of strictification produces
the anomaly witness. -/
theorem xi_multichannel_kappa_or_anomaly {Pi : Type*} (sqNeg : Pi → ℕ)
    (finiteConclusion strictification anomalyConclusion : Prop)
    (hRes : (∃ π, 0 < sqNeg π) → finiteConclusion)
    (hAnom : ¬ strictification → anomalyConclusion) :
    ((∃ π, 0 < sqNeg π) ∨ ¬ strictification) → finiteConclusion ∨ anomalyConclusion := by
  intro h
  rcases h with hResonance | hStrictification
  · exact Or.inl (hRes hResonance)
  · exact Or.inr (hAnom hStrictification)

end Omega.Zeta
