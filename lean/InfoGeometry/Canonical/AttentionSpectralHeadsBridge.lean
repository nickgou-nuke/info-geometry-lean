import InfoGeometry.LLM.FourierSuperposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LLM.SpectralToken

/-!
# Finite spectral multi-head positional readout

This module is the finite algebraic shadow of a multi-head positional
mechanism.  A head is a finite linear combination of relative characters of
an additive position group.  The construction is independent of a choice of
Fourier transform, Hilbert space, or physical interpretation.
-/

namespace InfoGeometry.Canonical.AttentionSpectralHeadsBridge

open InfoGeometry.LLM

noncomputable section

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

/-- One spectral head: coefficients paired with additive characters. -/
structure SpectralHead where
  coeff : ι → ℂ
  character : ι → FourierCharacter G

namespace SpectralHead

/-- The relative-position response of a spectral head. -/
noncomputable def response (H : SpectralHead (G := G) (ι := ι))
    (t s : G) : ℂ :=
  finiteFourierKernel H.coeff H.character t s

theorem response_eq_sum (H : SpectralHead (G := G) (ι := ι)) (t s : G) :
    H.response t s =
      ∑ i, H.coeff i * fourierCharacterKernel (H.character i) t s := by
  rfl

/-- The response depends only on relative position. -/
theorem response_translation_invariant
    (H : SpectralHead (G := G) (ι := ι)) (t s a : G) :
    H.response (t + a) (-(s + a)) = H.response t (-s) := by
  exact finiteFourierKernel_translation_invariant
    H.coeff H.character t s a

theorem response_at_opposite_position
    (H : SpectralHead (G := G) (ι := ι)) (t : G) :
    H.response t (-t) = ∑ i, H.coeff i := by
  exact finiteFourierKernel_zero H.coeff H.character t

end SpectralHead

/-- A finite collection of independent spectral heads. -/
structure SpectralHeads (n : ℕ) where
  head : Fin n → SpectralHead (G := G) (ι := ι)

namespace SpectralHeads

/-- The indexed response of a multi-head family. -/
noncomputable def response (A : SpectralHeads (G := G) (ι := ι) n)
    (h : Fin n) (t s : G) : ℂ :=
  (A.head h).response t s

theorem response_translation_invariant
    (A : SpectralHeads (G := G) (ι := ι) n) (h : Fin n) (t s a : G) :
    A.response h (t + a) (-(s + a)) = A.response h t (-s) := by
  exact (A.head h).response_translation_invariant t s a

end SpectralHeads

/-- The primal/dual swap is an involution on any spectral token carrier. -/
theorem spectral_token_swap_twice
    {V : Type*} (t : InfoGeometry.LLM.SpectralToken.SpectralToken V) :
    InfoGeometry.LLM.SpectralToken.SpectralToken.swap
        (InfoGeometry.LLM.SpectralToken.SpectralToken.swap t) = t := by
  exact InfoGeometry.LLM.SpectralToken.SpectralToken.swap_involutive t

end
end InfoGeometry.Canonical.AttentionSpectralHeadsBridge
