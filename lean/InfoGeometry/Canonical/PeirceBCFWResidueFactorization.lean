import InfoGeometry.Canonical.PeirceBCFWResidueSpecialization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BCFWAffineChannelPole

namespace InfoGeometry.Canonical

noncomputable section

/-! The scalar factorization-channel term for a Peirce quadratic channel.
This is an algebraic numerator/propagator identity only; it is not a residue
factorization theorem for differential forms or amplitudes. -/

def peirceBCFWChannelTerm
    (amplitudeLeft amplitudeRight : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  bcfwChannelTerm amplitudeLeft amplitudeRight
    (splitQuadratic (embedRealSplit M) : ℂ)

theorem peirceBCFWChannelTerm_eq
    (amplitudeLeft amplitudeRight : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    peirceBCFWChannelTerm amplitudeLeft amplitudeRight M =
      amplitudeLeft * amplitudeRight /
        (splitQuadratic (embedRealSplit M) : ℂ) := by
  rfl

theorem peirceBCFWChannelTerm_factorized
    (amplitudeLeft amplitudeRight : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hprop : splitQuadratic (embedRealSplit M) ≠ 0) :
    (splitQuadratic (embedRealSplit M) : ℂ) *
        peirceBCFWChannelTerm amplitudeLeft amplitudeRight M =
      amplitudeLeft * amplitudeRight := by
  unfold peirceBCFWChannelTerm bcfwChannelTerm
    bcfwChannelNumerator
  have hprop' : (splitQuadratic (embedRealSplit M) : ℂ) ≠ 0 := by
    exact_mod_cast hprop
  field_simp

end

end InfoGeometry.Canonical
