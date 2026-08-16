import InfoGeometry.Canonical.H3ZornS3JordanTopologicalReadout

/-!
# Closed equalizer of the S₃ Jordan-product action

The residual map is already owned by the S₃/Jordan readout.  This file gives
its intrinsic topological equalizer as a named closed set and records that
the algebraic preservation theorem identifies that set with the whole pair
space.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

def S3JordanProductEqualizer (σ : S3Perm) :
    Set (H3Zorn ℝ × H3Zorn ℝ) :=
  {p | S3JordanProductResidual σ p = 0}

theorem isClosed_S3JordanProductEqualizer (σ : S3Perm) :
    IsClosed (S3JordanProductEqualizer σ) := by
  change IsClosed ((S3JordanProductResidual σ) ⁻¹' ({0} : Set (H3Zorn ℝ)))
  exact isClosed_singleton.preimage (continuous_S3JordanProductResidual σ)

theorem S3JordanProductEqualizer_eq_univ (σ : S3Perm) :
    S3JordanProductEqualizer σ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact S3JordanProductResidual_eq_zero σ p.1 p.2

end InfoGeometry.Canonical
