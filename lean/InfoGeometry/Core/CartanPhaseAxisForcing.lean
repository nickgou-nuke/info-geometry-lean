import InfoGeometry.Core.SymmetricLie

/-!
# Cartan Phase-Axis Forcing

Owner surface for forcing lemmas that place phase-axis commutators in the odd
sector from symmetric-pair assumptions.
-/

namespace InfoGeometry.Core

namespace SymmetricLieAlgebra

/--
Minimal owner data for odd-sector commutator forcing of a phase-axis pair.

`K` is the odd generator candidate and `I` is the even phase-axis anchor.
-/
structure CartanPhaseAxisForcingData
    (L : Type _) [LieRing L] [LieAlgebra ℝ L] where
  S : SymmetricLieAlgebra L
  K : L
  I : L
  hK_odd : K ∈ S.oddSubmodule
  hI_even : I ∈ S.evenLieSubalgebra

/-- The ordered commutator `[I, K]` lies in the odd sector. -/
theorem commutator_IK_mem_odd
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (D : CartanPhaseAxisForcingData L) :
    ⁅D.I, D.K⁆ ∈ D.S.oddSubmodule := by
  exact
    SymmetricLieAlgebra.bracket_k_p (S := D.S) (x := D.I) (y := D.K)
      D.hI_even D.hK_odd

/-- The commutator `[K, I]` lies in the odd sector as well. -/
theorem commutator_KI_mem_odd
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (D : CartanPhaseAxisForcingData L) :
    ⁅D.K, D.I⁆ ∈ D.S.oddSubmodule := by
  simpa [lie_skew] using
    D.S.oddSubmodule.neg_mem (commutator_IK_mem_odd (D := D))

/-- Compatibility naming: odd sector as `𝔭`. -/
theorem commutator_KI_mem_p
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (D : CartanPhaseAxisForcingData L) :
    ⁅D.K, D.I⁆ ∈ D.S.𝔭 :=
  commutator_KI_mem_odd (D := D)

end SymmetricLieAlgebra

end InfoGeometry.Core
