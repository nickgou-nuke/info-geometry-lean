import InfoGeometry.Physics.SolovievInterferenceDependency
import InfoGeometry.Physics.SolovievTwoModePhonon

namespace InfoGeometry.Physics.SolovievDressedInterference.Tests

open SolovievCircularInterference SolovievPhononCorrections SolovievTwoModePhonon
open NuclearQuasiparticleCAR.QuasiparticleCAR

example : (circularAmplitude 2 1).re ≠ 0 :=
  circularAmplitude_not_pure_imaginary 2 1 (by norm_num)

example : Complex.normSq (circularAmplitude 2 1 + circularAmplitude (-2) 1) = 0 := by
  exact (circular_strength_zero_iff 2 (-2) 1 (by norm_num)).2 rfl

example : Complex.normSq (circularAmplitude 2 1 + circularAmplitude 2 1) = 4 := by
  rw [circular_strength_decomposition 2 2 1 (by norm_num)]
  norm_num

example : Complex.normSq ((1 : ℂ) + (-1 / 2 : ℂ)) <
    Complex.normSq (1 : ℂ) + Complex.normSq (-1 / 2 : ℂ) := by
  rw [strength_suppressed_iff]
  norm_num

example : starRingEnd ℂ (1 : ℂ) = 1 ∧ Complex.normSq ((1 : ℂ) + 1) = 4 := by
  norm_num [Complex.normSq_apply]

example (forward backward : ℂ) (forwardPhase backwardPhase : Circle) :
    comm (phononAnnihilation twoModeCAR 0 1
        ((forwardPhase : ℂ) * forward) ((backwardPhase : ℂ) * backward))
      (phononCreation twoModeCAR 0 1
        ((forwardPhase : ℂ) * forward) ((backwardPhase : ℂ) * backward)) =
    comm (phononAnnihilation twoModeCAR 0 1 forward backward)
      (phononCreation twoModeCAR 0 1 forward backward) :=
  phonon_commutator_unit_phases twoModeCAR 0 1 (by decide)
    forward backward forwardPhase backwardPhase

#print axioms circularAmplitude_re
#print axioms circularAmplitude_im
#print axioms circularAmplitude_conj
#print axioms circularAmplitude_not_pure_imaginary
#print axioms circularAmplitude_add
#print axioms circular_strength_decomposition
#print axioms circular_strength_zero_iff
#print axioms strength_suppressed_iff
#print axioms strength_zero_iff
#print axioms circular_phonon_split
#print axioms phonon_commutator_unit_phases
#print axioms isCocyclic_add
#print axioms dressed_total_strength
#print axioms dressed_cancellation_iff
#print axioms dressed_cross_term
#print axioms ProofDependency.causal_branches
#print axioms ProofDependency.interference_and_commutator_incomparable
#print axioms ProofDependency.no_cycle

end InfoGeometry.Physics.SolovievDressedInterference.Tests
