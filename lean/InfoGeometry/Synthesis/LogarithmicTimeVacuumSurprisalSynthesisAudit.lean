/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis

/-!
# Audit: `LogarithmicTimeVacuumSurprisalSynthesis`

Typecheck and signature audit for `InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis`.
-/

namespace InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis.Audit

open InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis

#check @milneDynamicalTime
#check @milne_two_clock_mutual_inversion
#check @milneComovingCoord
#check @milneComovingCoord_static_of_hubblesLaw
#check @milneGravitationalCoupling
#check @milneGravitationalCoupling_eq_linear_dynamical
#check @misnerOmega
#check @misnerScaleFactor
#check @misnerOmega_inversion_and_homomorphism
#check @hasDerivAt_misnerOmega
#check @radialDilatation
#check @cylinderObservable
#check @hasDerivAt_cylinderObservable_eq_radialDilatation
#check @modularSurprisal
#check @meanSurprisalEntropy
#check @expectedObservable
#check @gibbsState
#check @modularSurprisal_gibbsState
#check @meanSurprisalEntropy_gibbsState
#check @first_law_of_entanglement_gibbs
#check @surprisalVariance
#check @surprisalVariance_riesz_and_cumulant_identities
#check @attentionSoftmaxWeight
#check @attentionSoftmax_surprisal_eq

end InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis.Audit
