/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

/-!
# Kernel axiom audit for finite Markov transition kernels

This companion records the foundational axiom footprint of the finite
row-stochastic-matrix to Markov-kernel bridge and the finite-horizon
consistency theorem.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

#print axioms transitionKernel
#print axioms rowPMF
#print axioms transitionKernel_isMarkovKernel
#print axioms transitionKernel_singleton
#print axioms transitionKernel_integral_eq_mulVec
#print axioms historyTransitionKernel
#print axioms historyTransitionKernel_apply_eq_of_endpoint_eq
#print axioms historyTransitionKernel_piSingleton_singleton
#print axioms historyTransitionKernel_isMarkovKernel
#print axioms finiteTrajectoryKernel
#print axioms finiteTrajectoryKernel_isMarkovKernel
#print axioms finiteTrajectoryKernel_comp

#print axioms finiteTrajectoryKernel_succ_endpoint
#print axioms finiteTrajectoryKernel_initial_oneStep_successor_law

end InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
