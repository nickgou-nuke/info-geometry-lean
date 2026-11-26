/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov
import InfoGeometry.Canonical.SelfConcordantLyapunovDAGBridge

open InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov
open InfoGeometry.Canonical.SelfConcordantLyapunovDAGBridge

#check lyapunovPotential
#check hessianMetric
#check lyapunovLieDerivative_eq
#check lyapunovLieDerivative_nonpos
#check lyapunovLieDerivative_neg
#check lyapunovPotential_eq_zero_iff
#check naturalGradientField_zero_iff
#check naturalGradientField_pos_below
#check naturalGradientField_neg_above
#check lyapunovPotential_nonneg
#check hessianMetric_pos
#check global_selfConcordant_lyapunov
#check reachable_informationPotential_has_global_lyapunov

#print axioms lyapunovLieDerivative_eq
#print axioms lyapunovLieDerivative_neg
#print axioms naturalGradientField_zero_iff
#print axioms hessianMetric_pos
#print axioms global_selfConcordant_lyapunov
#print axioms reachable_informationPotential_has_global_lyapunov
