/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearSymmetrySectors
import InfoGeometry.Physics.NuclearFeshbachConfigurationBridge
import InfoGeometry.Physics.NuclearAlgebraicResolventObstruction
import InfoGeometry.Physics.NuclearFeshbachSymmetry
import InfoGeometry.Physics.NuclearFiniteEffectiveModel
import InfoGeometry.Physics.NuclearEffectiveSelection
import InfoGeometry.Physics.NuclearJointIdentifiability
import InfoGeometry.Core.PeirceTangent

/-!
# Symmetry-resolved configuration inference

This entry point joins chosen symmetry sectors, exact complementary-space
elimination, the existing five-grade nuclear readout, consistently normalized
effective transitions, and calibrated joint identifiability. The existing
Peirce tangent owner describes variations of the model projector.

The constituent theorems retain their native carriers and explicit hypotheses.
In particular, the finite Hilbert realization does not change the countable
algebraic common carrier, electromagnetic triangle support is not a
Wigner--Eckart construction, and the identifiability result assumes calibrated
transition amplitudes and a transfer observation of the configuration weight.
The explicit common-carrier obstruction prevents assuming a two-sided
complementary resolvent on all formal sequences at nonzero coupling.
-/
