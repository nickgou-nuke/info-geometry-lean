/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.SmoothedMangoldtMellin
import InfoGeometryGRH.VerifiedGRH
import InfoGeometryGRH.PrimeRemainderBridge
import InfoGeometryGRH.RealDoubledGRH

/-!
# Optional integration of the pinned Dirichlet GRH proof

This umbrella exposes the native smoothing and Mellin owners together with
their exact connection to the readable `lsernau/grh-lean` proof. The external
dependency belongs only to this independently pinned package. Import the
canonical `InfoGeometry.Arithmetic` owners directly for the native conditional
interfaces without that dependency.
-/
