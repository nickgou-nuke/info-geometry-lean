/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PluckerInfinityGeometry
import InfoGeometry.Projective.ExteriorKleinCliffordInversion
import InfoGeometry.Canonical.RealModularConjugationBridge
import InfoGeometry.Twistor.PluckerCl55InfinityBridge
import InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
import InfoGeometry.Canonical.Cl55InfinityChiralCharge
import InfoGeometry.Canonical.Cl55InfinityGradeReversal

import InfoGeometry.Twistor.PluckerPinAffineRestriction
import InfoGeometry.Clifford.Cl55NativeInternalFiveGrading
import InfoGeometry.Clifford.Cl55WittCalibratedColimit
import InfoGeometry.Canonical.Cl55ChiralAnalyticKMS
import InfoGeometry.Canonical.FilteredGNSHestenesPhaseCone
import InfoGeometry.Canonical.MatrixTraceTomitaColimit
import InfoGeometry.Canonical.FiniteSeedGibbsTomitaClosability
import InfoGeometry.Canonical.ExteriorFockOperatorLaws
import InfoGeometry.Twistor.WittenSpinorBCFW
import InfoGeometry.Twistor.WittenParkeTaylor
import InfoGeometry.Twistor.WittenIncidence
import InfoGeometry.Twistor.WittenCollinearityOperator
import InfoGeometry.Twistor.WittenExteriorScalarExtension

/-! Focused aggregate for Plücker/infinity geometry, its native Clifford
inversion domain, the existing `Cl55` source/sink grading and chiral charge,
and real bounded-operator modular conjugation.
No equality between the infinity twistor and a modular operator is asserted. -/
