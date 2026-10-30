/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Physics.MDPASJMSouriauGlobalObstruction
import InfoGeometry.Physics.MDPASJMSouriauExternalAudit

/-!
# Source audit: finite cellular obstruction and honest global scope

The minimal cellular `S²` model has a closed non-exact area 2-cochain. The
external audit packet records finite symplectic/KK/readout statements while
explicitly treating unavailable global de Rham computations as timeouts.
-/

#print axioms InfoGeometry.Physics.MDPASJMSouriauGlobalObstruction.sphereArea_not_exact
#print axioms InfoGeometry.Physics.MDPASJMSouriauGlobalObstruction.kk5_null_implies_four_mass_shell
#print axioms InfoGeometry.Physics.MDPASJMSouriauExternalAudit.observed_timeout_audit_packet
#print axioms InfoGeometry.Physics.MDPASJMSouriauExternalAudit.finite_global_story_packet
