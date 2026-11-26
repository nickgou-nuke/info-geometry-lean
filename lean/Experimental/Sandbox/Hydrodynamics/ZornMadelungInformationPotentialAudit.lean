/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Experimental.Sandbox.Hydrodynamics.ZornMadelungInformationPotential

namespace InfoGeometry.Experimental.Hydrodynamics.Audit

open InfoGeometry.Experimental.Hydrodynamics

-- Section 1: Vec3 Cross-Term Cancellation
#print axioms Vec3.dot_comm
#print axioms Vec3.dot_add_sub_cancel

-- Section 2: Zorn Determinant Decomposition & Incompressible Balance
#print axioms ZornMatrix.zorn_potential_det_split
#print axioms ZornMatrix.zorn_kinetic_fisher_balance

-- Section 3: Bohm-Fisher Potential Relations
#print axioms bohm_potential_is_fisher_gradient
#print axioms bohm_potential_balance

-- Section 4: Master Verification Certificate

end InfoGeometry.Experimental.Hydrodynamics.Audit
