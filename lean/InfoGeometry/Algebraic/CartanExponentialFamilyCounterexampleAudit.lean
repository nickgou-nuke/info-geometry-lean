/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebraic.CartanExponentialFamily

/-!
# Finite Cartan exponential-family counterexample audit

The finite two-state witness separates entropy change from log-partition
change.  The replacement statements are the entropy expectation formula and
the KL/Bregman identity in the owner module.
-/

namespace InfoGeometry.Algebraic.CartanExponentialFamilyAudit

#print axioms InfoGeometry.Algebraic.CartanExponentialFamily.boltzmannEntropy_delta_ne_massieu_delta_fin_two
#print axioms InfoGeometry.Algebraic.CartanExponentialFamily.boltzmannEntropy_eq_Phi_sub_expect_parameter
#print axioms InfoGeometry.Algebraic.CartanExponentialFamily.kl_eq_bregmanPhi

end InfoGeometry.Algebraic.CartanExponentialFamilyAudit
