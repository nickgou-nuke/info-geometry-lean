/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KMSOperatorExpRemainder

/-!
# Axiom audit for the operator exponential remainder owner.
-/

namespace InfoGeometry.Canonical.KMSOperatorExpRemainderAudit

open InfoGeometry.Canonical.KMSOperatorExpRemainder

#check @expSecondOrderTail
#check @exp_sub_one_sub_eq_secondOrderTail
#check @norm_exp_sub_one_sub_le_sq
#check @normedSpaceExp_hasBregmanQuadraticBound

#print axioms exp_sub_one_sub_eq_secondOrderTail
#print axioms norm_exp_sub_one_sub_le_sq
#print axioms normedSpaceExp_hasBregmanQuadraticBound

end InfoGeometry.Canonical.KMSOperatorExpRemainderAudit
