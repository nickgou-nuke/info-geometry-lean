/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.External.Auto.NonIsoConf3LogWedgeObstruction

/-!
# Source audit: the quadric logarithmic wedge relation has a concrete defect

For the specified integer triple, all three quadratic denominators are
nonzero, while the common-denominator `dx₀ ∧ dy₀` numerator is 52. This is a
counterexample to the literal dlog Arnold identity for these quadric divisors;
it does not affect the hyperplane-arrangement Arnold relation.
-/

#print axioms NonIsoConf3LogWedgeObstruction.point_triple_nonisotropic
#print axioms NonIsoConf3LogWedgeObstruction.naive_dlog_arnold_relation_obstructed
