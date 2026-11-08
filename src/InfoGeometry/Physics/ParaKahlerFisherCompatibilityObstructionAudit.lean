/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction

/-!
# Source audit: positivity and fixed para-symmetry force zero diagonal

The replacement statement is conditional and explicit: nonnegative Fisher
diagonals together with a globally fixed fundamental symmetry force every
diagonal to vanish. A finite log-partition Hessian is strictly positive when
the generator is nonconstant, so a global identification with that Hessian or
variance is impossible under those assumptions.
-/

#print axioms InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction.fisher_diagonal_eq_zero_of_nonneg
#print axioms InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction.fisher_diagonal_eq_zero_of_fixed_nonneg
#print axioms InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction.finite_logPartition_hessian_pos_of_generator_ne
#print axioms InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction.no_global_paraMetric_fisher_hessian_identification
#print axioms InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction.no_global_paraMetric_fisher_variance_identification
#print axioms InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction.no_global_paraMetric_fisher_hessian_identification_of_fixed
#print axioms InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction.no_global_paraMetric_fisher_variance_identification_of_fixed
