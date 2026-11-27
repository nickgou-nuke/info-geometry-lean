/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore
import InfoGeometry.Arithmetic.AlpogeDeligneKreinResidueBridge

/-! Declaration axiom audit for the finite algebraic and contour results. -/

open InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore
open InfoGeometry.Arithmetic.AlpogeDeligneKreinResidueBridge

#print axioms distinct_power_sum_eigenvalue_bound
#print axioms tensor_tower_eigenvalue_bound
#print axioms fourier_bilinear_plancherel
#print axioms chained_bilinear_transfer_l2_and_sum_bound
#print axioms gysin_plus_two_same_sign_remainder
#print axioms finite_positiveMultiplicities_pole_cauchyResidue_nonzero
