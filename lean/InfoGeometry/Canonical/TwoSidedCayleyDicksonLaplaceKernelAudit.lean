/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernel

namespace InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernelAudit

open InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernel

#print axioms hyperbolicKernel_mul_d
#print axioms d_mul_hyperbolicKernel
#print axioms hyperbolicKernel_mul_B
#print axioms B_mul_hyperbolicKernel
#print axioms hyperbolicKernel_mul_polePlus
#print axioms polePlus_mul_hyperbolicKernel
#print axioms hyperbolicKernel_mul_poleMinus
#print axioms poleMinus_mul_hyperbolicKernel
#print axioms twoSidedHyperbolicLaplace_sector_scaling
#print axioms symmetric_vs_antisymmetric_laplace_selectivity
#print axioms moufang_two_sided_laplace_convolution

end InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernelAudit