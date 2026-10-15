import InfoGeometry.Canonical.SupertraceScaleKernelSplit

/-!
# Audit declarations for the finite supertrace scale/kernel split.

This companion checks the kernel-facing declarations and their axiom footprints.
The parent module intentionally makes no projective or Krein-geometric claim.
-/

namespace InfoGeometry.Canonical.SupertraceScaleKernelSplit.Audit

open InfoGeometry.Canonical.SupertraceScaleKernelSplit

#check supertrace_scalarBlockGenerator
#check supertrace_even_neg_transpose
#check supertrace_even_neg_transpose_eq_zero_iff
#check blockBerezinian_exp_scalar_scale
#check blockBerezinian_exp_even_neg_transpose_eq_one
#check scalarBlockGenerator_supertrace_zero_iff
#check scalar_kernel_decomposition
#check scalar_kernel_decomposition_unique

#print axioms supertrace_scalarBlockGenerator
#print axioms supertrace_even_neg_transpose_eq_zero_iff
#print axioms blockBerezinian_exp_scalar_scale
#print axioms blockBerezinian_exp_even_neg_transpose_eq_one
#print axioms scalar_kernel_decomposition
#print axioms scalar_kernel_decomposition_unique

end InfoGeometry.Canonical.SupertraceScaleKernelSplit.Audit
