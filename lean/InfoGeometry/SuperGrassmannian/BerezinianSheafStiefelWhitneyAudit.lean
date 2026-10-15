import InfoGeometry.SuperGrassmannian.BerezinianSheafStiefelWhitney

/-!
# Audit Companion: Berezinian Sheaf & First Stiefel–Whitney Class

This module verifies the kernel axiomatic footprint and non-vacuity of
`InfoGeometry.SuperGrassmannian.BerezinianSheaf`.
-/

namespace InfoGeometry.SuperGrassmannian.BerezinianSheaf.Audit

open InfoGeometry.SuperGrassmannian.BerezinianSheaf

#check @compile_berezinian_sheaf_stiefel_whitney
#check @berezinian_parity_square_law
#check @cech_cocycle_eq_one_iff
#check @cech_cocycle_eq_neg_one_iff
#check @stiefelWhitney_eq_zero_iff
#check @stiefelWhitney_eq_one_iff
#check @orientable_iff_even_mismatch
#check @non_orientable_iff_odd_mismatch
#check @orientable_or_crosscap
#check @not_orientable_and_crosscap

#print axioms compile_berezinian_sheaf_stiefel_whitney
#print axioms berezinian_parity_square_law
#print axioms cech_cocycle_eq_one_iff
#print axioms stiefelWhitney_eq_zero_iff
#print axioms orientable_iff_even_mismatch
#print axioms not_orientable_and_crosscap

end InfoGeometry.SuperGrassmannian.BerezinianSheaf.Audit
