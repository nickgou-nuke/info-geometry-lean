import InfoGeometry.Algebra.ChiralZornCARAndSchurBridge

/-!
# Canonical compatibility forwarder for ChiralZornCARAndSchurBridge

This module re-exports `InfoGeometry.Algebra.ChiralZornCARAndSchurBridge` to preserve
backward compatibility for the Canonical subsystem while maintaining a single canonical
algebraic owner in `InfoGeometry.Algebra`.
-/

export InfoGeometry.Algebra.GogberashviliNilpotentCARBridge
  (DPlus DMinus GPlus GMinus D_plus D_minus G_plus G_minus
   DPlus_add_DMinus DPlus_idempotent DMinus_idempotent
   DPlus_mul_DMinus DMinus_mul_DPlus
   GPlus_square_zero GMinus_square_zero
   GPlus_mul_GMinus GMinus_mul_GPlus
   GPlus_GMinus_CAR full_car_packet
   D_plus_add_D_minus D_plus_idempotent D_minus_idempotent
   D_plus_mul_D_minus D_minus_mul_D_plus
   G_plus_square_zero G_minus_square_zero
   G_plus_mul_G_minus G_minus_mul_G_plus
   G_plus_G_minus_CAR)

export InfoGeometry.Algebra.ZornNormSchurScalarSpecialization
  (blockMatrix schurComplement berezinianScalar zornNorm
   det_blockMatrix schur_scalar_formula zornNorm_eq_schur_mul_beta
   berezinian_eq_zornNorm_div_sq berezinian_eq_det_div_sq
   scalar_schur_berezinian_packet
   zorn_norm berezinian_eq_zorn_norm_div_sq zorn_norm_eq_schur_mul_beta)

export InfoGeometry.Algebra.BdGSchurBerezinianCompatibility
  (bdgBlock det_bdgBlock schur_bdgBlock berezinian_bdgBlock bdg_schur_berezinian_packet)