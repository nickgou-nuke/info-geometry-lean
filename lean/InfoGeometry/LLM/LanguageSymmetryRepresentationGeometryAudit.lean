/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.LanguageSymmetryRepresentationGeometryPoset

/-!
# Public declaration axiom audit for language symmetry

Each public theorem and definition in the six source modules is listed below.
The printed dependencies are to be checked against the permitted foundational
axioms `propext`, `Classical.choice`, and `Quot.sound`.
-/

/-! ## LanguageSymmetryHelpers -/

#print axioms InfoGeometry.LLM.LanguageSymmetry.compressed_square_eq_helper_product
#print axioms InfoGeometry.LLM.LanguageSymmetry.helper_product_commutes
#print axioms InfoGeometry.LLM.LanguageSymmetry.helper_gram_ne_zero_iff
#print axioms InfoGeometry.LLM.LanguageSymmetry.adjoint_helper_intertwines
#print axioms InfoGeometry.LLM.LanguageSymmetry.helper_gram_commutes
#print axioms InfoGeometry.LLM.LanguageSymmetry.compressed_square_eq_helper_gram
#print axioms InfoGeometry.LLM.LanguageSymmetry.compressed_square_posSemidef
#print axioms InfoGeometry.LLM.LanguageSymmetry.compressed_square_ne_zero_iff
#print axioms InfoGeometry.LLM.LanguageSymmetry.ablationProjection
#print axioms InfoGeometry.LLM.LanguageSymmetry.ablationExchange
#print axioms InfoGeometry.LLM.LanguageSymmetry.ablationProjection_idempotent
#print axioms InfoGeometry.LLM.LanguageSymmetry.ablationExchange_direct_zero
#print axioms InfoGeometry.LLM.LanguageSymmetry.ablationExchange_square_compression
#print axioms InfoGeometry.LLM.LanguageSymmetry.ablationExchange_square_compression_ne_zero
#print axioms InfoGeometry.LLM.LanguageSymmetry.ablationExchange_not_commuting

/-! ## LanguageSymmetryFourier -/

#print axioms InfoGeometry.LLM.LanguageSymmetry.kernelEigenvalue
#print axioms InfoGeometry.LLM.LanguageSymmetry.circulant_translation_invariant
#print axioms InfoGeometry.LLM.LanguageSymmetry.translation_invariant_eq_circulant
#print axioms InfoGeometry.LLM.LanguageSymmetry.circulant_mulVec_character
#print axioms InfoGeometry.LLM.LanguageSymmetry.circulant_toMatrix_complexBasis
#print axioms InfoGeometry.LLM.LanguageSymmetry.character_real_imag_unit_circle
#print axioms InfoGeometry.LLM.LanguageSymmetry.productCharacter
#print axioms InfoGeometry.LLM.LanguageSymmetry.productCharacter_apply
#print axioms InfoGeometry.LLM.LanguageSymmetry.productCharacterEquiv
#print axioms InfoGeometry.LLM.LanguageSymmetry.circulant_add_separable_kronecker
#print axioms InfoGeometry.LLM.LanguageSymmetry.productCharacterBasis
#print axioms InfoGeometry.LLM.LanguageSymmetry.productCharacterBasis_apply
#print axioms InfoGeometry.LLM.LanguageSymmetry.kernelEigenvalue_add_separable
#print axioms InfoGeometry.LLM.LanguageSymmetry.additive_kernel_mixed_character_zero
#print axioms InfoGeometry.LLM.LanguageSymmetry.seasonalBinaryBasis
#print axioms InfoGeometry.LLM.LanguageSymmetry.seasonalBinaryBasis_apply
#print axioms InfoGeometry.LLM.LanguageSymmetry.binary_character_eq_one_or_neg_one
#print axioms InfoGeometry.LLM.LanguageSymmetry.circulant_mulVec_seasonalBinaryBasis

/-! ## LanguageSymmetryBinary -/

#print axioms InfoGeometry.LLM.LanguageSymmetry.log_ratio_eq_zero_iff
#print axioms InfoGeometry.LLM.LanguageSymmetry.binaryLogMean
#print axioms InfoGeometry.LLM.LanguageSymmetry.binaryLogContrast
#print axioms InfoGeometry.LLM.LanguageSymmetry.binary_log_affine
#print axioms InfoGeometry.LLM.LanguageSymmetry.binary_factor_pos
#print axioms InfoGeometry.LLM.LanguageSymmetry.binaryLogMean_eq_log
#print axioms InfoGeometry.LLM.LanguageSymmetry.binaryLogContrast_eq_log_ratio
#print axioms InfoGeometry.LLM.LanguageSymmetry.binary_log_affine_closed_form
#print axioms InfoGeometry.LLM.LanguageSymmetry.attribute_product_pos
#print axioms InfoGeometry.LLM.LanguageSymmetry.log_attribute_product

/-! ## LanguageSymmetryWalsh -/

#print axioms InfoGeometry.LLM.LanguageSymmetry.kernelEigenvalue_character
#print axioms InfoGeometry.LLM.LanguageSymmetry.kernelEigenvalue_character_expansion
#print axioms InfoGeometry.LLM.LanguageSymmetry.coordinateSign
#print axioms InfoGeometry.LLM.LanguageSymmetry.coordinateCharacter
#print axioms InfoGeometry.LLM.LanguageSymmetry.coordinateCharacter_apply
#print axioms InfoGeometry.LLM.LanguageSymmetry.coordinateSign_sq
#print axioms InfoGeometry.LLM.LanguageSymmetry.coordinateSign_sub
#print axioms InfoGeometry.LLM.LanguageSymmetry.coordinateCharacter_single
#print axioms InfoGeometry.LLM.LanguageSymmetry.coordinateCharacter_ne_zero
#print axioms InfoGeometry.LLM.LanguageSymmetry.coordinateCharacter_injective
#print axioms InfoGeometry.LLM.LanguageSymmetry.attributeLogKernel
#print axioms InfoGeometry.LLM.LanguageSymmetry.attributeLogKernel_sub
#print axioms InfoGeometry.LLM.LanguageSymmetry.attributeLogKernel_product_pos
#print axioms InfoGeometry.LLM.LanguageSymmetry.attributeLogKernel_expansion
#print axioms InfoGeometry.LLM.LanguageSymmetry.attributeLogKernel_eigenvalue
#print axioms InfoGeometry.LLM.LanguageSymmetry.attributeLogKernel_constant_eigenvalue
#print axioms InfoGeometry.LLM.LanguageSymmetry.attributeLogKernel_coordinate_eigenvalue
#print axioms InfoGeometry.LLM.LanguageSymmetry.attributeLogKernel_other_eigenvalue_zero
#print axioms InfoGeometry.LLM.LanguageSymmetry.attributeLogKernel_mulVec_character

/-! ## LanguageSymmetryToeplitz -/

#print axioms InfoGeometry.LLM.LanguageSymmetry.expToeplitz3
#print axioms InfoGeometry.LLM.LanguageSymmetry.tridiagonalPrecision3
#print axioms InfoGeometry.LLM.LanguageSymmetry.cyclicShift3
#print axioms InfoGeometry.LLM.LanguageSymmetry.endpointProjection3
#print axioms InfoGeometry.LLM.LanguageSymmetry.endpointProjection3_not_commute_cyclicShift3
#print axioms InfoGeometry.LLM.LanguageSymmetry.expToeplitz3_not_commute_cyclicShift3
#print axioms InfoGeometry.LLM.LanguageSymmetry.expToeplitz3_mul_precision
#print axioms InfoGeometry.LLM.LanguageSymmetry.precision_mul_expToeplitz3
#print axioms InfoGeometry.LLM.LanguageSymmetry.expToeplitz3_half_not_commute_cyclicShift3
#print axioms InfoGeometry.LLM.LanguageSymmetry.expToeplitz3_mul_scaled_precision
#print axioms InfoGeometry.LLM.LanguageSymmetry.scaled_precision_mul_expToeplitz3
#print axioms InfoGeometry.LLM.LanguageSymmetry.expToeplitz3_inv

/-! ## LanguageSymmetryRepresentationGeometryPoset -/

#print axioms InfoGeometry.LLM.LanguageSymmetry.helper_gram_translation_invariant
#print axioms InfoGeometry.LLM.LanguageSymmetry.helper_gram_eq_circulant
#print axioms InfoGeometry.LLM.LanguageSymmetry.helper_gram_mulVec_character
#print axioms InfoGeometry.LLM.LanguageSymmetry.helper_gram_toMatrix_complexBasis
#print axioms InfoGeometry.LLM.LanguageSymmetry.seasonal_attribute_eigenvalue
#print axioms InfoGeometry.LLM.LanguageSymmetry.seasonal_attribute_seasonal_eigenvalue
#print axioms InfoGeometry.LLM.LanguageSymmetry.seasonal_attribute_coordinate_eigenvalue
