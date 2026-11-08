/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FresnelCl11Isomorphism

/-!
# Concrete Examples and Axiom Audit for Section 124's Coordinate/Clifford Bridge
Target: `InfoGeometry/QuantumContext/FresnelCl11IsomorphismAudit.lean`

Verifies over `ℤ` (`decide`) that the coordinate-record map `M(ψ_+, ψ_-)` maps
slit pairs `(3, 4)` and `(1, 2)` to `[[3, 4], [1, 2]]` with `det(M) = 2 = H_{(+,-)}`,
`‖M‖²_HS = 30 = I_+ + I_-`, and `M · Mᵀ = [[25, 11], [11, 5]]` with `det(M · Mᵀ) = 4 = (det M)²`.
-/

namespace InfoGeometry.QuantumContext.FresnelCl11IsomorphismAudit

open InfoGeometry.QuantumContext.FresnelCl11Isomorphism
open InfoGeometry.QuantumContext.SorkinFluxQubit

/-- Concrete verification of `embedFresnelPair`, `det = H_{(+,-)}`, `frobeniusNormSq = I_+ + I_-`,
and `M · Mᵀ = [[25, 11], [11, 5]]` over `ℤ`. -/
theorem sample_fresnel_cl11_isomorphism_int :
    let ψ_pos : FresnelWave ℤ := ⟨3, 4⟩
    let ψ_neg : FresnelWave ℤ := ⟨1, 2⟩
    let M := Cl11Op.embedFresnelPair ψ_pos ψ_neg
    M = ⟨3, 4, 1, 2⟩ ∧
    Cl11Op.det M = 2 ∧
    FresnelWave.yinH ψ_pos ψ_neg = 2 ∧
    Cl11Op.frobeniusNormSq M = 30 ∧
    Cl11Op.mul M (Cl11Op.transpose M) = ⟨25, 11, 11, 5⟩ ∧
    Cl11Op.det (Cl11Op.mul M (Cl11Op.transpose M)) = 4 := by
  decide

/-- Concrete verification of the parameter-conjugated Gram matrix entry `(M · U(c, s) · Mᵀ).m12` over `ℤ`. -/
theorem sample_parameterized_gram_int :
    let ψ_pos : FresnelWave ℤ := ⟨3, 4⟩
    let ψ_neg : FresnelWave ℤ := ⟨1, 2⟩
    let M := Cl11Op.embedFresnelPair ψ_pos ψ_neg
    (Cl11Op.mul (Cl11Op.mul M (Cl11Op.parameterMatrix 0 1)) (Cl11Op.transpose M)).m12 = 2 ∧
    (Cl11Op.mul (Cl11Op.mul M (Cl11Op.parameterMatrix 1 0)) (Cl11Op.transpose M)).m12 = 11 := by
  decide

#print axioms Cl11Op.sampleCl11OpInt_ne_zero
#print axioms Cl11Op.cl11Op_mul_noncommutative
#print axioms Cl11Op.fresnelPairCoordEquiv
#print axioms Cl11Op.embed_add
#print axioms Cl11Op.embed_scale
#print axioms Cl11Op.det_embed_eq_yin_symplectic_H
#print axioms Cl11Op.frobenius_norm_sq_embed_eq_intensity_sum
#print axioms Cl11Op.gram_matrix_embed_explicit
#print axioms Cl11Op.trace_gram_embed_eq_intensity_sum
#print axioms Cl11Op.det_gram_embed_eq_yin_sq
#print axioms Cl11Op.parameterized_gram_m12
#print axioms Cl11Op.ab_prob_from_cl11_invariants
#print axioms Cl11Op.ab_prob_from_cl11_invariants_of_unit_circle
#print axioms Cl11Op.ofNativeMatrix_toNativeMatrix
#print axioms Cl11Op.toNativeMatrix_ofNativeMatrix
#print axioms Cl11Op.toNativeMatrix_mul
#print axioms Cl11Op.det_eq_nativeMatrix_det
#print axioms Cl11Op.toNativeClifford_mul
#print axioms Cl11Op.nativeMatrix_fresnelToNativeClifford
#print axioms Cl11Op.nativeCliffordDet_fresnel_eq_yin
#print axioms sample_fresnel_cl11_isomorphism_int
#print axioms sample_parameterized_gram_int

end InfoGeometry.QuantumContext.FresnelCl11IsomorphismAudit
