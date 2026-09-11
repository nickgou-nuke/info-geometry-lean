/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import InfoGeometry.Physics.AmariSurprisalIwasawaSynthesis

/-!
# Audit Module: AmariSurprisalIwasawaSynthesisAudit

Automated kernel verification of Section 5.87 / 5.96:
- Zero debt: 0 sorry, 0 admit.
- Verifies Shannon entropy as expected surprisal.
- Verifies CLR traceless projection onto the Cartan subalgebra a ⊂ sl(D, ℝ).
- Verifies natural parameters as surprisal contrasts.
- Verifies Bhattacharyya-Wootters square-root embedding into the unit sphere S^{D-1}.
- Verifies spinorial Born rule reconstruction and Wootters self-overlap.
- Verifies Inönü-Wigner curvature contraction: K(0) = 1/4 (sphere) and K(±1) = 0 (flat).
- Verifies complex amplitude modulus and quadric hypersurface norm on T* S^{D-1}.
- Verifies unimodular Iwasawa KAN determinant product on SL(D, ℝ).
- Certified Axiom Footprint: standard foundational axioms only [propext, Classical.choice, Quot.sound].
-/

namespace InfoGeometry.Physics.AmariSurprisalIwasawaSynthesisAudit

open InfoGeometry.Physics.AmariSurprisalIwasawa

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {D : ℕ}

-- 1. Signature and Type-Level Verification
#check (PositiveDist.shannon_entropy_eq_neg_sum_p_log :
  ∀ (P : PositiveDist D), P.shannonEntropy = - ∑ i, P.p i * Real.log (P.p i))

#check (PositiveDist.sum_clr_zero :
  ∀ (P : PositiveDist D) (hD : 0 < D), ∑ i, P.clr hD i = 0)

#check (PositiveDist.natural_param_eq_log_ratio :
  ∀ (P : PositiveDist D) (ref : Fin D) (i : Fin D),
    P.naturalParam ref i = Real.log (P.p i / P.p ref))

#check (PositiveDist.sum_amplitude_sq_eq_one :
  ∀ (P : PositiveDist D), ∑ i, (amplitude P i) ^ 2 = 1)

#check (PositiveDist.amplitude_sq_eq_prob :
  ∀ (P : PositiveDist D) (i : Fin D), (amplitude P i) ^ 2 = P.p i)

#check (PositiveDist.wootters_self_overlap_one :
  ∀ (P : PositiveDist D), ∑ i, Real.sqrt (P.p i * P.p i) = 1)

#check (amari_curvature_round_sphere : amariCurvature 0 = 1 / 4)

#check (amari_curvature_flat_limits : amariCurvature 1 = 0 ∧ amariCurvature (-1) = 0)

#check (PositiveDist.complex_amplitude_modulus :
  ∀ (P : PositiveDist D) (phi : Fin D → ℝ) (k : Fin D),
    c_abs (complexAmplitude P phi k) = amplitude P k)

#check (PositiveDist.complex_quadric_sum :
  ∀ (P : PositiveDist D) (phi : Fin D → ℝ),
    ∑ k, (c_abs (complexAmplitude P phi k)) ^ 2 = 1)

#check (IwasawaDecompositionData.unimodular_product :
  ∀ (decomp : IwasawaDecompositionData), decomp.det_K * decomp.det_A * decomp.det_N = 1)

#check (amari_surprisal_iwasawa_synthesis :
  ∀ (P : PositiveDist D) (hD : 0 < D) (ref : Fin D) (phi : Fin D → ℝ)
    (decomp : IwasawaDecompositionData),
    (P.shannonEntropy = - ∑ i, P.p i * Real.log (P.p i)) ∧
    (∑ i, P.clr hD i = 0) ∧
    (P.naturalParam ref ref = 0) ∧
    (∑ i, (amplitude P i) ^ 2 = 1) ∧
    (∑ i, Real.sqrt (P.p i * P.p i) = 1) ∧
    (amariCurvature 0 = 1 / 4) ∧
    (amariCurvature 1 = 0 ∧ amariCurvature (-1) = 0) ∧
    (∑ k, (c_abs (complexAmplitude P phi k)) ^ 2 = 1) ∧
    (decomp.det_K * decomp.det_A * decomp.det_N = 1))

-- 2. Axiom Footprint Verification
#print axioms PositiveDist.shannon_entropy_eq_neg_sum_p_log
#print axioms PositiveDist.sum_clr_zero
#print axioms PositiveDist.sum_amplitude_sq_eq_one
#print axioms amari_curvature_round_sphere
#print axioms amari_curvature_flat_limits
#print axioms PositiveDist.complex_quadric_sum
#print axioms IwasawaDecompositionData.unimodular_product
#print axioms amari_surprisal_iwasawa_synthesis

end InfoGeometry.Physics.AmariSurprisalIwasawaSynthesisAudit
