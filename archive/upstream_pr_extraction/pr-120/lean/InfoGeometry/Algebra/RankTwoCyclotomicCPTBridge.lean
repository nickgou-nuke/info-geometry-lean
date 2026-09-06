/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.RankTwoCyclotomicArtinBridge
import InfoGeometry.Physics.CPTGaloisBridge

namespace InfoGeometry.Algebra.RankTwoCyclotomicCPTBridge

open InfoGeometry.Algebra.RankTwoCyclotomicArtinBridge
open InfoGeometry.Physics.CPTGaloisBridge

variable {K : Type*} [Field K]

/-- On a nonzero twelfth root of unity, the inverse-based rank-two parameter
    agrees with the eleventh-power form used by the CPT arithmetic owner. -/
theorem quantumInteger_eq_root3Alg
    (ζ : K) (hζ : ζ ^ 12 = 1) (hζ0 : ζ ≠ 0) :
    quantumInteger ζ = root3Alg ζ := by
  have hinv : ζ⁻¹ = ζ ^ 11 := by
    calc
      ζ⁻¹ = ζ⁻¹ * 1 := by rw [mul_one]
      _ = ζ⁻¹ * ζ ^ 12 := by rw [hζ]
      _ = ζ⁻¹ * (ζ ^ 11 * ζ) := by rw [← pow_succ]
      _ = (ζ⁻¹ * ζ) * ζ ^ 11 := by ring
      _ = ζ ^ 11 := by rw [inv_mul_cancel₀ hζ0, one_mul]
  simp [quantumInteger, root3Alg, hinv]

/-- The CPT cyclotomic parameter is therefore an `I₂(6)` rank-two parameter. -/
theorem quantumInteger_six_of_cyclotomic
    (ζ : K) (hφ : cyclotomic12 ζ = 0) :
    (quantumInteger ζ) ^ 2 = 3 := by
  have hζ12 : ζ ^ 12 = 1 := zeta_pow_twelve_of_cyclotomic ζ hφ
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    rw [hzero] at hφ
    norm_num [cyclotomic12] at hφ
  have heq : quantumInteger ζ = root3Alg ζ :=
    quantumInteger_eq_root3Alg ζ hζ12 hζ0
  rw [heq]
  exact root3Alg_sq ζ hφ

end InfoGeometry.Algebra.RankTwoCyclotomicCPTBridge
