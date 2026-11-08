/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.SouriauOnsagerBKMStrictPositivity
import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm

noncomputable section

namespace SouriauOnsagerBKM

variable {n : ℕ}

/- The strictly positive finite BKM real bilinear form cannot satisfy a
   global anti-invariance equation under a linear map on a nonzero input. -/
theorem FaithfulDensityOperator.bkmRealBilinForm_no_antiInvariant
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (J : FiniteOperatorAlgebra n →ₗ[ℝ] FiniteOperatorAlgebra n)
    (hanti : ∀ A B : FiniteOperatorAlgebra n,
      D.bkmRealBilinForm h_rpow (J A) (J B) =
        - D.bkmRealBilinForm h_rpow A B)
    {A : FiniteOperatorAlgebra n} (hA : A ≠ 0) :
    False := by
  have hAA : 0 < D.bkmRealBilinForm h_rpow A A := by
    rw [FaithfulDensityOperator.bkmRealBilinForm_apply]
    exact D.kuboMoriPairing_self_pos A h_rpow hA
  have hJA : J A ≠ 0 := by
    intro hzero
    have hzero_pair : D.bkmRealBilinForm h_rpow (J A) (J A) = 0 := by
      rw [hzero]
      simp
    have hneg : 0 = -D.bkmRealBilinForm h_rpow A A :=
      hzero_pair.symm.trans (hanti A A)
    linarith
  have hJAA : 0 < D.bkmRealBilinForm h_rpow (J A) (J A) := by
    rw [FaithfulDensityOperator.bkmRealBilinForm_apply]
    exact D.kuboMoriPairing_self_pos (J A) h_rpow hJA
  rw [hanti A A] at hJAA
  linarith

end SouriauOnsagerBKM
