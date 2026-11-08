/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryDiracPair
import InfoGeometry.Canonical.ReflexiveMatrixDirac

/-! Explicit endpoint metric signs determine the Dirac conjugation of the
native boundary pair. Neither sign condition is an ordinary-adjoint claim. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryKrein

open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Algebra.GogberashviliNilpotentCARBridge
open InfoGeometry.Physics
open KitaevBoundaryDiracPair ReflexiveNilpotentFlows

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {N : ℕ} (hN : 0 < N) (ops : MajoranaCliffordOperators N A)
variable (K : KasparovKreinData A)

theorem boundaryAnnihilation_dirac_formula :
    K.diracAdjoint (boundaryAnnihilation hN ops) =
      (2 : ℂ)⁻¹ • (K.diracAdjoint (leftEndpoint hN ops) -
        Complex.I • K.diracAdjoint (rightEndpoint hN ops)) := by
  rw [boundaryAnnihilation_eq_GPlus]
  simp [GPlus, KasparovKreinData.diracAdjoint, star_smul, sub_eq_add_neg,
    mul_add, add_mul]

theorem boundaryCreation_dirac_formula :
    K.diracAdjoint (boundaryCreation hN ops) =
      (2 : ℂ)⁻¹ • (K.diracAdjoint (leftEndpoint hN ops) +
        Complex.I • K.diracAdjoint (rightEndpoint hN ops)) := by
  rw [boundaryCreation_eq_GMinus]
  simp [GMinus, KasparovKreinData.diracAdjoint, star_smul, sub_eq_add_neg,
    mul_add, add_mul]

theorem boundaryAnnihilation_dirac_of_negative
    (hL : K.diracAdjoint (leftEndpoint hN ops) = -leftEndpoint hN ops)
    (hR : K.diracAdjoint (rightEndpoint hN ops) = -rightEndpoint hN ops) :
    K.diracAdjoint (boundaryAnnihilation hN ops) = -boundaryCreation hN ops := by
  rw [boundaryAnnihilation_dirac_formula, hL, hR, boundaryCreation_eq_GMinus]
  simp only [GMinus, smul_neg, smul_sub]
  abel

theorem boundaryCreation_dirac_of_negative
    (hL : K.diracAdjoint (leftEndpoint hN ops) = -leftEndpoint hN ops)
    (hR : K.diracAdjoint (rightEndpoint hN ops) = -rightEndpoint hN ops) :
    K.diracAdjoint (boundaryCreation hN ops) = -boundaryAnnihilation hN ops := by
  rw [boundaryCreation_dirac_formula, hL, hR, boundaryAnnihilation_eq_GPlus]
  simp only [GPlus, smul_neg, smul_add]
  abel

theorem boundaryAnnihilation_dirac_of_positive
    (hL : K.diracAdjoint (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : K.diracAdjoint (rightEndpoint hN ops) = rightEndpoint hN ops) :
    K.diracAdjoint (boundaryAnnihilation hN ops) = boundaryCreation hN ops := by
  rw [boundaryAnnihilation_dirac_formula, hL, hR, boundaryCreation_eq_GMinus]
  rfl

theorem boundaryCreation_dirac_of_positive
    (hL : K.diracAdjoint (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : K.diracAdjoint (rightEndpoint hN ops) = rightEndpoint hN ops) :
    K.diracAdjoint (boundaryCreation hN ops) = boundaryAnnihilation hN ops := by
  rw [boundaryCreation_dirac_formula, hL, hR, boundaryAnnihilation_eq_GPlus]
  rfl

/-- The full represented two-by-two matrix transforms with the split metric. -/
theorem boundary_pairMatrix_dirac
    (hL : K.diracAdjoint (leftEndpoint hN ops) = -leftEndpoint hN ops)
    (hR : K.diracAdjoint (rightEndpoint hN ops) = -rightEndpoint hN ops)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    K.diracAdjoint (pairMatrixLinear (boundaryAnnihilation hN ops) (boundaryCreation hN ops) M) =
      pairMatrixLinear (boundaryAnnihilation hN ops) (boundaryCreation hN ops)
        (pairDiracMetric * M.conjTranspose * pairDiracMetric) :=
  pairMatrixLinear_dirac K
    (boundaryAnnihilation_dirac_of_negative hN ops K hL hR)
    (boundaryCreation_dirac_of_negative hN ops K hL hR) M

end InfoGeometry.Canonical.KitaevBoundaryKrein
