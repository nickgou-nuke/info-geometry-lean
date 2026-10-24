/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperMetriplectic.WittCyclotomicBridge
import InfoGeometry.Canonical.ReflexiveNilpotentFlows

/-! The actual neutral Witt pair identifies its triple-unipotent Weyl word
with the existing skew Majorana matrix. Its neutral metric adjoint fixes it;
this is self-adjunction, not metric unitarity.
-/
namespace InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
open Matrix InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open InfoGeometry.Canonical.ReflexiveNilpotentFlows
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

theorem witt_difference_eq_majoranaForm (n : ℕ) :
    wittAnnihilator n - wittCreator n = majoranaForm n := by
  rw [wittAnnihilator_eq_half_sum, wittCreator_eq_half_sub]
  simp only [smul_add, smul_sub]
  have hhalf : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  calc
    _ = (1 / 2 : ℝ) • majoranaForm n + (1 / 2 : ℝ) • majoranaForm n := by abel
    _ = majoranaForm n := by rw [← add_smul, hhalf, one_smul]

theorem witt_weyl_eq_majoranaForm (n : ℕ) :
    weyl (wittAnnihilator n) (wittCreator n) = majoranaForm n := by
  simp only [weyl, complement, support, witt_car_anticomm, sub_self, zero_add,
    witt_difference_eq_majoranaForm]

theorem witt_weylInv_eq_neg_majoranaForm (n : ℕ) :
    weylInv (wittAnnihilator n) (wittCreator n) = -majoranaForm n := by
  simp only [weylInv, complement, support, witt_car_anticomm, sub_self,
    zero_sub, witt_difference_eq_majoranaForm]

theorem witt_triple_unipotent_eq_majoranaForm (n : ℕ) :
    (1 + wittAnnihilator n) * (1 - wittCreator n) * (1 + wittAnnihilator n) =
      majoranaForm n := by
  rw [weyl_factorization (wittAnnihilator_sq_zero n)
    (wittAnnihilator_inner_inverse n), witt_weyl_eq_majoranaForm]

theorem witt_weyl_metric_adjoint (n : ℕ) :
    kreinMetric n * (weyl (wittAnnihilator n) (wittCreator n)).conjTranspose *
      kreinMetric n = weyl (wittAnnihilator n) (wittCreator n) := by
  rw [witt_weyl_eq_majoranaForm]
  exact majoranaForm_metric_adjoint n

theorem solder_witt_weyl_right (n : ℕ) (l r : Carrier n → ℝ) :
    solder (kreinMetric n) l (weyl (wittAnnihilator n) (wittCreator n) *ᵥ r) =
      solder (kreinMetric n) l r * weyl (wittAnnihilator n) (wittCreator n) := by
  rw [witt_weyl_eq_majoranaForm]
  exact solder_majoranaForm_right n l r

end InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
