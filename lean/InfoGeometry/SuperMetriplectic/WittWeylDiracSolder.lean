/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperMetriplectic.WittCyclotomicBridge

/-! The actual neutral Witt pair identifies its triple-unipotent Weyl word
with the existing skew Majorana matrix. Its neutral metric adjoint fixes it;
this is self-adjunction, not metric unitarity.
-/
namespace InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
open Matrix InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

theorem witt_difference_eq_majoranaForm (n : ℕ) :
    wittAnnihilator n - wittCreator n = majoranaForm n := by
  rw [wittAnnihilator_eq_half_sum, wittCreator_eq_half_sub]
  simp only [smul_add, smul_sub]
  have hhalf : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  calc
    _ = (1 / 2 : ℝ) • majoranaForm n + (1 / 2 : ℝ) • majoranaForm n := by abel
    _ = majoranaForm n := by rw [← add_smul, hhalf, one_smul]

theorem witt_triple_unipotent_eq_majoranaForm (n : ℕ) :
    (1 + wittAnnihilator n) * (1 - wittCreator n) * (1 + wittAnnihilator n) =
      majoranaForm n := by
  let a := wittAnnihilator n
  let b := wittCreator n
  change (1 + a) * (1 - b) * (1 + a) = _
  calc
    _ = 1 - (a * b + b * a) + (a - b) + a * a +
        (a - a * b * a) := by noncomm_ring
    _ = majoranaForm n := by
      dsimp [a, b]
      rw [witt_car_anticomm, wittAnnihilator_sq_zero,
        wittAnnihilator_inner_inverse, witt_difference_eq_majoranaForm]
      simp

theorem witt_triple_unipotent_metric_adjoint (n : ℕ) :
    kreinMetric n *
      ((1 + wittAnnihilator n) * (1 - wittCreator n) *
        (1 + wittAnnihilator n)).conjTranspose * kreinMetric n =
      (1 + wittAnnihilator n) * (1 - wittCreator n) * (1 + wittAnnihilator n) := by
  rw [witt_triple_unipotent_eq_majoranaForm]
  exact majoranaForm_metric_adjoint n

theorem solder_witt_triple_unipotent_right (n : ℕ) (l r : Carrier n → ℝ) :
    solder (kreinMetric n) l
      (((1 + wittAnnihilator n) * (1 - wittCreator n) *
        (1 + wittAnnihilator n)) *ᵥ r) =
      solder (kreinMetric n) l r *
        ((1 + wittAnnihilator n) * (1 - wittCreator n) * (1 + wittAnnihilator n)) := by
  rw [witt_triple_unipotent_eq_majoranaForm]
  exact solder_majoranaForm_right n l r

end InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
