/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceWeightedTrace

/-! Weyl transport of proper-support weights. No full-support CAR or
positivity assumption is needed. The Weyl element is an ambient unit. -/
namespace InfoGeometry.Canonical.PeirceWeylDensityTransport
open ReflexiveNilpotentFlows PeirceWeightedTrace
open InfoGeometry.NCG InfoGeometry.OperatorAlgebra.TracialCARDensity
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {d B : A}
variable (hd : d*d=0) (hB : B*B=0) (hr : d*B*d=d) (hs : B*d*B=B)
include hs

theorem weyl_conjugates_weight (a b : R) :
    (weylUnit hd hB hr : A) * supportWeight a b d B *
      (↑((weylUnit hd hB hr)⁻¹) : A) = supportWeight b a d B := by
  obtain ⟨hp, hm⟩ := weyl_swap_supports hd hB hr hs
  change weyl d B * (a • (B*d) + b • (d*B)) * weylInv d B =
    b • (B*d) + a • (d*B)
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hp, hm]
  abel

theorem weyl_weight_pullback (τ : TracialFunctional R A) (a b : R) (x : A) :
    weighted τ (supportWeight b a d B) x =
      weighted τ (supportWeight a b d B)
        ((↑((weylUnit hd hB hr)⁻¹) : A) * x * (weylUnit hd hB hr : A)) := by
  rw [← weyl_conjugates_weight hd hB hr hs a b]
  exact inverse_pullback τ _ _ _

theorem weyl_weight_joint_covariance (τ : TracialFunctional R A) (a b : R) (x : A) :
    weighted τ (supportWeight b a d B)
        ((weylUnit hd hB hr : A) * x * (↑((weylUnit hd hB hr)⁻¹) : A)) =
      weighted τ (supportWeight a b d B) x := by
  rw [← weyl_conjugates_weight hd hB hr hs a b]
  exact joint_covariance τ _ _ _

end InfoGeometry.Canonical.PeirceWeylDensityTransport
