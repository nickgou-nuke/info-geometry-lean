/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationGeometryTransport
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport
import Mathlib.Algebra.Group.Units.Hom

/-!
# Compatibility of simultaneous transport with unit gauge transformations

The unit is transported by the same coefficient algebra equivalence. The
inhomogeneous derivative term is retained, so this theorem relates the full
existing gauge action to simultaneous transport of the derivation geometry.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra

variable {R A B : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable {K : DerivationLieLane R A} {K' : DerivationLieLane R B}
variable (σ : K.L ≃ₗ⁅R⁆ K'.L) (e : A ≃ₐ[R] B)
variable (hρ : ∀ (x : K.L) (a : A),
  K'.operatorAction (σ x) (e a) = e (K.operatorAction x a))

include hρ

/-- Geometry transport intertwines the existing full gauge actions. -/
theorem transportOneForm_gaugeOneForm
    (Γ : OneForm K) (u : Aˣ) :
    transportOneForm σ e (gaugeOneForm K Γ u) =
      gaugeOneForm K' (transportOneForm σ e Γ)
        (Units.map e.toMonoidHom u) := by
  apply LinearMap.ext
  intro y
  have haction : K'.operatorAction y (e (u : A)) =
      e (K.operatorAction (σ.symm y) (u : A)) := by
    simpa only [LieEquiv.apply_symm_apply] using hρ (σ.symm y) (u : A)
  simp only [transportOneForm_apply, gaugeOneForm_apply,
    Units.coe_map, Units.coe_map_inv]
  change e _ = e (u : A) * e (Γ (σ.symm y)) * e (↑u⁻¹ : A) -
    K'.operatorAction y (e (u : A)) * e (↑u⁻¹ : A)
  rw [haction]
  simp only [map_sub, map_mul]

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
