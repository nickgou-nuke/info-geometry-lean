/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealDoubledWaveplate
import InfoGeometry.Krein.Representation

/-!
# Clifford representations under real doubled phase transport

The existing phase flow is bundled as a native linear isometry equivalence.
Mathlib's conjugation star-algebra equivalence then transports operators,
Clifford representations, and their left and right supports together.
Mode-space covariance is characterized on generators, not assumed from CAR.
-/

namespace InfoGeometry.Canonical.RealDoubledCliffordTransport

open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.RealDoubledWaveplate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H" => DoubledSpace E
local notation "Op" => H →L[ℝ] H

/-- The existing phase flow, with its proved inverse and inner-product law. -/
noncomputable def phaseIsometry (θ : ℝ) : H ≃ₗᵢ[ℝ] H where
  toFun := phaseFlow θ
  invFun := phaseFlow (-θ)
  left_inv := phaseFlow_left_inverse_apply θ
  right_inv := phaseFlow_right_inverse_apply θ
  map_add' := (phaseFlow θ).map_add
  map_smul' := (phaseFlow θ).map_smul
  norm_map' x := by
    change ‖phaseFlow θ x‖ = ‖x‖
    rw [norm_eq_sqrt_real_inner, phaseFlow_preserves_inner, ← norm_eq_sqrt_real_inner]

/-- The operator transport uses the inverse state rotation, matching
`phaseConjugation θ A = R(-θ) A R(θ)`. -/
noncomputable def phaseOperatorEquiv (θ : ℝ) : Op ≃⋆ₐ[ℝ] Op :=
  (phaseIsometry (E := E) θ).symm.conjStarAlgEquiv

theorem phaseOperatorEquiv_apply (θ : ℝ) (A : Op) :
    phaseOperatorEquiv θ A = phaseConjugation θ A := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- Kets and their acting operators transform by the same change of basis. -/
theorem phaseOperatorEquiv_apply_rotated (θ : ℝ) (A : Op) (x : H) :
    phaseOperatorEquiv θ A (phaseFlow (-θ) x) = phaseFlow (-θ) (A x) := by
  change phaseFlow (-θ) (A (phaseFlow θ (phaseFlow (-θ) x))) = _
  rw [phaseFlow_right_inverse_apply]

/-- The bra and ket rotate together; their rank-one operator undergoes
exactly the same conjugation as every other operator. -/
theorem phaseOperatorEquiv_rankOne (θ : ℝ) (x y : H) :
    phaseOperatorEquiv θ (InnerProductSpace.rankOne ℝ x y) =
      InnerProductSpace.rankOne ℝ (phaseFlow (-θ) x) (phaseFlow (-θ) y) := by
  apply ContinuousLinearMap.ext
  intro z
  change phaseFlow (-θ) (inner ℝ y (phaseFlow θ z) • x) =
    inner ℝ (phaseFlow (-θ) y) z • phaseFlow (-θ) x
  rw [map_smul]
  have hi := phaseFlow_preserves_inner (-θ) y (phaseFlow θ z)
  rw [phaseFlow_left_inverse_apply] at hi
  rw [hi]

/-- Two-sided operator actions transport both sides, with no commutativity
or invariance hypothesis on the operators. -/
theorem phaseOperatorEquiv_sandwich (θ : ℝ) (a x b : Op) :
    phaseOperatorEquiv θ (a * x * b) =
      phaseOperatorEquiv θ a * phaseOperatorEquiv θ x * phaseOperatorEquiv θ b := by
  rw [map_mul, map_mul]

/-- Left ideal support is transported together with its defining projection. -/
theorem phaseOperatorEquiv_left_support_iff (θ : ℝ) (p x : Op) :
    phaseOperatorEquiv θ p * phaseOperatorEquiv θ x = phaseOperatorEquiv θ x ↔
      p * x = x := by
  rw [← map_mul]
  exact ⟨fun h => (phaseOperatorEquiv θ).injective h, fun h => congrArg _ h⟩

/-- Right ideal support is transported together with its defining projection. -/
theorem phaseOperatorEquiv_right_support_iff (θ : ℝ) (p x : Op) :
    phaseOperatorEquiv θ x * phaseOperatorEquiv θ p = phaseOperatorEquiv θ x ↔
      x * p = x := by
  rw [← map_mul]
  exact ⟨fun h => (phaseOperatorEquiv θ).injective h, fun h => congrArg _ h⟩

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {q : QuadraticForm ℝ V}

/-- Transport of the actual algebra representation, not only its generators. -/
noncomputable def phaseRepresentation (θ : ℝ) (ρ : CliffordAlgebra q →ₐ[ℝ] Op) :
    CliffordAlgebra q →ₐ[ℝ] Op :=
  (phaseOperatorEquiv θ).toAlgEquiv.toAlgHom.comp ρ

/-- A mode isometry and an operator conjugation give the same representation
exactly when their actions agree on the Clifford generators. -/
theorem phaseRepresentation_eq_mode_map_iff (θ : ℝ)
    (ρ : CliffordAlgebra q →ₐ[ℝ] Op) (r : q →qᵢ q) :
    phaseRepresentation θ ρ = ρ.comp (CliffordAlgebra.map r) ↔
      ∀ v, phaseOperatorEquiv θ (ρ (CliffordAlgebra.ι q v)) =
        ρ (CliffordAlgebra.ι q (r v)) := by
  constructor
  · intro h v
    have hv := AlgHom.congr_fun h (CliffordAlgebra.ι q v)
    simpa [phaseRepresentation] using hv
  · intro h
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    simpa [phaseRepresentation] using h v

/-- Concrete 45-degree transport of the positive split-Clifford generator. -/
theorem phaseRepresentation_cl11_positive_pi_div_four :
    phaseRepresentation (Real.pi / 4) (InfoGeometry.Krein.cl11Rep (E := E))
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) =
        spectral_epsilon (E := E) := by
  change phaseOperatorEquiv _ (InfoGeometry.Krein.cl11Rep _ ) = _
  rw [InfoGeometry.Krein.cl11Rep_ι_one_zero, phaseOperatorEquiv_apply]
  exact phaseFlow_conj_modular_j_pi_div_four

/-- The represented volume element transforms with the same orientation. -/
theorem phaseRepresentation_cl11_volume_pi_div_four :
    phaseRepresentation (Real.pi / 4) (InfoGeometry.Krein.cl11Rep (E := E))
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0) *
       CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) =
        -(modular_j (E := E)) := by
  change phaseOperatorEquiv _ (InfoGeometry.Krein.cl11Rep _) = _
  rw [InfoGeometry.Krein.cl11Rep_pseudoscalar, phaseOperatorEquiv_apply]
  exact phaseFlow_conj_spectral_epsilon_pi_div_four

end InfoGeometry.Canonical.RealDoubledCliffordTransport
