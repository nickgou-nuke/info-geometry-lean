import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Clifford.Grading
import InfoGeometry.Cartan.Involution
import InfoGeometry.Krein.Metric
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge

Realization bridge from the neutral phase-space owner to the existing real
doubled Krein carrier.

This file stays deliberately narrow:

- a chosen linear duality equivalence `ρ : E ≃ₗ[ℝ] E*` identifies the dual leg
  with a second real copy of `E`,
- that identification yields a direct doubled realization used to transport
  `J`, `ε`, and the Hestenes rotation `J ∘ ε`,
- the realized doubled/Krein map is obtained by composing the same identification
  with the existing neutral-to-doubled rotation already present in the real
  Krein layer,
- exact transport of the neutral bilinear and quadratic forms is stated only in
  the doubled/Krein language.

No generalized-metric or KKT data is introduced here.
-/

namespace InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge

open InfoGeometry.Cartan
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Krein

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private noncomputable def realCopyRhoEquiv (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    PhaseSpaceCarrier E ≃ₗ[ℝ] (E × E) :=
  LinearEquiv.ofLinear
    { toFun := fun X => (X.1, ρ.symm X.2)
      map_add' := by
        intro X Y
        refine Prod.ext ?_ ?_
        · simp
        · simp
      map_smul' := by
        intro r X
        refine Prod.ext ?_ ?_
        · simp
        · simp }
    { toFun := fun X => (X.1, ρ X.2)
      map_add' := by
        intro X Y
        refine Prod.ext ?_ ?_
        · simp
        · simp
      map_smul' := by
        intro r X
        refine Prod.ext ?_ ?_
        · simp
        · simp }
    (by
      apply LinearMap.ext
      intro X
      refine Prod.ext ?_ ?_
      · simp
      · simp)
    (by
      apply LinearMap.ext
      intro X
      refine Prod.ext ?_ ?_
      · simp
      · simp)

private noncomputable def doubledCopyEquiv :
    (E × E) ≃ₗ[ℝ] DoubledSpace E :=
  LinearEquiv.ofLinear
    { toFun := fun X => to_doubled X.1 X.2
      map_add' := by
        intro X Y
        apply DoubledSpace.ext <;> simp
      map_smul' := by
        intro r X
        apply DoubledSpace.ext <;> simp }
    { toFun := fun u => (WithLp.fst u, WithLp.snd u)
      map_add' := by
        intro u v
        refine Prod.ext ?_ ?_
        · simp [WithLp.add_fst]
        · simp [WithLp.add_snd]
      map_smul' := by
        intro r u
        refine Prod.ext ?_ ?_
        · simp [WithLp.smul_fst]
        · simp [WithLp.smul_snd] }
    (by
      apply LinearMap.ext
      intro u
      apply DoubledSpace.ext <;> simp)
    (by
      apply LinearMap.ext
      intro X
      refine Prod.ext ?_ ?_
      · simp
      · simp)

private noncomputable def neutralDoubledEquiv :
    DoubledSpace E ≃ₗ[ℝ] NeutralSpace E :=
  LinearEquiv.ofLinear
    { toFun := fun u => NeutralSpace.ofWithLp (E := E) u
      map_add' := by
        intro u v
        apply NeutralSpace.ext
        rfl
      map_smul' := by
        intro r u
        apply NeutralSpace.ext
        rfl }
    { toFun := fun u => (u : DoubledSpace E)
      map_add' := by
        intro u v
        rfl
      map_smul' := by
        intro r u
        rfl }
    (by
      apply LinearMap.ext
      intro u
      apply NeutralSpace.ext
      rfl)
    (by
      apply LinearMap.ext
      intro u
      rfl)

private noncomputable def neutralRealizationEquiv :
    (E × E) ≃ₗ[ℝ] NeutralSpace E :=
  doubledCopyEquiv (E := E) |>.trans (neutralDoubledEquiv (E := E))

/-- Direct doubled realization of the phase-space carrier under a chosen duality
equivalence `ρ : E ≃ₗ[ℝ] E*`. -/
@[rep_depth krein]
noncomputable abbrev doubledCopyRhoEquiv (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    PhaseSpaceCarrier E ≃ₗ[ℝ] DoubledSpace E :=
  (realCopyRhoEquiv (E := E) ρ).trans (doubledCopyEquiv (E := E))

/-- Forward direct doubled realization under `ρ`. -/
@[rep_depth krein]
noncomputable abbrev toDoubledCopyRho (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E :=
  (doubledCopyRhoEquiv (E := E) ρ).toLinearMap

/-- Inverse direct doubled realization under `ρ`. -/
@[rep_depth krein]
noncomputable abbrev fromDoubledCopyRho (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    DoubledSpace E →ₗ[ℝ] PhaseSpaceCarrier E :=
  (doubledCopyRhoEquiv (E := E) ρ).symm.toLinearMap

/-- Realized doubled/Krein equivalence under `ρ`, obtained by composing the
phase-space identification with the existing real neutral-to-doubled rotation. -/
@[rep_depth krein]
noncomputable abbrev realizedDoubledRhoEquiv (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    PhaseSpaceCarrier E ≃ₗ[ℝ] DoubledSpace E :=
  ((realCopyRhoEquiv (E := E) ρ).trans (neutralRealizationEquiv (E := E))).trans
    (NeutralSpace.rotation45Isometry (E := E)).toLinearEquiv

/-- Forward realized doubled/Krein map under `ρ`. -/
@[rep_depth krein]
noncomputable abbrev realizeToDoubledRho (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E :=
  (realizedDoubledRhoEquiv (E := E) ρ).toLinearMap

/-- Inverse realized doubled/Krein map under `ρ`. -/
@[rep_depth krein]
noncomputable abbrev realizeFromDoubledRho (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    DoubledSpace E →ₗ[ℝ] PhaseSpaceCarrier E :=
  (realizedDoubledRhoEquiv (E := E) ρ).symm.toLinearMap

/-- Phase-space swap involution `J_ρ (x, φ) = (ρ⁻¹ φ, ρ x)`. -/
@[rep_depth krein]
noncomputable def phaseJ (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Module.End ℝ (PhaseSpaceCarrier E) where
  toFun := fun X => (ρ.symm X.2, ρ X.1)
  map_add' := by
    intro X Y
    refine Prod.ext ?_ ?_
    · simp
    · simp
  map_smul' := by
    intro r X
    refine Prod.ext ?_ ?_
    · simp
    · simp

/-- Phase-space sign involution `ε_ρ (x, φ) = (x, -φ)`. -/
@[rep_depth krein]
noncomputable def phaseEpsilon :
    Module.End ℝ (PhaseSpaceCarrier E) where
  toFun := fun X => (X.1, -X.2)
  map_add' := by
    intro X Y
    refine Prod.ext ?_ ?_
    · simp
    · simp [add_comm]
  map_smul' := by
    intro r X
    refine Prod.ext ?_ ?_
    · simp
    · simp

/-- Hestenes rotation `J_ρ ∘ ε_ρ` on phase space. -/
@[rep_depth krein]
noncomputable def phaseRotation (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Module.End ℝ (PhaseSpaceCarrier E) :=
  (phaseJ ρ).comp (phaseEpsilon (E := E))

/-! ### Automorphism seed layer

We expose the primitive phase-space symmetries as `LinearEquiv` first, and only
then pass to `Module.End` aliases for operator-level corridors.
-/

/-- Phase-space swap involution as a linear equivalence. -/
@[rep_depth krein]
noncomputable def phaseJEquiv (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    PhaseSpaceCarrier E ≃ₗ[ℝ] PhaseSpaceCarrier E where
  toFun := fun X => (ρ.symm X.2, ρ X.1)
  invFun := fun X => (ρ.symm X.2, ρ X.1)
  left_inv := by
    intro X
    rcases X with ⟨x, φ⟩
    simp
  right_inv := by
    intro X
    rcases X with ⟨x, φ⟩
    simp
  map_add' := by
    intro X Y
    refine Prod.ext ?_ ?_
    · simp
    · simp
  map_smul' := by
    intro r X
    refine Prod.ext ?_ ?_
    · simp
    · simp

/-- Phase-space sign involution as a linear equivalence. -/
@[rep_depth krein]
noncomputable def phaseEpsilonEquiv :
    PhaseSpaceCarrier E ≃ₗ[ℝ] PhaseSpaceCarrier E where
  toFun := fun X => (X.1, -X.2)
  invFun := fun X => (X.1, -X.2)
  left_inv := by
    intro X
    rcases X with ⟨x, φ⟩
    simp
  right_inv := by
    intro X
    rcases X with ⟨x, φ⟩
    simp
  map_add' := by
    intro X Y
    refine Prod.ext ?_ ?_
    · simp
    · simp [add_comm]
  map_smul' := by
    intro r X
    refine Prod.ext ?_ ?_
    · simp
    · simp

/-- Hestenes rotation as a linear equivalence. -/
@[rep_depth krein]
noncomputable def phaseRotationEquiv (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    PhaseSpaceCarrier E ≃ₗ[ℝ] PhaseSpaceCarrier E :=
  (phaseEpsilonEquiv (E := E)).trans (phaseJEquiv (E := E) ρ)

omit [CompleteSpace E] in
@[rep_depth krein] theorem phaseJEquiv_sq (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (phaseJEquiv (E := E) ρ).trans (phaseJEquiv (E := E) ρ)
      = LinearEquiv.refl ℝ (PhaseSpaceCarrier E) := by
  ext X <;> simp [phaseJEquiv]

omit [CompleteSpace E] in
@[rep_depth krein] theorem phaseEpsilonEquiv_sq :
    (phaseEpsilonEquiv (E := E)).trans (phaseEpsilonEquiv (E := E))
      = LinearEquiv.refl ℝ (PhaseSpaceCarrier E) := by
  ext X <;> simp [phaseEpsilonEquiv]

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem phaseJEquiv_toLinearMap
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (phaseJEquiv (E := E) ρ).toLinearMap = phaseJ (E := E) ρ := rfl

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem phaseEpsilonEquiv_toLinearMap :
    (phaseEpsilonEquiv (E := E)).toLinearMap = phaseEpsilon (E := E) := rfl

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem phaseRotationEquiv_toLinearMap
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (phaseRotationEquiv (E := E) ρ).toLinearMap = phaseRotation (E := E) ρ := by
  rfl

omit [CompleteSpace E] in
@[rep_depth krein] theorem phaseJEquiv_phaseEpsilonEquiv_anticommute
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (phaseJEquiv (E := E) ρ).toLinearMap.comp
        (phaseEpsilonEquiv (E := E)).toLinearMap
      = -((phaseEpsilonEquiv (E := E)).toLinearMap.comp
          (phaseJEquiv (E := E) ρ).toLinearMap) := by
  ext X <;> simp [phaseJEquiv_toLinearMap, phaseEpsilonEquiv_toLinearMap,
    phaseJ, phaseEpsilon, LinearMap.comp_apply]

/-- The `+1` projector attached to the phase-space sign involution. -/
@[rep_depth krein]
noncomputable def phasePlusProjector :
    Module.End ℝ (PhaseSpaceCarrier E) :=
  Pplus (phaseEpsilon (E := E))

/-- The `-1` projector attached to the phase-space sign involution. -/
@[rep_depth krein]
noncomputable def phaseMinusProjector :
    Module.End ℝ (PhaseSpaceCarrier E) :=
  Pminus (phaseEpsilon (E := E))

/-- Doubled Hestenes rotation `J ∘ ε` on the real doubled carrier. -/
@[rep_depth krein]
noncomputable def modularRotation :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  (modular_j (E := E)).comp (spectral_epsilon (E := E))

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem toDoubledCopyRho_apply
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) (X : PhaseSpaceCarrier E) :
    toDoubledCopyRho (E := E) ρ X = to_doubled X.1 (ρ.symm X.2) := by
  rcases X with ⟨x, φ⟩
  rfl

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem fromDoubledCopyRho_apply
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) (u : DoubledSpace E) :
    fromDoubledCopyRho (E := E) ρ u = (WithLp.fst u, ρ (WithLp.snd u)) := by
  rfl

@[rep_depth krein, simp] theorem realizeToDoubledRho_apply
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) (X : PhaseSpaceCarrier E) :
    realizeToDoubledRho (E := E) ρ X =
      let c : ℝ := 1 / Real.sqrt 2
      to_doubled (c • X.1 + c • ρ.symm X.2) (c • X.1 - c • ρ.symm X.2) := by
  rcases X with ⟨x, φ⟩
  simp [realizeToDoubledRho, realizedDoubledRhoEquiv, neutralRealizationEquiv,
    realCopyRhoEquiv, doubledCopyEquiv, neutralDoubledEquiv,
    NeutralSpace.rotation45_symm_toLp_pair]

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem phaseJ_apply
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) (X : PhaseSpaceCarrier E) :
    phaseJ ρ X = (ρ.symm X.2, ρ X.1) := rfl

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem phaseEpsilon_apply
    (X : PhaseSpaceCarrier E) :
    phaseEpsilon (E := E) X = (X.1, -X.2) := rfl

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem phaseRotation_apply
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) (X : PhaseSpaceCarrier E) :
    phaseRotation (E := E) ρ X = (-ρ.symm X.2, ρ X.1) := by
  rcases X with ⟨x, φ⟩
  refine Prod.ext ?_ ?_
  · simp [phaseRotation, phaseJ, phaseEpsilon]
  · simp [phaseRotation, phaseJ, phaseEpsilon]

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem phasePlusProjector_apply
    (X : PhaseSpaceCarrier E) :
    phasePlusProjector (E := E) X = ((2 : ℝ)⁻¹) • (X + phaseEpsilon (E := E) X) := by
  simp [phasePlusProjector, Pplus]

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem phaseMinusProjector_apply
    (X : PhaseSpaceCarrier E) :
    phaseMinusProjector (E := E) X = ((2 : ℝ)⁻¹) • (X - phaseEpsilon (E := E) X) := by
  simp [phaseMinusProjector, Pminus]

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem modularRotation_to_doubled
    (x ξ : E) :
    modularRotation (E := E) (to_doubled x ξ : DoubledSpace E) = to_doubled (-ξ) x := by
  apply DoubledSpace.ext <;> simp [modularRotation]

omit [CompleteSpace E] in
@[rep_depth krein] theorem phaseJ_sq
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    phaseJ ρ * phaseJ ρ = 1 := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  refine Prod.ext ?_ ?_
  · simp [phaseJ]
  · simp [phaseJ]

omit [CompleteSpace E] in
@[rep_depth krein] theorem phaseEpsilon_sq :
    phaseEpsilon (E := E) * phaseEpsilon (E := E) = 1 := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  refine Prod.ext ?_ ?_
  · simp [phaseEpsilon]
  · simp [phaseEpsilon]

omit [CompleteSpace E] in
@[rep_depth krein] theorem phaseJ_phaseEpsilon_anticommute
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    phaseJ ρ * phaseEpsilon (E := E) = -(phaseEpsilon (E := E) * phaseJ ρ) := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  refine Prod.ext ?_ ?_
  · simp [phaseJ, phaseEpsilon]
  · simp [phaseJ, phaseEpsilon]

omit [CompleteSpace E] in
@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseJ
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (phaseJ ρ)
      = (modular_j (E := E)).toLinearMap.comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  apply DoubledSpace.ext <;> simp [toDoubledCopyRho, doubledCopyRhoEquiv, realCopyRhoEquiv,
    doubledCopyEquiv, phaseJ_apply]

omit [CompleteSpace E] in
@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseEpsilon
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (phaseEpsilon (E := E))
      = (spectral_epsilon (E := E)).toLinearMap.comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  apply DoubledSpace.ext <;> simp [toDoubledCopyRho, doubledCopyRhoEquiv, realCopyRhoEquiv,
    doubledCopyEquiv, phaseEpsilon_apply]

omit [CompleteSpace E] in
@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseRotation
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (phaseRotation (E := E) ρ)
      = (modularRotation (E := E)).toLinearMap.comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  apply DoubledSpace.ext <;> simp [toDoubledCopyRho, doubledCopyRhoEquiv, realCopyRhoEquiv,
    doubledCopyEquiv, phaseRotation_apply, modularRotation]

omit [CompleteSpace E] in
@[rep_depth krein] theorem toDoubledCopyRho_comp_phasePlusProjector
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (phasePlusProjector (E := E))
      = (spectralPlusProj (E := E)).toLinearMap.comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  apply DoubledSpace.ext <;>
    simp [phasePlusProjector, Pplus, spectralPlusProj, phaseEpsilon_apply,
      toDoubledCopyRho, doubledCopyRhoEquiv, realCopyRhoEquiv, doubledCopyEquiv,
      spectral_epsilon, smul_add]

omit [CompleteSpace E] in
@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseMinusProjector
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (phaseMinusProjector (E := E))
      = (spectralMinusProj (E := E)).toLinearMap.comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, φ⟩
  apply DoubledSpace.ext <;>
    simp [phaseMinusProjector, Pminus, spectralMinusProj, phaseEpsilon_apply,
      toDoubledCopyRho, doubledCopyRhoEquiv, realCopyRhoEquiv, doubledCopyEquiv,
      spectral_epsilon, sub_eq_add_neg, smul_add]

@[rep_depth krein] theorem canonicalNeutralBilin_realizeToDoubledRho
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E)
    (hρ : ∀ x y, ρ x y = ⟪x, y⟫_ℝ)
    (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (E := E) X Y
      = hessian_indefinite_form
          (realizeToDoubledRho (E := E) ρ X)
          (realizeToDoubledRho (E := E) ρ Y) := by
  rcases X with ⟨x, φ⟩
  rcases Y with ⟨y, ψ⟩
  have hφ : φ y = ⟪y, ρ.symm φ⟫_ℝ := by
    calc
      φ y = ρ (ρ.symm φ) y := by simp
      _ = ⟪ρ.symm φ, y⟫_ℝ := by simpa using hρ (ρ.symm φ) y
      _ = ⟪y, ρ.symm φ⟫_ℝ := by simp [real_inner_comm]
  have hψ : ψ x = ⟪x, ρ.symm ψ⟫_ℝ := by
    calc
      ψ x = ρ (ρ.symm ψ) x := by simp
      _ = ⟪ρ.symm ψ, x⟫_ℝ := by simpa using hρ (ρ.symm ψ) x
      _ = ⟪x, ρ.symm ψ⟫_ℝ := by simp [real_inner_comm]
  calc
    canonicalNeutralBilin (E := E) (x, φ) (y, ψ)
        = ⟪x, ρ.symm ψ⟫_ℝ + ⟪y, ρ.symm φ⟫_ℝ := by
            simp [canonicalNeutralBilin_apply, hφ, hψ, add_comm]
    _ = hessian_indefinite_formCoord (x, ρ.symm φ) (y, ρ.symm ψ) := by
          simp [hessian_indefinite_formCoord]
    _ = hessian_indefinite_form
          (realizeToDoubledRho (E := E) ρ (x, φ))
          (realizeToDoubledRho (E := E) ρ (y, ψ)) := by
          simpa [realizeToDoubledRho_apply] using
            (hessian_indefinite_formCoord_eq_hessianDoubled
              (E := E) (v := (x, ρ.symm φ)) (w := (y, ρ.symm ψ)))

@[rep_depth krein] theorem canonicalNeutralForm_realizeToDoubledRho
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E)
    (hρ : ∀ x y, ρ x y = ⟪x, y⟫_ℝ)
    (X : PhaseSpaceCarrier E) :
    canonicalNeutralForm (E := E) X
      = hessian_indefinite_form
          (realizeToDoubledRho (E := E) ρ X)
          (realizeToDoubledRho (E := E) ρ X) := by
  simpa [canonicalNeutralForm] using
    canonicalNeutralBilin_realizeToDoubledRho ρ hρ X X

@[rep_depth krein] theorem canonicalNeutralFormUnscaled_realizeToDoubledRho
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E)
    (hρ : ∀ x y, ρ x y = ⟪x, y⟫_ℝ)
    (X : PhaseSpaceCarrier E) :
    canonicalNeutralFormUnscaled (E := E) X
      = (1 / 2 : ℝ) *
          hessian_indefinite_form
            (realizeToDoubledRho (E := E) ρ X)
            (realizeToDoubledRho (E := E) ρ X) := by
  calc
    canonicalNeutralFormUnscaled (E := E) X
        = (1 / 2 : ℝ) * canonicalNeutralForm (E := E) X := by
            rcases X with ⟨x, ξ⟩
            simp [canonicalNeutralFormUnscaled_apply, canonicalNeutralForm_apply]
    _ = (1 / 2 : ℝ) *
          hessian_indefinite_form
            (realizeToDoubledRho (E := E) ρ X)
            (realizeToDoubledRho (E := E) ρ X) := by
          rw [canonicalNeutralForm_realizeToDoubledRho ρ hρ X]

end Core

end InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
