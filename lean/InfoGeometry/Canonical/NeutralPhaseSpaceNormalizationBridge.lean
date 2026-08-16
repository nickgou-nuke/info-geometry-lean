import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Canonical.NeutralDualPairClifford

/-!
# Normalization bridge for the neutral phase-space Clifford algebras

The repository keeps both neutral quadratic normalizations:
`canonicalNeutralForm = 2 * canonicalNeutralFormUnscaled` and
`canonicalNeutralFormUnscaled (x, ξ) = ξ x`.  This file proves the explicit
linear isometry between them and lifts it through the Clifford universal
property.
-/

namespace InfoGeometry.Clifford.NeutralPhaseSpaceNormalizationBridge

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Rescale the dual coordinate by two. -/
noncomputable def normalizationEquiv :
    PhaseSpaceCarrier E ≃ₗ[ℝ] PhaseSpaceCarrier E :=
  LinearEquiv.ofLinear
    { toFun := fun X => (X.1, (2 : ℝ) • X.2)
      map_add' := by
        intro X Y
        ext <;> simp [smul_add]
      map_smul' := by
        intro c X
        ext <;> simp [smul_smul, mul_comm] }
    { toFun := fun X => (X.1, (1 / 2 : ℝ) • X.2)
      map_add' := by
        intro X Y
        ext <;> simp [smul_add]
      map_smul' := by
        intro c X
        ext <;> simp [smul_smul, mul_comm] }
    (by
      ext X <;> simp [smul_smul, mul_comm])
    (by
      ext X <;> simp [smul_smul, mul_comm])

@[simp] theorem normalizationEquiv_apply (X : PhaseSpaceCarrier E) :
    normalizationEquiv X = (X.1, (2 : ℝ) • X.2) := rfl

@[simp] theorem normalizationEquiv_preserves_form (X : PhaseSpaceCarrier E) :
    canonicalNeutralFormUnscaled (normalizationEquiv X) =
      canonicalNeutralForm X := by
  rcases X with ⟨x, ξ⟩
  simp [normalizationEquiv, canonicalNeutralForm_apply,
    canonicalNeutralFormUnscaled_apply]

@[simp] theorem normalizationEquiv_symm_preserves_form
    (X : PhaseSpaceCarrier E) :
    canonicalNeutralForm (normalizationEquiv.symm X) =
      canonicalNeutralFormUnscaled X := by
  have h := normalizationEquiv_preserves_form
    (E := E) (normalizationEquiv.symm X)
  simpa using h.symm

noncomputable def normalizationIsometry :
    (canonicalNeutralForm (E := E)).IsometryEquiv
      (canonicalNeutralFormUnscaled (E := E)) where
  __ := normalizationEquiv
  map_app' := by
    intro X
    exact normalizationEquiv_preserves_form X

abbrev ScaledClifford (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  NeutralPhaseClifford E

abbrev UnscaledClifford (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  CliffordAlgebra (canonicalNeutralFormUnscaled (E := E))

noncomputable def normalizationCliffordEquiv :
    ScaledClifford E ≃ₐ[ℝ] UnscaledClifford E :=
  CliffordAlgebra.equivOfIsometry normalizationIsometry

@[simp] theorem normalizationCliffordEquiv_ι
    (X : PhaseSpaceCarrier E) :
    normalizationCliffordEquiv
        (CliffordAlgebra.ι (canonicalNeutralForm (E := E)) X) =
      CliffordAlgebra.ι
        (canonicalNeutralFormUnscaled (E := E)) (normalizationEquiv X) := by
  exact CliffordAlgebra.map_apply_ι _ _

@[simp] theorem normalizationCliffordEquiv_symm_ι
    (X : PhaseSpaceCarrier E) :
    (normalizationCliffordEquiv (E := E)).symm
        (CliffordAlgebra.ι
          (canonicalNeutralFormUnscaled (E := E)) X) =
      CliffordAlgebra.ι
        (canonicalNeutralForm (E := E)) (normalizationEquiv.symm X) := by
  exact CliffordAlgebra.map_apply_ι _ _

theorem normalizationCliffordEquiv_primalGenerator (u : E) :
    normalizationCliffordEquiv
        (CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0)) =
      InfoGeometry.Canonical.NeutralDualPair.generator (u, 0) := by
  rw [normalizationCliffordEquiv_ι]
  simp [normalizationEquiv_apply,
    InfoGeometry.Canonical.NeutralDualPair.generator]

theorem normalizationCliffordEquiv_dualGenerator (ξ : Module.Dual ℝ E) :
    normalizationCliffordEquiv
        (CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ)) =
      InfoGeometry.Canonical.NeutralDualPair.generator (0, (2 : ℝ) • ξ) := by
  rw [normalizationCliffordEquiv_ι]
  simp [normalizationEquiv_apply,
    InfoGeometry.Canonical.NeutralDualPair.generator]

theorem normalizationCliffordEquiv_mixed_CAR
    (u : E) (ξ : Module.Dual ℝ E) :
    normalizationCliffordEquiv
        (CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0) *
          CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ) +
          CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ) *
          CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0)) =
      algebraMap ℝ (UnscaledClifford E) (((2 : ℝ) • ξ) u) := by
  rw [map_add, map_mul, map_mul,
    normalizationCliffordEquiv_ι, normalizationCliffordEquiv_ι,
    normalizationCliffordEquiv_ι, normalizationCliffordEquiv_ι]
  simpa [normalizationEquiv_apply,
    InfoGeometry.Canonical.NeutralDualPair.vectorGenerator,
    InfoGeometry.Canonical.NeutralDualPair.covectorGenerator] using
    (InfoGeometry.Canonical.NeutralDualPair.vector_covector_CAR
      (U := E) u ((2 : ℝ) • ξ))

theorem normalizationCliffordEquiv_reverse_mixed_CAR
    (u : E) (ξ : Module.Dual ℝ E) :
    normalizationCliffordEquiv
        (CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ) *
          CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0) +
          CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0) *
          CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ)) =
      algebraMap ℝ (UnscaledClifford E) (((2 : ℝ) • ξ) u) := by
  rw [map_add, map_mul, map_mul,
    normalizationCliffordEquiv_ι, normalizationCliffordEquiv_ι,
    normalizationCliffordEquiv_ι, normalizationCliffordEquiv_ι]
  simpa [normalizationEquiv_apply,
    InfoGeometry.Canonical.NeutralDualPair.vectorGenerator,
    InfoGeometry.Canonical.NeutralDualPair.covectorGenerator] using
    (InfoGeometry.Canonical.NeutralDualPair.covector_vector_CAR
      (U := E) ((2 : ℝ) • ξ) u)

theorem normalizationCliffordEquiv_primal_square_zero (u : E) :
    normalizationCliffordEquiv
        (CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0) *
          CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (u, 0)) = 0 := by
  rw [map_mul, normalizationCliffordEquiv_ι, normalizationCliffordEquiv_ι]
  simpa [normalizationEquiv_apply,
    InfoGeometry.Canonical.NeutralDualPair.vectorGenerator] using
    (InfoGeometry.Canonical.NeutralDualPair.vectorGenerator_sq_zero
      (U := E) u)

theorem normalizationCliffordEquiv_dual_square_zero
    (ξ : Module.Dual ℝ E) :
    normalizationCliffordEquiv
        (CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ) *
          CliffordAlgebra.ι (canonicalNeutralForm (E := E)) (0, ξ)) = 0 := by
  rw [map_mul, normalizationCliffordEquiv_ι, normalizationCliffordEquiv_ι]
  simpa [normalizationEquiv_apply,
    InfoGeometry.Canonical.NeutralDualPair.covectorGenerator] using
    (InfoGeometry.Canonical.NeutralDualPair.covectorGenerator_sq_zero
      (U := E) ξ)

end InfoGeometry.Clifford.NeutralPhaseSpaceNormalizationBridge
