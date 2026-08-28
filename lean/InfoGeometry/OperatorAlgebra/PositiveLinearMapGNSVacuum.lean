import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.OperatorAlgebra.GNSMathlibBridge

namespace InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum

open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The class of `1` in the pre-GNS space. -/
noncomputable def preGNSVacuum (φ : A →ₚ[ℂ] ℂ) : φ.PreGNS :=
  φ.toPreGNS (1 : A)

/-- The pre-GNS expectation identity for the cyclic vector. -/
theorem preGNSVacuum_expectation
    (φ : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪preGNSVacuum φ, φ.leftMulMapPreGNS a (preGNSVacuum φ)⟫_ℂ = φ a := by
  rw [preGNSVacuum, PositiveLinearMap.leftMulMapPreGNS_apply,
    PositiveLinearMap.preGNS_inner_def]
  simp [PositiveLinearMap.ofPreGNS_toPreGNS]

/-- The pre-GNS vacuum has squared norm `φ 1`. -/
theorem preGNSVacuum_inner_self
    (φ : A →ₚ[ℂ] ℂ) :
    ⟪preGNSVacuum φ, preGNSVacuum φ⟫_ℂ = φ 1 := by
  change φ (star (1 : A) * 1) = φ 1
  simp

/-- The image of the pre-GNS vacuum in the completed GNS Hilbert space. -/
noncomputable def gnsVacuum (φ : A →ₚ[ℂ] ℂ) : φ.GNS :=
  (preGNSVacuum φ : φ.GNS)

/-- The completed vacuum has squared norm `φ 1`. -/
theorem gnsVacuum_inner_self
    (φ : A →ₚ[ℂ] ℂ) :
    ⟪gnsVacuum φ, gnsVacuum φ⟫_ℂ = φ 1 := by
  rw [gnsVacuum]
  rw [UniformSpace.Completion.inner_coe]
  exact preGNSVacuum_inner_self φ

theorem gnsVacuum_norm_eq_one
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) :
    ‖gnsVacuum φ‖ = 1 := by
  have h := gnsVacuum_inner_self φ
  have h' : (‖gnsVacuum φ‖ ^ 2 : ℂ) = φ 1 := by
    simpa [inner_self_eq_norm_sq] using h
  rw [hφ] at h'
  have hs : ‖gnsVacuum φ‖ ^ 2 = (1 : ℝ) := by
    exact_mod_cast h'
  nlinarith [norm_nonneg (gnsVacuum φ)]

/-- The GNS representation recovers the original functional in the vacuum. -/
theorem gns_state_expectation_recovery
    (φ : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪gnsVacuum φ, (φ.gnsStarAlgHom a) (gnsVacuum φ)⟫_ℂ = φ a := by
  simpa [gnsVacuum, preGNSVacuum,
    InfoGeometry.OperatorAlgebra.GNSMathlibBridge.cyclicVector] using
    (InfoGeometry.OperatorAlgebra.GNSMathlibBridge.cyclicVector_inner_gnsStarAlgHom
      (f := φ) (a := a))

/-- The orbit map of the GNS cyclic vector, represented by the completion embedding. -/
noncomputable def gnsOrbitMap (φ : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] φ.GNS where
  toFun := fun a => (φ.toPreGNS a : φ.GNS)
  map_add' := by
    intro a b
    change (φ.toPreGNS (a + b) : φ.GNS) =
      (φ.toPreGNS a : φ.GNS) + (φ.toPreGNS b : φ.GNS)
    rw [φ.toPreGNS.map_add, UniformSpace.Completion.coe_add]
  map_smul' := by
    intro c a
    change (φ.toPreGNS (c • a) : φ.GNS) =
      c • (φ.toPreGNS a : φ.GNS)
    rw [φ.toPreGNS.map_smul, UniformSpace.Completion.coe_smul]

theorem gnsOrbitMap_eq_completionEmbedding
    (φ : A →ₚ[ℂ] ℂ) (a : A) :
    gnsOrbitMap φ a = (φ.toPreGNS a : φ.GNS) := rfl

theorem gnsOrbitMap_eq_gnsRepresentation
    (φ : A →ₚ[ℂ] ℂ) (a : A) :
    gnsOrbitMap φ a = (φ.gnsStarAlgHom a) (gnsVacuum φ) := by
  simpa [gnsOrbitMap, gnsVacuum, preGNSVacuum,
    InfoGeometry.OperatorAlgebra.GNSMathlibBridge.cyclicVector] using
    (InfoGeometry.OperatorAlgebra.GNSMathlibBridge.gnsStarAlgHom_apply_cyclicVector
      (f := φ) (a := a)).symm

theorem gnsOrbitMap_eq_gnsRepresentation_vacuum
    (φ : A →ₚ[ℂ] ℂ) (a : A) :
    gnsOrbitMap φ a = (φ.gnsStarAlgHom a) (gnsVacuum φ) :=
  gnsOrbitMap_eq_gnsRepresentation φ a

/-- The GNS cyclic orbit is dense in the completed GNS space. -/
theorem gnsOrbitMap_denseRange
    (φ : A →ₚ[ℂ] ℂ) :
    DenseRange (gnsOrbitMap φ) := by
  change DenseRange (fun a : A => (φ.toPreGNS a : φ.GNS))
  exact UniformSpace.Completion.denseRange_coe.comp
    φ.toPreGNS.surjective.denseRange
    (UniformSpace.Completion.continuous_coe φ.PreGNS)

end InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum
