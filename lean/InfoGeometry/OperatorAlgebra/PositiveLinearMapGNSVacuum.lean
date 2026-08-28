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

/--
  The normalized GNS variance inequality for an arbitrary observable.

  This is the exact complex-valued state statement.  It is deliberately
  expressed with `‖φ a‖²`; a real-valued variance requires a separate real
  state/readout and is not silently identified here.
-/
theorem gns_variance_nonneg
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (a : A) :
    0 ≤ (φ (star a * a)).re - ‖φ a‖ ^ 2 := by
  let x : φ.GNS := gnsVacuum φ
  let y : φ.GNS := (φ.gnsStarAlgHom a) x
  have hcs := inner_mul_inner_self_le (𝕜 := ℂ) x y
  have hxx : RCLike.re ⟪x, x⟫_ℂ = 1 := by
    rw [show ⟪x, x⟫_ℂ = φ 1 by
      simpa [x] using gnsVacuum_inner_self φ, hφ]
    norm_num
  have hyy : RCLike.re ⟪y, y⟫_ℂ = (φ (star a * a)).re := by
    simpa [x, y] using congrArg RCLike.re
      (InfoGeometry.OperatorAlgebra.GNSMathlibBridge.gnsStarAlgHom_matrix_coefficient φ a a)
  have hxy : ⟪x, y⟫_ℂ = φ a := by
    simpa [x, y] using gns_state_expectation_recovery φ a
  have hyx_norm : ‖⟪y, x⟫_ℂ‖ = ‖φ a‖ := by
    calc
      ‖⟪y, x⟫_ℂ‖ = ‖⟪x, y⟫_ℂ‖ :=
        (norm_inner_symm x y).symm
      _ = ‖φ a‖ := by rw [hxy]
  rw [hxy, hyx_norm, hxx, hyy] at hcs
  nlinarith

/-- A positive square has nonnegative real state readout, as witnessed by
the norm of its GNS orbit vector. -/
theorem gns_positive_square_re_nonneg
    (φ : A →ₚ[ℂ] ℂ) (a : A) :
    0 ≤ (φ (star a * a)).re := by
  have hcoeff :=
    InfoGeometry.OperatorAlgebra.GNSMathlibBridge.gnsStarAlgHom_matrix_coefficient
      φ a a
  change ⟪(φ.gnsStarAlgHom a) (gnsVacuum φ),
      (φ.gnsStarAlgHom a) (gnsVacuum φ)⟫_ℂ = φ (star a * a) at hcoeff
  have hnonneg :
      0 ≤ RCLike.re ⟪(φ.gnsStarAlgHom a) (gnsVacuum φ),
        (φ.gnsStarAlgHom a) (gnsVacuum φ)⟫_ℂ :=
    @inner_self_nonneg ℂ φ.GNS _ _ _ _
  rw [hcoeff] at hnonneg
  exact hnonneg

/-- A positive square has zero imaginary state readout, because its GNS
coefficient is a self-inner product. -/
theorem gns_positive_square_im_zero
    (φ : A →ₚ[ℂ] ℂ) (a : A) :
    (φ (star a * a)).im = 0 := by
  have hcoeff :=
    InfoGeometry.OperatorAlgebra.GNSMathlibBridge.gnsStarAlgHom_matrix_coefficient
      φ a a
  change ⟪(φ.gnsStarAlgHom a) (gnsVacuum φ),
      (φ.gnsStarAlgHom a) (gnsVacuum φ)⟫_ℂ = φ (star a * a) at hcoeff
  have him : RCLike.im ⟪(φ.gnsStarAlgHom a) (gnsVacuum φ),
      (φ.gnsStarAlgHom a) (gnsVacuum φ)⟫_ℂ = 0 :=
    inner_self_im _
  rw [hcoeff] at him
  exact him

/-- The state readout of a positive square is exactly the complex embedding of
its nonnegative real part. -/
theorem gns_positive_square_eq_ofReal_re
    (φ : A →ₚ[ℂ] ℂ) (a : A) :
    φ (star a * a) = (φ (star a * a)).re := by
  apply Complex.ext
  · simp
  · exact gns_positive_square_im_zero φ a

/-- The normalized GNS variance gap is the squared norm of the centered
observable orbit. -/
theorem gns_variance_gap_eq_centered_norm_sq
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) (a : A) :
    (φ (star a * a)).re - ‖φ a‖ ^ 2 =
      ‖(φ.gnsStarAlgHom a) (gnsVacuum φ) -
        (φ a) • gnsVacuum φ‖ ^ 2 := by
  let x : φ.GNS := gnsVacuum φ
  let y : φ.GNS := (φ.gnsStarAlgHom a) x
  have hxx : ⟪x, x⟫_ℂ = 1 := by
    rw [show ⟪x, x⟫_ℂ = φ 1 by
      simpa [x] using gnsVacuum_inner_self φ, hφ]
  have hyy : ⟪y, y⟫_ℂ = φ (star a * a) := by
    simpa [x, y] using
      (InfoGeometry.OperatorAlgebra.GNSMathlibBridge.gnsStarAlgHom_matrix_coefficient
        φ a a)
  have hxy : ⟪x, y⟫_ℂ = φ a := by
    simpa [x, y] using gns_state_expectation_recovery φ a
  have hyx : ⟪y, x⟫_ℂ = starRingEnd ℂ (φ a) := by
    rw [← inner_conj_symm, hxy]
  have hnormy : (‖y‖ : ℂ) ^ 2 = ⟪y, y⟫_ℂ := by
    exact (inner_self_eq_norm_sq_to_K y).symm
  rw [norm_sub_sq, hnormy, hyy, hxy, hyx]
  simp only [norm_smul, norm_one, mul_one]
  simp [Complex.normSq, starRingEnd_apply, ← Complex.sq_norm,
    sub_eq_add_neg, mul_add, add_mul]

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
