/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Canonical.CanonicalZornPalatiniCurvature
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# InfoGeometry.InformationGeometry.CoherencePullbackMetricAndPalatiniConfinement

Emergent Riemannian pullback metrics `g_μν(x) = ⟨∂_μ Ψ(x), ∂_ν Ψ(x)⟩_blade` and
Grace-weighted metrics `g^G_μν(x) = ⟨∂_μ Ψ(x), G_Q ∂_ν Ψ(x)⟩_blade` from
Clifford-valued coherence fields `Ψ : (Fin n → ℝ) → CliffordAlgebra Q`, smooth
`Cl(3,1)` immersion witnesses, `C²` Schwarz Hessian symmetry, and golden-vacuum
UV confinement inside `InfoGeometry.Canonical.ZornPalatiniCurvature`.
-/

set_option autoImplicit false

namespace InfoGeometry.InformationGeometry.CoherencePullbackMetricAndPalatiniConfinement

open CliffordAlgebra
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Canonical.ZornPalatiniCurvature
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open scoped goldenRatio Matrix
open scoped InfoGeometry.Clifford.GradedGraceContraction

section ScalarHelpers

private theorem scalar_regularized_ge (invPhiSq d : ℝ) (hd : 0 ≤ d) :
    invPhiSq ≤ invPhiSq + d := by
  linarith [hd]

private theorem scalar_inv_phi_sq_add_inv_phi (hinv : φ ^ (-(1 : ℤ)) = φ - 1)
    (hsq : φ ^ (-(2 : ℤ)) = 2 - φ) :
    φ ^ (-(2 : ℤ)) + φ ^ (-(1 : ℤ)) = 1 := by
  linarith [hinv, hsq]

private theorem scalar_strict_uv_density {invPhiSq invPhi d : ℝ}
    (hsum : invPhiSq + invPhi = 1) (hd : invPhi < d) :
    1 < invPhiSq + d := by
  linarith [hsum, hd]

end ScalarHelpers

/-! ## Part A: Emergent Coherence Pullback Metrics `g_μν` and `g^G_μν` -/

section PullbackMetric

/-- Coordinate partial Fréchet derivative `∂_μ Ψ(x) = dΨ_x(e_μ)` of a
Clifford-valued coherence field `Ψ : (Fin n → ℝ) → CliffordAlgebra Q`. -/
noncomputable def coherencePartial {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) (μ : Fin n) :
    CliffordAlgebra Q :=
  fderiv ℝ Ψ x (Pi.single μ (1 : ℝ))

theorem coherencePartial_of_hasFDerivAt {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {Ψ : (Fin n → ℝ) → CliffordAlgebra Q}
    {L : (Fin n → ℝ) →L[ℝ] CliffordAlgebra Q} {x : Fin n → ℝ}
    (hΨ : HasFDerivAt Ψ L x) (μ : Fin n) :
    coherencePartial Q Ψ x μ = L (Pi.single μ (1 : ℝ)) := by
  rw [coherencePartial, hΨ.fderiv]

theorem coord_sum_single {n : ℕ} (v : Fin n → ℝ) :
    (∑ μ : Fin n, v μ • Pi.single μ (1 : ℝ)) = v := by
  ext ν
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem fderiv_eq_sum_coherencePartial {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x v : Fin n → ℝ) :
    fderiv ℝ Ψ x v = ∑ μ : Fin n, v μ • coherencePartial Q Ψ x μ := by
  conv_lhs => rw [← coord_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  exact map_smul (fderiv ℝ Ψ x) (v μ) (Pi.single μ (1 : ℝ))

/-- Emergent Euclidean-blade pullback metric tensor
`g_μν(x) = ⟨∂_μ Ψ(x), ∂_ν Ψ(x)⟩_blade`. -/
noncomputable def coherenceMetricMatrix {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun μ ν =>
    cliffordBladeInner Q (coherencePartial Q Ψ x μ) (coherencePartial Q Ψ x ν)

theorem coherenceMetricMatrix_isSymm {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    (coherenceMetricMatrix Q Ψ x).IsSymm := by
  ext μ ν
  simp only [Matrix.transpose_apply, coherenceMetricMatrix, Matrix.of_apply]
  exact cliffordBladeInner_symm Q (coherencePartial Q Ψ x ν) (coherencePartial Q Ψ x μ)

theorem coherenceMetricMatrix_isHermitian {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    (coherenceMetricMatrix Q Ψ x).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (coherenceMetricMatrix_isSymm Q Ψ x)

theorem coherenceMetricMatrix_const {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (c : CliffordAlgebra Q) (x : Fin n → ℝ) :
    coherenceMetricMatrix Q (fun _ => c) x = 0 := by
  ext μ ν
  simp [coherenceMetricMatrix, coherencePartial]

theorem coherenceMetricMatrix_bilinear {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x v w : Fin n → ℝ) :
    v ⬝ᵥ (coherenceMetricMatrix Q Ψ x *ᵥ w) =
      cliffordBladeInner Q (fderiv ℝ Ψ x v) (fderiv ℝ Ψ x w) := by
  rw [fderiv_eq_sum_coherencePartial Q Ψ x v, fderiv_eq_sum_coherencePartial Q Ψ x w]
  simp only [dotProduct, Matrix.mulVec, coherenceMetricMatrix, Matrix.of_apply, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl fun μ _ => Finset.sum_congr (M := ℝ) rfl fun ν _ => ?_
  exact (mul_assoc (v μ) _ (w ν)).symm.trans (mul_comm _ (w ν))

theorem coherenceMetricMatrix_quadratic_form {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x v : Fin n → ℝ) :
    star v ⬝ᵥ (coherenceMetricMatrix Q Ψ x *ᵥ v) =
      cliffordBladeInner Q (fderiv ℝ Ψ x v) (fderiv ℝ Ψ x v) := by
  simpa only [star_trivial] using coherenceMetricMatrix_bilinear Q Ψ x v v

theorem coherenceMetricMatrix_posSemidef {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    (coherenceMetricMatrix Q Ψ x).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (coherenceMetricMatrix_isHermitian Q Ψ x) fun v => ?_
  rw [coherenceMetricMatrix_quadratic_form]
  exact cliffordBladeInner_self_nonneg Q _

/-- **Gram Positivity Theorem**: the emergent pullback metric `coherenceMetricMatrix Q Ψ x`
is strictly positive definite if and only if the tangent partials `∂_μ Ψ(x)` are linearly
independent in `CliffordAlgebra Q`. -/
theorem coherenceMetricMatrix_posDef_iff_linearIndependent {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    (coherenceMetricMatrix Q Ψ x).PosDef ↔
      LinearIndependent ℝ (coherencePartial Q Ψ x) := by
  constructor
  · intro hpd
    rw [Fintype.linearIndependent_iff]
    intro v hv μ
    by_contra hμ
    have hvne : v ≠ 0 := fun h0 => hμ (congrFun h0 μ)
    have hpos := hpd.dotProduct_mulVec_pos hvne
    rw [coherenceMetricMatrix_quadratic_form, fderiv_eq_sum_coherencePartial, hv, map_zero] at hpos
    exact lt_irrefl (0 : ℝ) hpos
  · intro hli
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (coherenceMetricMatrix_isHermitian Q Ψ x) fun v hv => ?_
    rw [coherenceMetricMatrix_quadratic_form, cliffordBladeInner_self_pos_iff]
    intro h0
    apply hv
    ext μ
    rw [fderiv_eq_sum_coherencePartial] at h0
    exact (Fintype.linearIndependent_iff.mp hli v h0) μ

theorem coherenceMetricMatrix_det_pos {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {Ψ : (Fin n → ℝ) → CliffordAlgebra Q} {x : Fin n → ℝ}
    (hli : LinearIndependent ℝ (coherencePartial Q Ψ x)) :
    0 < (coherenceMetricMatrix Q Ψ x).det :=
  ((coherenceMetricMatrix_posDef_iff_linearIndependent Q Ψ x).mpr hli).det_pos

theorem coherenceMetricMatrix_det_ne_zero {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {Ψ : (Fin n → ℝ) → CliffordAlgebra Q} {x : Fin n → ℝ}
    (hli : LinearIndependent ℝ (coherencePartial Q Ψ x)) :
    (coherenceMetricMatrix Q Ψ x).det ≠ 0 :=
  (coherenceMetricMatrix_det_pos Q hli).ne'

theorem coherenceMetricMatrix_isUnit {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {Ψ : (Fin n → ℝ) → CliffordAlgebra Q} {x : Fin n → ℝ}
    (hli : LinearIndependent ℝ (coherencePartial Q Ψ x)) :
    IsUnit (coherenceMetricMatrix Q Ψ x) :=
  (Matrix.isUnit_iff_isUnit_det (coherenceMetricMatrix Q Ψ x)).mpr
    (IsUnit.mk0 _ (coherenceMetricMatrix_det_ne_zero Q hli))

/-- Grace-weighted emergent coherence metric tensor
`g^G_μν(x) = ⟨∂_μ Ψ(x), G_Q ∂_ν Ψ(x)⟩_blade`. -/
noncomputable def coherenceGraceMetricMatrix {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun μ ν =>
    graceBladeInner Q (coherencePartial Q Ψ x μ) (coherencePartial Q Ψ x ν)

theorem coherenceGraceMetricMatrix_isSymm {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    (coherenceGraceMetricMatrix Q Ψ x).IsSymm := by
  ext μ ν
  simp only [Matrix.transpose_apply, coherenceGraceMetricMatrix, Matrix.of_apply]
  exact graceBladeInner_symm Q (coherencePartial Q Ψ x ν) (coherencePartial Q Ψ x μ)

theorem coherenceGraceMetricMatrix_isHermitian {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    (coherenceGraceMetricMatrix Q Ψ x).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (coherenceGraceMetricMatrix_isSymm Q Ψ x)

theorem coherenceGraceMetricMatrix_bilinear {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x v w : Fin n → ℝ) :
    v ⬝ᵥ (coherenceGraceMetricMatrix Q Ψ x *ᵥ w) =
      graceBladeInner Q (fderiv ℝ Ψ x v) (fderiv ℝ Ψ x w) := by
  rw [fderiv_eq_sum_coherencePartial Q Ψ x v, fderiv_eq_sum_coherencePartial Q Ψ x w]
  simp only [dotProduct, Matrix.mulVec, coherenceGraceMetricMatrix, Matrix.of_apply, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl fun μ _ => Finset.sum_congr (M := ℝ) rfl fun ν _ => ?_
  exact (mul_assoc (v μ) _ (w ν)).symm.trans (mul_comm _ (w ν))

theorem coherenceGraceMetricMatrix_quadratic_form {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x v : Fin n → ℝ) :
    star v ⬝ᵥ (coherenceGraceMetricMatrix Q Ψ x *ᵥ v) =
      graceBladeInner Q (fderiv ℝ Ψ x v) (fderiv ℝ Ψ x v) := by
  simpa only [star_trivial] using coherenceGraceMetricMatrix_bilinear Q Ψ x v v

theorem coherenceMetricMatrix_quadratic_bounds {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x v : Fin n → ℝ) :
    φ ^ (-(n : ℤ)) * (star v ⬝ᵥ (coherenceMetricMatrix Q Ψ x *ᵥ v)) ≤
        star v ⬝ᵥ (coherenceGraceMetricMatrix Q Ψ x *ᵥ v) ∧
      star v ⬝ᵥ (coherenceGraceMetricMatrix Q Ψ x *ᵥ v) ≤
        star v ⬝ᵥ (coherenceMetricMatrix Q Ψ x *ᵥ v) := by
  rw [coherenceMetricMatrix_quadratic_form, coherenceGraceMetricMatrix_quadratic_form]
  exact graceBladeInner_bounds Q (fderiv ℝ Ψ x v)

theorem coherenceGraceMetricMatrix_posSemidef {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    (coherenceGraceMetricMatrix Q Ψ x).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (coherenceGraceMetricMatrix_isHermitian Q Ψ x) fun v => ?_
  rw [coherenceGraceMetricMatrix_quadratic_form]
  exact graceBladeInner_self_nonneg Q _

theorem coherenceGraceMetricMatrix_posDef_iff_linearIndependent {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    (coherenceGraceMetricMatrix Q Ψ x).PosDef ↔
      LinearIndependent ℝ (coherencePartial Q Ψ x) := by
  constructor
  · intro hpd
    rw [Fintype.linearIndependent_iff]
    intro v hv μ
    by_contra hμ
    have hvne : v ≠ 0 := fun h0 => hμ (congrFun h0 μ)
    have hpos := hpd.dotProduct_mulVec_pos hvne
    rw [coherenceGraceMetricMatrix_quadratic_form, fderiv_eq_sum_coherencePartial, hv,
      map_zero] at hpos
    exact lt_irrefl (0 : ℝ) hpos
  · intro hli
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (coherenceGraceMetricMatrix_isHermitian Q Ψ x) fun v hv => ?_
    rw [coherenceGraceMetricMatrix_quadratic_form, graceBladeInner_self_pos_iff]
    intro h0
    apply hv
    ext μ
    rw [fderiv_eq_sum_coherencePartial] at h0
    exact (Fintype.linearIndependent_iff.mp hli v h0) μ

theorem coherenceGraceMetricMatrix_det_pos {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {Ψ : (Fin n → ℝ) → CliffordAlgebra Q} {x : Fin n → ℝ}
    (hli : LinearIndependent ℝ (coherencePartial Q Ψ x)) :
    0 < (coherenceGraceMetricMatrix Q Ψ x).det :=
  ((coherenceGraceMetricMatrix_posDef_iff_linearIndependent Q Ψ x).mpr hli).det_pos

end PullbackMetric

/-! ## Part B: Smooth `Cl(3,1)` Spacetime Immersion Witness -/

section SpacetimeImmersionWitness

/-- Continuous linear map realizing the canonical grade-1 embedding `ℝ⁴ →L[ℝ] Cl(3,1)`. -/
noncomputable def canonicalLinearCoherence31CLM : (Fin 4 → ℝ) →L[ℝ] Cl31 :=
  LinearMap.toContinuousLinearMap (CliffordAlgebra.ι Q31)

/-- Canonical smooth affine-plus-linear `Cl(3,1)` spacetime immersion witness:
`Ψ(x) = 1 + ι_{3,1}(x)`, carrying nonvanishing scalar amplitude `1` and full-rank
grade-1 spacetime tangents at every point `x : Fin 4 → ℝ`. -/
noncomputable def canonicalLinearCoherence31 (x : Fin 4 → ℝ) : Cl31 :=
  (1 : Cl31) + canonicalLinearCoherence31CLM x

theorem hasFDerivAt_canonicalLinearCoherence31 (x : Fin 4 → ℝ) :
    HasFDerivAt canonicalLinearCoherence31 canonicalLinearCoherence31CLM x :=
  (canonicalLinearCoherence31CLM.hasFDerivAt).const_add (1 : Cl31)

theorem contDiff_canonicalLinearCoherence31 :
    ContDiff ℝ (⊤ : ℕ∞) canonicalLinearCoherence31 :=
  contDiff_const.add canonicalLinearCoherence31CLM.contDiff

theorem coherencePartial_canonicalLinearCoherence31 (x : Fin 4 → ℝ) (μ : Fin 4) :
    coherencePartial Q31 canonicalLinearCoherence31 x μ =
      CliffordAlgebra.ι Q31 (Pi.single μ (1 : ℝ)) := by
  rw [coherencePartial_of_hasFDerivAt Q31 (hasFDerivAt_canonicalLinearCoherence31 x) μ]
  dsimp [canonicalLinearCoherence31CLM]

theorem linearIndependent_canonicalLinearCoherence31 (x : Fin 4 → ℝ) :
    LinearIndependent ℝ (coherencePartial Q31 canonicalLinearCoherence31 x) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg μ
  simp only [coherencePartial_canonicalLinearCoherence31] at hg
  have hsum : CliffordAlgebra.ι Q31 (∑ ν : Fin 4, g ν • Pi.single ν (1 : ℝ)) = 0 := by
    simpa only [map_sum, map_smul] using hg
  have hvec : (∑ ν : Fin 4, g ν • Pi.single ν (1 : ℝ)) = 0 :=
    clifford_ι_injective Q31 (hsum.trans (map_zero _).symm)
  rw [coord_sum_single] at hvec
  exact congrFun hvec μ

theorem coherenceMetricMatrix_canonicalLinearCoherence31_posDef (x : Fin 4 → ℝ) :
    (coherenceMetricMatrix Q31 canonicalLinearCoherence31 x).PosDef :=
  (coherenceMetricMatrix_posDef_iff_linearIndependent Q31 canonicalLinearCoherence31 x).mpr
    (linearIndependent_canonicalLinearCoherence31 x)

theorem coherenceMetricMatrix_canonicalLinearCoherence31_det_pos (x : Fin 4 → ℝ) :
    0 < (coherenceMetricMatrix Q31 canonicalLinearCoherence31 x).det :=
  (coherenceMetricMatrix_canonicalLinearCoherence31_posDef x).det_pos

theorem coherenceGraceMetricMatrix_canonicalLinearCoherence31_posDef (x : Fin 4 → ℝ) :
    (coherenceGraceMetricMatrix Q31 canonicalLinearCoherence31 x).PosDef :=
  (coherenceGraceMetricMatrix_posDef_iff_linearIndependent Q31 canonicalLinearCoherence31 x).mpr
    (linearIndependent_canonicalLinearCoherence31 x)

end SpacetimeImmersionWitness

/-! ## Part C: `C²` Scalar Density Hessian Symmetry (Schwarz Theorem) -/

section HessianSymmetry

theorem coherenceDensity_hessian_symm {n : ℕ} {ρ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hρ : ContDiffAt ℝ 2 ρ x) (v w : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ ρ) x v w = fderiv ℝ (fderiv ℝ ρ) x w v :=
  (hρ.isSymmSndFDerivAt (by simp)).eq v w

/-- Coordinate Hessian matrix `∂_μ ∂_ν ρ(x)` of a real scalar coherence density. -/
noncomputable def coherenceHessianMatrix {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun μ ν => fderiv ℝ (fderiv ℝ ρ) x (Pi.single μ (1 : ℝ)) (Pi.single ν (1 : ℝ))

theorem coherenceHessianMatrix_isSymm {n : ℕ} {ρ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hρ : ContDiffAt ℝ 2 ρ x) :
    (coherenceHessianMatrix ρ x).IsSymm := by
  ext μ ν
  exact coherenceDensity_hessian_symm hρ (Pi.single ν (1 : ℝ)) (Pi.single μ (1 : ℝ))

end HessianSymmetry

/-! ## Part D: Grace Coherence Density and Zorn–Palatini UV Confinement -/

section ZornPalatiniConfinement

/-- Euclidean-blade Dirichlet kinetic density `‖dΨ_x‖_HS² = tr(g(x))`. -/
noncomputable def coherenceGradientNormSq {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) : ℝ :=
  (coherenceMetricMatrix Q Ψ x).trace

/-- Grace-weighted Dirichlet kinetic density `tr(g^G(x)) = ∑_μ ⟨∂_μ Ψ(x), G_Q ∂_μ Ψ(x)⟩`. -/
noncomputable def graceCoherenceDensity {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) : ℝ :=
  (coherenceGraceMetricMatrix Q Ψ x).trace

theorem graceCoherenceDensity_nonneg {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    0 ≤ graceCoherenceDensity Q Ψ x := by
  dsimp [graceCoherenceDensity, coherenceGraceMetricMatrix, Matrix.trace, Matrix.diag]
  exact Finset.sum_nonneg fun μ _ => graceBladeInner_self_nonneg Q _

theorem graceCoherenceDensity_bounds {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    φ ^ (-(n : ℤ)) * coherenceGradientNormSq Q Ψ x ≤ graceCoherenceDensity Q Ψ x ∧
      graceCoherenceDensity Q Ψ x ≤ coherenceGradientNormSq Q Ψ x := by
  dsimp [graceCoherenceDensity, coherenceGradientNormSq,
    coherenceGraceMetricMatrix, coherenceMetricMatrix, Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun μ _ => (graceBladeInner_bounds Q _).1,
    Finset.sum_le_sum fun μ _ => (graceBladeInner_bounds Q _).2⟩

theorem graceCoherenceDensity_pos_of_linearIndependent {n : ℕ} [NeZero n]
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    {Ψ : (Fin n → ℝ) → CliffordAlgebra Q} {x : Fin n → ℝ}
    (hli : LinearIndependent ℝ (coherencePartial Q Ψ x)) :
    0 < graceCoherenceDensity Q Ψ x :=
  ((coherenceGraceMetricMatrix_posDef_iff_linearIndependent Q Ψ x).mpr hli).trace_pos

theorem graceCoherenceDensity_canonicalLinearCoherence31_pos (x : Fin 4 → ℝ) :
    0 < graceCoherenceDensity Q31 canonicalLinearCoherence31 x :=
  graceCoherenceDensity_pos_of_linearIndependent Q31
    (linearIndependent_canonicalLinearCoherence31 x)

/-- **Vacuum-Regularized Zorn–Palatini Stitch Density**:
`ρ_reg(x) = φ⁻² + tr(g^G(x))`, lifting stationary/caustic points strictly above `0`
via the golden vacuum gap `φ⁻² = 2 - φ = 1 - φ⁻¹`. -/
noncomputable def regularizedStitchDensity {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) : ℝ :=
  φ ^ (-(2 : ℤ)) + graceCoherenceDensity Q Ψ x

theorem regularizedStitchDensity_ge_inv_phi_sq {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    φ ^ (-(2 : ℤ)) ≤ regularizedStitchDensity Q Ψ x :=
  scalar_regularized_ge (φ ^ (-(2 : ℤ))) (graceCoherenceDensity Q Ψ x)
    (graceCoherenceDensity_nonneg Q Ψ x)

theorem regularizedStitchDensity_pos {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ) :
    0 < regularizedStitchDensity Q Ψ x :=
  lt_of_lt_of_le (zpow_pos Real.goldenRatio_pos _)
    (regularizedStitchDensity_ge_inv_phi_sq Q Ψ x)

/-- **Uniform Caustic Bound**: across every field configuration `Ψ` and point `x`
(including critical/stationary points where `∇Ψ = 0`), the vacuum-regularized effective
Newton coupling never blows up and satisfies `G_eff(x) ≤ φ² G₀`. -/
theorem effectiveNewtonConstant_regularized_le_phi_sq_mul {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ)
    {G0 : ℝ} (hG : 0 < G0) :
    effectiveNewtonConstant G0 (regularizedStitchDensity Q Ψ x) ≤ φ ^ 2 * G0 := by
  have hρ := regularizedStitchDensity_ge_inv_phi_sq Q Ψ x
  have hinvpos : (0 : ℝ) < φ ^ (-(2 : ℤ)) := zpow_pos Real.goldenRatio_pos _
  have hdiv :
      effectiveNewtonConstant G0 (regularizedStitchDensity Q Ψ x) ≤
        effectiveNewtonConstant G0 (φ ^ (-(2 : ℤ))) :=
    div_le_div_of_nonneg_left (le_of_lt hG) hinvpos hρ
  have heq : effectiveNewtonConstant G0 (φ ^ (-(2 : ℤ))) = φ ^ 2 * G0 := by
    rw [effectiveNewtonConstant, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
      div_inv_eq_mul, mul_comm]
  exact hdiv.trans_eq heq

theorem effectiveNewtonConstant_regularized_lt_caustic {n : ℕ} [NeZero n]
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    {Ψ : (Fin n → ℝ) → CliffordAlgebra Q} {x : Fin n → ℝ}
    (hli : LinearIndependent ℝ (coherencePartial Q Ψ x))
    {G0 : ℝ} (hG : 0 < G0) :
    effectiveNewtonConstant G0 (regularizedStitchDensity Q Ψ x) < φ ^ 2 * G0 := by
  have hpos : 0 < graceCoherenceDensity Q Ψ x :=
    graceCoherenceDensity_pos_of_linearIndependent Q hli
  have hlt : φ ^ (-(2 : ℤ)) < regularizedStitchDensity Q Ψ x := by
    simpa [regularizedStitchDensity] using hpos
  have hanti := effectiveNewtonConstant_strictly_anti_mono G0 (φ ^ (-(2 : ℤ)))
    (regularizedStitchDensity Q Ψ x) hG (zpow_pos Real.goldenRatio_pos _) hlt
  have heq : effectiveNewtonConstant G0 (φ ^ (-(2 : ℤ))) = φ ^ 2 * G0 := by
    rw [effectiveNewtonConstant, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
      div_inv_eq_mul, mul_comm]
  exact heq ▸ hanti

/-- **UV Confinement Theorem**: once the Grace coherence density exceeds the golden gap
`φ⁻¹`, we have `ρ_reg(x) > 1`, so Zorn–Palatini stitch dilution strictly screens Newton's
constant below its bare value: `G_eff(x) < G₀`. -/
theorem effectiveNewtonConstant_regularized_lt_bare {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    {Ψ : (Fin n → ℝ) → CliffordAlgebra Q} {x : Fin n → ℝ}
    (hthr : φ ^ (-(1 : ℤ)) < graceCoherenceDensity Q Ψ x)
    {G0 : ℝ} (hG : 0 < G0) :
    effectiveNewtonConstant G0 (regularizedStitchDensity Q Ψ x) < G0 := by
  have hgap := golden_spectral_gap_self_similar
  have hinv : φ ^ (-(1 : ℤ)) = φ - 1 := by
    linarith [hgap.1]
  have hsq : φ ^ (-(2 : ℤ)) = 2 - φ := by
    linarith [hgap.1, hgap.2.1]
  have hsum : φ ^ (-(2 : ℤ)) + φ ^ (-(1 : ℤ)) = 1 :=
    scalar_inv_phi_sq_add_inv_phi hinv hsq
  have hgt1 : 1 < regularizedStitchDensity Q Ψ x :=
    scalar_strict_uv_density hsum hthr
  have hanti := effectiveNewtonConstant_strictly_anti_mono G0 1
    (regularizedStitchDensity Q Ψ x) hG one_pos hgt1
  simpa [effectiveNewtonConstant] using hanti

theorem regularized_newton_planck_invariant {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ)
    (G0 M0_sq : ℝ) :
    effectiveNewtonConstant G0 (regularizedStitchDensity Q Ψ x) *
        effectivePlanckMassSq M0_sq (regularizedStitchDensity Q Ψ x) =
      G0 * M0_sq :=
  newton_planck_invariant G0 M0_sq (regularizedStitchDensity Q Ψ x)
    (regularizedStitchDensity_pos Q Ψ x).ne'

theorem regularized_stitch_on_klein_quadric {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ)
    (u v : Vec4 ℝ) :
    kleinQ (stitchDensity (regularizedStitchDensity Q Ψ x) (stitch u v)) = 0 :=
  stitchDensity_on_klein_quadric (regularizedStitchDensity Q Ψ x) (stitch u v)
    (stitch_on_klein_quadric u v)

theorem regularized_palatini_coupling {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ))
    (Ψ : (Fin n → ℝ) → CliffordAlgebra Q) (x : Fin n → ℝ)
    (P R_curv : Plucker6 ℝ) :
    palatiniStitchCoupling (stitchDensity (regularizedStitchDensity Q Ψ x) P) R_curv =
      regularizedStitchDensity Q Ψ x * palatiniStitchCoupling P R_curv :=
  palatiniStitchCoupling_scale (regularizedStitchDensity Q Ψ x) P R_curv

end ZornPalatiniConfinement

end InfoGeometry.InformationGeometry.CoherencePullbackMetricAndPalatiniConfinement
