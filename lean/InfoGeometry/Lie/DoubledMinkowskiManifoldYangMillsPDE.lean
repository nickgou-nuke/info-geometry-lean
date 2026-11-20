/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Smooth 4-Manifold Gauge Bundle, Chiral Krein Pairing & Yang–Mills PDE

This module extends `InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge` to a
native Mathlib smooth 4-manifold gauge-bundle and non-Abelian Yang–Mills PDE formulation:

1. **Smooth 4-Manifold, Rank-4 Complex Chiral Bundle & Krein Fiber Pairing**:
   Works over any smooth 4-manifold `[ChartedSpace FourSpace M] [IsManifold (𝓡 4) ⊤ M]`
   and rank-4 complex gauge vector bundle `[VectorBundle ℝ ChiralFiber E]` with
   `[ContMDiffVectorBundle ⊤ ChiralFiber E (𝓡 4)]`, instantiates the concrete trivial
   chiral bundle `TrivialChiralBundle FourSpace`, lifts `chiralProjMat4` to smooth global
   and local bundle projectors (`chiralBundleProjector`, `chiralLocalBundleProjector`),
   constructs the fiberwise `ℝ`-linear equivalence `chiralFiberToKreinFrame` pulling back
   the indefinite `chiralKreinForm` to `fiberKreinPairing`, and builds gauge covariant
   derivatives via `CovariantDerivative.addOneForm` (`trivialChiralConnection`,
   `circularBundleConnection`, `gaugeConnection`).
2. **Matrix-Valued Differential Forms, Curvature & Differential Bianchi Identity**:
   Defines `Mat4CForm k`, the pointwise continuous bilinear wedge-commutator `wedgeCommAt`,
   `halfWedgeSelf`, `ymCurvature := extDeriv A + halfWedgeSelf A`, and `covExtDeriv`,
   proving `bianchi_identity_ymCurvature : ContDiff ℝ 2 A → covExtDeriv A (ymCurvature A) = 0`.
3. **4D Hodge Stars, Yang–Mills PDE & Self-Duality**:
   Constructs `hodgeStar4Eucl` (`⋆² = id`) and `hodgeStar4Minkowski` using `minkowskiEta4`
   (`⋆² = -id`), defines `YangMillsPDE`, `YangMillsPDEMinkowski`, `IsSelfDualForm4`, and
   `IsAntiSelfDualForm4`, and proves `selfDual_solves_yangMillsPDE`.
4. **Explicit Non-Abelian Circular Split-Octonion Yang–Mills Solutions**:
   Constructs the smooth self-dual 1-form `circularGaugeForm` from `circularConnectionMat4`,
   proves `ymCurvature circularGaugeForm ≠ 0` and `YangMillsPDE circularGaugeForm`, bridges
   directly to `circularGaugeConnection4_yang_mills_bridge`,
   `weylChannel_commutator_eq_vorticity`, and `circularCurvatureMat4_vorticity_action_gap`,
   and constructs a spacetime-varying non-Abelian Minkowski plane-wave solution
   `circularMinkowskiWaveForm` solving `YangMillsPDEMinkowski`.
-/

noncomputable section

open scoped BigOperators Manifold ContDiff Bundle Topology Matrix ComplexConjugate
open scoped InnerProductSpace Matrix.Norms.Elementwise
open Bundle ContinuousLinearMap

namespace InfoGeometry.Lie

open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis hiding Coordinate
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame hiding FourSpace KreinFrame4
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge

local notation "Mat4C" => Matrix (Fin 4) (Fin 4) ℂ
abbrev ChiralFiber := Fin 4 → ℂ
abbrev TrivialChiralBundle (M : Type*) := Bundle.Trivial M ChiralFiber

/-- Explicit T16 noncommutativity witness for `Mat4C`. -/
theorem mat4C_noncomm_witness :
    ∃ A B : Mat4C, A * B ≠ B * A :=
  circularConnectionMat4_mat4C_noncomm_witness

/-! ## 1. Smooth 4-Manifold, Rank-4 Chiral Gauge Bundle & Covariant Derivative -/

/-- Continuous `ℝ`-linear map turning a `4 × 4` complex matrix into a real endomorphism of
`ChiralFiber`. -/
def mat4CToRealCLM : Mat4C →L[ℝ] (ChiralFiber →L[ℝ] ChiralFiber) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (A.mulVecLin.toContinuousLinearMap).restrictScalars ℝ
      map_add' := fun A B => by
        ext v i
        simp
      map_smul' := fun c A => by
        ext v i
        change ((c • A).mulVec v) i = c • (A.mulVec v) i
        rw [Matrix.smul_mulVec]
        rfl }

@[simp]
theorem mat4CToRealCLM_apply (A : Mat4C) (v : ChiralFiber) :
    mat4CToRealCLM A v = A.mulVec v :=
  rfl

theorem mat4CToRealCLM_mul (A B : Mat4C) :
    mat4CToRealCLM (A * B) = (mat4CToRealCLM A).comp (mat4CToRealCLM B) := by
  ext v i
  simp [Matrix.mulVec_mulVec]

/-- Chiral projector `chiralProjMat4` as a real continuous linear endomorphism of `ChiralFiber`. -/
def chiralProjCLM : ChiralFiber →L[ℝ] ChiralFiber :=
  mat4CToRealCLM chiralProjMat4

theorem chiralProjCLM_idempotent :
    chiralProjCLM.comp chiralProjCLM = chiralProjCLM := by
  rw [chiralProjCLM, ← mat4CToRealCLM_mul, chiralProjMat4_idempotent]

/-- Smooth global chiral bundle projector section on `TrivialChiralBundle M`. -/
def chiralBundleProjector (M : Type*) [TopologicalSpace M]
    [ChartedSpace FourSpace M] [IsManifold (𝓡 4) ⊤ M] :
    Cₛ^⊤⟮(𝓡 4); ChiralFiber →L[ℝ] ChiralFiber,
      fun x : M => TrivialChiralBundle M x →L[ℝ] TrivialChiralBundle M x⟯ where
  toFun _ := chiralProjCLM
  contMDiff_toFun := by
    intro x₀
    rw [Bundle.contMDiffAt_section]
    have hconst :
        (fun x : M => (trivializationAt (ChiralFiber →L[ℝ] ChiralFiber)
          (fun y : M => TrivialChiralBundle M y →L[ℝ] TrivialChiralBundle M y) x₀
            ⟨x, chiralProjCLM⟩).2) = fun _ => chiralProjCLM := by
      funext x
      rw [hom_trivializationAt_apply]
      ext v
      simp [ContinuousLinearMap.inCoordinates, Bundle.Trivial.fiberBundle_trivializationAt']
    rw [hconst]
    exact contMDiffAt_const

theorem chiralBundleProjector_idempotent (M : Type*) [TopologicalSpace M]
    [ChartedSpace FourSpace M] [IsManifold (𝓡 4) ⊤ M] (x : M) :
    (chiralBundleProjector M x).comp (chiralBundleProjector M x) =
      chiralBundleProjector M x :=
  chiralProjCLM_idempotent

section GeneralBundle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold (𝓡 4) ⊤ M]
  {E : M → Type*} [TopologicalSpace (TotalSpace ChiralFiber E)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [∀ x, TopologicalSpace (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)]
  [FiberBundle ChiralFiber E] [VectorBundle ℝ ChiralFiber E]
  [ContMDiffVectorBundle ⊤ ChiralFiber E (𝓡 4)]

/-- Local lifted chiral bundle projector on an arbitrary smooth rank-4 complex vector bundle `E`
over a smooth 4-manifold `M` in a trivialization `e`. -/
def chiralLocalBundleProjector
    (e : Trivialization ChiralFiber (π ChiralFiber E)) [MemTrivializationAtlas e]
    (x : M) : E x →L[ℝ] E x :=
  (e.symmL ℝ x).comp (chiralProjCLM.comp (e.continuousLinearMapAt ℝ x))

omit [ChartedSpace FourSpace M] [IsManifold (𝓡 4) ⊤ M]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)]
  [ContMDiffVectorBundle ⊤ ChiralFiber E (𝓡 4)] in
theorem chiralLocalBundleProjector_idempotent
    (e : Trivialization ChiralFiber (π ChiralFiber E)) [MemTrivializationAtlas e]
    {x : M} (hx : x ∈ e.baseSet) :
    (chiralLocalBundleProjector e x).comp (chiralLocalBundleProjector e x) =
      chiralLocalBundleProjector e x := by
  ext v
  simp only [chiralLocalBundleProjector, comp_apply]
  rw [e.continuousLinearMapAt_symmL hx]
  exact congrArg (e.symmL ℝ x)
    (congrFun (congrArg DFunLike.coe chiralProjCLM_idempotent) _)

/-- Gauge connection `cov + A` on an arbitrary smooth vector bundle `E` over `(M, 𝓡 4)` via
`CovariantDerivative.addOneForm`. -/
def gaugeConnection
    (cov : CovariantDerivative (𝓡 4) ChiralFiber E)
    (A : ∀ x : M, E x →L[ℝ] TangentSpace (𝓡 4) x →L[ℝ] E x) :
    CovariantDerivative (𝓡 4) ChiralFiber E :=
  cov.addOneForm A

omit [IsManifold (𝓡 4) ⊤ M] [VectorBundle ℝ ChiralFiber E]
  [ContMDiffVectorBundle ⊤ ChiralFiber E (𝓡 4)] in
theorem gaugeConnection_apply
    (cov : CovariantDerivative (𝓡 4) ChiralFiber E)
    (A : ∀ x : M, E x →L[ℝ] TangentSpace (𝓡 4) x →L[ℝ] E x)
    (σ : ∀ x : M, E x) (x : M) :
    gaugeConnection cov A σ x = cov σ x + A x (σ x) :=
  rfl

end GeneralBundle

/-- Explicit `ℝ`-linear isomorphism identifying `ChiralFiber = Fin 4 → ℂ` with the real
8-dimensional doubled Krein carrier `KreinFrame4`, mapping upper `(ψ 0, ψ 1)` to the `+` sheet
and lower `(ψ 2, ψ 3)` to the `-` sheet. -/
def chiralFiberToKreinFrame : ChiralFiber ≃ₗ[ℝ] KreinFrame4 where
  toFun ψ := InfoGeometry.Krein.to_doubled
    (WithLp.toLp (2 : ENNReal) ![(ψ 0).re, (ψ 0).im, (ψ 1).re, (ψ 1).im])
    (WithLp.toLp (2 : ENNReal) ![(ψ 2).re, (ψ 2).im, (ψ 3).re, (ψ 3).im])
  invFun u := ![
    ⟨WithLp.fst u 0, WithLp.fst u 1⟩,
    ⟨WithLp.fst u 2, WithLp.fst u 3⟩,
    ⟨WithLp.snd u 0, WithLp.snd u 1⟩,
    ⟨WithLp.snd u 2, WithLp.snd u 3⟩]
  left_inv ψ := by
    ext i
    fin_cases i <;> apply Complex.ext <;> rfl
  right_inv u := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      apply PiLp.ext <;> intro i <;> fin_cases i <;> rfl
  map_add' ψ φ := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      apply PiLp.ext <;> intro i <;> fin_cases i <;> simp
  map_smul' c ψ := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;>
      apply PiLp.ext <;> intro i <;> fin_cases i <;> simp

/-- `ℝ`-linear equivalence between `ChiralFiber` and the circular split-octonion `Coordinate`. -/
def fiberCoordEquiv : ChiralFiber ≃ₗ[ℝ] Coordinate :=
  chiralFiberToKreinFrame.trans circularCoordToKreinFrame.symm

/-- Indefinite, sheet-isotropic Krein bilinear pairing on `ChiralFiber` pulled back from
`chiralKreinForm` on `KreinFrame4`. -/
def fiberKreinPairing (u v : ChiralFiber) : ℝ :=
  chiralKreinForm (E := FourSpace)
    (chiralFiberToKreinFrame u) (chiralFiberToKreinFrame v)

theorem chiralFiberToKreinFrame_intertwines_proj (u : ChiralFiber) :
    chiralFiberToKreinFrame (chiralProjCLM u) =
      leftChiralProjector (E := FourSpace) (chiralFiberToKreinFrame u) := by
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    apply PiLp.ext <;> intro i <;> fin_cases i <;>
    simp [chiralProjCLM, chiralProjMat4, chiralProj4, chiralDiagBlock4,
      chiralFiberToKreinFrame, leftChiralProjector, gamma5,
      InfoGeometry.Krein.spectral_epsilon, dotProduct, Fin.sum_univ_four] <;>
    ring

/-- The scalar complex structure of the complex chiral fiber is not the
sheet-swapping Hestenes complex structure on `KreinFrame4`.  Under
`chiralFiberToKreinFrame`, multiplication by `Complex.I` rotates real and
imaginary coordinates within the positive sheet; `doubledComplexStructure`
instead transfers a positive-sheet vector to the negative sheet.  This
distinction is essential when translating the complex Yang--Mills matrices
into the real Koszul-graded matrix factors. -/
theorem chiralFiber_phase_not_doubledHestenesJ :
    chiralFiberToKreinFrame
        (Complex.I • ![(1 : ℂ), 0, 0, 0] : ChiralFiber) ≠
      doubledComplexStructure
        (chiralFiberToKreinFrame (![(1 : ℂ), 0, 0, 0] : ChiralFiber)) := by
  intro h
  have h' := congrArg (fun u : KreinFrame4 => WithLp.fst u) h
  have h'' := congrArg (fun u : FourSpace => u 1) h'
  norm_num [chiralFiberToKreinFrame, doubledComplexStructure,
    InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.chiralComplexStructure,
    InfoGeometry.Krein.complex_i, InfoGeometry.Krein.modular_j,
    InfoGeometry.Krein.spectral_epsilon, Complex.I_re, Complex.I_im] at h''

theorem fiberKreinPairing_chiralProj_isotropic (u v : ChiralFiber) :
    fiberKreinPairing (chiralProjCLM u) (chiralProjCLM v) = 0 := by
  simp only [fiberKreinPairing, chiralFiberToKreinFrame_intertwines_proj]
  exact chiralKreinForm_left_projected_left_projected _ _

/-- Canonical flat covariant derivative on `TrivialChiralBundle M` over any smooth 4-manifold. -/
def trivialChiralConnection (M : Type*) [TopologicalSpace M]
    [ChartedSpace FourSpace M] [IsManifold (𝓡 4) ⊤ M] :
    CovariantDerivative (𝓡 4) ChiralFiber (TrivialChiralBundle M) where
  toFun σ x := mvfderiv (𝓡 4) σ x
  isCovariantDerivativeOnUniv :=
    { add := fun {σ σ' x} hσ hσ' _ => by
        let σ₁ : M → ChiralFiber := σ
        let σ₂ : M → ChiralFiber := σ'
        have h1 : MDifferentiableAt (𝓡 4) 𝓘(ℝ, ChiralFiber) σ₁ x := by
          simpa [σ₁, Bundle.Trivial.fiberBundle_trivializationAt'] using
            (mdifferentiableAt_section (IB := 𝓡 4) (F := ChiralFiber)
              (E := TrivialChiralBundle M) σ).mp hσ
        have h2 : MDifferentiableAt (𝓡 4) 𝓘(ℝ, ChiralFiber) σ₂ x := by
          simpa [σ₂, Bundle.Trivial.fiberBundle_trivializationAt'] using
            (mdifferentiableAt_section (IB := 𝓡 4) (F := ChiralFiber)
              (E := TrivialChiralBundle M) σ').mp hσ'
        exact mvfderiv_add h1 h2
      leibniz := fun {σ g x} hσ hg _ => by
        let σ₁ : M → ChiralFiber := σ
        have h1 : MDifferentiableAt (𝓡 4) 𝓘(ℝ, ChiralFiber) σ₁ x := by
          simpa [σ₁, Bundle.Trivial.fiberBundle_trivializationAt'] using
            (mdifferentiableAt_section (IB := 𝓡 4) (F := ChiralFiber)
              (E := TrivialChiralBundle M) σ).mp hσ
        exact mvfderiv_smul hg h1 }

/-- Convert a `Mat4C`-valued differential 1-form on `FourSpace` to a bundle-endomorphism
1-form compatible with `CovariantDerivative.addOneForm`. -/
def mat4COneFormToBundleEnd
    (A : FourSpace → (FourSpace [⋀^Fin 1]→L[ℝ] Mat4C)) (x : FourSpace) :
    TrivialChiralBundle FourSpace x →L[ℝ]
      TangentSpace (𝓡 4) x →L[ℝ] TrivialChiralBundle FourSpace x :=
  (mat4CToRealCLM.comp
    ((ContinuousAlternatingMap.ofSubsingleton ℝ FourSpace Mat4C (0 : Fin 1)).symm (A x))).flip

/-- Gauge covariant derivative `∇^A = d + A` on `TrivialChiralBundle FourSpace` constructed via
`CovariantDerivative.addOneForm`. -/
def circularBundleConnection
    (A : FourSpace → (FourSpace [⋀^Fin 1]→L[ℝ] Mat4C)) :
    CovariantDerivative (𝓡 4) ChiralFiber (TrivialChiralBundle FourSpace) :=
  (trivialChiralConnection FourSpace).addOneForm (mat4COneFormToBundleEnd A)

theorem circularBundleConnection_apply
    (A : FourSpace → (FourSpace [⋀^Fin 1]→L[ℝ] Mat4C))
    (σ : FourSpace → ChiralFiber) (x v : FourSpace) :
    circularBundleConnection A σ x v =
      fderiv ℝ σ x v + (A x (fun _ => v)).mulVec (σ x) := by
  dsimp [circularBundleConnection, CovariantDerivative.addOneForm,
    trivialChiralConnection, mat4COneFormToBundleEnd]
  rw [mvfderiv_eq_fderiv]
  rfl

/-! ## 2. Matrix-Valued Differential Forms, Curvature & Differential Bianchi -/

instance instNormedAddCommGroupMat4CFormValue (k : ℕ) :
    NormedAddCommGroup (FourSpace [⋀^Fin k]→L[ℝ] Mat4C) :=
  let inst : NormedAddCommGroup (FourSpace [⋀^Fin k]→L[ℝ] Mat4C) :=
    letI : NormedAddCommGroup Mat4C := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ Mat4C := Matrix.normedSpace
    ContinuousAlternatingMap.instNormedAddCommGroup
  { inst with
    toAddCommGroup := ContinuousAlternatingMap.instAddCommGroup
    toUniformSpace :=
      { inst.toUniformSpace with
        toTopologicalSpace := ContinuousAlternatingMap.instTopologicalSpace } }

instance instNormedSpaceMat4CFormValue (k : ℕ) :
    NormedSpace ℝ (FourSpace [⋀^Fin k]→L[ℝ] Mat4C) where
  toModule := ContinuousAlternatingMap.instModule
  norm_smul_le c f := by
    let : NormedAddCommGroup Mat4C := Matrix.normedAddCommGroup
    let : NormedSpace ℝ Mat4C := Matrix.normedSpace
    exact (ContinuousAlternatingMap.instNormedSpace :
      NormedSpace ℝ (FourSpace [⋀^Fin k]→L[ℝ] Mat4C)).norm_smul_le c f

/-- Smooth `Mat4C`-valued differential `k`-form on `FourSpace`. -/
abbrev Mat4CForm (k : ℕ) :=
  FourSpace → (FourSpace [⋀^Fin k]→L[ℝ] Mat4C)

/-- Underlying continuous linear map `FourSpace →L[ℝ] Mat4C` of a `1`-form value. -/
def oneFormCLM :
    (FourSpace [⋀^Fin 1]→L[ℝ] Mat4C) →L[ℝ] (FourSpace →L[ℝ] Mat4C) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace)
    (F := Mat4C) (0 : Fin 1)).symm.toLinearIsometry.toContinuousLinearMap

@[simp]
theorem oneFormCLM_apply (α : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C) (u : FourSpace) :
    oneFormCLM α u = α (fun _ => u) :=
  rfl

/-- Continuous bilinear matrix commutator `(X, Y) ↦ X * Y - Y * X` on `Mat4C`. -/
def mat4CCommCLM : Mat4C →L[ℝ] Mat4C →L[ℝ] Mat4C :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X =>
        LinearMap.toContinuousLinearMap
          { toFun := fun Y => X * Y - Y * X
            map_add' := fun Y₁ Y₂ => by ext i j; simp [mul_add, add_mul]; ring
            map_smul' := fun c Y => by
              ext i j
              simp [Complex.real_smul]
              ring }
      map_add' := fun X₁ X₂ => by ext Y i j; simp [add_mul, mul_add]; ring
      map_smul' := fun c X => by
        ext Y i j
        simp [Complex.real_smul]
        ring }

@[simp]
theorem mat4CCommCLM_apply (X Y : Mat4C) :
    mat4CCommCLM X Y = X * Y - Y * X :=
  rfl

private lemma norm_mat4C_mul_le (X Y : Mat4C) :
    ‖X * Y‖ ≤ 4 * ‖X‖ * ‖Y‖ := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  calc
    ‖∑ k : Fin 4, X i k * Y k j‖ ≤ ∑ k : Fin 4, ‖X i k * Y k j‖ := norm_sum_le _ _
    _ = ∑ k : Fin 4, ‖X i k‖ * ‖Y k j‖ := by simp only [norm_mul]
    _ ≤ ∑ _k : Fin 4, ‖X‖ * ‖Y‖ := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm X)
        (Matrix.norm_entry_le_entrywise_sup_norm Y) (norm_nonneg _) (norm_nonneg _)
    _ = 4 * ‖X‖ * ‖Y‖ := by simp [mul_assoc]

private lemma norm_mat4CCommCLM_le (X Y : Mat4C) :
    ‖mat4CCommCLM X Y‖ ≤ 8 * ‖X‖ * ‖Y‖ := by
  change ‖X * Y - Y * X‖ ≤ 8 * ‖X‖ * ‖Y‖
  calc
    ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ 4 * ‖X‖ * ‖Y‖ + 4 * ‖Y‖ * ‖X‖ := add_le_add (norm_mat4C_mul_le X Y)
      (norm_mat4C_mul_le Y X)
    _ = 8 * ‖X‖ * ‖Y‖ := by ring

private def wedgeCommPre (k : ℕ)
    (α : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C)
    (η : FourSpace [⋀^Fin k]→L[ℝ] Mat4C) :
    FourSpace →L[ℝ] (FourSpace [⋀^Fin k]→L[ℝ] Mat4C) :=
  LinearMap.mkContinuous
    { toFun := fun u =>
        (mat4CCommCLM (α (fun _ => u))).compContinuousAlternatingMap η
      map_add' := fun u₁ u₂ => by
        apply ContinuousAlternatingMap.ext
        intro v
        have hadd : α (fun _ => u₁ + u₂) = α (fun _ => u₁) + α (fun _ => u₂) :=
          (oneFormCLM α).map_add u₁ u₂
        change mat4CCommCLM (α (fun _ => u₁ + u₂)) (η v) =
          mat4CCommCLM (α (fun _ => u₁)) (η v) + mat4CCommCLM (α (fun _ => u₂)) (η v)
        rw [hadd, map_add, add_apply]
      map_smul' := fun c u => by
        apply ContinuousAlternatingMap.ext
        intro v
        have hsmul : α (fun _ => c • u) = c • α (fun _ => u) :=
          (oneFormCLM α).map_smul c u
        change mat4CCommCLM (α (fun _ => c • u)) (η v) =
          c • mat4CCommCLM (α (fun _ => u)) (η v)
        rw [hsmul, map_smul, smul_apply] }
    (8 * ‖α‖ * ‖η‖)
    (fun u => by
      refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
      change ‖mat4CCommCLM (α (fun _ => u)) (η v)‖ ≤ _
      calc
        ‖mat4CCommCLM (α (fun _ => u)) (η v)‖
            ≤ 8 * ‖α (fun _ => u)‖ * ‖η v‖ := norm_mat4CCommCLM_le _ _
        _ ≤ 8 * (‖α‖ * ∏ _i : Fin 1, ‖u‖) * (‖η‖ * ∏ i : Fin k, ‖v i‖) := by
          gcongr
          · exact α.le_opNorm (fun _ => u)
          · exact η.le_opNorm v
        _ = (8 * ‖α‖ * ‖η‖ * ‖u‖) * ∏ i : Fin k, ‖v i‖ := by
          simp only [Fin.prod_univ_one]
          ring)

private lemma wedgeCommPre_apply (k : ℕ)
    (α : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C)
    (η : FourSpace [⋀^Fin k]→L[ℝ] Mat4C)
    (u : FourSpace) (w : Fin k → FourSpace) :
    wedgeCommPre k α η u w = mat4CCommCLM (α (fun _ => u)) (η w) :=
  rfl

private lemma alternatizeUncurryFin_mat4C_apply {k : ℕ}
    (f : FourSpace →L[ℝ] (FourSpace [⋀^Fin k]→L[ℝ] Mat4C))
    (v : Fin (k + 1) → FourSpace) :
    (letI : NormedAddCommGroup Mat4C := Matrix.normedAddCommGroup
     letI : NormedSpace ℝ Mat4C := Matrix.normedSpace
     (ContinuousAlternatingMap.alternatizeUncurryFin f :
       FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C)) v =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • f (v i) (i.removeNth v) := by
  let : NormedAddCommGroup Mat4C := Matrix.normedAddCommGroup
  let : NormedSpace ℝ Mat4C := Matrix.normedSpace
  exact ContinuousAlternatingMap.alternatizeUncurryFin_apply f v

private noncomputable def extD {k : ℕ} (η : Mat4CForm k) : Mat4CForm (k + 1) :=
  extDeriv η

private lemma extD_apply {k : ℕ} {η : Mat4CForm k} {x : FourSpace}
    (h : DifferentiableAt ℝ η x) (v : Fin (k + 1) → FourSpace) :
    extD η x v =
      ∑ i : Fin (k + 1), (-1) ^ i.val • fderiv ℝ (η · (i.removeNth v)) x (v i) :=
  extDeriv_apply h v

private lemma extD_add {k : ℕ} {η₁ η₂ : Mat4CForm k} {x : FourSpace}
    (h₁ : DifferentiableAt ℝ η₁ x) (h₂ : DifferentiableAt ℝ η₂ x) :
    extD (η₁ + η₂) x = extD η₁ x + extD η₂ x :=
  extDeriv_add h₁ h₂

private lemma extD_smul {k : ℕ} (c : ℝ) (η : Mat4CForm k) (x : FourSpace) :
    extD (c • η) x = c • extD η x :=
  extDeriv_smul c η

private lemma extD_extD {k : ℕ} {η : Mat4CForm k} (h : ContDiff ℝ 2 η) :
    extD (extD η) = 0 :=
  extDeriv_extDeriv h (by simp)

private lemma fderiv_mat4CForm_apply_const {k : ℕ} {c : Mat4CForm k} {x : FourSpace}
    (hc : DifferentiableAt ℝ c x) (u : Fin k → FourSpace) (m : FourSpace) :
    fderiv ℝ (fun y => c y u) x m = fderiv ℝ c x m u :=
  fderiv_continuousAlternatingMap_apply_const_apply hc u m

private def wedgeCommAtLM (k : ℕ) :
    (FourSpace [⋀^Fin 1]→L[ℝ] Mat4C) →ₗ[ℝ]
      (FourSpace [⋀^Fin k]→L[ℝ] Mat4C) →ₗ[ℝ]
        (FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) :=
  LinearMap.mk₂ ℝ
    (fun α η => ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α η))
    (fun α₁ α₂ η => by
      apply ContinuousAlternatingMap.ext
      intro v
      change (ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k (α₁ + α₂) η) :
          FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) v =
        ((ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α₁ η) :
            FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) +
          (ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α₂ η) :
            FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C)) v
      rw [ContinuousAlternatingMap.add_apply, alternatizeUncurryFin_mat4C_apply,
        alternatizeUncurryFin_mat4C_apply, alternatizeUncurryFin_mat4C_apply]
      simp only [wedgeCommPre_apply, ContinuousAlternatingMap.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, add_apply, smul_add])
    (fun c α η => by
      apply ContinuousAlternatingMap.ext
      intro v
      change (ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k (c • α) η) :
          FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) v =
        (c • (ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α η) :
          FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C)) v
      rw [ContinuousAlternatingMap.smul_apply, alternatizeUncurryFin_mat4C_apply,
        alternatizeUncurryFin_mat4C_apply]
      simp only [wedgeCommPre_apply, ContinuousAlternatingMap.smul_apply]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_apply, smul_comm])
    (fun α η₁ η₂ => by
      apply ContinuousAlternatingMap.ext
      intro v
      change (ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α (η₁ + η₂)) :
          FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) v =
        ((ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α η₁) :
            FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) +
          (ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α η₂) :
            FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C)) v
      rw [ContinuousAlternatingMap.add_apply, alternatizeUncurryFin_mat4C_apply,
        alternatizeUncurryFin_mat4C_apply, alternatizeUncurryFin_mat4C_apply]
      simp only [wedgeCommPre_apply, ContinuousAlternatingMap.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, smul_add])
    (fun c α η => by
      apply ContinuousAlternatingMap.ext
      intro v
      change (ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α (c • η)) :
          FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) v =
        (c • (ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α η) :
          FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C)) v
      rw [ContinuousAlternatingMap.smul_apply, alternatizeUncurryFin_mat4C_apply,
        alternatizeUncurryFin_mat4C_apply]
      simp only [wedgeCommPre_apply, ContinuousAlternatingMap.smul_apply]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_comm])

/-- Pointwise graded wedge-commutator `[α ∧ η]` for a `1`-form `α` and `k`-form `η`,
bundled as a continuous bilinear map via `ContinuousAlternatingMap.alternatizeUncurryFin`. -/
def wedgeCommAt (k : ℕ) :
    (FourSpace [⋀^Fin 1]→L[ℝ] Mat4C) →L[ℝ]
      (FourSpace [⋀^Fin k]→L[ℝ] Mat4C) →L[ℝ]
        (FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) :=
  LinearMap.mkContinuous₂ (wedgeCommAtLM k) (8 * ((k : ℝ) + 1)) <| by
    intro α η
    have h1 :
        ‖(ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α η) :
          FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C)‖ ≤
          ((k : ℝ) + 1) * ‖wedgeCommPre k α η‖ :=
      ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _
    have h2 : ‖wedgeCommPre k α η‖ ≤ 8 * ‖α‖ * ‖η‖ :=
      LinearMap.mkContinuous_norm_le _ (by positivity) _
    calc
      ‖wedgeCommAtLM k α η‖
          ≤ ((k : ℝ) + 1) * (8 * ‖α‖ * ‖η‖) := by
            refine h1.trans ?_
            gcongr
      _ = 8 * ((k : ℝ) + 1) * ‖α‖ * ‖η‖ := by ring

theorem wedgeCommAt_apply (k : ℕ)
    (α : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C)
    (η : FourSpace [⋀^Fin k]→L[ℝ] Mat4C)
    (v : Fin (k + 1) → FourSpace) :
    wedgeCommAt k α η v =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) •
        mat4CCommCLM (α (fun _ => v i)) (η (i.removeNth v)) := by
  change (ContinuousAlternatingMap.alternatizeUncurryFin (wedgeCommPre k α η) :
    FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) v = _
  rw [alternatizeUncurryFin_mat4C_apply]
  rfl

/-- Wedge-commutator `[A ∧ η]` of a `Mat4C`-valued 1-form `A` with a `k`-form `η`. -/
def wedgeComm {k : ℕ} (A : Mat4CForm 1) (η : Mat4CForm k) : Mat4CForm (k + 1) :=
  fun x => wedgeCommAt k (A x) (η x)

/-- Quadratic self-commutator `A ∧ A = (1 / 2) [A ∧ A]` as a `Mat4C`-valued 2-form. -/
def halfWedgeSelf (A : Mat4CForm 1) : Mat4CForm 2 :=
  fun x => (1 / 2 : ℝ) • wedgeCommAt 1 (A x) (A x)

/-- Non-Abelian Yang–Mills curvature 2-form `F = dA + A ∧ A`. -/
def ymCurvature (A : Mat4CForm 1) : Mat4CForm 2 :=
  fun x => extD A x + halfWedgeSelf A x

/-- Covariant exterior derivative `d_A η = dη + [A ∧ η]`. -/
def covExtDeriv {k : ℕ} (A : Mat4CForm 1) (η : Mat4CForm k) : Mat4CForm (k + 1) :=
  fun x => extD η x + wedgeComm A η x

theorem halfWedgeSelf_apply (A : Mat4CForm 1) (x : FourSpace) (w : Fin 2 → FourSpace) :
    halfWedgeSelf A x w =
      mat4CCommCLM (A x (fun _ => w 0)) (A x (fun _ => w 1)) := by
  dsimp [halfWedgeSelf]
  rw [wedgeCommAt_apply, Fin.sum_univ_two]
  have hr0 : (0 : Fin 2).removeNth w = fun _ => w 1 := by
    funext i
    fin_cases i
    rfl
  have hr1 : (1 : Fin 2).removeNth w = fun _ => w 0 := by
    funext i
    fin_cases i
    rfl
  rw [hr0, hr1]
  ext i j
  simp [mat4CCommCLM_apply]
  ring

theorem ymCurvature_apply_two (A : Mat4CForm 1) (hA : Differentiable ℝ A)
    (x : FourSpace) (u w : FourSpace) :
    ymCurvature A x ![u, w] =
      (fderiv ℝ (fun y => A y (fun _ => w)) x u -
        fderiv ℝ (fun y => A y (fun _ => u)) x w) +
      (A x (fun _ => u) * A x (fun _ => w) - A x (fun _ => w) * A x (fun _ => u)) := by
  dsimp [ymCurvature]
  rw [extD_apply (hA x), Fin.sum_univ_two, halfWedgeSelf_apply]
  have hr0 : (0 : Fin 2).removeNth ![u, w] = fun _ => w := by
    funext i
    fin_cases i
    rfl
  have hr1 : (1 : Fin 2).removeNth ![u, w] = fun _ => u := by
    funext i
    fin_cases i
    rfl
  rw [hr0, hr1]
  simp [mat4CCommCLM_apply, sub_eq_add_neg]

theorem covExtDeriv_neg {k : ℕ} (A : Mat4CForm 1) (η : Mat4CForm k) :
    covExtDeriv A (-η) = -covExtDeriv A η := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  have hd : extD (-η) x = -extD η x := by
    have hneg : (-η : Mat4CForm k) = (-1 : ℝ) • η := by
      funext y
      simp
    rw [hneg, extD_smul]
    simp
  simp only [covExtDeriv, wedgeComm, Pi.neg_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.neg_apply, hd, map_neg]
  abel

private lemma differentiable_extD_of_contDiff {k : ℕ} {η : Mat4CForm k}
    (hη : ContDiff ℝ 2 η) : Differentiable ℝ (extD η) := by
  have h1 : Differentiable ℝ (fderiv ℝ η) :=
    (hη.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : extD η =
      fun x => (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ FourSpace Mat4C
        (fderiv ℝ η x) : FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) :=
    rfl
  rw [h2]
  let clm : (FourSpace →L[ℝ] (FourSpace [⋀^Fin k]→L[ℝ] Mat4C)) →L[ℝ]
      (FourSpace [⋀^Fin (k + 1)]→L[ℝ] Mat4C) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ FourSpace Mat4C
  exact clm.differentiable.comp h1

private lemma differentiable_halfWedgeSelf {A : Mat4CForm 1} (hA : Differentiable ℝ A) :
    Differentiable ℝ (halfWedgeSelf A) := by
  intro x
  have hbil := (wedgeCommAt 1).hasFDerivAt_of_bilinear (hA x).hasFDerivAt (hA x).hasFDerivAt
  exact (hbil.const_smul (1 / 2 : ℝ)).differentiableAt

private lemma fderiv_mat4CComm_bilinear_apply {f g : FourSpace → Mat4C} {x u : FourSpace}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => mat4CCommCLM (f y) (g y)) x u =
      mat4CCommCLM (f x) (fderiv ℝ g x u) + mat4CCommCLM (fderiv ℝ f x u) (g x) := by
  exact congrArg (fun L : FourSpace →L[ℝ] Mat4C => L u) (mat4CCommCLM.fderiv_of_bilinear hf hg)

private lemma fderiv_halfWedgeSelf_eval {A : Mat4CForm 1} (hA : Differentiable ℝ A)
    (x u : FourSpace) (w : Fin 2 → FourSpace) :
    fderiv ℝ (fun y => halfWedgeSelf A y w) x u =
      mat4CCommCLM (A x (fun _ => w 0)) ((fderiv ℝ A x u) (fun _ => w 1)) +
      mat4CCommCLM ((fderiv ℝ A x u) (fun _ => w 0)) (A x (fun _ => w 1)) := by
  have hfun : (fun y => halfWedgeSelf A y w) =
      fun y => mat4CCommCLM (A y (fun _ => w 0)) (A y (fun _ => w 1)) := by
    funext y
    exact halfWedgeSelf_apply A y w
  rw [hfun]
  have hf0 : DifferentiableAt ℝ (fun y => A y (fun _ => w 0)) x :=
    (hA x).continuousAlternatingMap_apply_const (fun _ => w 0)
  have hf1 : DifferentiableAt ℝ (fun y => A y (fun _ => w 1)) x :=
    (hA x).continuousAlternatingMap_apply_const (fun _ => w 1)
  rw [fderiv_mat4CComm_bilinear_apply hf0 hf1,
    fderiv_mat4CForm_apply_const (hA x), fderiv_mat4CForm_apply_const (hA x)]

private lemma removeNth_three_zero (v : Fin 3 → FourSpace) :
    (0 : Fin 3).removeNth v = ![v 1, v 2] := by
  funext i
  fin_cases i <;> rfl

private lemma removeNth_three_one (v : Fin 3 → FourSpace) :
    (1 : Fin 3).removeNth v = ![v 0, v 2] := by
  funext i
  fin_cases i <;> rfl

private lemma removeNth_three_two (v : Fin 3 → FourSpace) :
    (2 : Fin 3).removeNth v = ![v 0, v 1] := by
  funext i
  fin_cases i <;> rfl

private lemma removeNth_two_zero (u w : FourSpace) :
    (0 : Fin 2).removeNth ![u, w] = fun _ => w := by
  funext i
  fin_cases i
  rfl

private lemma removeNth_two_one (u w : FourSpace) :
    (1 : Fin 2).removeNth ![u, w] = fun _ => u := by
  funext i
  fin_cases i
  rfl

private lemma extDeriv_halfWedgeSelf_add_wedgeComm_extDeriv
    {A : Mat4CForm 1} (hA : Differentiable ℝ A) (x : FourSpace) (v : Fin 3 → FourSpace) :
    extD (halfWedgeSelf A) x v + wedgeComm A (extD A) x v = 0 := by
  have hHd := differentiable_halfWedgeSelf hA
  rw [extD_apply (hHd x) v, Fin.sum_univ_three]
  dsimp [wedgeComm]
  rw [wedgeCommAt_apply, Fin.sum_univ_three]
  rw [removeNth_three_zero, removeNth_three_one, removeNth_three_two]
  have hf0 : fderiv ℝ (fun y => halfWedgeSelf A y ![v 1, v 2]) x (v 0) =
      mat4CCommCLM (A x (fun _ => v 1)) ((fderiv ℝ A x (v 0)) (fun _ => v 2)) +
      mat4CCommCLM ((fderiv ℝ A x (v 0)) (fun _ => v 1)) (A x (fun _ => v 2)) :=
    fderiv_halfWedgeSelf_eval hA x (v 0) ![v 1, v 2]
  have hf1 : fderiv ℝ (fun y => halfWedgeSelf A y ![v 0, v 2]) x (v 1) =
      mat4CCommCLM (A x (fun _ => v 0)) ((fderiv ℝ A x (v 1)) (fun _ => v 2)) +
      mat4CCommCLM ((fderiv ℝ A x (v 1)) (fun _ => v 0)) (A x (fun _ => v 2)) :=
    fderiv_halfWedgeSelf_eval hA x (v 1) ![v 0, v 2]
  have hf2 : fderiv ℝ (fun y => halfWedgeSelf A y ![v 0, v 1]) x (v 2) =
      mat4CCommCLM (A x (fun _ => v 0)) ((fderiv ℝ A x (v 2)) (fun _ => v 1)) +
      mat4CCommCLM ((fderiv ℝ A x (v 2)) (fun _ => v 0)) (A x (fun _ => v 1)) :=
    fderiv_halfWedgeSelf_eval hA x (v 2) ![v 0, v 1]
  have he12 : extD A x ![v 1, v 2] =
      (fderiv ℝ A x (v 1)) (fun _ => v 2) - (fderiv ℝ A x (v 2)) (fun _ => v 1) := by
    rw [extD_apply (hA x), Fin.sum_univ_two, removeNth_two_zero, removeNth_two_one]
    simp [fderiv_mat4CForm_apply_const (hA x), sub_eq_add_neg]
  have he02 : extD A x ![v 0, v 2] =
      (fderiv ℝ A x (v 0)) (fun _ => v 2) - (fderiv ℝ A x (v 2)) (fun _ => v 0) := by
    rw [extD_apply (hA x), Fin.sum_univ_two, removeNth_two_zero, removeNth_two_one]
    simp [fderiv_mat4CForm_apply_const (hA x), sub_eq_add_neg]
  have he01 : extD A x ![v 0, v 1] =
      (fderiv ℝ A x (v 0)) (fun _ => v 1) - (fderiv ℝ A x (v 1)) (fun _ => v 0) := by
    rw [extD_apply (hA x), Fin.sum_univ_two, removeNth_two_zero, removeNth_two_one]
    simp [fderiv_mat4CForm_apply_const (hA x), sub_eq_add_neg]
  rw [hf0, hf1, hf2, he12, he02, he01]
  simp [mat4CCommCLM_apply]
  noncomm_ring

private lemma wedgeComm_halfWedgeSelf_eq_zero
    (A : Mat4CForm 1) (x : FourSpace) (v : Fin 3 → FourSpace) :
    wedgeComm A (halfWedgeSelf A) x v = 0 := by
  dsimp [wedgeComm]
  rw [wedgeCommAt_apply, Fin.sum_univ_three]
  rw [removeNth_three_zero, removeNth_three_one, removeNth_three_two]
  rw [halfWedgeSelf_apply, halfWedgeSelf_apply, halfWedgeSelf_apply]
  simp [mat4CCommCLM_apply]
  noncomm_ring

/-- Differential Bianchi identity `d_A F = dF + [A ∧ F] = 0` for any `C²` gauge 1-form `A`. -/
theorem bianchi_identity_ymCurvature {A : Mat4CForm 1} (hA : ContDiff ℝ 2 A) :
    covExtDeriv A (ymCurvature A) = 0 := by
  have hAd : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hEd : Differentiable ℝ (extD A) := differentiable_extD_of_contDiff hA
  have hHd : Differentiable ℝ (halfWedgeSelf A) := differentiable_halfWedgeSelf hAd
  have hdd : extD (extD A) = 0 := extD_extD hA
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  dsimp [covExtDeriv, ymCurvature, wedgeComm]
  have hsum :
      extD (fun y => extD A y + halfWedgeSelf A y) x =
        extD (extD A) x + extD (halfWedgeSelf A) x :=
    extD_add (hEd x) (hHd x)
  change extD (fun y => extD A y + halfWedgeSelf A y) x v +
      wedgeCommAt 2 (A x) (extD A x + halfWedgeSelf A x) v = 0
  rw [hsum, hdd]
  simp only [Pi.zero_apply, zero_add, map_add, ContinuousAlternatingMap.add_apply]
  have hleib := extDeriv_halfWedgeSelf_add_wedgeComm_extDeriv hAd x v
  have hjac := wedgeComm_halfWedgeSelf_eq_zero A x v
  change extD (halfWedgeSelf A) x v +
      (wedgeComm A (extD A) x v + wedgeComm A (halfWedgeSelf A) x v) = 0
  rw [hjac, add_zero]
  exact hleib

/-! ## 3. Explicit 4D Hodge Stars, Yang–Mills PDE & Self-Duality -/

private def plucker2 (v : Fin 2 → FourSpace) (μ ν : Fin 4) : ℝ :=
  v 0 μ * v 1 ν - v 0 ν * v 1 μ

private lemma plucker2_self (w : FourSpace) (μ ν : Fin 4) :
    plucker2 (fun _ => w) μ ν = 0 := by
  simp [plucker2]
  ring

private lemma plucker2_diag (v : Fin 2 → FourSpace) (μ : Fin 4) :
    plucker2 v μ μ = 0 := by
  simp [plucker2, sub_self]

private lemma plucker2_skew (v : Fin 2 → FourSpace) (μ ν : Fin 4) :
    plucker2 v ν μ = -plucker2 v μ ν := by
  simp [plucker2]

private lemma plucker2_add_zero (u₁ u₂ w : FourSpace) (μ ν : Fin 4) :
    plucker2 ![u₁ + u₂, w] μ ν = plucker2 ![u₁, w] μ ν + plucker2 ![u₂, w] μ ν := by
  simp [plucker2]
  ring

private lemma plucker2_add_one (u w₁ w₂ : FourSpace) (μ ν : Fin 4) :
    plucker2 ![u, w₁ + w₂] μ ν = plucker2 ![u, w₁] μ ν + plucker2 ![u, w₂] μ ν := by
  simp [plucker2]
  ring

private lemma plucker2_smul_zero (c : ℝ) (u w : FourSpace) (μ ν : Fin 4) :
    plucker2 ![c • u, w] μ ν = c * plucker2 ![u, w] μ ν := by
  simp [plucker2]
  ring

private lemma plucker2_smul_one (c : ℝ) (u w : FourSpace) (μ ν : Fin 4) :
    plucker2 ![u, c • w] μ ν = c * plucker2 ![u, w] μ ν := by
  simp [plucker2]
  ring

private lemma norm_plucker2_le (v : Fin 2 → FourSpace) (μ ν : Fin 4) :
    |plucker2 v μ ν| ≤ 2 * ∏ i : Fin 2, ‖v i‖ := by
  have h0 : |v 0 μ| ≤ ‖v 0‖ := PiLp.norm_apply_le (v 0) μ
  have h1 : |v 1 ν| ≤ ‖v 1‖ := PiLp.norm_apply_le (v 1) ν
  have h2 : |v 0 ν| ≤ ‖v 0‖ := PiLp.norm_apply_le (v 0) ν
  have h3 : |v 1 μ| ≤ ‖v 1‖ := PiLp.norm_apply_le (v 1) μ
  calc
    |v 0 μ * v 1 ν - v 0 ν * v 1 μ|
        ≤ |v 0 μ * v 1 ν| + |v 0 ν * v 1 μ| := abs_sub _ _
    _ = |v 0 μ| * |v 1 ν| + |v 0 ν| * |v 1 μ| := by rw [abs_mul, abs_mul]
    _ ≤ ‖v 0‖ * ‖v 1‖ + ‖v 0‖ * ‖v 1‖ := by gcongr
    _ = 2 * ∏ i : Fin 2, ‖v i‖ := by
      rw [Fin.prod_univ_two]
      ring

private lemma frameBasis_apply (γ δ : Fin 4) :
    frameBasis γ δ = if δ = γ then 1 else 0 := by
  rw [frameBasis, EuclideanSpace.basisFun_apply]
  simp [EuclideanSpace.single, eq_comm]

private lemma fourSpace_basis_expansion (x : FourSpace) :
    x = ∑ μ : Fin 4, x μ • frameBasis μ := by
  apply PiLp.ext
  intro j
  simp [frameBasis_apply, Fin.sum_univ_four]
  fin_cases j <;> simp

private lemma norm_frameBasis (μ : Fin 4) : ‖frameBasis μ‖ = 1 := by
  simp [frameBasis]

private lemma norm_eval_basis_le (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) (α β : Fin 4) :
    ‖η ![frameBasis α, frameBasis β]‖ ≤ ‖η‖ := by
  have h : ‖η ![frameBasis α, frameBasis β]‖ ≤
      ‖η‖ * ∏ i : Fin 2, ‖![frameBasis α, frameBasis β] i‖ :=
    η.le_opNorm ![frameBasis α, frameBasis β]
  simpa [Fin.prod_univ_two, norm_frameBasis] using h

private lemma plucker2_update_add [DecidableEq (Fin 2)]
    (m : Fin 2 → FourSpace) (i : Fin 2) (x y : FourSpace) (μ ν : Fin 4) :
    plucker2 (Function.update m i (x + y)) μ ν =
      plucker2 (Function.update m i x) μ ν + plucker2 (Function.update m i y) μ ν := by
  fin_cases i <;> simp [plucker2, Function.update] <;> ring

private lemma plucker2_update_smul [DecidableEq (Fin 2)]
    (m : Fin 2 → FourSpace) (i : Fin 2) (c : ℝ) (x : FourSpace) (μ ν : Fin 4) :
    plucker2 (Function.update m i (c • x)) μ ν =
      c * plucker2 (Function.update m i x) μ ν := by
  fin_cases i <;> simp [plucker2, Function.update] <;> ring

private lemma plucker2_eq_zero_of_eq (m : Fin 2 → FourSpace) {i j : Fin 2}
    (hm : m i = m j) (hij : i ≠ j) (μ ν : Fin 4) :
    plucker2 m μ ν = 0 := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · dsimp at hm
    simp [plucker2, hm]
    ring
  · dsimp at hm
    simp [plucker2, hm]
    ring
  · exact False.elim (hij rfl)

/-- Basis expansion of any `Mat4C`-valued 2-form in the 6 ordered Plücker 2-minors. -/
theorem alternating_fourSpace_eq_plucker (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C)
    (v : Fin 2 → FourSpace) :
    η v =
      plucker2 v 0 1 • η ![frameBasis 0, frameBasis 1] +
      plucker2 v 2 3 • η ![frameBasis 2, frameBasis 3] +
      plucker2 v 0 2 • η ![frameBasis 0, frameBasis 2] +
      plucker2 v 3 1 • η ![frameBasis 3, frameBasis 1] +
      plucker2 v 0 3 • η ![frameBasis 0, frameBasis 3] +
      plucker2 v 1 2 • η ![frameBasis 1, frameBasis 2] := by
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  have hu := fourSpace_basis_expansion (v 0)
  have hw := fourSpace_basis_expansion (v 1)
  have hexp :
      η ![∑ μ : Fin 4, v 0 μ • frameBasis μ, ∑ ν : Fin 4, v 1 ν • frameBasis ν] =
        ∑ μ : Fin 4, ∑ ν : Fin 4,
          (v 0 μ * v 1 ν) • η ![frameBasis μ, frameBasis ν] := by
    have hleft :
        ∀ w : FourSpace,
          η ![∑ μ : Fin 4, v 0 μ • frameBasis μ, w] =
            ∑ μ : Fin 4, v 0 μ • η ![frameBasis μ, w] := by
      intro w
      have hupd :
          ![∑ μ : Fin 4, v 0 μ • frameBasis μ, w] =
            Function.update ![0, w] 0 (∑ μ : Fin 4, v 0 μ • frameBasis μ) := by
        funext i
        fin_cases i <;> rfl
      rw [hupd, ← ContinuousAlternatingMap.toContinuousLinearMap_apply, map_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [map_smul, ContinuousAlternatingMap.toContinuousLinearMap_apply]
      congr 2
      funext i
      fin_cases i <;> rfl
    have hright :
        ∀ μ : Fin 4,
          η ![frameBasis μ, ∑ ν : Fin 4, v 1 ν • frameBasis ν] =
            ∑ ν : Fin 4, v 1 ν • η ![frameBasis μ, frameBasis ν] := by
      intro μ
      have hupd :
          ![frameBasis μ, ∑ ν : Fin 4, v 1 ν • frameBasis ν] =
            Function.update ![frameBasis μ, 0] 1 (∑ ν : Fin 4, v 1 ν • frameBasis ν) := by
        funext i
        fin_cases i <;> rfl
      rw [hupd, ← ContinuousAlternatingMap.toContinuousLinearMap_apply, map_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [map_smul, ContinuousAlternatingMap.toContinuousLinearMap_apply]
      congr 2
      funext i
      fin_cases i <;> rfl
    rw [hleft]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hright, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_smul]
  conv_lhs => rw [hu, hw, hexp]
  have hdiag : ∀ α : Fin 4, η ![frameBasis α, frameBasis α] = 0 := fun α =>
    η.map_eq_zero_of_eq ![frameBasis α, frameBasis α] (i := 0) (j := 1) rfl (by decide)
  have hskew : ∀ α β : Fin 4,
      η ![frameBasis β, frameBasis α] = -η ![frameBasis α, frameBasis β] := by
    intro α β
    have hs := η.map_swap ![frameBasis α, frameBasis β] (by decide : (0 : Fin 2) ≠ 1)
    have hswap :
        ![frameBasis α, frameBasis β] ∘ Equiv.swap 0 1 = ![frameBasis β, frameBasis α] := by
      funext i
      fin_cases i <;> rfl
    rw [hswap] at hs
    exact hs
  simp only [Fin.sum_univ_four, hdiag, smul_zero, add_zero, zero_add]
  rw [hskew 0 1, hskew 0 2, hskew 0 3, hskew 1 2, hskew 1 3, hskew 2 3]
  simp only [plucker2, Matrix.cons_val_zero, Matrix.cons_val_one]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Complex.real_smul]
  push_cast
  ring

private def hodgeStar4EuclAlt (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    FourSpace [⋀^Fin 2]→ₗ[ℝ] Mat4C where
  toFun v :=
    plucker2 v 0 1 • η ![frameBasis 2, frameBasis 3] +
    plucker2 v 2 3 • η ![frameBasis 0, frameBasis 1] +
    plucker2 v 0 2 • η ![frameBasis 3, frameBasis 1] +
    plucker2 v 3 1 • η ![frameBasis 0, frameBasis 2] +
    plucker2 v 0 3 • η ![frameBasis 1, frameBasis 2] +
    plucker2 v 1 2 • η ![frameBasis 0, frameBasis 3]
  map_update_add' m i x y := by
    ext a b
    simp only [plucker2_update_add, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring
  map_update_smul' m i c x := by
    ext a b
    simp only [plucker2_update_smul, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring
  map_eq_zero_of_eq' v i j hv hij := by
    simp only [plucker2_eq_zero_of_eq v hv hij, zero_smul, add_zero]

private def hodgeStar4EuclLM :
    (FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) →ₗ[ℝ] (FourSpace [⋀^Fin 2]→ₗ[ℝ] Mat4C) where
  toFun := hodgeStar4EuclAlt
  map_add' η₁ η₂ := by
    ext v a b
    simp only [hodgeStar4EuclAlt, AlternatingMap.coe_mk, MultilinearMap.coe_mk,
      AlternatingMap.add_apply, ContinuousAlternatingMap.add_apply, Matrix.add_apply,
      smul_add]
    ring
  map_smul' c η := by
    ext v a b
    simp only [hodgeStar4EuclAlt, AlternatingMap.coe_mk, MultilinearMap.coe_mk,
      AlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      RingHom.id_apply, smul_add, smul_comm c]

private lemma hodgeStar4EuclLM_bound (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C)
    (v : Fin 2 → FourSpace) :
    ‖hodgeStar4EuclLM η v‖ ≤ 12 * ‖η‖ * ∏ i : Fin 2, ‖v i‖ := by
  have hterm : ∀ (μ ν α β : Fin 4),
      ‖plucker2 v μ ν • η ![frameBasis α, frameBasis β]‖ ≤
        2 * ‖η‖ * ∏ i : Fin 2, ‖v i‖ := by
    intro μ ν α β
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |plucker2 v μ ν| * ‖η ![frameBasis α, frameBasis β]‖
          ≤ (2 * ∏ i : Fin 2, ‖v i‖) * ‖η‖ :=
            mul_le_mul (norm_plucker2_le v μ ν) (norm_eval_basis_le η α β)
              (norm_nonneg _) (by positivity)
      _ = 2 * ‖η‖ * ∏ i : Fin 2, ‖v i‖ := by ring
  dsimp [hodgeStar4EuclLM, hodgeStar4EuclAlt]
  have h01 := hterm 0 1 2 3
  have h23 := hterm 2 3 0 1
  have h02 := hterm 0 2 3 1
  have h31 := hterm 3 1 0 2
  have h03 := hterm 0 3 1 2
  have h12 := hterm 1 2 0 3
  calc
    ‖plucker2 v 0 1 • η ![frameBasis 2, frameBasis 3] +
        plucker2 v 2 3 • η ![frameBasis 0, frameBasis 1] +
        plucker2 v 0 2 • η ![frameBasis 3, frameBasis 1] +
        plucker2 v 3 1 • η ![frameBasis 0, frameBasis 2] +
        plucker2 v 0 3 • η ![frameBasis 1, frameBasis 2] +
        plucker2 v 1 2 • η ![frameBasis 0, frameBasis 3]‖
        ≤ ‖plucker2 v 0 1 • η ![frameBasis 2, frameBasis 3] +
            plucker2 v 2 3 • η ![frameBasis 0, frameBasis 1] +
            plucker2 v 0 2 • η ![frameBasis 3, frameBasis 1] +
            plucker2 v 3 1 • η ![frameBasis 0, frameBasis 2] +
            plucker2 v 0 3 • η ![frameBasis 1, frameBasis 2]‖ +
          ‖plucker2 v 1 2 • η ![frameBasis 0, frameBasis 3]‖ := norm_add_le _ _
    _ ≤ ‖plucker2 v 0 1 • η ![frameBasis 2, frameBasis 3] +
            plucker2 v 2 3 • η ![frameBasis 0, frameBasis 1] +
            plucker2 v 0 2 • η ![frameBasis 3, frameBasis 1] +
            plucker2 v 3 1 • η ![frameBasis 0, frameBasis 2]‖ +
          ‖plucker2 v 0 3 • η ![frameBasis 1, frameBasis 2]‖ +
          ‖plucker2 v 1 2 • η ![frameBasis 0, frameBasis 3]‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖plucker2 v 0 1 • η ![frameBasis 2, frameBasis 3] +
            plucker2 v 2 3 • η ![frameBasis 0, frameBasis 1] +
            plucker2 v 0 2 • η ![frameBasis 3, frameBasis 1]‖ +
          ‖plucker2 v 3 1 • η ![frameBasis 0, frameBasis 2]‖ +
          ‖plucker2 v 0 3 • η ![frameBasis 1, frameBasis 2]‖ +
          ‖plucker2 v 1 2 • η ![frameBasis 0, frameBasis 3]‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖plucker2 v 0 1 • η ![frameBasis 2, frameBasis 3] +
            plucker2 v 2 3 • η ![frameBasis 0, frameBasis 1]‖ +
          ‖plucker2 v 0 2 • η ![frameBasis 3, frameBasis 1]‖ +
          ‖plucker2 v 3 1 • η ![frameBasis 0, frameBasis 2]‖ +
          ‖plucker2 v 0 3 • η ![frameBasis 1, frameBasis 2]‖ +
          ‖plucker2 v 1 2 • η ![frameBasis 0, frameBasis 3]‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖plucker2 v 0 1 • η ![frameBasis 2, frameBasis 3]‖ +
          ‖plucker2 v 2 3 • η ![frameBasis 0, frameBasis 1]‖ +
          ‖plucker2 v 0 2 • η ![frameBasis 3, frameBasis 1]‖ +
          ‖plucker2 v 3 1 • η ![frameBasis 0, frameBasis 2]‖ +
          ‖plucker2 v 0 3 • η ![frameBasis 1, frameBasis 2]‖ +
          ‖plucker2 v 1 2 • η ![frameBasis 0, frameBasis 3]‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 12 * ‖η‖ * ∏ i : Fin 2, ‖v i‖ := by linarith

/-- Fiberwise Euclidean 4D Hodge star `⋆_E : Ω²(ℝ⁴, Mat4C) →L[ℝ] Ω²(ℝ⁴, Mat4C)`. -/
def hodgeStar4EuclMap :
    (FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) →L[ℝ] (FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :=
  AlternatingMap.mkContinuousLinear hodgeStar4EuclLM 12 hodgeStar4EuclLM_bound

/-- Euclidean 4D Hodge star on smooth `Mat4C`-valued 2-forms. -/
def hodgeStar4Eucl (η : Mat4CForm 2) : Mat4CForm 2 :=
  fun x => hodgeStar4EuclMap (η x)

private lemma plucker2_basis (α β μ ν : Fin 4) :
    plucker2 ![frameBasis α, frameBasis β] μ ν =
      (if α = μ ∧ β = ν then 1 else 0) - (if α = ν ∧ β = μ then 1 else 0) := by
  fin_cases α <;> fin_cases β <;> fin_cases μ <;> fin_cases ν <;>
    simp [plucker2, frameBasis_apply]

@[simp]
theorem hodgeStar4EuclMap_basis_01 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap η ![frameBasis 0, frameBasis 1] = η ![frameBasis 2, frameBasis 3] := by
  change hodgeStar4EuclAlt η ![frameBasis 0, frameBasis 1] = _
  simp [hodgeStar4EuclAlt, plucker2_basis]

@[simp]
theorem hodgeStar4EuclMap_basis_23 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap η ![frameBasis 2, frameBasis 3] = η ![frameBasis 0, frameBasis 1] := by
  change hodgeStar4EuclAlt η ![frameBasis 2, frameBasis 3] = _
  simp [hodgeStar4EuclAlt, plucker2_basis]

@[simp]
theorem hodgeStar4EuclMap_basis_02 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap η ![frameBasis 0, frameBasis 2] = η ![frameBasis 3, frameBasis 1] := by
  change hodgeStar4EuclAlt η ![frameBasis 0, frameBasis 2] = _
  simp [hodgeStar4EuclAlt, plucker2_basis]

@[simp]
theorem hodgeStar4EuclMap_basis_31 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap η ![frameBasis 3, frameBasis 1] = η ![frameBasis 0, frameBasis 2] := by
  change hodgeStar4EuclAlt η ![frameBasis 3, frameBasis 1] = _
  simp [hodgeStar4EuclAlt, plucker2_basis]

@[simp]
theorem hodgeStar4EuclMap_basis_03 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap η ![frameBasis 0, frameBasis 3] = η ![frameBasis 1, frameBasis 2] := by
  change hodgeStar4EuclAlt η ![frameBasis 0, frameBasis 3] = _
  simp [hodgeStar4EuclAlt, plucker2_basis]

@[simp]
theorem hodgeStar4EuclMap_basis_12 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap η ![frameBasis 1, frameBasis 2] = η ![frameBasis 0, frameBasis 3] := by
  change hodgeStar4EuclAlt η ![frameBasis 1, frameBasis 2] = _
  simp [hodgeStar4EuclAlt, plucker2_basis]

theorem hodgeStar4EuclMap_involutive (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap (hodgeStar4EuclMap η) = η := by
  apply ContinuousAlternatingMap.ext
  intro v
  change hodgeStar4EuclAlt (hodgeStar4EuclMap η) v = η v
  dsimp [hodgeStar4EuclAlt]
  rw [hodgeStar4EuclMap_basis_23, hodgeStar4EuclMap_basis_01, hodgeStar4EuclMap_basis_31,
    hodgeStar4EuclMap_basis_02, hodgeStar4EuclMap_basis_12, hodgeStar4EuclMap_basis_03]
  exact (alternating_fourSpace_eq_plucker η v).symm

theorem hodgeStar4Eucl_involutive (η : Mat4CForm 2) :
    hodgeStar4Eucl (hodgeStar4Eucl η) = η := by
  funext x
  exact hodgeStar4EuclMap_involutive (η x)

theorem hodgeStar4Eucl_contDiff {r : WithTop ℕ∞} {η : Mat4CForm 2}
    (hη : ContDiff ℝ r η) : ContDiff ℝ r (hodgeStar4Eucl η) :=
  hodgeStar4EuclMap.contDiff.comp hη

theorem hodgeStar4Eucl_eq_self_iff (η : Mat4CForm 2) :
    hodgeStar4Eucl η = η ↔
      ∀ x,
        η x ![frameBasis 0, frameBasis 1] = η x ![frameBasis 2, frameBasis 3] ∧
        η x ![frameBasis 0, frameBasis 2] = η x ![frameBasis 3, frameBasis 1] ∧
        η x ![frameBasis 0, frameBasis 3] = η x ![frameBasis 1, frameBasis 2] := by
  constructor
  · intro h x
    have hx := congrFun h x
    refine ⟨?_, ?_, ?_⟩
    · simpa [hodgeStar4Eucl] using congrArg (fun f => f ![frameBasis 2, frameBasis 3]) hx
    · simpa [hodgeStar4Eucl] using congrArg (fun f => f ![frameBasis 3, frameBasis 1]) hx
    · simpa [hodgeStar4Eucl] using congrArg (fun f => f ![frameBasis 1, frameBasis 2]) hx
  · intro h
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    rcases h x with ⟨h01, h02, h03⟩
    change hodgeStar4EuclAlt (η x) v = η x v
    dsimp [hodgeStar4EuclAlt]
    rw [← h01, ← h02, ← h03]
    rw [alternating_fourSpace_eq_plucker (η x) v, ← h01, ← h02, ← h03]

private def minkowskiSign2 (μ ν : Fin 4) : ℝ :=
  minkowskiEta4 μ μ * minkowskiEta4 ν ν

private lemma minkowskiSign2_abs_one (μ ν : Fin 4) : |minkowskiSign2 μ ν| = 1 := by
  fin_cases μ <;> fin_cases ν <;>
    simp [minkowskiSign2, minkowskiEta4, Matrix.diagonal]

private def hodgeStar4MinkowskiAlt (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    FourSpace [⋀^Fin 2]→ₗ[ℝ] Mat4C where
  toFun v :=
    (minkowskiSign2 0 1 * plucker2 v 0 1) • η ![frameBasis 2, frameBasis 3] +
    (minkowskiSign2 2 3 * plucker2 v 2 3) • η ![frameBasis 0, frameBasis 1] +
    (minkowskiSign2 0 2 * plucker2 v 0 2) • η ![frameBasis 3, frameBasis 1] +
    (minkowskiSign2 3 1 * plucker2 v 3 1) • η ![frameBasis 0, frameBasis 2] +
    (minkowskiSign2 0 3 * plucker2 v 0 3) • η ![frameBasis 1, frameBasis 2] +
    (minkowskiSign2 1 2 * plucker2 v 1 2) • η ![frameBasis 0, frameBasis 3]
  map_update_add' m i x y := by
    ext a b
    simp only [plucker2_update_add, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring
  map_update_smul' m i c x := by
    ext a b
    simp only [plucker2_update_smul, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring
  map_eq_zero_of_eq' v i j hv hij := by
    simp only [plucker2_eq_zero_of_eq v hv hij, mul_zero, zero_smul, add_zero]

private def hodgeStar4MinkowskiLM :
    (FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) →ₗ[ℝ] (FourSpace [⋀^Fin 2]→ₗ[ℝ] Mat4C) where
  toFun := hodgeStar4MinkowskiAlt
  map_add' η₁ η₂ := by
    ext v a b
    simp only [hodgeStar4MinkowskiAlt, AlternatingMap.coe_mk, MultilinearMap.coe_mk,
      AlternatingMap.add_apply, ContinuousAlternatingMap.add_apply, Matrix.add_apply, smul_add]
    ring
  map_smul' c η := by
    ext v a b
    simp only [hodgeStar4MinkowskiAlt, AlternatingMap.coe_mk, MultilinearMap.coe_mk,
      AlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      RingHom.id_apply, smul_add, smul_comm c]

private lemma hodgeStar4MinkowskiLM_bound (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C)
    (v : Fin 2 → FourSpace) :
    ‖hodgeStar4MinkowskiLM η v‖ ≤ 12 * ‖η‖ * ∏ i : Fin 2, ‖v i‖ := by
  have hterm : ∀ (μ ν α β : Fin 4),
      ‖(minkowskiSign2 μ ν * plucker2 v μ ν) • η ![frameBasis α, frameBasis β]‖ ≤
        2 * ‖η‖ * ∏ i : Fin 2, ‖v i‖ := by
    intro μ ν α β
    rw [norm_smul, Real.norm_eq_abs, abs_mul, minkowskiSign2_abs_one, one_mul]
    calc
      |plucker2 v μ ν| * ‖η ![frameBasis α, frameBasis β]‖
          ≤ (2 * ∏ i : Fin 2, ‖v i‖) * ‖η‖ :=
            mul_le_mul (norm_plucker2_le v μ ν) (norm_eval_basis_le η α β)
              (norm_nonneg _) (by positivity)
      _ = 2 * ‖η‖ * ∏ i : Fin 2, ‖v i‖ := by ring
  dsimp [hodgeStar4MinkowskiLM, hodgeStar4MinkowskiAlt]
  have h01 := hterm 0 1 2 3
  have h23 := hterm 2 3 0 1
  have h02 := hterm 0 2 3 1
  have h31 := hterm 3 1 0 2
  have h03 := hterm 0 3 1 2
  have h12 := hterm 1 2 0 3
  calc
    ‖(minkowskiSign2 0 1 * plucker2 v 0 1) • η ![frameBasis 2, frameBasis 3] +
        (minkowskiSign2 2 3 * plucker2 v 2 3) • η ![frameBasis 0, frameBasis 1] +
        (minkowskiSign2 0 2 * plucker2 v 0 2) • η ![frameBasis 3, frameBasis 1] +
        (minkowskiSign2 3 1 * plucker2 v 3 1) • η ![frameBasis 0, frameBasis 2] +
        (minkowskiSign2 0 3 * plucker2 v 0 3) • η ![frameBasis 1, frameBasis 2] +
        (minkowskiSign2 1 2 * plucker2 v 1 2) • η ![frameBasis 0, frameBasis 3]‖
        ≤ ‖(minkowskiSign2 0 1 * plucker2 v 0 1) • η ![frameBasis 2, frameBasis 3] +
            (minkowskiSign2 2 3 * plucker2 v 2 3) • η ![frameBasis 0, frameBasis 1] +
            (minkowskiSign2 0 2 * plucker2 v 0 2) • η ![frameBasis 3, frameBasis 1] +
            (minkowskiSign2 3 1 * plucker2 v 3 1) • η ![frameBasis 0, frameBasis 2] +
            (minkowskiSign2 0 3 * plucker2 v 0 3) • η ![frameBasis 1, frameBasis 2]‖ +
          ‖(minkowskiSign2 1 2 * plucker2 v 1 2) • η ![frameBasis 0, frameBasis 3]‖ :=
        norm_add_le _ _
    _ ≤ ‖(minkowskiSign2 0 1 * plucker2 v 0 1) • η ![frameBasis 2, frameBasis 3] +
            (minkowskiSign2 2 3 * plucker2 v 2 3) • η ![frameBasis 0, frameBasis 1] +
            (minkowskiSign2 0 2 * plucker2 v 0 2) • η ![frameBasis 3, frameBasis 1] +
            (minkowskiSign2 3 1 * plucker2 v 3 1) • η ![frameBasis 0, frameBasis 2]‖ +
          ‖(minkowskiSign2 0 3 * plucker2 v 0 3) • η ![frameBasis 1, frameBasis 2]‖ +
          ‖(minkowskiSign2 1 2 * plucker2 v 1 2) • η ![frameBasis 0, frameBasis 3]‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖(minkowskiSign2 0 1 * plucker2 v 0 1) • η ![frameBasis 2, frameBasis 3] +
            (minkowskiSign2 2 3 * plucker2 v 2 3) • η ![frameBasis 0, frameBasis 1] +
            (minkowskiSign2 0 2 * plucker2 v 0 2) • η ![frameBasis 3, frameBasis 1]‖ +
          ‖(minkowskiSign2 3 1 * plucker2 v 3 1) • η ![frameBasis 0, frameBasis 2]‖ +
          ‖(minkowskiSign2 0 3 * plucker2 v 0 3) • η ![frameBasis 1, frameBasis 2]‖ +
          ‖(minkowskiSign2 1 2 * plucker2 v 1 2) • η ![frameBasis 0, frameBasis 3]‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖(minkowskiSign2 0 1 * plucker2 v 0 1) • η ![frameBasis 2, frameBasis 3] +
            (minkowskiSign2 2 3 * plucker2 v 2 3) • η ![frameBasis 0, frameBasis 1]‖ +
          ‖(minkowskiSign2 0 2 * plucker2 v 0 2) • η ![frameBasis 3, frameBasis 1]‖ +
          ‖(minkowskiSign2 3 1 * plucker2 v 3 1) • η ![frameBasis 0, frameBasis 2]‖ +
          ‖(minkowskiSign2 0 3 * plucker2 v 0 3) • η ![frameBasis 1, frameBasis 2]‖ +
          ‖(minkowskiSign2 1 2 * plucker2 v 1 2) • η ![frameBasis 0, frameBasis 3]‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖(minkowskiSign2 0 1 * plucker2 v 0 1) • η ![frameBasis 2, frameBasis 3]‖ +
          ‖(minkowskiSign2 2 3 * plucker2 v 2 3) • η ![frameBasis 0, frameBasis 1]‖ +
          ‖(minkowskiSign2 0 2 * plucker2 v 0 2) • η ![frameBasis 3, frameBasis 1]‖ +
          ‖(minkowskiSign2 3 1 * plucker2 v 3 1) • η ![frameBasis 0, frameBasis 2]‖ +
          ‖(minkowskiSign2 0 3 * plucker2 v 0 3) • η ![frameBasis 1, frameBasis 2]‖ +
          ‖(minkowskiSign2 1 2 * plucker2 v 1 2) • η ![frameBasis 0, frameBasis 3]‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 12 * ‖η‖ * ∏ i : Fin 2, ‖v i‖ := by linarith

/-- Fiberwise Minkowski 4D Hodge star `⋆_M` using `minkowskiEta4 = diag(1, -1, -1, -1)`. -/
def hodgeStar4MinkowskiMap :
    (FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) →L[ℝ] (FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :=
  AlternatingMap.mkContinuousLinear hodgeStar4MinkowskiLM 12 hodgeStar4MinkowskiLM_bound

/-- Minkowski 4D Hodge star on smooth `Mat4C`-valued 2-forms. -/
def hodgeStar4Minkowski (η : Mat4CForm 2) : Mat4CForm 2 :=
  fun x => hodgeStar4MinkowskiMap (η x)

@[simp]
theorem hodgeStar4MinkowskiMap_basis_01 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4MinkowskiMap η ![frameBasis 0, frameBasis 1] = -η ![frameBasis 2, frameBasis 3] := by
  change hodgeStar4MinkowskiAlt η ![frameBasis 0, frameBasis 1] = _
  simp [hodgeStar4MinkowskiAlt, plucker2_basis, minkowskiSign2, minkowskiEta4]

@[simp]
theorem hodgeStar4MinkowskiMap_basis_23 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4MinkowskiMap η ![frameBasis 2, frameBasis 3] = η ![frameBasis 0, frameBasis 1] := by
  change hodgeStar4MinkowskiAlt η ![frameBasis 2, frameBasis 3] = _
  simp [hodgeStar4MinkowskiAlt, plucker2_basis, minkowskiSign2, minkowskiEta4]

@[simp]
theorem hodgeStar4MinkowskiMap_basis_02 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4MinkowskiMap η ![frameBasis 0, frameBasis 2] = -η ![frameBasis 3, frameBasis 1] := by
  change hodgeStar4MinkowskiAlt η ![frameBasis 0, frameBasis 2] = _
  simp [hodgeStar4MinkowskiAlt, plucker2_basis, minkowskiSign2, minkowskiEta4]

@[simp]
theorem hodgeStar4MinkowskiMap_basis_31 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4MinkowskiMap η ![frameBasis 3, frameBasis 1] = η ![frameBasis 0, frameBasis 2] := by
  change hodgeStar4MinkowskiAlt η ![frameBasis 3, frameBasis 1] = _
  simp [hodgeStar4MinkowskiAlt, plucker2_basis, minkowskiSign2, minkowskiEta4]

@[simp]
theorem hodgeStar4MinkowskiMap_basis_03 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4MinkowskiMap η ![frameBasis 0, frameBasis 3] = -η ![frameBasis 1, frameBasis 2] := by
  change hodgeStar4MinkowskiAlt η ![frameBasis 0, frameBasis 3] = _
  simp [hodgeStar4MinkowskiAlt, plucker2_basis, minkowskiSign2, minkowskiEta4]

@[simp]
theorem hodgeStar4MinkowskiMap_basis_12 (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4MinkowskiMap η ![frameBasis 1, frameBasis 2] = η ![frameBasis 0, frameBasis 3] := by
  change hodgeStar4MinkowskiAlt η ![frameBasis 1, frameBasis 2] = _
  simp [hodgeStar4MinkowskiAlt, plucker2_basis, minkowskiSign2, minkowskiEta4]

theorem hodgeStar4MinkowskiMap_sq_neg (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4MinkowskiMap (hodgeStar4MinkowskiMap η) = -η := by
  apply ContinuousAlternatingMap.ext
  intro v
  change hodgeStar4MinkowskiAlt (hodgeStar4MinkowskiMap η) v = -(η v)
  dsimp [hodgeStar4MinkowskiAlt]
  rw [hodgeStar4MinkowskiMap_basis_23, hodgeStar4MinkowskiMap_basis_01,
    hodgeStar4MinkowskiMap_basis_31, hodgeStar4MinkowskiMap_basis_02,
    hodgeStar4MinkowskiMap_basis_12, hodgeStar4MinkowskiMap_basis_03]
  rw [alternating_fourSpace_eq_plucker η v]
  simp only [minkowskiSign2, minkowskiEta4, Matrix.diagonal_apply_eq]
  norm_num
  ext a b
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Complex.real_smul]
  ring

theorem hodgeStar4Minkowski_sq_neg (η : Mat4CForm 2) :
    hodgeStar4Minkowski (hodgeStar4Minkowski η) = -η := by
  funext x
  exact hodgeStar4MinkowskiMap_sq_neg (η x)

theorem hodgeStar4Minkowski_contDiff {r : WithTop ℕ∞} {η : Mat4CForm 2}
    (hη : ContDiff ℝ r η) : ContDiff ℝ r (hodgeStar4Minkowski η) :=
  hodgeStar4MinkowskiMap.contDiff.comp hη

/-- Euclidean Yang–Mills PDE `d_A (⋆_E F_A) = 0`. -/
def YangMillsPDE (A : Mat4CForm 1) : Prop :=
  covExtDeriv A (hodgeStar4Eucl (ymCurvature A)) = 0

/-- Minkowski Yang–Mills PDE `d_A (⋆_M F_A) = 0`. -/
def YangMillsPDEMinkowski (A : Mat4CForm 1) : Prop :=
  covExtDeriv A (hodgeStar4Minkowski (ymCurvature A)) = 0

/-- Euclidean self-duality predicate `⋆_E F_A = F_A`. -/
def IsSelfDualForm4 (A : Mat4CForm 1) : Prop :=
  hodgeStar4Eucl (ymCurvature A) = ymCurvature A

/-- Euclidean anti-self-duality predicate `⋆_E F_A = -F_A`. -/
def IsAntiSelfDualForm4 (A : Mat4CForm 1) : Prop :=
  hodgeStar4Eucl (ymCurvature A) = -(ymCurvature A)

theorem selfDual_solves_yangMillsPDE {A : Mat4CForm 1}
    (hA : ContDiff ℝ 2 A) (hSD : IsSelfDualForm4 A) : YangMillsPDE A := by
  unfold YangMillsPDE
  rw [hSD]
  exact bianchi_identity_ymCurvature hA

theorem antiSelfDual_solves_yangMillsPDE {A : Mat4CForm 1}
    (hA : ContDiff ℝ 2 A) (hASD : IsAntiSelfDualForm4 A) : YangMillsPDE A := by
  unfold YangMillsPDE
  rw [hASD, covExtDeriv_neg, bianchi_identity_ymCurvature hA, neg_zero]

/-! ## 4. Explicit Non-Abelian Circular Split-Octonion Yang–Mills Solutions -/

/-- Four circular Peirce basis coordinates `(e⁺₁, e⁺₂, e⁻₂, e⁻₁)` forming a self-dual
non-Abelian Yang–Mills connection on `FourSpace`. -/
def circularSelfDualCoords : Fin 4 → Coordinate :=
  ![ coordinateEquiv (rootPlus 0)
   , coordinateEquiv (rootPlus 1)
   , coordinateEquiv (rootMinus 1)
   , coordinateEquiv (rootMinus 0) ]

/-- `ℝ`-linear map evaluating the constant circular gauge 1-form on `FourSpace`. -/
def circularGaugeOneFormCLM : FourSpace →L[ℝ] Mat4C :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v =>
        ∑ μ : Fin 4, (v μ : ℂ) • circularConnectionMat4 (circularSelfDualCoords μ)
      map_add' := fun u v => by
        simp only [PiLp.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [← smul_assoc, Complex.real_smul] }

/-- Pointwise value of the circular gauge 1-form as a continuous alternating 1-form. -/
def circularGaugeOneForm : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C :=
  ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace)
    (F := Mat4C) (0 : Fin 1) circularGaugeOneFormCLM

/-- Explicit smooth non-Abelian self-dual gauge 1-form on `FourSpace` built from
`circularConnectionMat4`. -/
def circularGaugeForm : Mat4CForm 1 :=
  fun _ => circularGaugeOneForm

theorem circularGaugeForm_contDiff : ContDiff ℝ ⊤ circularGaugeForm :=
  contDiff_const

theorem circularGaugeForm_apply_basis (x : FourSpace) (μ : Fin 4) :
    circularGaugeForm x ![frameBasis μ] =
      circularConnectionMat4 (circularSelfDualCoords μ) := by
  have h : circularGaugeForm x ![frameBasis μ] =
      circularGaugeOneFormCLM (frameBasis μ) :=
    rfl
  rw [h]
  fin_cases μ <;> simp [circularGaugeOneFormCLM, frameBasis_apply]

theorem circularGaugeForm_mat4C_noncomm_witness :
    ∃ A B : Mat4C, A * B ≠ B * A := by
  refine ⟨circularGaugeForm 0 ![frameBasis 0], circularGaugeForm 0 ![frameBasis 2], ?_⟩
  rw [circularGaugeForm_apply_basis, circularGaugeForm_apply_basis]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have hU0 : weylUpperMat (circularSelfDualCoords 0) = σ1 := by
    simpa [circularSelfDualCoords] using weylUpperMat_rootPlus 0
  have hL2 : weylLowerMat (circularSelfDualCoords 2) = -σ2 := by
    simpa [circularSelfDualCoords] using weylLowerMat_rootMinus 1
  have hL0 : weylLowerMat (circularSelfDualCoords 0) = 0 := by
    have hc : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
      simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [circularSelfDualCoords, hc, weylLowerMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]
  have hU2 : weylUpperMat (circularSelfDualCoords 2) = 0 := by
    have hc : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
      simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 6
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [circularSelfDualCoords, hc, weylUpperMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3]
  simp [circularConnectionMat4, chiralOffBlock4_mul, hU0, hL2, hL0, hU2,
    chiralDiagBlock4, σ1, σ2, Complex.ext_iff] at h00

private lemma circularSelfDual_block_0 :
    circularConnectionMat4 (circularSelfDualCoords 0) = chiralOffBlock4 σ1 0 := by
  have hc : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularConnectionMat4, circularSelfDualCoords, hc, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, chiralOffBlock4, σ0, σ1, σ2, σ3]

private lemma circularSelfDual_block_1 :
    circularConnectionMat4 (circularSelfDualCoords 1) = chiralOffBlock4 σ2 0 := by
  have hc : coordinateEquiv (rootPlus 1) = Pi.single 2 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularConnectionMat4, circularSelfDualCoords, hc, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, chiralOffBlock4, σ0, σ1, σ2, σ3]

private lemma circularSelfDual_block_2 :
    circularConnectionMat4 (circularSelfDualCoords 2) = chiralOffBlock4 0 (-σ2) := by
  have hc : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 6
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularConnectionMat4, circularSelfDualCoords, hc, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, chiralOffBlock4, σ0, σ1, σ2, σ3]

private lemma circularSelfDual_block_3 :
    circularConnectionMat4 (circularSelfDualCoords 3) = chiralOffBlock4 0 (-σ1) := by
  have hc : coordinateEquiv (rootMinus 0) = Pi.single 5 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 5
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularConnectionMat4, circularSelfDualCoords, hc, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, chiralOffBlock4, σ0, σ1, σ2, σ3]

private lemma ymCurvature_circularGaugeForm_basis (x : FourSpace) (μ ν : Fin 4) :
    ymCurvature circularGaugeForm x ![frameBasis μ, frameBasis ν] =
      circularConnectionMat4 (circularSelfDualCoords μ) *
        circularConnectionMat4 (circularSelfDualCoords ν) -
      circularConnectionMat4 (circularSelfDualCoords ν) *
        circularConnectionMat4 (circularSelfDualCoords μ) := by
  have hc0 : fderiv ℝ (fun y => circularGaugeForm y ![frameBasis ν]) x = 0 := by
    change fderiv ℝ (fun _ => circularGaugeOneForm ![frameBasis ν]) x = 0
    simp
  have hc1 : fderiv ℝ (fun y => circularGaugeForm y ![frameBasis μ]) x = 0 := by
    change fderiv ℝ (fun _ => circularGaugeOneForm ![frameBasis μ]) x = 0
    simp
  rw [ymCurvature_apply_two circularGaugeForm
    (circularGaugeForm_contDiff.differentiable (by norm_num))]
  have ha0 : (fun _ : Fin 1 => frameBasis μ) = ![frameBasis μ] := by
    funext i; fin_cases i; rfl
  have ha1 : (fun _ : Fin 1 => frameBasis ν) = ![frameBasis ν] := by
    funext i; fin_cases i; rfl
  rw [ha0, ha1, hc0, hc1, zero_apply, zero_apply,
    sub_zero, zero_add, circularGaugeForm_apply_basis, circularGaugeForm_apply_basis]

theorem circularGaugeForm_ymCurvature_ne_zero :
    ymCurvature circularGaugeForm ≠ 0 := by
  intro h
  have h02 := congrFun (congrFun (congrArg (fun f => f 0 ![frameBasis 0, frameBasis 2]) h) 0) 0
  rw [ymCurvature_circularGaugeForm_basis, circularSelfDual_block_0,
    circularSelfDual_block_2, chiralOffBlock4_mul, chiralOffBlock4_mul] at h02
  simp [chiralDiagBlock4, σ1, σ2, Complex.ext_iff] at h02

theorem circularGaugeForm_isSelfDual : IsSelfDualForm4 circularGaugeForm := by
  rw [IsSelfDualForm4, hodgeStar4Eucl_eq_self_iff]
  intro x
  refine ⟨?_, ?_, ?_⟩
  · rw [ymCurvature_circularGaugeForm_basis, ymCurvature_circularGaugeForm_basis,
      circularSelfDual_block_0, circularSelfDual_block_1,
      circularSelfDual_block_2, circularSelfDual_block_3,
      chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul]
    simp
  · rw [ymCurvature_circularGaugeForm_basis, ymCurvature_circularGaugeForm_basis,
      circularSelfDual_block_0, circularSelfDual_block_2,
      circularSelfDual_block_3, circularSelfDual_block_1,
      chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralDiagBlock4, σ1, σ2, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [ymCurvature_circularGaugeForm_basis, ymCurvature_circularGaugeForm_basis,
      circularSelfDual_block_0, circularSelfDual_block_3,
      circularSelfDual_block_1, circularSelfDual_block_2,
      chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralDiagBlock4, σ1, σ2, Matrix.mul_apply, Fin.sum_univ_two]

theorem circularGaugeForm_solves_yangMillsPDE : YangMillsPDE circularGaugeForm :=
  selfDual_solves_yangMillsPDE (circularGaugeForm_contDiff.of_le le_top)
    circularGaugeForm_isSelfDual

/-- Exterior-algebra lift `ω_circ` of the four circular Peirce coordinate directions on
`Fin 4 → ℂ`. -/
def circularSelfDualExtOmega : Fin 8 → ExteriorAlgebra ℂ ChiralFiber :=
  fun i => ∑ μ : Fin 4, ((circularSelfDualCoords μ i : ℝ) : ℂ) •
    ExteriorAlgebra.ι ℂ (Pi.single μ 1)

private lemma circularGaugeForm_chiralProj_eq (x : FourSpace) :
    let x02 := circularSelfDualCoords 0 + circularSelfDualCoords 2
    chiralProjMat4 * ymCurvature circularGaugeForm x ![frameBasis 0, frameBasis 2] =
      chiralProjMat4 * circularCurvatureMat4 x02 ∧
    chiralVorticityVec x02 = ![0, 0, 1] ∧
    ((circularCurvatureMat4 x02)ᴴ * circularCurvatureMat4 x02).trace -
      (circularCurvatureMat4 x02 * circularCurvatureMat4 x02).trace = 8 := by
  intro x02
  have hx02 : x02 = Pi.single 1 1 + Pi.single 6 1 := by
    have hc1 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
      simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 1
    have hc6 : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
      simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 6
    simp [x02, circularSelfDualCoords, hc1, hc6]
  refine ⟨?_, ?_, ?_⟩
  · rw [ymCurvature_circularGaugeForm_basis, circularSelfDual_block_0,
      circularSelfDual_block_2, chiralOffBlock4_mul, chiralOffBlock4_mul]
    have hconn : circularConnectionMat4 x02 = chiralOffBlock4 σ1 (-σ2) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [circularConnectionMat4, hx02, weylUpperMat, weylLowerMat,
          pauliSolder2x2, solder, chiralOffBlock4, σ0, σ1, σ2, σ3]
    rw [circularCurvatureMat4, hconn, chiralOffBlock4_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralProjMat4, chiralProj4, chiralDiagBlock4, Matrix.mul_apply,
        Fin.sum_univ_four, σ1, σ2, Fin.sum_univ_two]
  · ext i
    fin_cases i <;> simp [hx02, chiralVorticityVec]
  · have hgap := circularCurvatureMat4_vorticity_action_gap x02
    have hv : chiralVorticityVec x02 = ![0, 0, 1] := by
      ext i
      fin_cases i <;> simp [hx02, chiralVorticityVec]
    rw [hgap, hv]
    simp [normSq3]

/-- Main R3 non-Abelian circular Yang–Mills PDE solution and bridge theorem connecting
`circularGaugeForm` to `circularBundleConnection`, `circularGaugeConnection4_yang_mills_bridge`,
`weylChannel_commutator_eq_vorticity`, and `circularCurvatureMat4_vorticity_action_gap`. -/
theorem circularGaugeForm_nonabelian_ym_solution
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (star d : Module.End ℂ (ExteriorAlgebra ℂ V))
    (X : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ V))
    (σ : FourSpace → ChiralFiber) (x v : FourSpace) :
    ymCurvature circularGaugeForm ≠ 0 ∧
    IsSelfDualForm4 circularGaugeForm ∧
    YangMillsPDE circularGaugeForm ∧
    (circularBundleConnection circularGaugeForm σ x v =
      fderiv ℝ σ x v +
        (∑ μ : Fin 4, (v μ : ℂ) • circularConnectionMat4 (circularSelfDualCoords μ)).mulVec
          (σ x)) ∧
    (∀ μ : Fin 4,
      (circularGaugeForm x ![frameBasis μ]).map (algebraMap ℂ (ExteriorAlgebra ℂ V)) =
        circularGaugeConnection4
          (fun i => algebraMap ℂ (ExteriorAlgebra ℂ V) ((circularSelfDualCoords μ i : ℝ) : ℂ))) ∧
    (let x02 := circularSelfDualCoords 0 + circularSelfDualCoords 2
     chiralProjMat4 * ymCurvature circularGaugeForm x ![frameBasis 0, frameBasis 2] =
       chiralProjMat4 * circularCurvatureMat4 x02 ∧
     chiralVorticityVec x02 = ![0, 0, 1] ∧
     ((circularCurvatureMat4 x02)ᴴ * circularCurvatureMat4 x02).trace -
       (circularCurvatureMat4 x02 * circularCurvatureMat4 x02).trace = 8) ∧
    (let P := chiralExteriorProj4 V
     let A_ext := circularGaugeConnection4
       (fun i => algebraMap ℂ (ExteriorAlgebra ℂ V) ((circularSelfDualCoords 0 i : ℝ) : ℂ))
     genPhi P A_ext A_ext = A_ext ∧
     evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) = genV P X X ∧
     (matrixExteriorDerivative d A_ext = peirceGradingDeriv P A_ext →
       curvatureFromConnection d A_ext = genJ P A_ext A_ext + genV P A_ext A_ext ∧
       evenGrade P (curvatureFromConnection d A_ext) = genV P A_ext A_ext) ∧
     curvatureFromConnection 0 A_ext = genV P A_ext A_ext ∧
     covariantDerivative A_ext 0 (genV P A_ext A_ext) = 0 ∧
     (isSelfDualCurvature star (genV P A_ext A_ext) →
       covariantDerivative A_ext 0
         (matrixHodgeStar star (curvatureFromConnection 0 A_ext)) = 0)) := by
  refine ⟨circularGaugeForm_ymCurvature_ne_zero, circularGaugeForm_isSelfDual,
    circularGaugeForm_solves_yangMillsPDE, ?_, ?_, ?_, ?_⟩
  · rw [circularBundleConnection_apply]
    rfl
  · intro μ
    rw [circularGaugeForm_apply_basis, ← circularGaugeConnection4_evalScalar]
  · exact circularGaugeForm_chiralProj_eq x
  · exact circularGaugeConnection4_yang_mills_bridge star d
      (fun i => algebraMap ℂ (ExteriorAlgebra ℂ V) ((circularSelfDualCoords 0 i : ℝ) : ℂ)) X

/-- Spacetime-varying Minkowski plane-wave 1-form profile along the light-cone coordinate
`x 0 - x 1` with circular Peirce generators `(e⁺₁, e⁻₁, e⁻₂)`. -/
def waveDirForm : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C :=
  ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace) (F := Mat4C) (0 : Fin 1)
    (LinearMap.toContinuousLinearMap
      { toFun := fun v =>
          ((v 0 - v 1 : ℝ) : ℂ) • circularConnectionMat4 (coordinateEquiv (rootPlus 0))
        map_add' := fun u v => by
          ext i j
          simp [PiLp.add_apply]
          ring
        map_smul' := fun c v => by
          ext i j
          simp [PiLp.smul_apply, Complex.real_smul]
          ring })

def waveSpatialForm : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C :=
  ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace) (F := Mat4C) (0 : Fin 1)
    (LinearMap.toContinuousLinearMap
      { toFun := fun v =>
          (v 2 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 0)) +
          (v 3 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 1))
        map_add' := fun u v => by
          simp only [PiLp.add_apply, Complex.ofReal_add, add_smul]
          abel
        map_smul' := fun c v => by
          simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
            smul_add, ← smul_assoc, Complex.real_smul] })

/-- Non-Abelian spacetime-varying light-cone wave 1-form on `FourSpace`. -/
def circularMinkowskiWaveForm (f : ℝ → ℝ) : Mat4CForm 1 :=
  fun x => f (x 0 - x 1) • waveDirForm + waveSpatialForm

private lemma waveDirForm_basis (μ : Fin 4) :
    waveDirForm ![frameBasis μ] =
      if μ = 0 then circularConnectionMat4 (coordinateEquiv (rootPlus 0))
      else if μ = 1 then -circularConnectionMat4 (coordinateEquiv (rootPlus 0))
      else 0 := by
  have h : waveDirForm ![frameBasis μ] =
      ((frameBasis μ 0 - frameBasis μ 1 : ℝ) : ℂ) •
        circularConnectionMat4 (coordinateEquiv (rootPlus 0)) :=
    rfl
  rw [h]
  fin_cases μ <;> simp [frameBasis_apply]

private lemma waveSpatialForm_basis (μ : Fin 4) :
    waveSpatialForm ![frameBasis μ] =
      if μ = 2 then circularConnectionMat4 (coordinateEquiv (rootMinus 0))
      else if μ = 3 then circularConnectionMat4 (coordinateEquiv (rootMinus 1))
      else 0 := by
  have h : waveSpatialForm ![frameBasis μ] =
      (frameBasis μ 2 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 0)) +
      (frameBasis μ 3 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 1)) :=
    rfl
  rw [h]
  fin_cases μ <;> simp [frameBasis_apply]

private lemma circularMinkowskiWaveForm_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (circularMinkowskiWaveForm f) := by
  let lc : FourSpace →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun x => x 0 - x 1
        map_add' := fun x y => by simp; ring
        map_smul' := fun c x => by simp; ring }
  have hlc : ContDiff ℝ 2 (fun x : FourSpace => f (lc x)) := hf.comp lc.contDiff
  have h1 : ContDiff ℝ 2 (fun x : FourSpace => f (x 0 - x 1) • waveDirForm) :=
    hlc.smul contDiff_const
  exact h1.add contDiff_const

private lemma circularMinkowskiWave_b5_b6_comm :
    circularConnectionMat4 (coordinateEquiv (rootMinus 0)) *
        circularConnectionMat4 (coordinateEquiv (rootMinus 1)) = 0 ∧
    circularConnectionMat4 (coordinateEquiv (rootMinus 1)) *
        circularConnectionMat4 (coordinateEquiv (rootMinus 0)) = 0 := by
  rw [show coordinateEquiv (rootMinus 0) = circularSelfDualCoords 3 from rfl,
    show coordinateEquiv (rootMinus 1) = circularSelfDualCoords 2 from rfl,
    circularSelfDual_block_3, circularSelfDual_block_2,
    chiralOffBlock4_mul, chiralOffBlock4_mul]
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]

private lemma circularMinkowskiWave_jacobi_cancel :
    mat4CCommCLM (circularConnectionMat4 (coordinateEquiv (rootMinus 0)))
        (mat4CCommCLM (circularConnectionMat4 (coordinateEquiv (rootPlus 0)))
          (circularConnectionMat4 (coordinateEquiv (rootMinus 0)))) +
      mat4CCommCLM (circularConnectionMat4 (coordinateEquiv (rootMinus 1)))
        (mat4CCommCLM (circularConnectionMat4 (coordinateEquiv (rootPlus 0)))
          (circularConnectionMat4 (coordinateEquiv (rootMinus 1)))) = 0 := by
  rw [show coordinateEquiv (rootPlus 0) = circularSelfDualCoords 0 from rfl,
    show coordinateEquiv (rootMinus 0) = circularSelfDualCoords 3 from rfl,
    show coordinateEquiv (rootMinus 1) = circularSelfDualCoords 2 from rfl,
    circularSelfDual_block_0, circularSelfDual_block_3, circularSelfDual_block_2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat4CCommCLM_apply, chiralOffBlock4, σ1, σ2]

private lemma circularMinkowskiWave_comm_cancel (r : ℝ) (v : Fin 3 → FourSpace) :
    let b1 := circularConnectionMat4 (coordinateEquiv (rootPlus 0))
    let b5 := circularConnectionMat4 (coordinateEquiv (rootMinus 0))
    let b6 := circularConnectionMat4 (coordinateEquiv (rootMinus 1))
    let c02 := mat4CCommCLM b1 b5
    let c03 := mat4CCommCLM b1 b6
    let Aop : FourSpace → Mat4C := fun u =>
      (r * (u 0 - u 1)) • b1 + u 2 • b5 + u 3 • b6
    let Sop : FourSpace → FourSpace → Mat4C := fun u w =>
      ((u 3 * w 1 - u 1 * w 3) + (u 0 * w 3 - u 3 * w 0)) • c02 +
      ((u 1 * w 2 - u 2 * w 1) - (u 0 * w 2 - u 2 * w 0)) • c03
    mat4CCommCLM (Aop (v 0)) (r • Sop (v 1) (v 2)) -
      mat4CCommCLM (Aop (v 1)) (r • Sop (v 0) (v 2)) +
      mat4CCommCLM (Aop (v 2)) (r • Sop (v 0) (v 1)) = 0 := by
  intro b1 b5 b6 c02 c03 Aop Sop
  have hb6c03 : mat4CCommCLM b6 c03 = -mat4CCommCLM b5 c02 :=
    eq_neg_of_add_eq_zero_right circularMinkowskiWave_jacobi_cancel
  dsimp only [Aop, Sop]
  simp only [map_add, map_smul, add_apply, smul_apply, hb6c03, smul_neg]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
    Matrix.zero_apply, Complex.real_smul]
  push_cast
  ring

private lemma circularMinkowskiWave_deriv_cancel (d : ℝ) (v : Fin 3 → FourSpace)
    (c02 c03 : Mat4C) :
    (d * ((v 0) 0 - (v 0) 1)) •
        (((v 1 3 * v 2 1 - v 1 1 * v 2 3) + (v 1 0 * v 2 3 - v 1 3 * v 2 0)) • c02 +
         ((v 1 1 * v 2 2 - v 1 2 * v 2 1) - (v 1 0 * v 2 2 - v 1 2 * v 2 0)) • c03) +
    -((d * ((v 1) 0 - (v 1) 1)) •
        (((v 0 3 * v 2 1 - v 0 1 * v 2 3) + (v 0 0 * v 2 3 - v 0 3 * v 2 0)) • c02 +
         ((v 0 1 * v 2 2 - v 0 2 * v 2 1) - (v 0 0 * v 2 2 - v 0 2 * v 2 0)) • c03)) +
    (d * ((v 2) 0 - (v 2) 1)) •
        (((v 0 3 * v 1 1 - v 0 1 * v 1 3) + (v 0 0 * v 1 3 - v 0 3 * v 1 0)) • c02 +
         ((v 0 1 * v 1 2 - v 0 2 * v 1 1) - (v 0 0 * v 1 2 - v 0 2 * v 1 0)) • c03) = 0 := by
  ext a b
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.zero_apply,
    Complex.real_smul]
  push_cast
  ring

private def waveLightConeCLM : FourSpace →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => x 0 - x 1
      map_add' := fun x y => by simp; ring
      map_smul' := fun c x => by simp; ring }

private lemma circularMinkowskiWaveForm_fderiv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (x u : FourSpace) (w : Fin 1 → FourSpace) :
    (fderiv ℝ (circularMinkowskiWaveForm f) x u) w =
      (deriv f (x 0 - x 1) * (u 0 - u 1)) • waveDirForm w := by
  have hlc_fderiv :
      fderiv ℝ (fun y => f (y 0 - y 1)) x u =
        deriv f (x 0 - x 1) * (u 0 - u 1) := by
    have hfd : HasDerivAt f (deriv f (waveLightConeCLM x)) (waveLightConeCLM x) :=
      ((hf.differentiable (by norm_num)) (waveLightConeCLM x)).hasDerivAt
    have hd : HasFDerivAt (fun y : FourSpace => f (waveLightConeCLM y))
        ((deriv f (waveLightConeCLM x)) • waveLightConeCLM) x :=
      hfd.comp_hasFDerivAt x waveLightConeCLM.hasFDerivAt
    simpa [waveLightConeCLM] using congrArg (fun L : FourSpace →L[ℝ] ℝ => L u) hd.fderiv
  have hsm : HasFDerivAt (fun y : FourSpace => f (y 0 - y 1) • waveDirForm)
      ((fderiv ℝ (fun y : FourSpace => f (y 0 - y 1)) x).smulRight waveDirForm) x :=
    ((hf.differentiable (by norm_num)).comp
        waveLightConeCLM.differentiable x).hasFDerivAt.smul_const
      waveDirForm
  have hsum : fderiv ℝ (circularMinkowskiWaveForm f) x =
      (fderiv ℝ (fun y : FourSpace => f (y 0 - y 1)) x).smulRight waveDirForm := by
    change fderiv ℝ ((fun y : FourSpace => f (y 0 - y 1) • waveDirForm) +
      (fun _ : FourSpace => waveSpatialForm)) x = _
    have hfd := (hsm.add (hasFDerivAt_const waveSpatialForm x)).fderiv
    exact hfd.trans (add_zero _)
  rw [hsum]
  simp [hlc_fderiv]

private lemma circularMinkowskiWaveForm_F01 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : FourSpace) :
    ymCurvature (circularMinkowskiWaveForm f) x ![frameBasis 0, frameBasis 1] = 0 := by
  have hAd := (circularMinkowskiWaveForm_contDiff hf).differentiable (by norm_num)
  rw [ymCurvature_apply_two _ hAd x]
  have hf0 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 1]) x (frameBasis 0) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 0)) ![frameBasis 1] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 1] (frameBasis 0)
  have hf1 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 0]) x (frameBasis 1) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 1)) ![frameBasis 0] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 0] (frameBasis 1)
  have ha0 : (fun _ : Fin 1 => frameBasis 0) = ![frameBasis 0] := by
    funext i; fin_cases i; rfl
  have ha1 : (fun _ : Fin 1 => frameBasis 1) = ![frameBasis 1] := by
    funext i; fin_cases i; rfl
  rw [ha0, ha1, hf0, hf1, circularMinkowskiWaveForm_fderiv hf, circularMinkowskiWaveForm_fderiv hf]
  simp only [circularMinkowskiWaveForm, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, waveDirForm_basis, waveSpatialForm_basis,
    frameBasis_apply]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Complex.real_smul, Fin.isValue]
  norm_num

private lemma circularMinkowskiWaveForm_F23 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : FourSpace) :
    ymCurvature (circularMinkowskiWaveForm f) x ![frameBasis 2, frameBasis 3] = 0 := by
  have hAd := (circularMinkowskiWaveForm_contDiff hf).differentiable (by norm_num)
  rw [ymCurvature_apply_two _ hAd x]
  have hf2 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 3]) x (frameBasis 2) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 2)) ![frameBasis 3] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 3] (frameBasis 2)
  have hf3 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 2]) x (frameBasis 3) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 3)) ![frameBasis 2] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 2] (frameBasis 3)
  have ha2 : (fun _ : Fin 1 => frameBasis 2) = ![frameBasis 2] := by
    funext i; fin_cases i; rfl
  have ha3 : (fun _ : Fin 1 => frameBasis 3) = ![frameBasis 3] := by
    funext i; fin_cases i; rfl
  rw [ha2, ha3, hf2, hf3, circularMinkowskiWaveForm_fderiv hf, circularMinkowskiWaveForm_fderiv hf]
  simp [circularMinkowskiWaveForm, waveDirForm_basis, waveSpatialForm_basis,
    frameBasis_apply, circularMinkowskiWave_b5_b6_comm]

private lemma circularMinkowskiWaveForm_F02 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : FourSpace) :
    ymCurvature (circularMinkowskiWaveForm f) x ![frameBasis 0, frameBasis 2] =
      f (x 0 - x 1) •
        mat4CCommCLM (circularConnectionMat4 (coordinateEquiv (rootPlus 0)))
          (circularConnectionMat4 (coordinateEquiv (rootMinus 0))) := by
  have hAd := (circularMinkowskiWaveForm_contDiff hf).differentiable (by norm_num)
  rw [ymCurvature_apply_two _ hAd x]
  have hf0 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 2]) x (frameBasis 0) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 0)) ![frameBasis 2] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 2] (frameBasis 0)
  have hf2 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 0]) x (frameBasis 2) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 2)) ![frameBasis 0] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 0] (frameBasis 2)
  have ha0 : (fun _ : Fin 1 => frameBasis 0) = ![frameBasis 0] := by
    funext i; fin_cases i; rfl
  have ha2 : (fun _ : Fin 1 => frameBasis 2) = ![frameBasis 2] := by
    funext i; fin_cases i; rfl
  rw [ha0, ha2, hf0, hf2, circularMinkowskiWaveForm_fderiv hf, circularMinkowskiWaveForm_fderiv hf]
  simp only [circularMinkowskiWaveForm, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, waveDirForm_basis, waveSpatialForm_basis,
    frameBasis_apply, mat4CCommCLM_apply]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Complex.real_smul, Fin.isValue]
  norm_num
  ring

private lemma circularMinkowskiWaveForm_F03 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : FourSpace) :
    ymCurvature (circularMinkowskiWaveForm f) x ![frameBasis 0, frameBasis 3] =
      f (x 0 - x 1) •
        mat4CCommCLM (circularConnectionMat4 (coordinateEquiv (rootPlus 0)))
          (circularConnectionMat4 (coordinateEquiv (rootMinus 1))) := by
  have hAd := (circularMinkowskiWaveForm_contDiff hf).differentiable (by norm_num)
  rw [ymCurvature_apply_two _ hAd x]
  have hf0 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 3]) x (frameBasis 0) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 0)) ![frameBasis 3] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 3] (frameBasis 0)
  have hf3 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 0]) x (frameBasis 3) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 3)) ![frameBasis 0] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 0] (frameBasis 3)
  have ha0 : (fun _ : Fin 1 => frameBasis 0) = ![frameBasis 0] := by
    funext i; fin_cases i; rfl
  have ha3 : (fun _ : Fin 1 => frameBasis 3) = ![frameBasis 3] := by
    funext i; fin_cases i; rfl
  rw [ha0, ha3, hf0, hf3, circularMinkowskiWaveForm_fderiv hf, circularMinkowskiWaveForm_fderiv hf]
  simp only [circularMinkowskiWaveForm, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, waveDirForm_basis, waveSpatialForm_basis,
    frameBasis_apply, mat4CCommCLM_apply]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Complex.real_smul, Fin.isValue]
  norm_num
  ring

private lemma circularMinkowskiWaveForm_F12 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : FourSpace) :
    ymCurvature (circularMinkowskiWaveForm f) x ![frameBasis 1, frameBasis 2] =
      -(ymCurvature (circularMinkowskiWaveForm f) x ![frameBasis 0, frameBasis 2]) := by
  have hAd := (circularMinkowskiWaveForm_contDiff hf).differentiable (by norm_num)
  rw [ymCurvature_apply_two _ hAd x, circularMinkowskiWaveForm_F02 hf]
  have hf1 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 2]) x (frameBasis 1) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 1)) ![frameBasis 2] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 2] (frameBasis 1)
  have hf2 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 1]) x (frameBasis 2) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 2)) ![frameBasis 1] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 1] (frameBasis 2)
  have ha1 : (fun _ : Fin 1 => frameBasis 1) = ![frameBasis 1] := by
    funext i; fin_cases i; rfl
  have ha2 : (fun _ : Fin 1 => frameBasis 2) = ![frameBasis 2] := by
    funext i; fin_cases i; rfl
  rw [ha1, ha2, hf1, hf2, circularMinkowskiWaveForm_fderiv hf, circularMinkowskiWaveForm_fderiv hf]
  simp only [circularMinkowskiWaveForm, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, waveDirForm_basis, waveSpatialForm_basis,
    frameBasis_apply, mat4CCommCLM_apply]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
    Complex.real_smul, Fin.isValue]
  norm_num
  ring

private lemma circularMinkowskiWaveForm_F31 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : FourSpace) :
    ymCurvature (circularMinkowskiWaveForm f) x ![frameBasis 3, frameBasis 1] =
      ymCurvature (circularMinkowskiWaveForm f) x ![frameBasis 0, frameBasis 3] := by
  have hAd := (circularMinkowskiWaveForm_contDiff hf).differentiable (by norm_num)
  rw [ymCurvature_apply_two _ hAd x, circularMinkowskiWaveForm_F03 hf]
  have hf3 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 1]) x (frameBasis 3) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 3)) ![frameBasis 1] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 1] (frameBasis 3)
  have hf1 : fderiv ℝ (fun y => circularMinkowskiWaveForm f y ![frameBasis 3]) x (frameBasis 1) =
      (fderiv ℝ (circularMinkowskiWaveForm f) x (frameBasis 1)) ![frameBasis 3] :=
    fderiv_mat4CForm_apply_const (hAd x) ![frameBasis 3] (frameBasis 1)
  have ha3 : (fun _ : Fin 1 => frameBasis 3) = ![frameBasis 3] := by
    funext i; fin_cases i; rfl
  have ha1 : (fun _ : Fin 1 => frameBasis 1) = ![frameBasis 1] := by
    funext i; fin_cases i; rfl
  rw [ha3, ha1, hf3, hf1, circularMinkowskiWaveForm_fderiv hf, circularMinkowskiWaveForm_fderiv hf]
  simp only [circularMinkowskiWaveForm, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, waveDirForm_basis, waveSpatialForm_basis,
    frameBasis_apply, mat4CCommCLM_apply]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Complex.real_smul, Fin.isValue]
  norm_num
  ring

private def waveC02 : Mat4C :=
  mat4CCommCLM (circularConnectionMat4 (coordinateEquiv (rootPlus 0)))
    (circularConnectionMat4 (coordinateEquiv (rootMinus 0)))

private def waveC03 : Mat4C :=
  mat4CCommCLM (circularConnectionMat4 (coordinateEquiv (rootPlus 0)))
    (circularConnectionMat4 (coordinateEquiv (rootMinus 1)))

private def waveBaseForm : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C :=
  AlternatingMap.mkContinuous
    { toFun := fun v =>
        (plucker2 v 0 2 - plucker2 v 1 2) • waveC02 +
        (plucker2 v 0 3 + plucker2 v 3 1) • waveC03
      map_update_add' := fun m i x y => by
        ext a b
        simp only [plucker2_update_add, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
        push_cast
        ring
      map_update_smul' := fun m i c x => by
        ext a b
        simp only [plucker2_update_smul, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
        push_cast
        ring
      map_eq_zero_of_eq' := fun v i j hv hij => by
        simp only [plucker2_eq_zero_of_eq v hv hij, sub_self, add_zero, zero_smul] }
    (4 * (‖waveC02‖ + ‖waveC03‖))
    (fun v => by
      have hp02 := norm_plucker2_le v 0 2
      have hp12 := norm_plucker2_le v 1 2
      have hp03 := norm_plucker2_le v 0 3
      have hp31 := norm_plucker2_le v 3 1
      calc
        ‖(plucker2 v 0 2 - plucker2 v 1 2) • waveC02 +
            (plucker2 v 0 3 + plucker2 v 3 1) • waveC03‖
            ≤ ‖(plucker2 v 0 2 - plucker2 v 1 2) • waveC02‖ +
              ‖(plucker2 v 0 3 + plucker2 v 3 1) • waveC03‖ := norm_add_le _ _
        _ = |plucker2 v 0 2 - plucker2 v 1 2| * ‖waveC02‖ +
            |plucker2 v 0 3 + plucker2 v 3 1| * ‖waveC03‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ (|plucker2 v 0 2| + |plucker2 v 1 2|) * ‖waveC02‖ +
            (|plucker2 v 0 3| + |plucker2 v 3 1|) * ‖waveC03‖ := by
          gcongr
          · exact abs_sub _ _
          · exact abs_add_le _ _
        _ ≤ (4 * ∏ i : Fin 2, ‖v i‖) * ‖waveC02‖ +
            (4 * ∏ i : Fin 2, ‖v i‖) * ‖waveC03‖ := by
          gcongr <;> linarith
        _ = 4 * (‖waveC02‖ + ‖waveC03‖) * ∏ i : Fin 2, ‖v i‖ := by ring)

private def waveConstStar : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C :=
  hodgeStar4MinkowskiMap waveBaseForm

private lemma waveConstStar_eval (w : Fin 2 → FourSpace) :
    waveConstStar w =
      (plucker2 w 3 1 + plucker2 w 0 3) • waveC02 +
      (plucker2 w 1 2 - plucker2 w 0 2) • waveC03 := by
  have hb01 : waveBaseForm ![frameBasis 0, frameBasis 1] = 0 := by
    change (plucker2 ![frameBasis 0, frameBasis 1] 0 2 -
      plucker2 ![frameBasis 0, frameBasis 1] 1 2) • waveC02 +
      (plucker2 ![frameBasis 0, frameBasis 1] 0 3 +
      plucker2 ![frameBasis 0, frameBasis 1] 3 1) • waveC03 = 0
    simp [plucker2_basis]
  have hb23 : waveBaseForm ![frameBasis 2, frameBasis 3] = 0 := by
    change (plucker2 ![frameBasis 2, frameBasis 3] 0 2 -
      plucker2 ![frameBasis 2, frameBasis 3] 1 2) • waveC02 +
      (plucker2 ![frameBasis 2, frameBasis 3] 0 3 +
      plucker2 ![frameBasis 2, frameBasis 3] 3 1) • waveC03 = 0
    simp [plucker2_basis]
  have hb02 : waveBaseForm ![frameBasis 0, frameBasis 2] = waveC02 := by
    change (plucker2 ![frameBasis 0, frameBasis 2] 0 2 -
      plucker2 ![frameBasis 0, frameBasis 2] 1 2) • waveC02 +
      (plucker2 ![frameBasis 0, frameBasis 2] 0 3 +
      plucker2 ![frameBasis 0, frameBasis 2] 3 1) • waveC03 = waveC02
    simp [plucker2_basis]
  have hb31 : waveBaseForm ![frameBasis 3, frameBasis 1] = waveC03 := by
    change (plucker2 ![frameBasis 3, frameBasis 1] 0 2 -
      plucker2 ![frameBasis 3, frameBasis 1] 1 2) • waveC02 +
      (plucker2 ![frameBasis 3, frameBasis 1] 0 3 +
      plucker2 ![frameBasis 3, frameBasis 1] 3 1) • waveC03 = waveC03
    simp [plucker2_basis]
  have hb03 : waveBaseForm ![frameBasis 0, frameBasis 3] = waveC03 := by
    change (plucker2 ![frameBasis 0, frameBasis 3] 0 2 -
      plucker2 ![frameBasis 0, frameBasis 3] 1 2) • waveC02 +
      (plucker2 ![frameBasis 0, frameBasis 3] 0 3 +
      plucker2 ![frameBasis 0, frameBasis 3] 3 1) • waveC03 = waveC03
    simp [plucker2_basis]
  have hb12 : waveBaseForm ![frameBasis 1, frameBasis 2] = -waveC02 := by
    change (plucker2 ![frameBasis 1, frameBasis 2] 0 2 -
      plucker2 ![frameBasis 1, frameBasis 2] 1 2) • waveC02 +
      (plucker2 ![frameBasis 1, frameBasis 2] 0 3 +
      plucker2 ![frameBasis 1, frameBasis 2] 3 1) • waveC03 = -waveC02
    simp [plucker2_basis]
  dsimp [waveConstStar]
  change hodgeStar4MinkowskiAlt waveBaseForm w = _
  dsimp [hodgeStar4MinkowskiAlt]
  rw [hb01, hb23, hb02, hb31, hb03, hb12]
  simp only [minkowskiSign2, minkowskiEta4, Matrix.diagonal_apply_eq]
  norm_num
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Complex.real_smul]
  push_cast
  ring

private lemma hodgeStar4Minkowski_waveForm {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    hodgeStar4Minkowski (ymCurvature (circularMinkowskiWaveForm f)) =
      fun x => f (x 0 - x 1) • waveConstStar := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  have hy : ymCurvature (circularMinkowskiWaveForm f) x =
      f (x 0 - x 1) • waveBaseForm := by
    apply ContinuousAlternatingMap.ext
    intro w
    rw [alternating_fourSpace_eq_plucker, circularMinkowskiWaveForm_F01 hf,
      circularMinkowskiWaveForm_F23 hf, circularMinkowskiWaveForm_F12 hf,
      circularMinkowskiWaveForm_F31 hf, circularMinkowskiWaveForm_F02 hf,
      circularMinkowskiWaveForm_F03 hf]
    change _ = f (x 0 - x 1) • ((plucker2 w 0 2 - plucker2 w 1 2) • waveC02 +
      (plucker2 w 0 3 + plucker2 w 3 1) • waveC03)
    ext a b
    simp only [waveC02, waveC03, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_zero, zero_add, add_zero, Complex.real_smul]
    push_cast
    ring
  change hodgeStar4MinkowskiMap (ymCurvature (circularMinkowskiWaveForm f) x) v =
    (f (x 0 - x 1) • waveConstStar) v
  rw [hy, map_smul]
  rfl

theorem circularMinkowskiWaveForm_solves_yangMillsPDEMinkowski
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    YangMillsPDEMinkowski (circularMinkowskiWaveForm f) := by
  unfold YangMillsPDEMinkowski
  rw [hodgeStar4Minkowski_waveForm hf]
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  dsimp [covExtDeriv, wedgeComm]
  have hdiff_star : DifferentiableAt ℝ (fun y : FourSpace => f (y 0 - y 1) • waveConstStar) x :=
    ((hf.differentiable (by norm_num)).comp waveLightConeCLM.differentiable x).smul_const
      waveConstStar
  have hlc_fderiv : ∀ u : FourSpace,
      fderiv ℝ (fun y => f (y 0 - y 1)) x u =
        deriv f (x 0 - x 1) * (u 0 - u 1) := by
    intro u
    have hfd : HasDerivAt f (deriv f (waveLightConeCLM x)) (waveLightConeCLM x) :=
      ((hf.differentiable (by norm_num)) (waveLightConeCLM x)).hasDerivAt
    have hd : HasFDerivAt (fun y : FourSpace => f (waveLightConeCLM y))
        ((deriv f (waveLightConeCLM x)) • waveLightConeCLM) x :=
      hfd.comp_hasFDerivAt x waveLightConeCLM.hasFDerivAt
    simpa [waveLightConeCLM] using congrArg (fun L : FourSpace →L[ℝ] ℝ => L u) hd.fderiv
  have hf_star : ∀ u : FourSpace, ∀ w : Fin 2 → FourSpace,
      fderiv ℝ (fun y => (f (y 0 - y 1) • waveConstStar) w) x u =
        (deriv f (x 0 - x 1) * (u 0 - u 1)) • waveConstStar w := by
    intro u w
    rw [fderiv_mat4CForm_apply_const hdiff_star]
    have hsm : HasFDerivAt (fun y : FourSpace => f (y 0 - y 1) • waveConstStar)
        ((fderiv ℝ (fun y : FourSpace => f (y 0 - y 1)) x).smulRight waveConstStar) x :=
      ((hf.differentiable (by norm_num)).comp
        waveLightConeCLM.differentiable x).hasFDerivAt.smul_const waveConstStar
    rw [hsm.fderiv]
    simp [hlc_fderiv]
  rw [extD_apply hdiff_star v, wedgeCommAt_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  rw [removeNth_three_zero, removeNth_three_one, removeNth_three_two]
  rw [hf_star, hf_star, hf_star]
  have hw_const : ∀ u w : FourSpace,
      waveConstStar ![u, w] =
        (plucker2 ![u, w] 3 1 + plucker2 ![u, w] 0 3) • waveC02 +
        (plucker2 ![u, w] 1 2 - plucker2 ![u, w] 0 2) • waveC03 :=
    fun u w => waveConstStar_eval ![u, w]
  simp only [ContinuousAlternatingMap.smul_apply, hw_const]
  simp only [plucker2, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hA_val : ∀ u : FourSpace,
      circularMinkowskiWaveForm f x (fun _ => u) =
        (f (x 0 - x 1) * (u 0 - u 1)) • circularConnectionMat4 (coordinateEquiv (rootPlus 0)) +
          u 2 • circularConnectionMat4 (coordinateEquiv (rootMinus 0)) +
          u 3 • circularConnectionMat4 (coordinateEquiv (rootMinus 1)) := by
    intro u
    have hdir : waveDirForm (fun _ => u) =
        ((u 0 - u 1 : ℝ) : ℂ) • circularConnectionMat4 (coordinateEquiv (rootPlus 0)) := rfl
    have hsp : waveSpatialForm (fun _ => u) =
        (u 2 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 0)) +
        (u 3 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 1)) := rfl
    change f (x 0 - x 1) • waveDirForm (fun _ => u) + waveSpatialForm (fun _ => u) = _
    rw [hdir, hsp]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring
  have hcomm_cancel := circularMinkowskiWave_comm_cancel (f (x 0 - x 1)) v
  dsimp only at hcomm_cancel
  simp only [hA_val]
  have hpow0 : (-1 : ℤ) ^ (0 : ℕ) = 1 := rfl
  have hpow1 : (-1 : ℤ) ^ (1 : ℕ) = -1 := rfl
  have hpow2 : (-1 : ℤ) ^ (2 : ℕ) = 1 := rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hpow0, hpow1, hpow2, one_zsmul, neg_one_zsmul]
  have hd_zero := circularMinkowskiWave_deriv_cancel (deriv f (x 0 - x 1)) v waveC02 waveC03
  rw [← add_assoc, hd_zero, zero_add]
  simp only [waveC02, waveC03, map_add, map_smul] at hcomm_cancel ⊢
  abel_nf at hcomm_cancel ⊢
  exact hcomm_cancel

theorem circularMinkowskiWaveForm_ymCurvature_ne_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hf0 : f 0 ≠ 0) :
    ymCurvature (circularMinkowskiWaveForm f) ≠ 0 := by
  intro h
  have h02 := congrFun (congrFun (congrArg (fun g => g 0 ![frameBasis 0, frameBasis 2]) h) 0) 0
  rw [circularMinkowskiWaveForm_F02 hf 0] at h02
  rw [show coordinateEquiv (rootPlus 0) = circularSelfDualCoords 0 from rfl,
    show coordinateEquiv (rootMinus 0) = circularSelfDualCoords 3 from rfl,
    circularSelfDual_block_0, circularSelfDual_block_3] at h02
  simp [mat4CCommCLM_apply, chiralOffBlock4_mul, chiralDiagBlock4, sub_self, σ1,
    Complex.ext_iff] at h02
  exact hf0 h02

end InfoGeometry.Lie
