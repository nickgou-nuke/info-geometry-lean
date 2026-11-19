/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Erlangen.InvariantGeometry
import InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle

/-!
# Smooth Manifold Cartan Geometries `(P → M, ω ∈ Ω¹(P, 𝔤))`, Curvature, & Maurer–Cartan Flatness

This owner module formalizes smooth manifold Cartan geometries generalizing homogeneous spaces
`G → G / H` over native Mathlib `IsManifold`, `LieGroup`, `TangentSpace`, `mfderiv`,
`VectorField.mlieBracket`, and `GroupLieAlgebra`, bridging to `Erlangen.InvariantGeometry` and
`Erlangen20Datum`:

1. **Noncommutative Operator Lie Group `GL(2, ℝ)` (`UnitsOfNormedAlgebra`) & General Maurer–Cartan
   Connection**:
   Constructs `EndR2 := (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)` and `GL2R := EndR2ˣ` with explicit T17
   noncommutativity witnesses, and constructs for any smooth Lie group `G`
   (`LieGroup I (minSmoothness ℝ 3) G`) the left Maurer–Cartan continuous linear equivalence
   `leftMaurerCartanEquiv I g : TangentSpace I g ≃L[ℝ] GroupLieAlgebra I G`.
2. **Smooth Cartan Geometry `(P → M, H, 𝔤, 𝔥 ↪ 𝔤, ω ∈ Ω¹(P, 𝔤))`, Tangent Soldering, & Curvature**:
   Defines `SmoothCartanGeometry`, proves the canonical soldering quotient isomorphism
   `cartanTangentQuotientEquiv` between `TₚP / ker(dπₚ)` and `𝔤 / 𝔥`, defines `cartanExteriorDeriv`,
   `cartanCurvatureForm`, and `cartanTorsionForm`, proves skew-symmetry and Sharpe's absolute
   parallelism curvature identity, and proves universal Kleinian flatness
   (`maurerCartan_cartanCurvature_eq_zero`) on arbitrary smooth Lie groups and on `GL2R`.
3. **Non-Trivial Smooth Principal Bundle `ℝ² × ℝ → ℝ²` Contrasting Flat (`κ = 0`) vs. Curved (`κ ≠ 0`)**:
   Constructs the 3D non-abelian homothety Lie algebra `HomothetyLieAlg`, installs its Cartan
   connection family `homothetyCartanGeometry (κ : ℝ)` over `P = (Fin 2 → ℝ) × ℝ → Fin 2 → ℝ`,
   evaluates `cartanCurvatureForm` explicitly as `⟨(-κ * Real.exp (-s)) • x, 2 * κ⟩`, and separates
   flat Kleinian specialization (`κ = 0`, curvature `= 0` everywhere) from genuinely curved Cartan
   geometries (`κ ≠ 0`, curvature `≠ 0` everywhere, zero torsion on the origin fiber `x = 0`, and
   non-zero Cartan torsion for `x ≠ 0`).
4. **Fiberwise Bridge to `Erlangen20Datum` & `Erlangen.InvariantGeometry`**:
   Constructs `cartanFiberErlangen20Datum C p` and `cartanAdjointIntertwiner C p X`, together with
   T17 noncommutativity on `Module.End ℝ ((Fin 2 → ℝ) × ℝ)` and `H`-invariant readouts.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

noncomputable section

namespace InfoGeometry.Erlangen.SmoothCartanGeometry

open Bundle Function Set
open scoped Manifold ContDiff LieAlgebra
open InfoGeometry.Erlangen.InvariantGeometry
open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.MetaCompiler
open InfoGeometry.MetaCompiler

scoped instance moduleEndLieRing (R V : Type*) [Ring R]
    [AddCommGroup V] [Module R V] : LieRing (Module.End R V) :=
  LieRing.ofAssociativeRing

scoped instance moduleEndLieAlgebra (R V : Type*) [CommRing R]
    [AddCommGroup V] [Module R V] : LieAlgebra R (Module.End R V) :=
  LieAlgebra.ofAssociativeAlgebra

/-! ## Section 1: Noncommutative Operator Lie Group `GL(2, ℝ)` & General Maurer–Cartan Form -/

/-- The normed associative algebra of bounded linear operators on `ℝ²`. -/
abbrev EndR2 : Type := (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)

/-- The smooth Lie group `GL(2, ℝ) := ((Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))ˣ` via Mathlib `UnitsOfNormedAlgebra`. -/
abbrev GL2R : Type := EndR2ˣ

private def shearUpperLin : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0 + v 1, v 1]
  map_add' u v := by
    ext i
    fin_cases i <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [mul_add]

private def shearUpperInvLin : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0 - v 1, v 1]
  map_add' u v := by
    ext i
    fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [mul_sub]

private def shearLowerLin : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0, v 0 + v 1]
  map_add' u v := by
    ext i
    fin_cases i <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [mul_add]

private def shearLowerInvLin : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0, v 1 - v 0]
  map_add' u v := by
    ext i
    fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [mul_sub]

def shearUpperCLM : EndR2 := shearUpperLin.toContinuousLinearMap
def shearUpperInvCLM : EndR2 := shearUpperInvLin.toContinuousLinearMap
def shearLowerCLM : EndR2 := shearLowerLin.toContinuousLinearMap
def shearLowerInvCLM : EndR2 := shearLowerInvLin.toContinuousLinearMap

private lemma shearUpper_mul_inv : shearUpperCLM * shearUpperInvCLM = 1 := by
  ext v i
  fin_cases i <;> simp [shearUpperCLM, shearUpperInvCLM, shearUpperLin, shearUpperInvLin]

private lemma shearUpperInv_mul_upper : shearUpperInvCLM * shearUpperCLM = 1 := by
  ext v i
  fin_cases i <;> simp [shearUpperCLM, shearUpperInvCLM, shearUpperLin, shearUpperInvLin]

private lemma shearLower_mul_inv : shearLowerCLM * shearLowerInvCLM = 1 := by
  ext v i
  fin_cases i <;> simp [shearLowerCLM, shearLowerInvCLM, shearLowerLin, shearLowerInvLin]

private lemma shearLowerInv_mul_lower : shearLowerInvCLM * shearLowerCLM = 1 := by
  ext v i
  fin_cases i <;> simp [shearLowerCLM, shearLowerInvCLM, shearLowerLin, shearLowerInvLin]

def shearUpperGL2 : GL2R := ⟨shearUpperCLM, shearUpperInvCLM, shearUpper_mul_inv, shearUpperInv_mul_upper⟩
def shearLowerGL2 : GL2R := ⟨shearLowerCLM, shearLowerInvCLM, shearLower_mul_inv, shearLowerInv_mul_lower⟩

/-- Mandatory T17 noncommutativity ground witness on `EndR2`. -/
theorem shearUpperCLM_mul_shearLowerCLM_ne :
    shearUpperCLM * shearLowerCLM ≠ shearLowerCLM * shearUpperCLM := by
  intro hEq
  have hv := congrArg (fun f : EndR2 => f ![1, 0] 0) hEq
  change (shearUpperCLM (shearLowerCLM ![1, 0])) 0 = (shearLowerCLM (shearUpperCLM ![1, 0])) 0 at hv
  simp [shearUpperCLM, shearLowerCLM, shearUpperLin, shearLowerLin] at hv

/-- Mandatory T17 noncommutativity witness on the smooth Lie group `GL2R`. -/
theorem shearUpperGL2_mul_shearLowerGL2_ne :
    shearUpperGL2 * shearLowerGL2 ≠ shearLowerGL2 * shearUpperGL2 := by
  intro hEq
  exact shearUpperCLM_mul_shearLowerCLM_ne (congrArg Units.val hEq)

section MaurerCartanGeneral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]

private lemma mfderiv_mul_left_comp_eq_id (a b x y : G)
    (hy : b * x = y) (hab : a * b = 1) :
    ((mfderiv I I (fun z : G => a * z) y : TangentSpace I y →L[ℝ] TangentSpace I x)).comp
      (mfderiv I I (fun z : G => b * z) x : TangentSpace I x →L[ℝ] TangentSpace I y) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  subst hy
  have M : minSmoothness ℝ 3 ≠ 0 := (lt_of_lt_of_le (by simp) le_minSmoothness).ne'
  have hid : ((fun z : G => a * z) ∘ (fun z : G => b * z)) = id := by
    funext z
    simp [Function.comp_apply, ← mul_assoc, hab]
  have A : mfderiv I I ((fun z : G => a * z) ∘ (fun z : G => b * z)) x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    rw [hid, mfderiv_id]
  rw [mfderiv_comp (I' := I) x
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)] at A
  exact A

/-- The left-trivialized Maurer–Cartan continuous linear equivalence
`θ_g = d(L_{g⁻¹})_g : T_g G ≃L[ℝ] Lie(G)` on any smooth Lie group `G`. -/
def leftMaurerCartanEquiv (g : G) : TangentSpace I g ≃L[ℝ] GroupLieAlgebra I G :=
  ContinuousLinearEquiv.equivOfInverse'
    (mfderiv I I (fun x : G => g⁻¹ * x) g)
    (mfderiv I I (fun x : G => g * x) (1 : G))
    (mfderiv_mul_left_comp_eq_id I g⁻¹ g (1 : G) g (mul_one g) (inv_mul_cancel g))
    (mfderiv_mul_left_comp_eq_id I g g⁻¹ g (1 : G) (inv_mul_cancel g) (mul_inv_cancel g))

theorem leftMaurerCartanEquiv_mulInvariantVectorField (g : G) (v : GroupLieAlgebra I G) :
    leftMaurerCartanEquiv I g (mulInvariantVectorField v g) = v := by
  exact (leftMaurerCartanEquiv I g).apply_symm_apply v

end MaurerCartanGeneral

/-! ## Section 2: Smooth Cartan Geometries, Soldering Quotients, & Cartan Curvature -/

/-- Smooth Cartan-form package on Mathlib smooth manifolds `IsManifold`.
It records the bundle map, a smooth right action, isotropy inclusion, adjoint action, and an
equivariant pointwise linear isomorphism `ω : TP ≃ 𝔤` whose kernel over `d(proj)` is `𝔥`.
The generic structure does not include principal-bundle axioms. The concrete homothety model has
a separate theorem proving free and transitive action on each fiber; smooth local trivializations
are not part of this package. -/
structure SmoothCartanGeometry
    (EP EM : Type*) [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    (HP HM : Type*) [TopologicalSpace HP] [TopologicalSpace HM]
    (IP : ModelWithCorners ℝ EP HP) (IM : ModelWithCorners ℝ EM HM)
    (P M : Type*) [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    (H : Type*) [Group H]
    (𝔤 𝔥 : Type*) [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥] where
  smoothP : IsManifold IP (minSmoothness ℝ 3) P
  smoothM : IsManifold IM (minSmoothness ℝ 3) M
  proj : P → M
  contMDiff_proj : ContMDiff IP IM (minSmoothness ℝ 3) proj
  rightAct : H → P → P
  rightAct_one : ∀ p : P, rightAct 1 p = p
  rightAct_mul : ∀ h₁ h₂ : H, ∀ p : P, rightAct (h₁ * h₂) p = rightAct h₂ (rightAct h₁ p)
  contMDiff_rightAct : ∀ h : H, ContMDiff IP IP (minSmoothness ℝ 3) (rightAct h)
  proj_rightAct : ∀ (h : H) (p : P), proj (rightAct h p) = proj p
  iotaH : 𝔥 →ₗ⁅ℝ⁆ 𝔤
  iotaH_injective : Function.Injective iotaH
  AdH : H → 𝔤 →ₗ⁅ℝ⁆ 𝔤
  AdH_one : ∀ X : 𝔤, AdH 1 X = X
  AdH_mul : ∀ (h₁ h₂ : H) (X : 𝔤), AdH (h₁ * h₂) X = AdH h₁ (AdH h₂ X)
  fundamentalVec : 𝔥 → ∀ p : P, TangentSpace IP p
  mfderiv_proj_fundamentalVec : ∀ (A : 𝔥) (p : P),
    mfderiv IP IM proj p (fundamentalVec A p) = 0
  omega : ∀ p : P, TangentSpace IP p ≃L[ℝ] 𝔤
  omega_fundamental : ∀ (A : 𝔥) (p : P), omega p (fundamentalVec A p) = iotaH A
  omega_equivariant : ∀ (h : H) (p : P) (v : TangentSpace IP p),
    omega (rightAct h p) (mfderiv IP IP (rightAct h) p v) = AdH h⁻¹ (omega p v)
  ker_proj_eq_vertical : ∀ (p : P) (v : TangentSpace IP p),
    mfderiv IP IM proj p v = 0 ↔ omega p v ∈ iotaH.range

section LocalPrincipalOrbit

variable {EP EM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HP HM : Type*} [TopologicalSpace HP] [TopologicalSpace HM]
  {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
  {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [Group H] [TopologicalSpace H]
  {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]

/-- At each point, the Cartan fundamental-vector map identifies the isotropy
Lie algebra with the vertical tangent space. The reverse inclusion follows
from the kernel characterization and the pointwise Cartan isomorphism. -/
theorem fundamentalVec_range_eq_proj_kernel
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) :
    Set.range (fun A : 𝔥 => C.fundamentalVec A p) =
      (mfderiv IP IM C.proj p).toLinearMap.ker := by
  ext v
  change (∃ A : 𝔥, C.fundamentalVec A p = v) ↔
    (mfderiv IP IM C.proj p).toLinearMap v = 0
  constructor
  · rintro ⟨A, rfl⟩
    exact C.mfderiv_proj_fundamentalVec A p
  · intro hv
    have hvertical : C.omega p v ∈ C.iotaH.range :=
      (C.ker_proj_eq_vertical p v).mp hv
    obtain ⟨A, hA⟩ := hvertical
    refine ⟨A, ?_⟩
    apply (C.omega p).injective
    rw [C.omega_fundamental]
    exact hA

/-- A local bundle chart whose fiber coordinate transforms by right multiplication
forces a unique right-action element between any two points in the same charted
fiber. This is a conditional local torsor theorem: the pretrivialization and
its action-compatibility law are explicit inputs, so it does not assert that an
arbitrary `SmoothCartanGeometry` already has principal-bundle charts. -/
theorem local_chart_right_action_unique
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e : Bundle.Pretrivialization H C.proj)
    (hchart : ∀ (h : H) (p : P), p ∈ e.source →
      e (C.rightAct h p) = (C.proj p, (e p).2 * h))
    (p q : P) (hp : p ∈ e.source) (hq : q ∈ e.source)
    (hbase : C.proj p = C.proj q) :
    ∃! h : H, C.rightAct h p = q := by
  let hpCoord := (e p).2
  let hqCoord := (e q).2
  let h := hpCoord⁻¹ * hqCoord
  have hactSource : C.rightAct h p ∈ e.source := by
    rw [e.mem_source, C.proj_rightAct]
    exact (e.mem_source.mp hp)
  have hcharts : e (C.rightAct h p) = e q := by
    calc
      e (C.rightAct h p) = (C.proj p, (e p).2 * h) := hchart h p hp
      _ = (C.proj q, (e q).2) := by
        dsimp [h, hpCoord, hqCoord]
        rw [hbase]
        congr 1
        group
      _ = e q := e.mk_proj_snd hq
  refine ⟨h, ?_, ?_⟩
  · calc
      C.rightAct h p = e.toPartialEquiv.symm (e (C.rightAct h p)) :=
        (e.symm_apply_apply hactSource).symm
      _ = e.toPartialEquiv.symm (e q) := congrArg e.toPartialEquiv.symm hcharts
      _ = q := e.symm_apply_apply hq
  · intro h' hh'
    have h'chart : e (C.rightAct h' p) = e q := by rw [hh']
    have hsecond : (e p).2 * h' = (e q).2 := by
      have hc := congrArg Prod.snd h'chart
      change (e (C.rightAct h' p)).2 = (e q).2 at hc
      rw [hchart h' p hp] at hc
      exact hc
    dsimp [h, hpCoord, hqCoord]
    calc
      h' = ((e p).2)⁻¹ * ((e p).2 * h') := by group
      _ = ((e p).2)⁻¹ * (e q).2 := by rw [hsecond]
      _ = (e p).2⁻¹ * (e q).2 := rfl

/-- A covering family of action-compatible local bundle charts makes every fiber a right
`H`-torsor: any two points in one fiber are related by exactly one group element. The chart
cover and its equivariance law are explicit hypotheses; this theorem does not silently equip an
arbitrary `SmoothCartanGeometry` with a principal-bundle atlas. -/
theorem principal_atlas_action_transitive_unique
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (atlas : Set (Bundle.Pretrivialization H C.proj))
    (hcover : ∀ p : P, ∃ e, e ∈ atlas ∧ p ∈ e.source)
    (hchart : ∀ (e : Bundle.Pretrivialization H C.proj), e ∈ atlas →
      ∀ (h : H) (p : P), p ∈ e.source →
        e (C.rightAct h p) = (C.proj p, (e p).2 * h))
    (p q : P) (hbase : C.proj p = C.proj q) :
    ∃! h : H, C.rightAct h p = q := by
  obtain ⟨e, he, hp⟩ := hcover p
  have hq : q ∈ e.source := by
    rw [e.mem_source, ← hbase]
    exact e.mem_source.mp hp
  exact local_chart_right_action_unique C e (hchart e he) p q hp hq hbase

end LocalPrincipalOrbit

section SolderingQuotient

variable {EP EM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HP HM : Type*} [TopologicalSpace HP] [TopologicalSpace HM]
  {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
  {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [Group H]
  {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]

/-- The Cartan connection induces a canonical soldering isomorphism
`TₚP / ker(dπₚ) ≃ₗ[ℝ] 𝔤 / 𝔥` at every point `p ∈ P`. -/
def cartanTangentQuotientEquiv (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) :
    (TangentSpace IP p ⧸ LinearMap.ker (mfderiv IP IM C.proj p).toLinearMap) ≃ₗ[ℝ]
      (𝔤 ⧸ C.iotaH.range.toSubmodule) :=
  let kerProj : Submodule ℝ (TangentSpace IP p) :=
    LinearMap.ker (mfderiv IP IM C.proj p).toLinearMap
  let Hsub : Submodule ℝ 𝔤 := C.iotaH.range.toSubmodule
  let fwd : (TangentSpace IP p ⧸ kerProj) →ₗ[ℝ] (𝔤 ⧸ Hsub) :=
    Submodule.liftQ kerProj (Hsub.mkQ.comp (C.omega p).toLinearMap) fun v hv => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact (C.ker_proj_eq_vertical p v).mp (LinearMap.mem_ker.mp hv)
  let bwd : (𝔤 ⧸ Hsub) →ₗ[ℝ] (TangentSpace IP p ⧸ kerProj) :=
    Submodule.liftQ Hsub (kerProj.mkQ.comp (C.omega p).symm.toLinearMap) fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      have hmem : C.omega p ((C.omega p).symm x) ∈ C.iotaH.range := by
        rw [(C.omega p).apply_symm_apply x]
        exact hx
      exact (C.ker_proj_eq_vertical p ((C.omega p).symm x)).mpr hmem
  LinearEquiv.ofLinearMap fwd bwd
    (by
      refine LinearMap.ext fun q => Submodule.Quotient.induction_on Hsub q fun x => ?_
      change Submodule.Quotient.mk (C.omega p ((C.omega p).symm x)) = Submodule.Quotient.mk x
      rw [(C.omega p).apply_symm_apply x])
    (by
      refine LinearMap.ext fun q => Submodule.Quotient.induction_on kerProj q fun v => ?_
      change Submodule.Quotient.mk ((C.omega p).symm (C.omega p v)) = Submodule.Quotient.mk v
      rw [(C.omega p).symm_apply_apply v])

/-- The tangent-quotient soldering map sends the class of a tangent vector to
the class of its Cartan-coordinate value in `𝔤 / 𝔥`. -/
theorem cartanTangentQuotientEquiv_apply_mk
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P)
    (v : TangentSpace IP p) :
    cartanTangentQuotientEquiv C p (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (C.omega p v) := by
  simp only [cartanTangentQuotientEquiv, LinearEquiv.coe_ofLinearMap,
    Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
  rfl

/-- When the bundle projection is a submersion at `p` (expressed by
surjectivity of its tangent map), the Cartan soldering identifies the base
tangent space itself with `𝔤 / 𝔥`. This composes the first-isomorphism
equivalence for `dπₚ` with the existing Cartan quotient equivalence. -/
noncomputable def cartanBaseTangentEquiv
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P)
    (hsubmersion : Function.Surjective
      (mfderiv IP IM C.proj p).toLinearMap) :
    TangentSpace IM (C.proj p) ≃ₗ[ℝ] (𝔤 ⧸ C.iotaH.range.toSubmodule) :=
  ((mfderiv IP IM C.proj p).toLinearMap.quotKerEquivOfSurjective hsubmersion).symm.trans
    (cartanTangentQuotientEquiv C p)

/-- On a tangent vector lifted through `dπₚ`, the base-tangent soldering map
is exactly the quotient class of its Cartan-coordinate value. -/
theorem cartanBaseTangentEquiv_apply_mfderiv
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P)
    (hsubmersion : Function.Surjective
      (mfderiv IP IM C.proj p).toLinearMap)
    (v : TangentSpace IP p) :
    cartanBaseTangentEquiv C p hsubmersion (mfderiv IP IM C.proj p v) =
      Submodule.Quotient.mk (C.omega p v) := by
  let f := (mfderiv IP IM C.proj p).toLinearMap
  let e := f.quotKerEquivOfSurjective hsubmersion
  have he : e.symm (f v) = Submodule.Quotient.mk v := by
    apply e.injective
    simp [e, f]
  change cartanTangentQuotientEquiv C p (e.symm (f v)) = _
  rw [he, cartanTangentQuotientEquiv_apply_mk]

end SolderingQuotient

section CurvatureForms

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners ℝ EP HP)
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

/-- Coordinate-free Cartan exterior derivative `(dω)(X, Y)(p) := X(ω(Y))(p) - Y(ω(X))(p) - ω([X, Y])(p)`
using native Mathlib `mfderiv`, `VectorField.mlieBracket`, and a linear-topological model chart
`toModel : 𝔤 ≃L[ℝ] E𝔤`. -/
def cartanExteriorDerivWith
    {𝔤 E𝔤 : Type*} [TopologicalSpace 𝔤] [AddCommGroup 𝔤] [Module ℝ 𝔤]
    [NormedAddCommGroup E𝔤] [NormedSpace ℝ E𝔤]
    (toModel : 𝔤 ≃L[ℝ] E𝔤)
    (form : ∀ p : P, TangentSpace IP p →L[ℝ] 𝔤)
    (X Y : Π p : P, TangentSpace IP p) (p : P) : 𝔤 :=
  toModel.symm
    (NormedSpace.fromTangentSpace (toModel (form p (Y p)))
      (mfderiv IP 𝓘(ℝ, E𝔤) (fun q => toModel (form q (Y q))) p (X p)) -
     NormedSpace.fromTangentSpace (toModel (form p (X p)))
      (mfderiv IP 𝓘(ℝ, E𝔤) (fun q => toModel (form q (X q))) p (Y p))) -
  form p (VectorField.mlieBracket IP X Y p)

/-- Cartan curvature 2-form `Ω_ω(X, Y)(p) := (dω)(X, Y)(p) + [ω(X), ω(Y)]` via `toModel`. -/
def cartanCurvatureFormWith
    {𝔤 E𝔤 : Type*} [TopologicalSpace 𝔤] [AddCommGroup 𝔤] [Module ℝ 𝔤] [Bracket 𝔤 𝔤]
    [NormedAddCommGroup E𝔤] [NormedSpace ℝ E𝔤]
    (toModel : 𝔤 ≃L[ℝ] E𝔤)
    (form : ∀ p : P, TangentSpace IP p →L[ℝ] 𝔤)
    (X Y : Π p : P, TangentSpace IP p) (p : P) : 𝔤 :=
  cartanExteriorDerivWith IP toModel form X Y p + ⁅form p (X p), form p (Y p)⁆

section NormedTarget

variable {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [Bracket 𝔤 𝔤]

/-- Coordinate-free Cartan exterior derivative `(dω)(X, Y)(p) := X(ω(Y))(p) - Y(ω(X))(p) - ω([X, Y])(p)`
using native Mathlib `mfderiv` and `VectorField.mlieBracket`. -/
def cartanExteriorDeriv (form : ∀ p : P, TangentSpace IP p →L[ℝ] 𝔤)
    (X Y : Π p : P, TangentSpace IP p) (p : P) : 𝔤 :=
  cartanExteriorDerivWith IP (ContinuousLinearEquiv.refl ℝ 𝔤) form X Y p

/-- Cartan curvature 2-form `Ω_ω(X, Y)(p) := (dω)(X, Y)(p) + [ω(X), ω(Y)]`. -/
def cartanCurvatureForm (form : ∀ p : P, TangentSpace IP p →L[ℝ] 𝔤)
    (X Y : Π p : P, TangentSpace IP p) (p : P) : 𝔤 :=
  cartanCurvatureFormWith IP (ContinuousLinearEquiv.refl ℝ 𝔤) form X Y p

/-- Cartan torsion 2-form `Θ_ω(X, Y)(p)` obtained by projecting `Ω_ω(X, Y)(p)` modulo `Hsub ⊂ 𝔤`. -/
def cartanTorsionForm (Hsub : Submodule ℝ 𝔤)
    (form : ∀ p : P, TangentSpace IP p →L[ℝ] 𝔤)
    (X Y : Π p : P, TangentSpace IP p) (p : P) : 𝔤 ⧸ Hsub :=
  Hsub.mkQ (cartanCurvatureForm IP form X Y p)

end NormedTarget

private lemma fromTangentSpace_mfderiv_eq_zero_of_const
    {E𝔤 : Type*} [NormedAddCommGroup E𝔤] [NormedSpace ℝ E𝔤]
    (f : P → E𝔤) (c : E𝔤) (hf : f = Function.const P c)
    (p : P) (v : TangentSpace IP p) :
    NormedSpace.fromTangentSpace (f p) (mfderiv IP 𝓘(ℝ, E𝔤) f p v) = 0 := by
  subst hf
  rw [show Function.const P c = fun _ : P => c from rfl, mfderiv_const, zero_apply, map_zero]

private lemma cartanExteriorDerivWith_eq_neg_bracket_of_const
    {𝔤 E𝔤 : Type*} [TopologicalSpace 𝔤] [AddCommGroup 𝔤] [Module ℝ 𝔤]
    [NormedAddCommGroup E𝔤] [NormedSpace ℝ E𝔤]
    (toModel : 𝔤 ≃L[ℝ] E𝔤)
    (form : ∀ p : P, TangentSpace IP p →L[ℝ] 𝔤)
    (X Y : Π p : P, TangentSpace IP p) (cX cY : E𝔤)
    (hX : (fun q => toModel (form q (X q))) = Function.const P cX)
    (hY : (fun q => toModel (form q (Y q))) = Function.const P cY)
    (p : P) :
    cartanExteriorDerivWith IP toModel form X Y p =
      -form p (VectorField.mlieBracket IP X Y p) := by
  have d1 := fromTangentSpace_mfderiv_eq_zero_of_const IP _ cY hY p (X p)
  have d2 := fromTangentSpace_mfderiv_eq_zero_of_const IP _ cX hX p (Y p)
  unfold cartanExteriorDerivWith
  rw [d1, d2, sub_self, map_zero, zero_sub]

theorem cartanCurvatureFormWith_skew
    {𝔤 E𝔤 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [NormedAddCommGroup E𝔤] [NormedSpace ℝ E𝔤]
    (toModel : 𝔤 ≃L[ℝ] E𝔤)
    (form : ∀ p : P, TangentSpace IP p →L[ℝ] 𝔤)
    (X Y : Π p : P, TangentSpace IP p) (p : P) :
    cartanCurvatureFormWith IP toModel form Y X p =
      -cartanCurvatureFormWith IP toModel form X Y p := by
  unfold cartanCurvatureFormWith cartanExteriorDerivWith
  rw [VectorField.mlieBracket_swap, Pi.neg_apply, map_neg, map_sub, map_sub]
  rw [(lie_skew (form p (Y p)) (form p (X p))).symm]
  abel

theorem cartanCurvatureFormWith_constantVectorField
    {𝔤 E𝔤 : Type*} [TopologicalSpace 𝔤] [AddCommGroup 𝔤] [Module ℝ 𝔤] [Bracket 𝔤 𝔤]
    [NormedAddCommGroup E𝔤] [NormedSpace ℝ E𝔤]
    (toModel : 𝔤 ≃L[ℝ] E𝔤)
    (omega : ∀ p : P, TangentSpace IP p ≃L[ℝ] 𝔤)
    (v w : 𝔤) (p : P) :
    let U : 𝔤 → Π q : P, TangentSpace IP q := fun u q => (omega q).symm u
    cartanCurvatureFormWith IP toModel (fun q => (omega q).toContinuousLinearMap) (U v) (U w) p =
      ⁅v, w⁆ - omega p (VectorField.mlieBracket IP (U v) (U w) p) := by
  dsimp only
  let U : 𝔤 → Π q : P, TangentSpace IP q := fun u q => (omega q).symm u
  have hU : ∀ u : 𝔤,
      (fun q => toModel (((omega q).toContinuousLinearMap) (U u q))) =
        Function.const P (toModel u) := by
    intro u
    funext q
    rw [ContinuousLinearEquiv.coe_coe, (omega q).apply_symm_apply u]
    rfl
  have hval : ∀ u : 𝔤, (omega p).toContinuousLinearMap (U u p) = u := by
    intro u
    exact (omega p).apply_symm_apply u
  unfold cartanCurvatureFormWith
  rw [cartanExteriorDerivWith_eq_neg_bracket_of_const IP toModel
    (fun q => (omega q).toContinuousLinearMap) (U v) (U w) (toModel v) (toModel w)
    (hU v) (hU w) p, hval v, hval w]
  change -(omega p (VectorField.mlieBracket IP (U v) (U w) p)) + ⁅v, w⁆ =
    ⁅v, w⁆ - omega p (VectorField.mlieBracket IP (U v) (U w) p)
  abel

theorem cartanCurvatureForm_constantVectorField
    {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [Bracket 𝔤 𝔤]
    (omega : ∀ p : P, TangentSpace IP p ≃L[ℝ] 𝔤)
    (v w : 𝔤) (p : P) :
    let U : 𝔤 → Π q : P, TangentSpace IP q := fun u q => (omega q).symm u
    cartanCurvatureForm IP (fun q => (omega q).toContinuousLinearMap) (U v) (U w) p =
      ⁅v, w⁆ - omega p (VectorField.mlieBracket IP (U v) (U w) p) :=
  cartanCurvatureFormWith_constantVectorField IP (ContinuousLinearEquiv.refl ℝ 𝔤) omega v w p

end CurvatureForms

section MaurerCartanFlatness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]

/-- **Universal Kleinian Maurer–Cartan Flatness Theorem**: On any smooth Lie group `G`,
the Cartan curvature 2-form of the left Maurer–Cartan form evaluates identically to `0` on
left-invariant vector fields (`dθ + [θ, θ] = 0`). -/
theorem maurerCartan_cartanCurvature_eq_zero
    (v w : GroupLieAlgebra I G) (g : G) :
    cartanCurvatureFormWith I (tangentSpaceCastModel I (1 : G))
      (fun q => (leftMaurerCartanEquiv I q).toContinuousLinearMap)
      (mulInvariantVectorField v) (mulInvariantVectorField w) g = 0 := by
  have hconst : ∀ u : GroupLieAlgebra I G,
      (fun q => (tangentSpaceCastModel I (1 : G))
        (((leftMaurerCartanEquiv I q).toContinuousLinearMap) (mulInvariantVectorField u q))) =
        Function.const G (tangentSpaceCastModel I (1 : G) u) := by
    intro u
    funext q
    rw [ContinuousLinearEquiv.coe_coe, leftMaurerCartanEquiv_mulInvariantVectorField]
    rfl
  have hval : ∀ u : GroupLieAlgebra I G,
      (leftMaurerCartanEquiv I g).toContinuousLinearMap (mulInvariantVectorField u g) = u := by
    intro u
    exact leftMaurerCartanEquiv_mulInvariantVectorField I g u
  have hbr :
      VectorField.mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) g =
        mulInvariantVectorField ⁅v, w⁆ g := by
    rw [← mulInvariantVector_mlieBracket v w, GroupLieAlgebra.bracket_def]
  unfold cartanCurvatureFormWith
  rw [cartanExteriorDerivWith_eq_neg_bracket_of_const I (tangentSpaceCastModel I (1 : G))
    (fun q => (leftMaurerCartanEquiv I q).toContinuousLinearMap)
    (mulInvariantVectorField v) (mulInvariantVectorField w)
    ((tangentSpaceCastModel I (1 : G)) v) ((tangentSpaceCastModel I (1 : G)) w)
    (hconst v) (hconst w) g, hval v, hval w]
  change -(leftMaurerCartanEquiv I g
    (VectorField.mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) g)) +
      ⁅v, w⁆ = 0
  rw [hbr]
  rw [leftMaurerCartanEquiv_mulInvariantVectorField]
  exact neg_add_cancel ⁅v, w⁆

/-- Specialization of Maurer–Cartan flatness to the concrete noncommutative Banach Lie group
`GL2R = ((Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))ˣ`. -/
theorem gl2R_maurerCartan_flat
    (v w : GroupLieAlgebra 𝓘(ℝ, EndR2) GL2R) (g : GL2R) :
    cartanCurvatureFormWith 𝓘(ℝ, EndR2) (tangentSpaceCastModel 𝓘(ℝ, EndR2) (1 : GL2R))
      (fun q => (leftMaurerCartanEquiv 𝓘(ℝ, EndR2) q).toContinuousLinearMap)
      (mulInvariantVectorField v) (mulInvariantVectorField w) g = 0 :=
  maurerCartan_cartanCurvature_eq_zero 𝓘(ℝ, EndR2) v w g

end MaurerCartanFlatness

/-! ## Section 3: Trivial Smooth Principal Bundle `ℝ² × ℝ → ℝ²`: Flat vs. Curved Cartan Geometry -/

/-- Abelian 1-dimensional Lie algebra `𝔥 ≅ ℝ` of vertical scale transformations. -/
@[ext]
structure HomothetyH where
  val : ℝ

instance instZeroHomothetyH : Zero HomothetyH := ⟨⟨0⟩⟩
instance instAddHomothetyH : Add HomothetyH := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance instNegHomothetyH : Neg HomothetyH := ⟨fun a => ⟨-a.val⟩⟩
instance instSubHomothetyH : Sub HomothetyH := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance instSMulRealHomothetyH : SMul ℝ HomothetyH := ⟨fun c a => ⟨c * a.val⟩⟩

@[simp] private lemma homothetyH_zero_val : (0 : HomothetyH).val = 0 := rfl
@[simp] private lemma homothetyH_add_val (a b : HomothetyH) : (a + b).val = a.val + b.val := rfl
@[simp] private lemma homothetyH_neg_val (a : HomothetyH) : (-a).val = -a.val := rfl
@[simp] private lemma homothetyH_sub_val (a b : HomothetyH) : (a - b).val = a.val - b.val := rfl
@[simp] private lemma homothetyH_smul_val (c : ℝ) (a : HomothetyH) : (c • a).val = c * a.val := rfl

instance instAddCommGroupHomothetyH : AddCommGroup HomothetyH where
  add_assoc a b c := by ext; exact add_assoc _ _ _
  zero_add a := by ext; exact zero_add _
  add_zero a := by ext; exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext; exact neg_add_cancel _
  add_comm a b := by ext; exact add_comm _ _
  sub_eq_add_neg a b := by ext; exact sub_eq_add_neg _ _

instance instModuleRealHomothetyH : Module ℝ HomothetyH where
  one_smul a := by ext; exact one_mul _
  mul_smul c d a := by ext; exact mul_assoc _ _ _
  smul_zero c := by ext; exact mul_zero _
  smul_add c a b := by ext; exact mul_add _ _ _
  add_smul c d a := by ext; exact add_mul _ _ _
  zero_smul a := by ext; exact zero_mul _

private def homothetyHLinearEquiv : HomothetyH ≃ₗ[ℝ] ℝ where
  toFun := HomothetyH.val
  invFun x := ⟨x⟩
  left_inv a := by cases a; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance instModuleFiniteRealHomothetyH : Module.Finite ℝ HomothetyH :=
  Module.Finite.equiv homothetyHLinearEquiv.symm

instance instNormedAddCommGroupHomothetyH : NormedAddCommGroup HomothetyH :=
  NormedAddCommGroup.induced HomothetyH ℝ homothetyHLinearEquiv.toAddEquiv homothetyHLinearEquiv.injective

instance instNormedSpaceRealHomothetyH : NormedSpace ℝ HomothetyH where
  norm_smul_le c a := by
    change ‖c * a.val‖ ≤ ‖c‖ * ‖a.val‖
    rw [norm_mul]

instance instBracketHomothetyH : Bracket HomothetyH HomothetyH := ⟨fun _ _ => 0⟩

private lemma homothetyH_bracket_def (x y : HomothetyH) : ⁅x, y⁆ = 0 := rfl

instance instLieRingHomothetyH : LieRing HomothetyH where
  add_lie _ _ _ := by simp [homothetyH_bracket_def]
  lie_add _ _ _ := by simp [homothetyH_bracket_def]
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp [homothetyH_bracket_def]

instance instLieAlgebraRealHomothetyH : LieAlgebra ℝ HomothetyH where
  lie_smul _ _ _ := by simp [homothetyH_bracket_def]

/-- The 3-dimensional non-abelian homothety Lie algebra `𝔤 = ℝ² ⋊ ℝ` with bracket
`⁅(u, a), (v, b)⁆ = (a • v - b • u, 0)`. -/
@[ext]
structure HomothetyLieAlg where
  trans : Fin 2 → ℝ
  scale : ℝ

instance instZeroHomothetyLieAlg : Zero HomothetyLieAlg := ⟨⟨0, 0⟩⟩
instance instAddHomothetyLieAlg : Add HomothetyLieAlg := ⟨fun x y => ⟨x.trans + y.trans, x.scale + y.scale⟩⟩
instance instNegHomothetyLieAlg : Neg HomothetyLieAlg := ⟨fun x => ⟨-x.trans, -x.scale⟩⟩
instance instSubHomothetyLieAlg : Sub HomothetyLieAlg := ⟨fun x y => ⟨x.trans - y.trans, x.scale - y.scale⟩⟩
instance instSMulRealHomothetyLieAlg : SMul ℝ HomothetyLieAlg := ⟨fun c x => ⟨c • x.trans, c * x.scale⟩⟩

@[simp] private lemma homothety_zero_trans : (0 : HomothetyLieAlg).trans = 0 := rfl
@[simp] private lemma homothety_zero_scale : (0 : HomothetyLieAlg).scale = 0 := rfl
@[simp] private lemma homothety_add_trans (a b : HomothetyLieAlg) :
    (a + b).trans = a.trans + b.trans := rfl
@[simp] private lemma homothety_add_scale (a b : HomothetyLieAlg) :
    (a + b).scale = a.scale + b.scale := rfl
@[simp] private lemma homothety_neg_trans (a : HomothetyLieAlg) : (-a).trans = -a.trans := rfl
@[simp] private lemma homothety_neg_scale (a : HomothetyLieAlg) : (-a).scale = -a.scale := rfl
@[simp] private lemma homothety_sub_trans (a b : HomothetyLieAlg) :
    (a - b).trans = a.trans - b.trans := rfl
@[simp] private lemma homothety_sub_scale (a b : HomothetyLieAlg) :
    (a - b).scale = a.scale - b.scale := rfl
@[simp] private lemma homothety_smul_trans (c : ℝ) (a : HomothetyLieAlg) :
    (c • a).trans = c • a.trans := rfl
@[simp] private lemma homothety_smul_scale (c : ℝ) (a : HomothetyLieAlg) :
    (c • a).scale = c * a.scale := rfl

instance instAddCommGroupHomothetyLieAlg : AddCommGroup HomothetyLieAlg where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]

instance instModuleRealHomothetyLieAlg : Module ℝ HomothetyLieAlg where
  one_smul a := by ext <;> simp
  mul_smul c d a := by ext <;> simp [mul_assoc]
  smul_zero c := by ext <;> simp
  smul_add c a b := by ext <;> simp [mul_add]
  add_smul c d a := by ext <;> simp [add_mul]
  zero_smul a := by ext <;> simp

private def homothetyLieAlgLinearEquiv : HomothetyLieAlg ≃ₗ[ℝ] ((Fin 2 → ℝ) × ℝ) where
  toFun x := (x.trans, x.scale)
  invFun p := ⟨p.1, p.2⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance instModuleFiniteRealHomothetyLieAlg : Module.Finite ℝ HomothetyLieAlg :=
  Module.Finite.equiv homothetyLieAlgLinearEquiv.symm

instance instNormedAddCommGroupHomothetyLieAlg : NormedAddCommGroup HomothetyLieAlg :=
  NormedAddCommGroup.induced HomothetyLieAlg ((Fin 2 → ℝ) × ℝ)
    homothetyLieAlgLinearEquiv.toAddEquiv homothetyLieAlgLinearEquiv.injective

instance instNormedSpaceRealHomothetyLieAlg : NormedSpace ℝ HomothetyLieAlg where
  norm_smul_le c x := by
    change ‖(c • x.trans, c * x.scale)‖ ≤ ‖c‖ * ‖(x.trans, x.scale)‖
    change ‖c • (x.trans, x.scale)‖ ≤ ‖c‖ * ‖(x.trans, x.scale)‖
    rw [norm_smul]

instance instBracketHomothetyLieAlg : Bracket HomothetyLieAlg HomothetyLieAlg :=
  ⟨fun u v => ⟨u.scale • v.trans - v.scale • u.trans, 0⟩⟩

@[simp] private lemma homothety_bracket_trans (u v : HomothetyLieAlg) :
    ⁅u, v⁆.trans = u.scale • v.trans - v.scale • u.trans := rfl

@[simp] private lemma homothety_bracket_scale (u v : HomothetyLieAlg) :
    ⁅u, v⁆.scale = 0 := rfl

instance instLieRingHomothetyLieAlg : LieRing HomothetyLieAlg where
  add_lie u v w := by
    ext i <;> simp
    ring
  lie_add u v w := by
    ext i <;> simp
    ring
  lie_self u := by
    ext <;> simp
  leibniz_lie u v w := by
    ext i <;> simp
    ring

instance instLieAlgebraRealHomothetyLieAlg : LieAlgebra ℝ HomothetyLieAlg where
  lie_smul c u v := by
    ext i <;> simp
    ring

/-- Non-abelian Lie bracket witness on `HomothetyLieAlg`. -/
theorem homothetyLieAlg_nonabelian :
    ⁅(⟨0, 1⟩ : HomothetyLieAlg), (⟨![1, 0], 0⟩ : HomothetyLieAlg)⁆ ≠ 0 := by
  intro h0
  have h := congrArg (fun x : HomothetyLieAlg => x.trans 0) h0
  simp at h

private def iotaHomothety : HomothetyH →ₗ⁅ℝ⁆ HomothetyLieAlg where
  toFun a := ⟨0, a.val⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  map_lie' := by
    intro x y
    ext <;> simp [homothetyH_bracket_def]

private lemma iotaHomothety_injective : Function.Injective iotaHomothety := by
  intro a b h
  ext
  exact congrArg HomothetyLieAlg.scale h

private def AdHomothety (t : Multiplicative ℝ) : HomothetyLieAlg →ₗ⁅ℝ⁆ HomothetyLieAlg where
  toFun v := ⟨Real.exp (Multiplicative.toAdd t) • v.trans, v.scale⟩
  map_add' _ _ := by ext <;> simp [mul_add]
  map_smul' c v := by ext <;> simp [mul_left_comm]
  map_lie' := by
    intro u v
    ext i
    · simp [mul_sub]
      ring
    · simp

private def prodToHomothetyCLM : ((Fin 2 → ℝ) × ℝ) →L[ℝ] HomothetyLieAlg :=
  ({ toFun := fun p => ⟨p.1, p.2⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : ((Fin 2 → ℝ) × ℝ) →ₗ[ℝ] HomothetyLieAlg).toContinuousLinearMap

private def homothetyCartanOmegaModel (κ : ℝ) (p : (Fin 2 → ℝ) × ℝ) :
    ((Fin 2 → ℝ) × ℝ) ≃L[ℝ] HomothetyLieAlg :=
  let fwdLin : ((Fin 2 → ℝ) × ℝ) →ₗ[ℝ] HomothetyLieAlg :=
    { toFun := fun v => ⟨Real.exp (-p.2) • v.1, v.2 + κ * (p.1 0 * v.1 1 - p.1 1 * v.1 0)⟩
      map_add' := fun u v => by
        ext i <;> simp only [homothety_add_trans, homothety_add_scale, Prod.fst_add, Prod.snd_add,
          Pi.add_apply]
        · simp [mul_add]
        · ring
      map_smul' := fun c v => by
        ext i <;> simp only [homothety_smul_trans, homothety_smul_scale, Prod.smul_fst, Prod.smul_snd,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring }
  let bwdLin : HomothetyLieAlg →ₗ[ℝ] ((Fin 2 → ℝ) × ℝ) :=
    { toFun := fun g =>
        (Real.exp p.2 • g.trans,
          g.scale - κ * Real.exp p.2 * (p.1 0 * g.trans 1 - p.1 1 * g.trans 0))
      map_add' := fun g₁ g₂ => by
        refine Prod.ext (funext fun i => ?_) ?_
        · simp [mul_add]
        · simp only [Prod.snd_add, homothety_add_scale, homothety_add_trans, Pi.add_apply]
          ring
      map_smul' := fun c g => by
        refine Prod.ext (funext fun i => ?_) ?_
        · simp only [Prod.smul_fst, homothety_smul_trans, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply]
          ring
        · simp only [Prod.smul_snd, homothety_smul_scale, homothety_smul_trans, Pi.smul_apply,
            smul_eq_mul, RingHom.id_apply]
          ring }
  let fwdCLM : ((Fin 2 → ℝ) × ℝ) →L[ℝ] HomothetyLieAlg := fwdLin.toContinuousLinearMap
  let bwdCLM : HomothetyLieAlg →L[ℝ] ((Fin 2 → ℝ) × ℝ) := bwdLin.toContinuousLinearMap
  ContinuousLinearEquiv.equivOfInverse' fwdCLM bwdCLM
    (by
      refine ContinuousLinearMap.ext fun g => HomothetyLieAlg.ext (funext fun i => ?_) ?_
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
        change Real.exp (-p.2) * (Real.exp p.2 * g.trans i) = g.trans i
        have hexp : Real.exp (-p.2) * Real.exp p.2 = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        rw [← mul_assoc, hexp, one_mul]
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
        change g.scale - κ * Real.exp p.2 * (p.1 0 * g.trans 1 - p.1 1 * g.trans 0) +
            κ * (p.1 0 * (Real.exp p.2 * g.trans 1) - p.1 1 * (Real.exp p.2 * g.trans 0)) =
          g.scale
        ring)
    (by
      refine ContinuousLinearMap.ext fun v => Prod.ext (funext fun i => ?_) ?_
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
        change Real.exp p.2 * (Real.exp (-p.2) * v.1 i) = v.1 i
        have hexp : Real.exp p.2 * Real.exp (-p.2) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        rw [← mul_assoc, hexp, one_mul]
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
        have hexp : Real.exp p.2 * Real.exp (-p.2) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        change v.2 + κ * (p.1 0 * v.1 1 - p.1 1 * v.1 0) -
            κ * Real.exp p.2 * (p.1 0 * (Real.exp (-p.2) * v.1 1) - p.1 1 * (Real.exp (-p.2) * v.1 0)) =
          v.2
        calc
          v.2 + κ * (p.1 0 * v.1 1 - p.1 1 * v.1 0) -
              κ * Real.exp p.2 * (p.1 0 * (Real.exp (-p.2) * v.1 1) - p.1 1 * (Real.exp (-p.2) * v.1 0))
              = v.2 + κ * (p.1 0 * v.1 1 - p.1 1 * v.1 0) -
                  κ * (Real.exp p.2 * Real.exp (-p.2)) * (p.1 0 * v.1 1 - p.1 1 * v.1 0) := by ring
          _ = v.2 := by rw [hexp]; ring)

/-- Explicit smooth Cartan connection family `ω_κ` parametrized by `κ : ℝ` on the trivial principal
dilation bundle `P = ℝ² × ℝ → ℝ²`:
`ω_κ (x, s) (δx, δs) = (e⁻ˢ δx, δs + κ (x₀ δx₁ - x₁ δx₀))`. -/
def homothetyCartanOmega (κ : ℝ) (p : (Fin 2 → ℝ) × ℝ) :
    TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) p ≃L[ℝ] HomothetyLieAlg :=
  (NormedSpace.fromTangentSpace p).trans (homothetyCartanOmegaModel κ p)

@[simp] private lemma homothetyCartanOmegaModel_apply (κ : ℝ) (p v : (Fin 2 → ℝ) × ℝ) :
    homothetyCartanOmegaModel κ p v =
      ⟨Real.exp (-p.2) • v.1, v.2 + κ * (p.1 0 * v.1 1 - p.1 1 * v.1 0)⟩ :=
  rfl

@[simp] theorem homothetyCartanOmega_apply (κ : ℝ) (p : (Fin 2 → ℝ) × ℝ)
    (v : TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) p) :
    homothetyCartanOmega κ p v =
      homothetyCartanOmegaModel κ p (NormedSpace.fromTangentSpace p v) :=
  rfl

/-- Full `SmoothCartanGeometry` package on `P = (Fin 2 → ℝ) × ℝ → M = Fin 2 → ℝ` with structure
group `H = Multiplicative ℝ`, Lie algebras `𝔥 = HomothetyH ↪ 𝔤 = HomothetyLieAlg`, and curvature
parameter `κ : ℝ`. -/
def homothetyCartanGeometry (κ : ℝ) :
    SmoothCartanGeometry
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ)
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ)
      𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, Fin 2 → ℝ)
      ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ)
      (Multiplicative ℝ)
      HomothetyLieAlg HomothetyH where
  smoothP := inferInstance
  smoothM := inferInstance
  proj := Prod.fst
  contMDiff_proj := contDiff_fst.contMDiff
  rightAct t p := (p.1, p.2 + Multiplicative.toAdd t)
  rightAct_one p := by ext <;> simp
  rightAct_mul t₁ t₂ p := by ext <;> simp [add_assoc]
  contMDiff_rightAct t :=
    (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contMDiff
  proj_rightAct _ _ := rfl
  iotaH := iotaHomothety
  iotaH_injective := iotaHomothety_injective
  AdH := AdHomothety
  AdH_one X := by ext <;> simp [AdHomothety]
  AdH_mul t₁ t₂ X := by
    ext <;> simp [AdHomothety, Real.exp_add, mul_assoc]
  fundamentalVec A p := (NormedSpace.fromTangentSpace p).symm (0, A.val)
  mfderiv_proj_fundamentalVec A p := by
    rw [show (Prod.fst : (Fin 2 → ℝ) × ℝ → Fin 2 → ℝ) = ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ from rfl]
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  omega := homothetyCartanOmega κ
  omega_fundamental A p := by
    change homothetyCartanOmegaModel κ p
      (NormedSpace.fromTangentSpace p ((NormedSpace.fromTangentSpace p).symm (0, A.val))) =
      iotaHomothety A
    rw [(NormedSpace.fromTangentSpace p).apply_symm_apply]
    ext i <;> simp [iotaHomothety]
  omega_equivariant t p v := by
    have hact :
        (fun q : (Fin 2 → ℝ) × ℝ => (q.1, q.2 + Multiplicative.toAdd t)) =
          fun q => id q + (0, Multiplicative.toAdd t) := by
      funext q
      exact Prod.ext (add_zero q.1).symm rfl
    have hfd :
        fderiv ℝ (fun q : (Fin 2 → ℝ) × ℝ => (q.1, q.2 + Multiplicative.toAdd t)) p =
          ContinuousLinearMap.id ℝ ((Fin 2 → ℝ) × ℝ) := by
      rw [hact]
      exact ((hasFDerivAt_id p).add_const (0, Multiplicative.toAdd t)).fderiv
    have harg :
        NormedSpace.fromTangentSpace (p.1, p.2 + Multiplicative.toAdd t)
          (mfderiv 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
            (fun q : (Fin 2 → ℝ) × ℝ => (q.1, q.2 + Multiplicative.toAdd t)) p v) =
          NormedSpace.fromTangentSpace p v := by
      let vE : (Fin 2 → ℝ) × ℝ := NormedSpace.fromTangentSpace p v
      have hmfE :
          (mfderiv 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
            (fun q : (Fin 2 → ℝ) × ℝ => (q.1, q.2 + Multiplicative.toAdd t)) p :
            ((Fin 2 → ℝ) × ℝ) →L[ℝ] ((Fin 2 → ℝ) × ℝ)) =
            ContinuousLinearMap.id ℝ ((Fin 2 → ℝ) × ℝ) :=
        mfderiv_eq_fderiv.trans hfd
      exact congrArg (fun T : ((Fin 2 → ℝ) × ℝ) →L[ℝ] ((Fin 2 → ℝ) × ℝ) => T vE) hmfE
    change homothetyCartanOmegaModel κ (p.1, p.2 + Multiplicative.toAdd t)
        (NormedSpace.fromTangentSpace (p.1, p.2 + Multiplicative.toAdd t)
          (mfderiv 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
            (fun q : (Fin 2 → ℝ) × ℝ => (q.1, q.2 + Multiplicative.toAdd t)) p v)) =
      AdHomothety t⁻¹ (homothetyCartanOmegaModel κ p (NormedSpace.fromTangentSpace p v))
    rw [harg]
    ext i
    · change Real.exp (-(p.2 + Multiplicative.toAdd t)) * ((NormedSpace.fromTangentSpace p) v).1 i =
        Real.exp (Multiplicative.toAdd t⁻¹) * (Real.exp (-p.2) * ((NormedSpace.fromTangentSpace p) v).1 i)
      simp only [toAdd_inv, neg_add, Real.exp_add]
      ring
    · rfl
  ker_proj_eq_vertical p v := by
    let vE : (Fin 2 → ℝ) × ℝ := NormedSpace.fromTangentSpace p v
    have hf :
        mfderiv 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, Fin 2 → ℝ) Prod.fst p v = 0 ↔
          vE.1 = (0 : Fin 2 → ℝ) := by
      have hcast :
          NormedSpace.fromTangentSpace p.1
            (mfderiv 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, Fin 2 → ℝ) Prod.fst p v) = vE.1 := by
        rw [show (Prod.fst : (Fin 2 → ℝ) × ℝ → Fin 2 → ℝ) = ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ from rfl]
        rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
        rfl
      constructor
      · intro h0
        rw [← hcast, h0, map_zero]
      · intro h0
        apply (NormedSpace.fromTangentSpace p.1).injective
        rw [hcast, map_zero, h0]
    rw [hf]
    constructor
    · intro hv1
      refine ⟨⟨vE.2⟩, ?_⟩
      have htr : Real.exp (-p.2) • vE.1 = 0 := by rw [hv1, smul_zero]
      have hv00 : vE.1 0 = 0 := by rw [hv1]; rfl
      have hv01 : vE.1 1 = 0 := by rw [hv1]; rfl
      change iotaHomothety ⟨vE.2⟩ = homothetyCartanOmegaModel κ p vE
      refine HomothetyLieAlg.ext ?_ ?_
      · change 0 = Real.exp (-p.2) • vE.1
        exact htr.symm
      · change vE.2 = vE.2 + κ * (p.1 0 * vE.1 1 - p.1 1 * vE.1 0)
        rw [hv01, hv00, mul_zero, mul_zero, sub_self, mul_zero, add_zero]
    · rintro ⟨a, ha⟩
      have htrans := congrArg HomothetyLieAlg.trans ha
      change (0 : Fin 2 → ℝ) = Real.exp (-p.2) • vE.1 at htrans
      exact (smul_eq_zero.mp htrans.symm).resolve_left (Real.exp_pos (-p.2)).ne'

/-- In the homothety model, each fiber is a single free orbit of `Multiplicative ℝ`:
for points over the same base point there is a unique group element carrying one to the other. -/
theorem homothety_fiber_action_is_free_and_transitive (κ : ℝ)
    (x : Fin 2 → ℝ) (s₁ s₂ : ℝ) :
    ∃! t : Multiplicative ℝ,
      (homothetyCartanGeometry κ).rightAct t (x, s₁) = (x, s₂) := by
  refine ⟨Multiplicative.ofAdd (s₂ - s₁), ?_, ?_⟩
  · change (x, s₁ + Multiplicative.toAdd (Multiplicative.ofAdd (s₂ - s₁))) = (x, s₂)
    simp
  · intro t ht
    have hsecond := congrArg Prod.snd ht
    change s₁ + Multiplicative.toAdd t = s₂ at hsecond
    have hval : Multiplicative.toAdd t = s₂ - s₁ := by linarith
    have heq := congrArg Multiplicative.ofAdd hval
    simpa using heq

/-- Any two points in one homothety-bundle fiber are related by a unique group element.
This is the point-independent principal-orbit statement, derived from the explicit action rather
than added as a field or assumed in a downstream theorem. -/
theorem homothety_fiber_action_unique_between_points (κ : ℝ)
    (p q : (Fin 2 → ℝ) × ℝ)
    (hbase : (homothetyCartanGeometry κ).proj p =
      (homothetyCartanGeometry κ).proj q) :
    ∃! t : Multiplicative ℝ,
      (homothetyCartanGeometry κ).rightAct t p = q := by
  rcases p with ⟨x, s₁⟩
  rcases q with ⟨y, s₂⟩
  change x = y at hbase
  subst y
  exact homothety_fiber_action_is_free_and_transitive κ x s₁ s₂

/-- The total space of the homothety model is globally trivialized by the zero section:
`(x,s)` corresponds to the base point `x` and the unique group element carrying `(x,0)` to
`(x,s)`. This is the explicit global bundle chart, not merely a fiberwise orbit assertion. -/
def homothetyBundleTrivialization :
    ((Fin 2 → ℝ) × ℝ) ≃ ((Fin 2 → ℝ) × Multiplicative ℝ) where
  toFun p := (p.1, Multiplicative.ofAdd p.2)
  invFun q := (q.1, Multiplicative.toAdd q.2)
  left_inv p := by simp
  right_inv q := by simp

@[simp] theorem homothetyBundleTrivialization_apply (x : Fin 2 → ℝ) (s : ℝ) :
    homothetyBundleTrivialization (x, s) = (x, Multiplicative.ofAdd s) := rfl

@[simp] theorem homothetyBundleTrivialization_proj (p : (Fin 2 → ℝ) × ℝ) :
    (homothetyBundleTrivialization p).1 = p.1 := rfl

theorem homothetyBundleTrivialization_action_compat (κ : ℝ) (t : Multiplicative ℝ)
    (p : (Fin 2 → ℝ) × ℝ) :
    homothetyBundleTrivialization ((homothetyCartanGeometry κ).rightAct t p) =
      ((homothetyBundleTrivialization p).1, (homothetyBundleTrivialization p).2 * t) := by
  rcases p with ⟨x, s⟩
  apply Prod.ext rfl
  change Multiplicative.ofAdd (s + Multiplicative.toAdd t) =
    Multiplicative.ofAdd s * t
  simp

/-- The translation direction in the total-space coordinate of the homothety
right action. -/
private def homothetyTranslationCLM : ℝ →L[ℝ] (Fin 2 → ℝ) × ℝ where
  toFun t := (0, t)
  map_add' t₁ t₂ := by ext <;> simp
  map_smul' c t := by ext <;> simp

/-- Every orbit map of the concrete homothety right action is smooth. -/
theorem homothety_rightAct_orbit_coordinate_contMDiff
    (κ : ℝ) (p : (Fin 2 → ℝ) × ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) ∞
      (fun t => (homothetyCartanGeometry κ).rightAct (Multiplicative.ofAdd t) p) := by
  rcases p with ⟨x, s⟩
  change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) ∞
    (fun t => (x, s + t))
  have hconst : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) ∞
      (fun _ : ℝ => (x, s)) := contMDiff_const
  have hlinear : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) ∞
      (fun t => homothetyTranslationCLM t) := homothetyTranslationCLM.contMDiff
  have hsum := hconst.add hlinear
  convert hsum using 1
  funext t
  simp [homothetyTranslationCLM]

/-- The homothety action is jointly smooth when the group is expressed in its
additive coordinate. This is stronger than smoothness of each fixed group
translation, but remains a theorem about this concrete model. -/
private def homothetyJointCoordinateCLM :
    ℝ × ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ) × ℝ where
  toFun q := (q.2.1, q.2.2 + q.1)
  map_add' q r := by
    ext <;> simp [add_assoc, add_comm, add_left_comm]
  map_smul' c q := by
    ext <;> simp <;> ring

/-- Joint smoothness of the concrete homothety right action in the additive
coordinate on `Multiplicative ℝ` and the product coordinates on the total
space. -/
theorem homothety_rightAct_joint_coordinate_contMDiff (κ : ℝ) :
    ContMDiff
      𝓘(ℝ, ℝ × ((Fin 2 → ℝ) × ℝ))
      𝓘(ℝ, (Fin 2 → ℝ) × ℝ) ∞
      (fun q : ℝ × ((Fin 2 → ℝ) × ℝ) =>
        (homothetyCartanGeometry κ).rightAct (Multiplicative.ofAdd q.1) q.2) := by
  change ContMDiff
    𝓘(ℝ, ℝ × ((Fin 2 → ℝ) × ℝ))
    𝓘(ℝ, (Fin 2 → ℝ) × ℝ) ∞
    (fun q : ℝ × ((Fin 2 → ℝ) × ℝ) => (q.2.1, q.2.2 + q.1))
  exact homothetyJointCoordinateCLM.contMDiff

/-- The multiplicative group `Multiplicative ℝ` uses its additive coordinate as a smooth
one-dimensional model. This model keeps the group carrier and records the coordinate chart. -/
def multiplicativeRealModel : ModelWithCorners ℝ ℝ (Multiplicative ℝ) :=
  ModelWithCorners.ofTargetUniv ℝ Multiplicative.toAdd.toPartialEquiv rfl rfl
    continuous_toAdd continuous_ofAdd

/-- The algebraic global chart is a smooth diffeomorphism for the product model whose group
coordinate is modelled on `ℝ`. -/
def homothetyBundleDiffeomorph :
    Diffeomorph
      ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Fin 2 → ℝ)).prod multiplicativeRealModel)
      ((Fin 2 → ℝ) × ℝ) ((Fin 2 → ℝ) × Multiplicative ℝ) ∞ where
  toEquiv := homothetyBundleTrivialization
  contMDiff_toFun := by
    have h_ofAdd : ContMDiff 𝓘(ℝ, ℝ) multiplicativeRealModel ∞
        (fun x : ℝ => (Multiplicative.ofAdd x : Multiplicative ℝ)) := by
      have hrange : Set.range (multiplicativeRealModel : Multiplicative ℝ → ℝ) = Set.univ := by
        change Set.range (fun x : Multiplicative ℝ => Multiplicative.toAdd x) = Set.univ
        exact Set.range_eq_univ.mpr Multiplicative.toAdd.surjective
      have hsymm := multiplicativeRealModel.contMDiffOn_symm (n := ∞)
      rw [hrange] at hsymm
      have hcoord : ContMDiffOn 𝓘(ℝ, ℝ) multiplicativeRealModel ∞
          (fun x : ℝ => (Multiplicative.ofAdd x : Multiplicative ℝ)) Set.univ := by
        change ContMDiffOn 𝓘(ℝ, ℝ) multiplicativeRealModel ∞
          (fun x : ℝ => (Multiplicative.ofAdd x : Multiplicative ℝ)) Set.univ at hsymm
        exact hsymm
      exact contMDiffOn_univ.mp hcoord
    change ContMDiff
      ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Fin 2 → ℝ)).prod multiplicativeRealModel) ∞
      (fun p : (Fin 2 → ℝ) × ℝ =>
        (p.1, (Multiplicative.ofAdd p.2 : Multiplicative ℝ)))
    exact (contMDiff_id : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ id).prodMap h_ofAdd
  contMDiff_invFun := by
    change ContMDiff
      ((𝓘(ℝ, Fin 2 → ℝ)).prod multiplicativeRealModel)
      ((𝓘(ℝ, Fin 2 → ℝ)).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : (Fin 2 → ℝ) × Multiplicative ℝ =>
        (q.1, (Multiplicative.toAdd q.2 : ℝ)))
    exact (contMDiff_id : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ id).prodMap
      multiplicativeRealModel.contMDiff

/-- The smooth global chart preserves the principal right action on its group coordinate. -/
theorem homothetyBundleDiffeomorph_action_compat (κ : ℝ) (t : Multiplicative ℝ)
    (p : (Fin 2 → ℝ) × ℝ) :
    homothetyBundleDiffeomorph ((homothetyCartanGeometry κ).rightAct t p) =
      ((homothetyBundleDiffeomorph p).1, (homothetyBundleDiffeomorph p).2 * t) :=
  homothetyBundleTrivialization_action_compat κ t p

/-- The explicit smooth product chart proves that the homothety Cartan bundle is a
Mathlib trivial fiber bundle over its projection.  Surjectivity, continuity, and openness
of the projection are then consequences of this theorem, rather than extra fields or
hypotheses on the Cartan package. -/
theorem homothety_isHomeomorphicTrivialFiberBundle (κ : ℝ) :
    IsHomeomorphicTrivialFiberBundle (F := Multiplicative ℝ)
      (homothetyCartanGeometry κ).proj := by
  refine ⟨homothetyBundleDiffeomorph.toHomeomorph, ?_⟩
  intro p
  rfl

/-- The homothety bundle projection is surjective, derived from its global trivialization. -/
theorem homothety_proj_surjective (κ : ℝ) :
    Function.Surjective (homothetyCartanGeometry κ).proj := by
  exact homothety_isHomeomorphicTrivialFiberBundle κ |>.surjective_proj

/-- The homothety bundle projection is continuous, derived from its global trivialization. -/
theorem homothety_proj_continuous (κ : ℝ) :
    Continuous (homothetyCartanGeometry κ).proj := by
  exact homothety_isHomeomorphicTrivialFiberBundle κ |>.continuous_proj

/-- The homothety bundle projection is open, derived from its global trivialization. -/
theorem homothety_proj_isOpenMap (κ : ℝ) :
    IsOpenMap (homothetyCartanGeometry κ).proj := by
  exact homothety_isHomeomorphicTrivialFiberBundle κ |>.isOpenMap_proj

/-- Explicit T17 inhabitant witness for `SmoothCartanGeometry` on the flat bundle `κ = 0`. -/
def flatHomothetyCartanGeometry :
    SmoothCartanGeometry ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ) ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ)
      𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, Fin 2 → ℝ) ((Fin 2 → ℝ) × ℝ) (Fin 2 → ℝ)
      (Multiplicative ℝ) HomothetyLieAlg HomothetyH :=
  homothetyCartanGeometry 0

/-- Smooth coordinate vector fields `coordX0 = (e₀, 0)` and `coordX1 = (e₁, 0)` on `ℝ² × ℝ`. -/
def homothetyCoordX0 : Π p : (Fin 2 → ℝ) × ℝ, TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) p :=
  fun _ => (![1, 0], 0)

def homothetyCoordX1 : Π p : (Fin 2 → ℝ) × ℝ, TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) p :=
  fun _ => (![0, 1], 0)

private lemma mlieBracket_homothetyCoords (p : (Fin 2 → ℝ) × ℝ) :
    VectorField.mlieBracket 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) homothetyCoordX0 homothetyCoordX1 p = 0 := by
  have h1 :
      VectorField.mlieBracket 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) homothetyCoordX0 homothetyCoordX1 =
        VectorField.mlieBracketWithin 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) homothetyCoordX0 homothetyCoordX1 univ := rfl
  have h2 :
      VectorField.mlieBracketWithin 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) homothetyCoordX0 homothetyCoordX1 univ =
        VectorField.lieBracketWithin ℝ homothetyCoordX0 homothetyCoordX1 univ :=
    VectorField.mlieBracketWithin_eq_lieBracketWithin
  have h3 :
      VectorField.lieBracketWithin ℝ homothetyCoordX0 homothetyCoordX1 univ =
        VectorField.lieBracket ℝ homothetyCoordX0 homothetyCoordX1 :=
    VectorField.lieBracketWithin_univ
  rw [h1, h2, h3]
  unfold VectorField.lieBracket
  change
    (fderiv ℝ (fun _ : (Fin 2 → ℝ) × ℝ => ((![0, 1], 0) : (Fin 2 → ℝ) × ℝ)) p) (![1, 0], 0) -
      (fderiv ℝ (fun _ : (Fin 2 → ℝ) × ℝ => ((![1, 0], 0) : (Fin 2 → ℝ) × ℝ)) p) (![0, 1], 0) = 0
  rw [fderiv_const_apply, fderiv_const_apply]
  simp

private lemma fderiv_omega_coordX1 (κ : ℝ) (x : Fin 2 → ℝ) (s : ℝ) :
    mfderiv 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, HomothetyLieAlg)
      (fun q => (homothetyCartanGeometry κ).omega q (homothetyCoordX1 q)) (x, s) (![1, 0], 0) =
      ⟨0, κ⟩ := by
  rw [mfderiv_eq_fderiv]
  have hfunc :
      (fun q : (Fin 2 → ℝ) × ℝ => (homothetyCartanGeometry κ).omega q (homothetyCoordX1 q)) =
        prodToHomothetyCLM ∘ (fun q : (Fin 2 → ℝ) × ℝ =>
          (Real.exp (-q.2) • (![0, 1] : Fin 2 → ℝ), κ * q.1 0)) := by
    funext q
    ext i
    · change Real.exp (-q.2) * (![0, 1] : Fin 2 → ℝ) i = Real.exp (-q.2) * (![0, 1] : Fin 2 → ℝ) i
      rfl
    · change 0 + κ * (q.1 0 * 1 - q.1 1 * 0) = κ * q.1 0
      ring
  have hsnd : HasFDerivAt (fun q : (Fin 2 → ℝ) × ℝ => -q.2)
      (-(ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ)) (x, s) :=
    (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ).hasFDerivAt.neg
  have hexp : HasFDerivAt (fun q : (Fin 2 → ℝ) × ℝ => Real.exp (-q.2))
      (Real.exp (-s) • (-(ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ))) (x, s) :=
    hsnd.exp
  have h1 := hexp.smul_const (![0, 1] : Fin 2 → ℝ)
  have h2 :
      HasFDerivAt (fun q : (Fin 2 → ℝ) × ℝ => κ * q.1 0)
        (κ • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ))) (x, s) := by
    have hlin : HasFDerivAt (fun q : (Fin 2 → ℝ) × ℝ => q.1 0)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
          (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)) (x, s) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)).hasFDerivAt
    exact hlin.const_smul κ
  have hfull := (prodToHomothetyCLM.hasFDerivAt).comp (x, s) (h1.prodMk h2)
  have hfd := hfull.fderiv
  change (fderiv ℝ (fun q => ((homothetyCartanGeometry κ).omega q) (homothetyCoordX1 q)) (x, s)) (![1, 0], 0) =
    (⟨0, κ⟩ : HomothetyLieAlg)
  rw [hfunc, hfd]
  ext i <;> simp [prodToHomothetyCLM]

private lemma fderiv_omega_coordX0 (κ : ℝ) (x : Fin 2 → ℝ) (s : ℝ) :
    mfderiv 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, HomothetyLieAlg)
      (fun q => (homothetyCartanGeometry κ).omega q (homothetyCoordX0 q)) (x, s) (![0, 1], 0) =
      ⟨0, -κ⟩ := by
  rw [mfderiv_eq_fderiv]
  have hfunc :
      (fun q : (Fin 2 → ℝ) × ℝ => (homothetyCartanGeometry κ).omega q (homothetyCoordX0 q)) =
        prodToHomothetyCLM ∘ (fun q : (Fin 2 → ℝ) × ℝ =>
          (Real.exp (-q.2) • (![1, 0] : Fin 2 → ℝ), -(κ * q.1 1))) := by
    funext q
    ext i
    · change Real.exp (-q.2) * (![1, 0] : Fin 2 → ℝ) i = Real.exp (-q.2) * (![1, 0] : Fin 2 → ℝ) i
      rfl
    · change 0 + κ * (q.1 0 * 0 - q.1 1 * 1) = -(κ * q.1 1)
      ring
  have hsnd : HasFDerivAt (fun q : (Fin 2 → ℝ) × ℝ => -q.2)
      (-(ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ)) (x, s) :=
    (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ).hasFDerivAt.neg
  have hexp : HasFDerivAt (fun q : (Fin 2 → ℝ) × ℝ => Real.exp (-q.2))
      (Real.exp (-s) • (-(ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ))) (x, s) :=
    hsnd.exp
  have h1 := hexp.smul_const (![1, 0] : Fin 2 → ℝ)
  have h2 :
      HasFDerivAt (fun q : (Fin 2 → ℝ) × ℝ => -(κ * q.1 1))
        (-(κ • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp
          (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)))) (x, s) := by
    have hlin : HasFDerivAt (fun q : (Fin 2 → ℝ) × ℝ => q.1 1)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp
          (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)) (x, s) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)).hasFDerivAt
    exact (hlin.const_smul κ).neg
  have hfull := (prodToHomothetyCLM.hasFDerivAt).comp (x, s) (h1.prodMk h2)
  have hfd := hfull.fderiv
  change (fderiv ℝ (fun q => ((homothetyCartanGeometry κ).omega q) (homothetyCoordX0 q)) (x, s)) (![0, 1], 0) =
    (⟨0, -κ⟩ : HomothetyLieAlg)
  rw [hfunc, hfd]
  ext i <;> simp [prodToHomothetyCLM]

private lemma fromTangentSpace_refl_eq
    (form : ∀ q : (Fin 2 → ℝ) × ℝ, TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) q →L[ℝ] HomothetyLieAlg)
    (x : Fin 2 → ℝ) (s : ℝ)
    (X Y : Π q : (Fin 2 → ℝ) × ℝ, TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) q)
    (res : HomothetyLieAlg)
    (hres : mfderiv 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, HomothetyLieAlg)
      (fun q => form q (Y q)) (x, s) (X (x, s)) = res) :
    NormedSpace.fromTangentSpace
      ((ContinuousLinearEquiv.refl ℝ HomothetyLieAlg) (form (x, s) (Y (x, s))))
      (mfderiv 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) 𝓘(ℝ, HomothetyLieAlg)
        (fun q => (ContinuousLinearEquiv.refl ℝ HomothetyLieAlg) (form q (Y q)))
        (x, s) (X (x, s))) = res :=
  hres

/-- **Exact Curvature Formula on the Smooth Homothety Bundle**:
`Ω_{ω_κ}(∂_{x₀}, ∂_{x₁})(x, s) = (-κ e⁻ˢ x, 2κ)`. -/
theorem homothetyCartanGeometry_curvature_formula (κ : ℝ) (x : Fin 2 → ℝ) (s : ℝ) :
    cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 (x, s) =
      ⟨(-κ * Real.exp (-s)) • x, 2 * κ⟩ := by
  have hbr : VectorField.mlieBracket 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) homothetyCoordX0 homothetyCoordX1 (x, s) = 0 :=
    mlieBracket_homothetyCoords (x, s)
  unfold cartanCurvatureForm cartanCurvatureFormWith cartanExteriorDerivWith
  rw [hbr, map_zero, sub_zero]
  rw [fromTangentSpace_refl_eq
        (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
        x s homothetyCoordX0 homothetyCoordX1 ⟨0, κ⟩ (by exact fderiv_omega_coordX1 κ x s),
      fromTangentSpace_refl_eq
        (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
        x s homothetyCoordX1 homothetyCoordX0 ⟨0, -κ⟩ (by exact fderiv_omega_coordX0 κ x s)]
  change (⟨0, κ⟩ - ⟨0, -κ⟩ : HomothetyLieAlg) +
    ⁅homothetyCartanOmegaModel κ (x, s) (![1, 0], 0),
     homothetyCartanOmegaModel κ (x, s) (![0, 1], 0)⁆ =
      ⟨(-κ * Real.exp (-s)) • x, 2 * κ⟩
  ext i
  · fin_cases i <;> simp <;> ring
  · simp
    ring

theorem homothetyCartanGeometry_flat_of_zero (p : (Fin 2 → ℝ) × ℝ) :
    cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (fun q => ((homothetyCartanGeometry 0).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 p = 0 := by
  rcases p with ⟨x, s⟩
  rw [homothetyCartanGeometry_curvature_formula]
  ext <;> simp

theorem homothetyCartanGeometry_curved_of_ne_zero {κ : ℝ} (hκ : κ ≠ 0) (p : (Fin 2 → ℝ) × ℝ) :
    cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 p ≠ 0 := by
  rcases p with ⟨x, s⟩
  rw [homothetyCartanGeometry_curvature_formula]
  intro h0
  have hscale := congrArg HomothetyLieAlg.scale h0
  simp only [homothety_zero_scale] at hscale
  exact hκ (by linarith [hscale])

theorem homothetyCartanGeometry_torsion_free_at_origin (κ s : ℝ) :
    cartanTorsionForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (homothetyCartanGeometry κ).iotaH.range.toSubmodule
      (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 (0, s) = 0 := by
  simp only [cartanTorsionForm, homothetyCartanGeometry_curvature_formula, smul_zero,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨⟨2 * κ⟩, rfl⟩

theorem homothetyCartanGeometry_torsion_nonzero_away_from_origin {κ : ℝ} (hκ : κ ≠ 0) (s : ℝ) :
    cartanTorsionForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (homothetyCartanGeometry κ).iotaH.range.toSubmodule
      (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 (![1, 0], s) ≠ 0 := by
  simp only [cartanTorsionForm, homothetyCartanGeometry_curvature_formula, Submodule.mkQ_apply,
    ne_eq, Submodule.Quotient.mk_eq_zero]
  rintro ⟨a, ha⟩
  have ht0 := congrArg (fun g : HomothetyLieAlg => g.trans 0) ha
  simp only [homothetyCartanGeometry, iotaHomothety, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at ht0
  have hexp : Real.exp (-s) ≠ 0 := (Real.exp_pos (-s)).ne'
  have hzero : (-κ) * Real.exp (-s) = 0 := ht0.symm
  exact (mul_eq_zero.mp hzero).elim (fun hk => hκ (neg_eq_zero.mp hk)) hexp

/-! ## Section 4: Fiberwise Bridge to `Erlangen20Datum`, `OperatorIntertwiner`, & `InvariantGeometry` -/

/-- The conjugated adjoint representation on `TangentSpace IP p` induced by a Cartan connection `ω_p`:
`ρ_p(X)(v) = ω_p⁻¹(⁅X, ω_p(v)⁆)`. -/
def cartanFiberAdjointRep
    {EP EM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HP HM : Type*} [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) :
    𝔤 →ₗ⁅ℝ⁆ Module.End ℝ (TangentSpace IP p) where
  toFun X :=
    (C.omega p).symm.toLinearMap.comp ((LieModule.toEnd ℝ 𝔤 𝔤 X).comp (C.omega p).toLinearMap)
  map_add' X Y := by
    ext v
    simp [LinearMap.comp_apply, map_add]
  map_smul' c X := by
    ext v
    simp [LinearMap.comp_apply, map_smul]
  map_lie' := by
    intro X Y
    ext v
    simp [LinearMap.comp_apply, Ring.lie_def, Module.End.mul_apply]

/-- Fiberwise `Erlangen20Datum` at `p ∈ P` realized directly on `TangentSpace IP p` via the
Cartan connection isomorphism `ω_p`. -/
def cartanFiberErlangen20Datum
    {EP EM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HP HM : Type*} [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) :
    Erlangen20Datum ℝ (TangentSpace IP p) 𝔤
      (Submodule ℝ (TangentSpace IP p)) (TangentSpace IP p ≃L[ℝ] 𝔤) where
  operatorAlgebra := ⊤
  representation := cartanFiberAdjointRep C p
  representation_mem _ := Algebra.mem_top
  symmetryData := LinearMap.ker (mfderiv IP IM C.proj p).toLinearMap
  invariantData := C.omega p

/-- Explicit `OperatorIntertwiner` showing `C.omega p` intertwines the fiberwise Cartan adjoint
operator `cartanFiberAdjointRep C p X` with `LieModule.toEnd ℝ 𝔤 𝔤 X`. -/
def cartanAdjointIntertwiner
    {EP EM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HP HM : Type*} [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) (X : 𝔤) :
    OperatorIntertwiner ℝ (TangentSpace IP p) 𝔤 where
  carrierEquiv := (C.omega p).toLinearEquiv
  source := (cartanFiberErlangen20Datum C p).representation X
  target := LieModule.toEnd ℝ 𝔤 𝔤 X
  intertwines v := by
    change LieModule.toEnd ℝ 𝔤 𝔤 X (C.omega p v) =
      C.omega p ((C.omega p).symm (LieModule.toEnd ℝ 𝔤 𝔤 X (C.omega p v)))
    rw [(C.omega p).apply_symm_apply]

/-- Mandatory T17 noncommutativity witness on `Module.End ℝ (TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) p)`. -/
theorem homothety_fiberEnd_noncommutative (κ : ℝ) (p : (Fin 2 → ℝ) × ℝ) :
    (cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨0, 1⟩ *
      (cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨![1, 0], 0⟩ ≠
    (cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨![1, 0], 0⟩ *
      (cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨0, 1⟩ := by
  intro hEq
  let D := cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p
  have hlie := D.representation_map_lie (⟨0, 1⟩ : HomothetyLieAlg) (⟨![1, 0], 0⟩ : HomothetyLieAlg)
  have hzero : D.representation ⁅(⟨0, 1⟩ : HomothetyLieAlg), (⟨![1, 0], 0⟩ : HomothetyLieAlg)⁆ = 0 := by
    change (cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation
      ⁅(⟨0, 1⟩ : HomothetyLieAlg), (⟨![1, 0], 0⟩ : HomothetyLieAlg)⁆ = 0
    rw [hlie, hEq, sub_self]
  have hval := congrArg (fun T : Module.End ℝ (TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) p) =>
    ((homothetyCartanGeometry κ).omega p) (T (((homothetyCartanGeometry κ).omega p).symm ⟨0, 1⟩))) hzero
  have hlhs :
      ((homothetyCartanGeometry κ).omega p)
        (D.representation ⁅(⟨0, 1⟩ : HomothetyLieAlg), (⟨![1, 0], 0⟩ : HomothetyLieAlg)⁆
          (((homothetyCartanGeometry κ).omega p).symm ⟨0, 1⟩)) =
        ⁅⁅(⟨0, 1⟩ : HomothetyLieAlg), (⟨![1, 0], 0⟩ : HomothetyLieAlg)⁆, (⟨0, 1⟩ : HomothetyLieAlg)⁆ := by
    change ((homothetyCartanGeometry κ).omega p)
        (((homothetyCartanGeometry κ).omega p).symm
          (LieModule.toEnd ℝ HomothetyLieAlg HomothetyLieAlg
            ⁅(⟨0, 1⟩ : HomothetyLieAlg), (⟨![1, 0], 0⟩ : HomothetyLieAlg)⁆
            (((homothetyCartanGeometry κ).omega p) (((homothetyCartanGeometry κ).omega p).symm ⟨0, 1⟩)))) =
      ⁅⁅(⟨0, 1⟩ : HomothetyLieAlg), (⟨![1, 0], 0⟩ : HomothetyLieAlg)⁆, (⟨0, 1⟩ : HomothetyLieAlg)⁆
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
      LieModule.toEnd_apply_apply]
  have hrhs :
      ((homothetyCartanGeometry κ).omega p)
        ((0 : Module.End ℝ (TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) p))
          (((homothetyCartanGeometry κ).omega p).symm ⟨0, 1⟩)) = 0 := by
    rw [LinearMap.zero_apply, map_zero]
  rw [hlhs, hrhs] at hval
  have hcoord := congrArg (fun g : HomothetyLieAlg => g.trans 0) hval
  simp at hcoord

/-- Right `Multiplicative ℝ`-action on `(Fin 2 → ℝ) × ℝ` makes `HomothetyLieAlg.scale`
of the curvature an `Erlangen.InvariantGeometry.IsInvariantReadout` along fibers. -/
@[instance_reducible]
def homothetyFiberAction : MulAction (Multiplicative ℝ) ((Fin 2 → ℝ) × ℝ) where
  smul := (homothetyCartanGeometry 0).rightAct
  one_smul := (homothetyCartanGeometry 0).rightAct_one
  mul_smul t₁ t₂ p := by
    change (homothetyCartanGeometry 0).rightAct (t₁ * t₂) p =
      (homothetyCartanGeometry 0).rightAct t₁ ((homothetyCartanGeometry 0).rightAct t₂ p)
    rw [mul_comm t₁ t₂]
    exact (homothetyCartanGeometry 0).rightAct_mul t₂ t₁ p

theorem homothety_curvature_scale_invariantReadout (κ : ℝ) :
    @IsInvariantReadout (Multiplicative ℝ) ((Fin 2 → ℝ) × ℝ) _ homothetyFiberAction ℝ
      (fun p => (cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
        (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
        homothetyCoordX0 homothetyCoordX1 p).scale) := by
  intro t p
  rcases p with ⟨x, s⟩
  change (cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 (x, s + Multiplicative.toAdd t)).scale =
    (cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 (x, s)).scale
  rw [homothetyCartanGeometry_curvature_formula, homothetyCartanGeometry_curvature_formula]

/-! ## Section 5: Master Synthesis & QMS Archetype Registration -/

def SmoothCartanGeometrySynthesis : Prop :=
  (shearUpperCLM * shearLowerCLM ≠ shearLowerCLM * shearUpperCLM) ∧
  (shearUpperGL2 * shearLowerGL2 ≠ shearLowerGL2 * shearUpperGL2) ∧
  (∀ (v w : GroupLieAlgebra 𝓘(ℝ, EndR2) GL2R) (g : GL2R),
    cartanCurvatureFormWith 𝓘(ℝ, EndR2) (tangentSpaceCastModel 𝓘(ℝ, EndR2) (1 : GL2R))
      (fun q => (leftMaurerCartanEquiv 𝓘(ℝ, EndR2) q).toContinuousLinearMap)
      (mulInvariantVectorField v) (mulInvariantVectorField w) g = 0) ∧
  (∀ p : (Fin 2 → ℝ) × ℝ,
    cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (fun q => ((homothetyCartanGeometry 0).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 p = 0) ∧
  (∀ (κ : ℝ), κ ≠ 0 → ∀ p : (Fin 2 → ℝ) × ℝ,
    cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 p ≠ 0) ∧
  (∀ (κ : ℝ) (s : ℝ),
    cartanTorsionForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (homothetyCartanGeometry κ).iotaH.range.toSubmodule
      (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 (0, s) = 0) ∧
  (∀ (κ : ℝ), κ ≠ 0 → ∀ s : ℝ,
    cartanTorsionForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
      (homothetyCartanGeometry κ).iotaH.range.toSubmodule
      (fun q => ((homothetyCartanGeometry κ).omega q).toContinuousLinearMap)
      homothetyCoordX0 homothetyCoordX1 (![1, 0], s) ≠ 0)

theorem smooth_cartan_geometry_synthesis : SmoothCartanGeometrySynthesis :=
  ⟨shearUpperCLM_mul_shearLowerCLM_ne,
   shearUpperGL2_mul_shearLowerGL2_ne,
   gl2R_maurerCartan_flat,
   homothetyCartanGeometry_flat_of_zero,
   fun _ hκ p => homothetyCartanGeometry_curved_of_ne_zero hκ p,
   homothetyCartanGeometry_torsion_free_at_origin,
   fun _ hκ s => homothetyCartanGeometry_torsion_nonzero_away_from_origin hκ s⟩

def smoothCartanGeometryArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.Erlangen.SmoothCartanGeometry.smooth_cartan_geometry_synthesis
  phase := 5
  claim := fun _ => SmoothCartanGeometrySynthesis
  evidence := fun _ => smooth_cartan_geometry_synthesis

#register_archetype smoothCartanGeometryArchetype
#audit_archetype smoothCartanGeometryArchetype

end InfoGeometry.Erlangen.SmoothCartanGeometry
