/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.CoordinateLessCliffordInvariance
import InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
import InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
import InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
import InfoGeometry.Canonical.SplitCliffordTowerUnification
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Clifford.Cl11GradedDifferential
import InfoGeometry.Canonical.Erlangen20Unification
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.KK.ClNNFredholmBridge
import InfoGeometry.KK.Examples
import InfoGeometry.KK.SpectralTripleKreinCycleBridge
import InfoGeometry.KK.RealSplitKreinEquivarianceBridge
import InfoGeometry.Canonical.ConnesNCGFormAlgebra
import InfoGeometry.OperatorAlgebra.MaurerCartanTower
import InfoGeometry.Algebra.KreinPeirceTowerIntertwine
import InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
import InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis

/-!
# R1 ↔ R2 ↔ R3 Unified Triangle Bridge (`F2.4` / `M3.5`)

This leaf module collects checked bridges among the three mathematical pillars without introducing any
global typeclass diamonds (`open scoped Erlangen20Unification` and
`open scoped FiniteTensorProduct` are deliberately omitted, and `instAlgebraClTower`
remains non-global):

- **Component A (`T3-19`)**: Functorial naturality of `OneForms (CliffordAlgebra Q)`
  under `CliffordAlgebra.equivOfIsometry` (`cliffordOneFormsEquiv`, `cliffordOneFormsAutHom`),
  `negIsometryEquiv Q` ↔ `involuteEquiv`, `v4ToQ11IsometryHom` ↔ `localCl11RootMap` via
  `cl11EquivMat`, and `hTrace_cl` / `LieActionLane` compatibility.
- **Component B (`T3-15`, `T4-06`)**: Full chain
  `SplitCliffordInfinity ≃+* DoubleCylinderColimit ℝ ≃+* cantorDoubleCylinderErlangen20Datum.operatorAlgebra`
  with transported `V₄` symmetry restricting along `gSwapToV4` to `G_swap`,
  `J_lp_clm` sewing invariance, and zero chiral anomaly.
- **Component C (`T3-20`, `T4-05`, `T4-07`)**: Krein-frame and cycle facts on
  `SplitDoubledSpace ℝ ≃ₗᵢ[ℝ] DoubledSpace ℝ` (proving `dim E = 1` forces every
  odd Krein-skew-adjoint `F` to vanish) and on `SplitDoubledSpace (FinModelE 2)`
  (`nontrivialSplitKasparovCycle` and `splitDoubledWitnessKasparovCycle_cfc`,
  together with an `EquivariantDatum`, its `Erlangen20Datum` extension, and the nonzero
  cycle one-form. These are bundled facts; the theorem does not assert a commuting diagram
  identifying the independent generic Lie-action lane with the concrete cycle carrier.
- **Component D (`T3-18`, R1↔R3)**: `KreinPeirceTowerIntertwine` transported to `Clsplit n`
  via `ringHom_preserves_peirce_yang_mills`, coupled with `ZornDifferentialFormsCliffordBridge`
  and `CartanHestenesRotorSpinConnectionMaurerCartanSynthesis` (`spinGroupToIsometryHom`).
-/

noncomputable section

namespace InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge

/-! ## Component A (`T3-19`): `CliffordAlgebra.equivOfIsometry` Naturality on `OneForms` -/

section ComponentA_CliffordOneFormsNaturality

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance
open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
open InfoGeometry.Canonical.Erlangen20Unification
open InfoGeometry.Canonical.ConnesNCGFormAlgebra
open InfoGeometry.Riemannian

/-- Pushforward of `OneForms A` along a ring homomorphism `φ : A →+* B`. -/
abbrev mapOneForms {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) :
    OneForms A →+ OneForms B :=
  ringHomMapOneForms φ

@[simp] theorem mapOneForms_id {A : Type*} [Ring A] (ω : OneForms A) :
    mapOneForms (RingHom.id A) ω = ω := by
  change ringHomMapOneForms (RingHom.id A) ω = ω
  rw [ringHomMapOneForms_id]
  rfl

@[simp] theorem mapOneForms_comp {A B C : Type*} [Ring A] [Ring B] [Ring C]
    (ψ : B →+* C) (φ : A →+* B) (ω : OneForms A) :
    mapOneForms (ψ.comp φ) ω = mapOneForms ψ (mapOneForms φ ω) := by
  apply Subtype.ext
  change TensorProduct.map (ringHomToIntLinear (ψ.comp φ))
      (ringHomToIntLinear (ψ.comp φ)) ω.1 =
    TensorProduct.map (ringHomToIntLinear ψ) (ringHomToIntLinear ψ)
      (TensorProduct.map (ringHomToIntLinear φ) (ringHomToIntLinear φ) ω.1)
  have hcomp : ringHomToIntLinear (ψ.comp φ) =
      (ringHomToIntLinear ψ).comp (ringHomToIntLinear φ) := by
    ext x; rfl
  rw [hcomp, TensorProduct.map_comp]
  rfl

/-- Functorial additive equivalence `OneForms A ≃+ OneForms B` induced by `e : A ≃+* B`. -/
def equivOneForms {A B : Type*} [Ring A] [Ring B] (e : A ≃+* B) :
    OneForms A ≃+ OneForms B where
  toFun := mapOneForms e.toRingHom
  invFun := mapOneForms e.symm.toRingHom
  left_inv ω := by
    rw [← mapOneForms_comp]
    have h : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by
      ext x; exact e.symm_apply_apply x
    rw [h, mapOneForms_id]
  right_inv ω := by
    rw [← mapOneForms_comp]
    have h : e.toRingHom.comp e.symm.toRingHom = RingHom.id B := by
      ext x; exact e.apply_symm_apply x
    rw [h, mapOneForms_id]
  map_add' := map_add (mapOneForms e.toRingHom)

@[simp] theorem equivOneForms_differential {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (a : A) :
    equivOneForms e (differential A a) = differential B (e a) :=
  ringHomMapOneForms_differential e.toRingHom a

@[simp] theorem equivOneForms_leftDifferentialForm {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (a b : A) :
    equivOneForms e (leftDifferentialForm A a b) = leftDifferentialForm B (e a) (e b) :=
  ringHomMapOneForms_leftDifferentialForm e.toRingHom a b

/-- Naturality of `mapOneForms` with `rightDifferentialForm`. -/
@[simp] theorem mapOneForms_rightDifferentialForm {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) (a b : A) :
    mapOneForms φ (rightDifferentialForm A a b) = rightDifferentialForm B (φ a) (φ b) := by
  have h := congrArg (mapOneForms φ) (differential_mul_forms A a b)
  have hdiff : mapOneForms φ (differential A (a * b)) =
      leftDifferentialForm B (φ a) (φ b) + rightDifferentialForm B (φ a) (φ b) := by
    rw [ringHomMapOneForms_differential, map_mul]
    exact differential_mul_forms B (φ a) (φ b)
  rw [map_add, ringHomMapOneForms_leftDifferentialForm, hdiff] at h
  exact (add_left_cancel h).symm

/-- Naturality of `mapOneForms` with left bimodule multiplication `leftAction`. -/
theorem mapOneForms_leftAction {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) (c : A) (ω : OneForms A) :
    mapOneForms φ (leftAction A c ω) = leftAction B (φ c) (mapOneForms φ ω) := by
  refine Submodule.span_induction
    (p := fun η _ => mapOneForms φ (leftAction A c η) = leftAction B (φ c) (mapOneForms φ η))
    ?_ ?_ ?_ ?_ (oneForms_mem_span A ω)
  · rintro η ⟨⟨a, b⟩, rfl⟩
    rw [leftAction_leftDifferentialForm, ringHomMapOneForms_leftDifferentialForm,
      ringHomMapOneForms_leftDifferentialForm, leftAction_leftDifferentialForm, map_mul]
  · simp [map_zero]
  · intro η₁ η₂ _ _ h₁ h₂
    simp only [map_add, h₁, h₂]
  · intro n η _ hη
    simp only [map_zsmul, hη]

/-- Naturality of `mapOneForms` with right bimodule multiplication `rightAction`. -/
theorem mapOneForms_rightAction {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) (c : A) (ω : OneForms A) :
    mapOneForms φ (rightAction A c ω) = rightAction B (φ c) (mapOneForms φ ω) := by
  refine Submodule.span_induction
    (p := fun η _ => mapOneForms φ (rightAction A c η) = rightAction B (φ c) (mapOneForms φ η))
    ?_ ?_ ?_ ?_ (oneForms_mem_span A ω)
  · rintro η ⟨⟨a, b⟩, rfl⟩
    rw [rightAction_leftDifferentialForm, map_sub,
      ringHomMapOneForms_leftDifferentialForm, ringHomMapOneForms_leftDifferentialForm,
      ringHomMapOneForms_leftDifferentialForm,
      rightAction_leftDifferentialForm]
    simp only [map_mul]
  · simp [map_zero]
  · intro η₁ η₂ _ _ h₁ h₂
    simp only [map_add, h₁, h₂]
  · intro n η _ hη
    simp only [map_zsmul, hη]

/-- Coordinate-less `Q.IsometryEquiv Q` action on `OneForms (CliffordAlgebra Q)` induced by
`CliffordAlgebra.equivOfIsometry`. -/
def cliffordOneFormsEquiv {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (g : Q.IsometryEquiv Q) :
    OneForms (CliffordAlgebra Q) ≃+ OneForms (CliffordAlgebra Q) :=
  equivOneForms (CliffordAlgebra.equivOfIsometry g).toRingEquiv

/-- Group homomorphism `Q.IsometryEquiv Q →* AddMonoid.End (OneForms (CliffordAlgebra Q))`. -/
def cliffordOneFormsEndHom {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) :
    Q.IsometryEquiv Q →* AddMonoid.End (OneForms (CliffordAlgebra Q)) where
  toFun g := (cliffordOneFormsEquiv Q g).toAddMonoidHom
  map_one' := by
    apply AddMonoidHom.ext
    intro ω
    change cliffordOneFormsEquiv Q (QuadraticMap.IsometryEquiv.refl Q) ω = ω
    have hrefl : (CliffordAlgebra.equivOfIsometry (QuadraticMap.IsometryEquiv.refl Q)).toRingHom =
        RingHom.id (CliffordAlgebra Q) := by
      ext x
      change CliffordAlgebra.equivOfIsometry (QuadraticMap.IsometryEquiv.refl Q) x = x
      rw [CliffordAlgebra.equivOfIsometry_refl]
      rfl
    dsimp [cliffordOneFormsEquiv, equivOneForms]
    change mapOneForms
        (CliffordAlgebra.equivOfIsometry (QuadraticMap.IsometryEquiv.refl Q)).toRingHom ω = ω
    rw [hrefl, mapOneForms_id]
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro ω
    change mapOneForms (CliffordAlgebra.equivOfIsometry (h.trans g)).toRingHom ω =
      mapOneForms (CliffordAlgebra.equivOfIsometry g).toRingHom
        (mapOneForms (CliffordAlgebra.equivOfIsometry h).toRingHom ω)
    have hcomp :
        (CliffordAlgebra.equivOfIsometry (h.trans g)).toRingHom =
          (CliffordAlgebra.equivOfIsometry g).toRingHom.comp
            (CliffordAlgebra.equivOfIsometry h).toRingHom := by
      ext x
      change CliffordAlgebra.equivOfIsometry (h.trans g) x =
        CliffordAlgebra.equivOfIsometry g (CliffordAlgebra.equivOfIsometry h x)
      rw [← CliffordAlgebra.equivOfIsometry_trans]
      rfl
    rw [hcomp, mapOneForms_comp]

@[simp] theorem cliffordOneFormsEquiv_differential
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (g : Q.IsometryEquiv Q) (x : CliffordAlgebra Q) :
    cliffordOneFormsEquiv Q g (differential (CliffordAlgebra Q) x) =
      differential (CliffordAlgebra Q) ((cliffordSymmetryAction Q).act g x) :=
  equivOneForms_differential (CliffordAlgebra.equivOfIsometry g).toRingEquiv x

@[simp] theorem cliffordOneFormsEquiv_leftDifferentialForm
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (g : Q.IsometryEquiv Q) (a b : CliffordAlgebra Q) :
    cliffordOneFormsEquiv Q g (leftDifferentialForm (CliffordAlgebra Q) a b) =
      leftDifferentialForm (CliffordAlgebra Q)
        ((cliffordSymmetryAction Q).act g a) ((cliffordSymmetryAction Q).act g b) :=
  equivOneForms_leftDifferentialForm (CliffordAlgebra.equivOfIsometry g).toRingEquiv a b

/-- `cliffordOneFormsEquiv` at `negIsometryEquiv Q` equals the pushforward along
`CliffordAlgebra.involuteEquiv`. -/
theorem cliffordOneFormsEquiv_negIsometryEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (ω : OneForms (CliffordAlgebra Q)) :
    cliffordOneFormsEquiv Q (negIsometryEquiv Q) ω =
      equivOneForms CliffordAlgebra.involuteEquiv.toRingEquiv ω := by
  have h : (CliffordAlgebra.equivOfIsometry (negIsometryEquiv Q)).toRingEquiv =
      CliffordAlgebra.involuteEquiv.toRingEquiv := by
    ext x
    change CliffordAlgebra.equivOfIsometry (negIsometryEquiv Q) x =
      CliffordAlgebra.involuteEquiv x
    rw [equivOfIsometry_negIsometryEquiv]
  dsimp [cliffordOneFormsEquiv]
  rw [h]

/-- `V₄`-naturality on `OneForms (CliffordAlgebra q11)` intertwining `v4ToQ11IsometryHom`
and `localCl11RootMap` through `cl11EquivMat`. -/
theorem cl11EquivMat_oneForms_v4_naturality
    (g : InfoGeometry.Topology.V4RootSystem.V4Group)
    (ω : OneForms (CliffordAlgebra q11)) :
    equivOneForms cl11EquivMat.toRingEquiv
        (cliffordOneFormsEquiv q11 (v4ToQ11IsometryHom g) ω) =
      equivOneForms (localCl11RootMap g).toRingEquiv
        (equivOneForms cl11EquivMat.toRingEquiv ω) := by
  change mapOneForms cl11EquivMat.toRingHom
      (mapOneForms (CliffordAlgebra.equivOfIsometry (v4ToQ11IsometryHom g)).toRingHom ω) =
    mapOneForms (localCl11RootMap g).toRingHom
      (mapOneForms cl11EquivMat.toRingHom ω)
  rw [← mapOneForms_comp, ← mapOneForms_comp]
  have hring :
      cl11EquivMat.toRingHom.comp
          (CliffordAlgebra.equivOfIsometry (v4ToQ11IsometryHom g)).toRingHom =
        (localCl11RootMap g).toRingHom.comp cl11EquivMat.toRingHom := by
    ext a i j
    exact congrArg (fun m : Clifford.Cl11Matrix.Mat2 => m i j)
      (cl11EquivMat_v4_equivOfIsometry g a)
  rw [hring]

/-- `hTrace_cl` naturality under `CliffordAlgebra.equivOfIsometry g`. -/
theorem cliffordOneFormsEquiv_hTrace_naturality
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
    (Q : QuadraticForm R M) (g : Q.IsometryEquiv Q) (x : CliffordAlgebra Q) :
    hTrace_cl Q ((cliffordSymmetryAction Q).act g x) = hTrace_cl Q x :=
  hTrace_cl_equivOfIsometry g x

end ComponentA_CliffordOneFormsNaturality

/-! ## Component B (`T3-15`, `T4-06`): Cantor Double Cylinder ↔ `V₄` / `SplitCliffordInfinity` ↔ `Erlangen20Datum` -/

section ComponentB_CantorSplitCliffordErlangen20

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
open InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
open InfoGeometry.Canonical.Erlangen20Unification
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Clifford.Cl11GradedDifferential
open InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
open scoped InnerProductSpace

/-- Ring equivalence identifying `SplitCliffordInfinity` with `DoubleCylinderColimit ℝ`. -/
def splitCliffordInfinityToDoubleCylinder :
    SplitCliffordInfinity ≃+* DoubleCylinderColimit ℝ :=
  splitCliffordInfinityEquivLimit.toRingEquiv.trans matTowerLimitEquivDoubleCylinderColimit

/-- Ring equivalence identifying `SplitCliffordInfinity` directly with
`cantorDoubleCylinderErlangen20Datum.operatorAlgebra`. -/
def splitCliffordInfinityToCantorOpAlg :
    SplitCliffordInfinity ≃+* cantorDoubleCylinderErlangen20Datum.operatorAlgebra :=
  splitCliffordInfinityToDoubleCylinder.trans cantorDoubleCylinderOperatorAlgebraEquiv.toRingEquiv

/-- Transport `doubleCylinderColimitV4SymmetryAction` onto
`cantorDoubleCylinderErlangen20Datum.operatorAlgebra`. -/
def cantorDoubleCylinderOperatorAlgebraV4Action :
    SymmetryAction InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation.V4
      cantorDoubleCylinderErlangen20Datum.operatorAlgebra where
  act g :=
    (cantorDoubleCylinderOperatorAlgebraEquiv.toRingEquiv.symm.trans
      (doubleCylinderColimitV4SymmetryAction.act g)).trans
      cantorDoubleCylinderOperatorAlgebraEquiv.toRingEquiv
  act_one a := by
    simp only [RingEquiv.trans_apply, doubleCylinderColimitV4SymmetryAction.act_one,
      RingEquiv.apply_symm_apply]
  act_mul g h a := by
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
      doubleCylinderColimitV4SymmetryAction.act_mul]

/-- Restricting `cantorDoubleCylinderOperatorAlgebraV4Action` along `gSwapToV4` reproduces
`cantorDoubleCylinderOperatorAlgebraSymmetryAction`. -/
theorem cantorDoubleCylinderOperatorAlgebraV4_restrict_gSwap
    (g : G_swap)
    (a : cantorDoubleCylinderErlangen20Datum.operatorAlgebra) :
    cantorDoubleCylinderOperatorAlgebraV4Action.act (gSwapToV4 g) a =
      cantorDoubleCylinderOperatorAlgebraSymmetryAction.act g a := by
  dsimp only [cantorDoubleCylinderOperatorAlgebraV4Action,
    cantorDoubleCylinderOperatorAlgebraSymmetryAction, RingEquiv.trans_apply]
  congr 1
  rw [doubleCylinderColimitV4_restrict_gSwap]
  rfl

/-- Unified Cantor–`SplitCliffordInfinity`–`Erlangen20Datum` theorem:
every `x : SplitCliffordInfinity` maps into `DoubleCylinderColimit ℝ` and `H_lp ℝ`
satisfying `J_lp_clm` sewing invariance, zero chiral anomaly, and stage-1 `localCl11Map T`
compatibility. -/
theorem splitCliffordInfinity_cantor_sewn_and_chiral_zero
    (x : SplitCliffordInfinity) (v : H_lp ℝ)
    (A : DoubleCylinderStage ℝ 1) :
    let X := splitCliffordInfinityToDoubleCylinder x
    ((J_lp_clm (E := ℝ)).comp ((colimitRepresentationCLM X).comp (J_lp_clm (E := ℝ))) =
        colimitRepresentationCLM X) ∧
      (inner ℝ canonicalCantorSewnState
        (((epsilon_lp_clm (E := ℝ)).comp (colimitRepresentationCLM X))
          canonicalCantorSewnState) = 0) ∧
      (((J_lp_clm (E := ℝ)).toLinearMap *
          cantorDoubleCylinderErlangen20Datum.representation X *
          (J_lp_clm (E := ℝ)).toLinearMap) v =
        cantorDoubleCylinderErlangen20Datum.representation X v) ∧
      (doubleCylinderStageEquivMat2 (stageSwapEquiv ℝ 1 A) =
        localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
          (doubleCylinderStageEquivMat2 A)) :=
  ⟨colimitRepresentation_sewn_invariant (splitCliffordInfinityToDoubleCylinder x),
    doubleCylinderColimit_canonicalVacuum_chiral_zero (splitCliffordInfinityToDoubleCylinder x),
    cantorDoubleCylinder_sewn_fixes_operatorAlgebra (splitCliffordInfinityToDoubleCylinder x) v,
    stageSwapEquiv_one_eq_localCl11Map_T A⟩

end ComponentB_CantorSplitCliffordErlangen20

/-! ## Component C (`T3-20`, `T4-05`, `T4-07`): Full 3-Pillar Triangle (`DoubledSpace ℝ` & `SplitDoubledSpace (FinModelE 2)`) -/

section ComponentC_ThreePillarTriangle

open scoped InnerProductSpace
open InfoGeometry.Krein
open InfoGeometry.KK
open InfoGeometry.KK.ClNNFredholmBridge
open InfoGeometry.KK.RealSplitKreinEquivarianceBridge
open InfoGeometry.KK.SpectralTripleKreinCycleBridge
open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.Canonical.Erlangen20Unification
open InfoGeometry.Canonical.ConnesNCGFormAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.MaurerCartanTower

/-- On `SplitDoubledSpace ℝ` (`dim E = 1`, `≃ₗᵢ[ℝ] DoubledSpace ℝ`), every operator
`F : EndH (SplitDoubledSpace ℝ)` that is both grading-odd (`IsOdd F`) and Krein-skew-adjoint
(`IsKreinSkewAdjoint F`) necessarily vanishes (`F = 0`), establishing why `dim E = 2`
(`SplitDoubledSpace (FinModelE 2)`) is minimal for a nontrivial cycle (`F ≠ 0`). -/
theorem splitDoubledReal_odd_kreinSkew_eq_zero
    (F : EndH (SplitDoubledSpace ℝ))
    (hOdd : KreinGradedModule.IsOdd (H := SplitDoubledSpace ℝ) F)
    (hSkew : KreinSpace.IsKreinSkewAdjoint (H := SplitDoubledSpace ℝ) F) :
    F = 0 := by
  let u₀ : SplitDoubledSpace ℝ := ⟨to_doubled (1 : ℝ) 0⟩
  let u₁ : SplitDoubledSpace ℝ := ⟨to_doubled (0 : ℝ) 1⟩
  let a : ℝ := WithLp.fst (F u₀).toDoubled
  let c : ℝ := WithLp.snd (F u₀).toDoubled
  let b : ℝ := WithLp.fst (F u₁).toDoubled
  let d : ℝ := WithLp.snd (F u₁).toDoubled
  have hGrade_u0 : KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ) u₀ = u₁ := by
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> simp [u₀, u₁, SplitDoubledSpace.gradeCLM_eq_splitDoubledModularJ,
      SplitDoubledSpace.splitDoubledModularJ, modular_j_apply]
  have hOdd_u0 :
      KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ) (F u₀) = -(F u₁) := by
    have hcomp := congrArg (fun T : EndH (SplitDoubledSpace ℝ) => T u₀) hOdd
    change (KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ))
        (F (KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ) u₀)) = -(F u₀) at hcomp
    have hcomp2 := congrArg (KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ)) hcomp
    have hgg : KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ)
        (KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ) (F (KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ) u₀))) =
        F (KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ) u₀) := by
      have hsq := congrArg (fun T : EndH (SplitDoubledSpace ℝ) =>
          T (F (KreinGradedModule.gradeCLM (H := SplitDoubledSpace ℝ) u₀)))
        (KreinGradedModule.gradeCLM_comp_self (H := SplitDoubledSpace ℝ))
      simpa using hsq
    rw [hgg, hGrade_u0, map_neg] at hcomp2
    rw [← neg_inj, neg_neg, hcomp2]
  have hcb : c = -b := by
    have h := congrArg (fun z : SplitDoubledSpace ℝ => WithLp.fst z.toDoubled) hOdd_u0
    change WithLp.fst (modular_j (F u₀).toDoubled) =
      WithLp.fst (-(F u₁)).toDoubled at h
    simpa [c, b, modular_j_apply, SplitDoubledSpace.toDoubled_neg] using h
  have had : a = -d := by
    have h := congrArg (fun z : SplitDoubledSpace ℝ => WithLp.snd z.toDoubled) hOdd_u0
    change WithLp.snd (modular_j (F u₀).toDoubled) =
      WithLp.snd (-(F u₁)).toDoubled at h
    simpa [a, d, modular_j_apply, SplitDoubledSpace.toDoubled_neg] using h
  have hSkew' := (KreinSpace.isKreinSkewAdjoint_iff (H := SplitDoubledSpace ℝ) F).mp hSkew
  have ha0 : a = 0 := by
    have h00 := hSkew' u₀ u₀
    have hk : ∀ z : SplitDoubledSpace ℝ,
        KreinSpace.kreinInner z u₀ = WithLp.fst z.toDoubled := by
      intro z
      change KreinSpace.kreinInner (H := DoubledSpace ℝ) z.toDoubled u₀.toDoubled = _
      have hz : z.toDoubled = to_doubled (WithLp.fst z.toDoubled) (WithLp.snd z.toDoubled) := rfl
      rw [hz, kreinInner_to_doubled]
      simp
    have hk2 : ∀ z : SplitDoubledSpace ℝ,
        KreinSpace.kreinInner u₀ z = WithLp.fst z.toDoubled := by
      intro z
      rw [KreinSpace.kreinInner_symm]
      exact hk z
    rw [hk (F u₀), hk2 (F u₀)] at h00
    change a + a = 0 at h00
    linarith
  have hd0 : d = 0 := by linarith
  have hbc : b = c := by
    have h01 := hSkew' u₀ u₁
    have hk1 : KreinSpace.kreinInner (F u₀) u₁ = -c := by
      change KreinSpace.kreinInner (H := DoubledSpace ℝ) (F u₀).toDoubled u₁.toDoubled = -c
      have hz : (F u₀).toDoubled = to_doubled a c := rfl
      rw [hz, kreinInner_to_doubled]
      simp
    have hk2 : KreinSpace.kreinInner u₀ (F u₁) = b := by
      change KreinSpace.kreinInner (H := DoubledSpace ℝ) u₀.toDoubled (F u₁).toDoubled = b
      have hz : (F u₁).toDoubled = to_doubled b d := rfl
      rw [hz, kreinInner_to_doubled]
      simp
    rw [hk1, hk2] at h01
    linarith
  have hb0 : b = 0 := by linarith
  have hc0 : c = 0 := by linarith
  have hFu0 : F u₀ = 0 := by
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> simp [a, c, ha0, hc0]
  have hFu1 : F u₁ = 0 := by
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> simp [b, d, hb0, hd0]
  apply ContinuousLinearMap.ext
  intro w
  have hw : w = (WithLp.fst w.toDoubled) • u₀ + (WithLp.snd w.toDoubled) • u₁ := by
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;>
      simp [u₀, u₁, SplitDoubledSpace.toDoubled_add, SplitDoubledSpace.toDoubled_smul]
  rw [hw, map_add, map_smul, map_smul, hFu0, hFu1, smul_zero, smul_zero, add_zero]
  simp

/-- Collected R1/R2/R3 component facts over the doubled Krein carrier. The displayed
equivalences and cycle/one-form results are kernel-checked individually and appear in one
conjunction; this statement does not identify the independent generic Lie-action lane `(K, g)`
with the concrete spectral-cycle algebra or claim a natural transformation between them.

- **R3**: `splitDoubledCl11Action` + `clSplitToStageEnd 1` (`Clsplit 1 ≃ₐ[ℝ] EndH (FinModelE 2)`)
- **R2**: `nontrivialSplitKasparovCycle` (`F ≠ 0`, `F² = 1`, `[F, π proj0E2] ≠ 0`),
  `splitDoubledWitnessSpectralTriple → splitDoubledWitnessUnboundedCycle → splitDoubledWitnessKasparovCycle_cfc`
  with the exact inverse identity for its finite-dimensional phase defect,
  `doubledSpaceSplitEquivariantDatum`, and `Erlangen20Datum`
- **R1**: `ncDeriv` / `kasparovCycleOneForm` nonvanishing (`[F, π proj0E2] ≠ 0`),
  and the separate Maurer–Cartan flatness result `actionThetaL_flat`. -/
theorem r1r2r3_unified_triangle_on_doubledSpace
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : InfoGeometry.Algebra.LieActionLane R A) (hK : IsLeibnizAction K) (g : Aˣ)
    (u : (EndH (SplitDoubledSpace (FinModelE 2)))ˣ) :
    let _instLieRing : LieRing ℝ := LieRing.ofAssociativeRing
    let _instLieAlg : LieAlgebra ℝ ℝ := LieAlgebra.ofAssociativeAlgebra
    let eReal : SplitDoubledSpace ℝ ≃ₗᵢ[ℝ] DoubledSpace ℝ :=
      SplitDoubledSpace.toDoubledLIE (E := ℝ)
    let e2 : SplitDoubledSpace (FinModelE 2) ≃ₗᵢ[ℝ] DoubledSpace (FinModelE 2) :=
      SplitDoubledSpace.toDoubledLIE (E := FinModelE 2)
    let X := nontrivialSplitKasparovCycle
    let Xcfc := splitDoubledWitnessKasparovCycle_cfc
    let E := doubledSpaceSplitEquivariantDatum (L := ℝ) LinearMap.id
      (fun x y => by change x * y - y * x = 0; ring)
    let E20 : Erlangen20Datum ℝ (SplitDoubledSpace (FinModelE 2)) ℝ
        (EquivariantSymmetryData X) (EquivariantInvariantData X) :=
      E.toErlangen20Datum
    (∀ u₀ : SplitDoubledSpace ℝ, KreinSpace.J (eReal u₀) = eReal (KreinSpace.J u₀)) ∧
      (∀ u₂ : SplitDoubledSpace (FinModelE 2), KreinSpace.J (e2 u₂) = e2 (KreinSpace.J u₂)) ∧
      (X.F ≠ 0 ∧ X.F * X.F = 1) ∧
      (Xcfc.F ≠ 0 ∧
        (1 + splitDoubledWitnessSpectralTriple.spectralGenerator.D *
          splitDoubledWitnessSpectralTriple.spectralGenerator.D) *
          (1 - Xcfc.F * Xcfc.F) = 1) ∧
      (E20.representation (1 : ℝ) = LinearMap.id) ∧
      (kasparovCycleOneForm X (differential (EndH (FinModelE 2)) proj0E2) ≠ 0) ∧
      (1 - X.F * X.F = 0 ∧
        (((u : EndH (SplitDoubledSpace (FinModelE 2))) * X.F *
            (↑u⁻¹ : EndH (SplitDoubledSpace (FinModelE 2)))) *
          ((u : EndH (SplitDoubledSpace (FinModelE 2))) * X.F *
            (↑u⁻¹ : EndH (SplitDoubledSpace (FinModelE 2)))) = 1)) ∧
      (actionCurvature K (actionThetaL K g) = 0) := by
  let _instLieRing : LieRing ℝ := LieRing.ofAssociativeRing
  let _instLieAlg : LieAlgebra ℝ ℝ := LieAlgebra.ofAssociativeAlgebra
  refine ⟨splitDoubled_toDoubledLIE_intertwines_J (E := ℝ),
    splitDoubled_toDoubledLIE_intertwines_J (E := FinModelE 2),
    ⟨nontrivialSplitKasparovCycle_F_ne_zero, nontrivialSplitKasparovCycle_F_sq⟩,
    ⟨splitDoubledWitnessKasparovCycle_cfc_F_ne_zero,
      (finiteDimPhase_sq_add_inv_one_add_sq
        splitDoubledWitnessSpectralTriple.D_selfAdjoint).1⟩,
    ?_, ?_, ⟨?_, ?_⟩, actionThetaL_flat K hK g⟩
  · apply LinearMap.ext
    intro v
    simp [doubledSpaceSplitEquivariantDatum]
  · simp [kasparovCycleOneForm]
    exact nontrivialSplitKasparovCycle_comm_ne_zero
  · rw [nontrivialSplitKasparovCycle_F_sq, sub_self]
  · calc
      ((u : EndH (SplitDoubledSpace (FinModelE 2))) * nontrivialSplitKasparovCycle.F *
          (↑u⁻¹ : EndH (SplitDoubledSpace (FinModelE 2)))) *
        ((u : EndH (SplitDoubledSpace (FinModelE 2))) * nontrivialSplitKasparovCycle.F *
          (↑u⁻¹ : EndH (SplitDoubledSpace (FinModelE 2))))
          = (u : EndH (SplitDoubledSpace (FinModelE 2))) *
              (nontrivialSplitKasparovCycle.F *
                (((↑u⁻¹ : EndH (SplitDoubledSpace (FinModelE 2))) *
                  (u : EndH (SplitDoubledSpace (FinModelE 2)))) *
                  nontrivialSplitKasparovCycle.F)) *
              (↑u⁻¹ : EndH (SplitDoubledSpace (FinModelE 2))) := by
                simp only [mul_assoc]
      _ = (u : EndH (SplitDoubledSpace (FinModelE 2))) *
            (nontrivialSplitKasparovCycle.F * nontrivialSplitKasparovCycle.F) *
            (↑u⁻¹ : EndH (SplitDoubledSpace (FinModelE 2))) := by
              rw [Units.inv_mul, one_mul]
      _ = 1 := by
            rw [nontrivialSplitKasparovCycle_F_sq, mul_one, Units.mul_inv]

end ComponentC_ThreePillarTriangle

/-! ## Component D (`T3-18` & R1↔R3 Cross-References) -/

section ComponentD_KreinPeirceZornRotorBridge

open InfoGeometry.Clifford
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.Algebra.KreinPeirceTowerIntertwine
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
open InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis
open InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
open InfoGeometry.Algebra.NoncommutativePeierlsBerryKitaevSynthesis
open InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open InfoGeometry.Canonical.ConnesNCGFormAlgebra
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-- Transport the Peirce Yang–Mills spine (`peirce11`, `idempotencyDefect`,
`peirceMaurerCartanCurvature`, `peirceCovariantDeriv`) between `Clsplit n` and `ClTower ℝ n`
via `(clSplitEquivClTowerReal n).toRingHom`, without making `instAlgebraClTower` global. -/
theorem clSplit_peirce_yang_mills_transport
    (n : ℕ) (P A C X : Clsplit n) :
    let f : Clsplit n →+*
        InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis.ClTower ℝ n :=
      (clSplitEquivClTowerReal n).toRingHom
    f (peirce11 P X) = peirce11 (f P) (f X) ∧
      f (idempotencyDefect X) = idempotencyDefect (f X) ∧
      f (peirceMaurerCartanCurvature P A C) =
        peirceMaurerCartanCurvature (f P) (f A) (f C) ∧
      f (peirceCovariantDeriv P A C X) =
        peirceCovariantDeriv (f P) (f A) (f C) (f X) :=
  ringHom_preserves_peirce_yang_mills (clSplitEquivClTowerReal n).toRingHom P A C X

/-- Re-export `peirce11_positive_sector_krein_positivity_and_bianchi` and
`clTower_and_colimit_peirce_transport` alongside `Clsplit` transport (`T3-18`). -/
theorem krein_peirce_clSplit_colimit_bridge
    {B : Type*} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
    [StarRing B] [StarOrderedRing B]
    {γ₀ : B} (hγ₀_star : star γ₀ = γ₀)
    (n : ℕ) (P X A C :
      InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.ClTower B n)
    (hP_sq : P * P = P) (hP_star : star P = P)
    (hP_pos : kroneckerGamma γ₀ n * P = P) :
    (kreinAdjoint γ₀ n (peirce11 P X) = star (peirce11 P X) ∧
      (0 : B) ≤ towerTrace (kreinAdjoint γ₀ n (peirce11 P X) * peirce11 P X) ∧
      peirce11 P (idempotencyDefect X) - idempotencyDefect (peirce11 P X) = qgtPlus P X X ∧
      peirceCovariantDeriv P A C (genV P A C) = 0) ∧
    (∀ (k : ℕ) (h : n ≤ k),
      clTowerHom B h (peirceMaurerCartanCurvature P A C) =
        peirceMaurerCartanCurvature (clTowerHom B h P) (clTowerHom B h A) (clTowerHom B h C)) := by
  refine ⟨peirce11_positive_sector_krein_positivity_and_bianchi hγ₀_star n P X A C
    hP_sq hP_star hP_pos, fun k h => ?_⟩
  exact (clTower_and_colimit_peirce_transport h P A C X).1

/-- Couple `spinGroup Q` rotor conjugation (`spinGroupToIsometryHom`) directly with
Component A's `cliffordOneFormsEquiv` on `OneForms (CliffordAlgebra Q)` and
`cl11HyperbolicRotor_darboux`. -/
theorem spinGroup_cliffordOneForms_naturality
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
    (Q : QuadraticForm R M) (g : spinGroup Q) (a : CliffordAlgebra Q) :
    cliffordOneFormsEquiv Q (spinGroupToIsometryHom Q g) (differential (CliffordAlgebra Q) a) =
      differential (CliffordAlgebra Q)
        ((g : CliffordAlgebra Q) * a * CliffordAlgebra.reverse (g : CliffordAlgebra Q)) := by
  rw [cliffordOneFormsEquiv_differential]
  congr 1
  exact equivOfIsometry_spinGroupToIsometryHom Q g a

theorem hyperbolicRotor_darboux_and_spinGroup_witness (θ : ℝ) :
    clRotorDarbouxConnection (cl11HyperbolicRotor θ) (cl11HyperbolicRotorDeriv θ) = J1_cl ∧
      cl11HyperbolicRotor θ ∈ spinGroup q11 :=
  ⟨cl11HyperbolicRotor_darboux θ, cl11HyperbolicRotor_mem_spinGroup θ⟩

/-- Couple `ZornDifferentialFormsCliffordBridge.FormHodgeCliffordData` (`cliffordAlternatingEval`,
`cliffordMorphismPullbackForm`) with Component A's `cliffordOneFormsEquiv`, `spinGroup Q` rotor
conjugation (`spinGroupToIsometryHom`), and Chevalley–Eilenberg curvature preservation
(`ceCurvature`, including Maurer–Cartan flatness transport). -/
theorem zornHodgeClifford_oneForms_and_ceCurvature_bridge
    {R V C_ring A_mod : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [Invertible (2 : R)]
    [Ring C_ring] [Algebra R C_ring]
    [AddCommGroup A_mod] [Module R A_mod]
    (D : FormHodgeCliffordData R V C_ring)
    (g : spinGroup D.Q)
    (ω : ∀ i : ℕ, V [⋀^Fin i]→ₗ[R] A_mod)
    (x : CliffordAlgebra D.Q)
    {K : DerivationLieLane R (CliffordAlgebra D.Q)}
    {K_C : DerivationLieLane R C_ring}
    (φ : K_C.L →ₗ⁅R⁆ K.L)
    (hact : ∀ (y : K_C.L) (u : CliffordAlgebra D.Q),
      cliffordMorphism D (K.operatorAction (φ y) u) =
        K_C.operatorAction y (cliffordMorphism D u))
    (Γ : DerivationOperatorForm K 1) :
    (cliffordOneFormsEquiv D.Q (spinGroupToIsometryHom D.Q g) (differential (CliffordAlgebra D.Q) x) =
        differential (CliffordAlgebra D.Q)
          ((g : CliffordAlgebra D.Q) * x * CliffordAlgebra.reverse (g : CliffordAlgebra D.Q))) ∧
      (cliffordAlternatingEval D ω
          ((g : CliffordAlgebra D.Q) * x * CliffordAlgebra.reverse (g : CliffordAlgebra D.Q)) =
        cliffordAlternatingEval D
          (fun i => (ExteriorAlgebra.liftAlternating ω).compAlternatingMap
            ((ExteriorAlgebra.map
                ((spinGroupToIsometryHom D.Q g : D.Q.IsometryEquiv D.Q) : V →ₗ[R] V)).toLinearMap.compAlternatingMap
              (ExteriorAlgebra.ιMulti R i))) x) ∧
      (ceCurvature K_C
          (cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
            (φ : K_C.L →ₗ[R] K.L) 1 Γ) =
        cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
          (φ : K_C.L →ₗ[R] K.L) 2 (ceCurvature K Γ)) := by
  refine ⟨spinGroup_cliffordOneForms_naturality D.Q g x, ?_,
    cliffordMorphismPullbackForm_ceCurvature D φ hact Γ⟩
  rw [← equivOfIsometry_spinGroupToIsometryHom D.Q g x]
  exact cliffordAlternatingEval_equivOfIsometry D ω (spinGroupToIsometryHom D.Q g) x

end ComponentD_KreinPeirceZornRotorBridge

end InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge
