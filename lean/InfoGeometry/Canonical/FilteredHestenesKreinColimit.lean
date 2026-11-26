/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport
import InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesAnalyticity
import InfoGeometry.Canonical.FilteredDirectInverseColimit

/-!
# Filtered Hestenes--Krein colimit

Concrete doubled-space realization of filtered inductive phase analyticity.
Every bonding map and cone map is required to commute with the Hestenes clock
axis.  The resulting Cauchy analyticity is then constructed from the native
continuous-linear derivative theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredHestenesKreinColimit

open InfoGeometry.Krein
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open FilteredColimit
open CategoryTheory
open CategoryTheory.Limits

/-! ## Hestenes phase operators on the actual module colimit

The analytic cone below records a chosen target carrier and compatible maps.
Here we separately use the genuine `ModuleCat` colimit: compatible real
stage operators descend by its universal property. This establishes an
algebraic phase operator only; it does not equip that colimit with a norm,
completion, or manifold structure.
-/

section NativeColimitPhase

variable {I : Type} [Preorder I]
variable {A : I → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℝ (A i)]
variable (sys : DirectInductiveSystem ℝ I A)

/-- The native `ModuleCat` colimit object of the direct system. -/
noncomputable abbrev nativeColimitModule : ModuleCat ℝ :=
  colimit (Native.moduleDiagram sys)

/-- A family of stage endomorphisms commuting with every transition map of a
filtered real-module system. -/
structure CompatibleStageEndomorphism where
  map : ∀ i, A i →ₗ[ℝ] A i
  commute : ∀ {i j : I} (hij : i ≤ j),
    (sys.f hij).comp (map i) = (map j).comp (sys.f hij)

namespace CompatibleStageEndomorphism

variable (K : CompatibleStageEndomorphism sys)

/-- The compatible linear cocone of stage operators followed by the canonical
maps into the genuine `ModuleCat` colimit. -/
def linearColimitCocone :
    InductiveCocone ℝ sys (↑(nativeColimitModule sys)) where
  psi i := (colimit.ι (Native.moduleDiagram sys) i).hom.comp (K.map i)
  psi_comm := by
    intro i j hij
    ext x
    calc
      (colimit.ι (Native.moduleDiagram sys) j).hom
          (K.map j (sys.f hij x)) =
        (colimit.ι (Native.moduleDiagram sys) j).hom
          (sys.f hij (K.map i x)) := by
            exact congrArg _ (LinearMap.congr_fun (K.commute hij).symm x)
      _ = (colimit.ι (Native.moduleDiagram sys) i).hom (K.map i x) := by
        have hι :
            (colimit.ι (Native.moduleDiagram sys) j).hom.comp
                (sys.f (leOfHom (homOfLE hij))) =
              (colimit.ι (Native.moduleDiagram sys) i).hom := by
          have h := congrArg (fun f => f.hom)
            (colimit.w (Native.moduleDiagram sys) (homOfLE hij))
          exact h
        have hproof : leOfHom (homOfLE hij) = hij := Subsingleton.elim _ _
        rw [hproof] at hι
        exact LinearMap.congr_fun hι (K.map i x)

/-- The categorical cocone of the compatible stage operators. -/
noncomputable def moduleColimitCocone :
    Cocone (Native.moduleDiagram sys) :=
  Native.moduleCocone sys K.linearColimitCocone

/-- The stagewise endomorphism induced on the actual filtered module
colimit. -/
noncomputable def colimitMap :
    nativeColimitModule sys ⟶ nativeColimitModule sys :=
  Native.descendModuleCocone sys K.linearColimitCocone

/-- On each canonical stage image, the colimit operator agrees with the given
stage operator. -/
@[reassoc]
theorem colimitMap_stage (i : I) :
    colimit.ι (Native.moduleDiagram sys) i ≫ K.colimitMap =
      K.moduleColimitCocone.ι.app i :=
  Native.moduleColimit_desc_stage sys K.linearColimitCocone i

/-- Ordered commutator curvature identities verified at every real stage
descend to the genuine `ModuleCat` colimit. The order of the two operators is
retained; this is the transport law needed when a stagewise spin connection
has curvature equal to the action of a bracket operator. -/
theorem colimitMap_commutator_eq_of_stagewise
    (L H : CompatibleStageEndomorphism sys)
    (hcurv : ∀ i,
      (L.map i).comp (K.map i) - (K.map i).comp (L.map i) = H.map i) :
    K.colimitMap ≫ L.colimitMap - L.colimitMap ≫ K.colimitMap =
      H.colimitMap := by
  apply colimit.hom_ext
  intro i
  ext x
  change A i at x
  have stage (J : CompatibleStageEndomorphism sys) (y : A i) :
      J.colimitMap.hom
          ((colimit.ι (Native.moduleDiagram sys) i).hom y) =
        (colimit.ι (Native.moduleDiagram sys) i).hom (J.map i y) := by
    have h := congrArg (fun f => f.hom) (colimitMap_stage (sys := sys) J i)
    exact LinearMap.congr_fun h y
  change L.colimitMap.hom
        (K.colimitMap.hom ((colimit.ι (Native.moduleDiagram sys) i).hom x)) -
      K.colimitMap.hom
        (L.colimitMap.hom ((colimit.ι (Native.moduleDiagram sys) i).hom x)) =
    H.colimitMap.hom ((colimit.ι (Native.moduleDiagram sys) i).hom x)
  calc
    _ = (colimit.ι (Native.moduleDiagram sys) i).hom
        (L.map i (K.map i x) - K.map i (L.map i x)) := by
          rw [stage L x, stage K (L.map i x), stage K x, stage L (K.map i x)]
          exact (map_sub ((colimit.ι (Native.moduleDiagram sys) i).hom)
            (L.map i (K.map i x)) (K.map i (L.map i x))).symm
    _ = (colimit.ι (Native.moduleDiagram sys) i).hom (H.map i x) := by
          exact congrArg _ (LinearMap.congr_fun (hcurv i) x)
    _ = H.colimitMap.hom
        ((colimit.ι (Native.moduleDiagram sys) i).hom x) := (stage H x).symm

/-- A square-minus-identity law verified at every stage descends to the
genuine algebraic colimit. -/
theorem colimitMap_sq_eq_neg_id
    (hK : ∀ i, (K.map i).comp (K.map i) = -LinearMap.id) :
    K.colimitMap ≫ K.colimitMap = -𝟙 (nativeColimitModule sys) := by
  apply colimit.hom_ext
  intro i
  ext x
  change K.colimitMap.hom (K.colimitMap.hom
      ((colimit.ι (Native.moduleDiagram sys) i).hom x)) =
    -((colimit.ι (Native.moduleDiagram sys) i).hom x)
  have hstage (y : A i) :
      K.colimitMap.hom ((colimit.ι (Native.moduleDiagram sys) i).hom y) =
        (colimit.ι (Native.moduleDiagram sys) i).hom (K.map i y) := by
    have h := congrArg (fun f => f.hom)
      (colimitMap_stage (sys := sys) (K := K) i)
    exact LinearMap.congr_fun h y
  calc
    K.colimitMap.hom (K.colimitMap.hom
        ((colimit.ι (Native.moduleDiagram sys) i).hom x)) =
      (colimit.ι (Native.moduleDiagram sys) i).hom
        (K.map i (K.map i x)) := by rw [hstage x, hstage (K.map i x)]
    _ = -(colimit.ι (Native.moduleDiagram sys) i).hom x := by
      calc
        (colimit.ι (Native.moduleDiagram sys) i).hom
            (K.map i (K.map i x)) =
          (colimit.ι (Native.moduleDiagram sys) i).hom (-x) :=
            congrArg _ (LinearMap.congr_fun (hK i) x)
        _ = -(colimit.ι (Native.moduleDiagram sys) i).hom x := by simp

end CompatibleStageEndomorphism

variable {E : I → Type}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

/-- The internal real Hestenes phase axis descends to a genuine ModuleCat
colimit whenever all real transition maps intertwine the stage axes. No
complex scalar structure is introduced on the stages or the colimit. -/
theorem clockAxisColimit_square_eq_neg_id
    (sys : DirectInductiveSystem ℝ I (fun i => DoubledSpace (E i)))
    (hphase : ∀ {i j : I} (hij : i ≤ j),
      (sys.f hij).comp (clockAxis (E := E i)).toLinearMap =
        (clockAxis (E := E j)).toLinearMap.comp (sys.f hij)) :
    let K : CompatibleStageEndomorphism sys :=
      { map := fun i => (clockAxis (E := E i)).toLinearMap
        commute := hphase }
    K.colimitMap ≫ K.colimitMap = -𝟙 (nativeColimitModule sys) := by
  let K : CompatibleStageEndomorphism sys :=
    { map := fun i => (clockAxis (E := E i)).toLinearMap
      commute := hphase }
  have hK : ∀ i, (K.map i).comp (K.map i) = -LinearMap.id := by
    intro i
    apply LinearMap.ext
    intro x
    change clockAxis (E := E i) (clockAxis (E := E i) x) = -x
    have h := congrArg
      (fun f : DoubledSpace (E i) →L[ℝ] DoubledSpace (E i) => f x)
      (clockAxis_sq (E i))
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      neg_apply] using h
  exact CompatibleStageEndomorphism.colimitMap_sq_eq_neg_id sys K hK

end NativeColimitPhase

/-- A sequential system of real Hilbert carriers whose doubled spaces form a
compatible Hestenes--Krein cone. -/
structure HestenesKreinCone where
  Base : ℕ → Type
  baseNormedAddCommGroup : ∀ n, NormedAddCommGroup (Base n)
  baseInnerProductSpace : ∀ n, InnerProductSpace ℝ (Base n)
  baseCompleteSpace : ∀ n, CompleteSpace (Base n)
  LimitBase : Type
  limitNormedAddCommGroup : NormedAddCommGroup LimitBase
  limitInnerProductSpace : InnerProductSpace ℝ LimitBase
  limitCompleteSpace : CompleteSpace LimitBase
  bond : ∀ n, DoubledSpace (Base n) →L[ℝ] DoubledSpace (Base (n + 1))
  bond_hestenes :
    ∀ n, IsHestenesHolomorphicDifferential (E := Base n) (F := Base (n + 1)) (bond n)
  ι : ∀ n, DoubledSpace (Base n) →L[ℝ] DoubledSpace LimitBase
  ι_hestenes :
    ∀ n, IsHestenesHolomorphicDifferential (E := Base n) (F := LimitBase) (ι n)
  ι_bond : ∀ n, (ι (n + 1)).comp (bond n) = ι n

attribute [instance] HestenesKreinCone.baseNormedAddCommGroup
attribute [instance] HestenesKreinCone.baseInnerProductSpace
attribute [instance] HestenesKreinCone.baseCompleteSpace
attribute [instance] HestenesKreinCone.limitNormedAddCommGroup
attribute [instance] HestenesKreinCone.limitInnerProductSpace
attribute [instance] HestenesKreinCone.limitCompleteSpace

namespace HestenesKreinCone

variable (C : HestenesKreinCone)

/-- The Hestenes clock-axis commutation law is exactly phase-linearity for the
canonical doubled-space phase structures. -/
theorem bond_phaseLinear {n : ℕ} :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (C.bond n) (clockPhaseStructure (C.Base (n + 1))) :=
  C.bond_hestenes n

/-- Cone maps preserve the Hestenes clock axis. -/
theorem ι_phaseLinear {n : ℕ} :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (C.ι n) (clockPhaseStructure C.LimitBase) :=
  C.ι_hestenes n

/-- Forgetting the Hilbert presentation yields the generic filtered phase
cone, with the Hestenes clock axis as its phase structure. -/
def toFilteredPhaseCone : FilteredPhaseCone where
  Stage := fun n => DoubledSpace (C.Base n)
  stageNormedAddCommGroup := fun _ => inferInstance
  stageNormedSpace := fun _ => inferInstance
  phase := fun n => clockPhaseStructure (C.Base n)
  bond := C.bond
  bond_phase := C.bond_hestenes
  Limit := DoubledSpace C.LimitBase
  limitNormedAddCommGroup := inferInstance
  limitNormedSpace := inferInstance
  limitPhase := clockPhaseStructure C.LimitBase
  ι := C.ι
  ι_phase := C.ι_hestenes
  ι_bond := C.ι_bond

/-- Every finite Hestenes--Krein bonding map is Cauchy-analytic, without a
power-series or scalar-complex analyticity hypothesis. -/
def bondCauchyAnalyticAt (n : ℕ) (x : DoubledSpace (C.Base n)) :
    CauchyAnalyticAt
      (clockPhaseStructure (C.Base n))
      (clockPhaseStructure (C.Base (n + 1)))
      (fun y => C.bond n y) x :=
  (C.toFilteredPhaseCone).bondCauchyAnalyticAt n x

@[simp] theorem bondCauchyAnalyticAt_deriv
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    (C.bondCauchyAnalyticAt n x).deriv = C.bond n :=
  rfl

/-- Every canonical map from a finite doubled stage into the doubled colimit
carrier is Cauchy-analytic. -/
def ιCauchyAnalyticAt (n : ℕ) (x : DoubledSpace (C.Base n)) :
    CauchyAnalyticAt
      (clockPhaseStructure (C.Base n))
      (clockPhaseStructure C.LimitBase)
      (fun y => C.ι n y) x :=
  (C.toFilteredPhaseCone).includeCauchyAnalyticAt n x

@[simp] theorem ιCauchyAnalyticAt_deriv
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    (C.ιCauchyAnalyticAt n x).deriv = C.ι n :=
  rfl

/-- The derivative computed after one filtered stage transition equals the
canonical derivative from the original stage. -/
theorem transported_deriv_eq_ι
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    ((C.toFilteredPhaseCone).includeAfterBondCauchyAnalyticAt n x).deriv =
      C.ι n :=
  (C.toFilteredPhaseCone).includeAfterBond_deriv_eq_include n x

/-- Hestenes Cauchy--Riemann compatibility survives one filtered transition. -/
theorem filtered_clockAxis_compatibility
    (n : ℕ) (x v : DoubledSpace (C.Base n)) :
    ((C.toFilteredPhaseCone).includeAfterBondCauchyAnalyticAt n x).deriv
        (clockAxis (E := C.Base n) v) =
      clockAxis (E := C.LimitBase) (C.ι n v) :=
  (C.toFilteredPhaseCone).filtered_cauchyRiemann_compatibility n x v

/-- Compatible stage representatives have equal images in the doubled colimit
carrier. -/
theorem ι_bond_apply (n : ℕ) (x : DoubledSpace (C.Base n)) :
    C.ι (n + 1) (C.bond n x) = C.ι n x :=
  (C.toFilteredPhaseCone).include_bond_apply n x

/-! ### Native stage maps and algebraic colimit

The transition maps below are built from `C.bond` by induction on the order
relation, following the repository's native sequential-tower construction.
This connects the cone's own finite stages to Mathlib's module colimit; the
separately supplied `LimitBase` remains an analytic target and is not silently
identified with the algebraic colimit.
-/

/-- The composite of the Hestenes cone's actual bonding maps from stage `m`
to stage `n`, for `m ≤ n`. -/
noncomputable def bondMap {m n : ℕ} (h : m ≤ n) :
    DoubledSpace (C.Base m) →L[ℝ] DoubledSpace (C.Base n) :=
  Nat.leRecOn h
    (C := fun n => DoubledSpace (C.Base m) →L[ℝ] DoubledSpace (C.Base n))
    (fun {k} f => (C.bond k).comp f)
    (ContinuousLinearMap.id ℝ (DoubledSpace (C.Base m)))

@[simp] theorem bondMap_refl (n : ℕ) :
    C.bondMap (le_rfl : n ≤ n) = ContinuousLinearMap.id ℝ (DoubledSpace (C.Base n)) := by
  simpa [bondMap] using
    (Nat.leRecOn_self
      (C := fun k => DoubledSpace (C.Base n) →L[ℝ] DoubledSpace (C.Base k))
      (next := fun {k} f => (C.bond k).comp f)
      (x := ContinuousLinearMap.id ℝ (DoubledSpace (C.Base n))))

@[simp] theorem bondMap_succ (m n : ℕ) (h : m ≤ n) :
    C.bondMap (h.trans (Nat.le_succ n)) =
      (C.bond n).comp (C.bondMap h) := by
  unfold bondMap
  rw [Nat.leRecOn_trans h (Nat.le_succ n)]
  rw [Nat.leRecOn_succ']

/-- The arbitrary-length Hestenes stage maps compose in chronological order. -/
theorem bondMap_comp {m n k : ℕ} (h₁ : m ≤ n) (h₂ : n ≤ k) :
    C.bondMap (h₁.trans h₂) = (C.bondMap h₂).comp (C.bondMap h₁) := by
  refine Nat.le_induction
    (m := n)
    (P := fun t ht =>
      C.bondMap (h₁.trans ht) = (C.bondMap ht).comp (C.bondMap h₁))
    ?base ?succ k h₂
  · simp [bondMap_refl]
  · intro t hnt ih
    rw [bondMap_succ (C := C) _ _ (h₁.trans hnt)]
    rw [bondMap_succ (C := C) _ _ hnt]
    rw [ih]
    simp [ContinuousLinearMap.comp_assoc]

/-- The successive bonds determine a real direct system on the doubled
stages. -/
noncomputable def nativeModuleSystem :
    DirectInductiveSystem ℝ ℕ (fun n => DoubledSpace (C.Base n)) where
  f := fun {m n} h => (C.bondMap h).toLinearMap
  f_id := by
    intro n
    change (C.bondMap (le_rfl : n ≤ n)).toLinearMap = LinearMap.id
    rw [bondMap_refl]
    rfl
  f_comp := by
    intro m n k h₁ h₂
    exact congrArg (fun f => f.toLinearMap) (C.bondMap_comp h₁ h₂).symm

/-- The composite of the actual cone bonds intertwines the stage Hestenes
phase axes. -/
theorem bondMap_phaseLinear (m : ℕ) :
    ∀ n (h : m ≤ n),
      (clockPhaseStructure (C.Base m)).IsPhaseLinearMap
        (C.bondMap h) (clockPhaseStructure (C.Base n)) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base =>
      simpa [bondMap_refl] using
        PhaseStructure.id_phaseLinear (clockPhaseStructure (C.Base m))
  | @succ n hmn ih =>
      rw [bondMap_succ (C := C) m n hmn]
      exact PhaseStructure.comp_phaseLinear
        (clockPhaseStructure (C.Base m))
        (clockPhaseStructure (C.Base n))
        (clockPhaseStructure (C.Base (n + 1)))
        ih (C.bond_phaseLinear (n := n))

/-- The given analytic target maps form a cocone over the native algebraic
direct system. -/
def nativeLimitCocone :
    InductiveCocone ℝ C.nativeModuleSystem (DoubledSpace C.LimitBase) where
  psi n := (C.ι n).toLinearMap
  psi_comm := by
    intro m n h
    apply LinearMap.ext
    intro x
    change C.ι n (C.bondMap h x) = C.ι m x
    induction n, h using Nat.le_induction with
    | base =>
        simp [bondMap_refl]
    | @succ n hmn ih =>
        rw [bondMap_succ (C := C) m n hmn]
        simp only [ContinuousLinearMap.comp_apply]
        calc
          C.ι (n + 1) (C.bond n (C.bondMap hmn x)) =
              C.ι n (C.bondMap hmn x) := by
                exact congrArg (fun L : DoubledSpace (C.Base n) →L[ℝ]
                  DoubledSpace C.LimitBase => L (C.bondMap hmn x)) (C.ι_bond n)
          _ = C.ι m x := ih

/-- The native algebraic colimit maps to the cone's analytic target by the
universal property. This is only a comparison map; the cone fields do not
assert that it is an isomorphism. -/
noncomputable def nativeColimitToLimitBase :
    nativeColimitModule C.nativeModuleSystem ⟶ ModuleCat.of ℝ (DoubledSpace C.LimitBase) :=
  Native.descendModuleCocone C.nativeModuleSystem C.nativeLimitCocone

/-- The comparison map agrees with every original cone map on its stage. -/
@[reassoc]
theorem nativeColimitToLimitBase_stage (n : ℕ) :
    colimit.ι (Native.moduleDiagram C.nativeModuleSystem) n ≫
        C.nativeColimitToLimitBase =
      (Native.moduleCocone C.nativeModuleSystem C.nativeLimitCocone).ι.app n :=
  Native.moduleColimit_desc_stage C.nativeModuleSystem C.nativeLimitCocone n

/-- The compatible stage Hestenes axes induce an endomorphism of the
algebraic colimit. -/
noncomputable def nativeClockAxis :
    nativeColimitModule C.nativeModuleSystem ⟶
      nativeColimitModule C.nativeModuleSystem := by
  let sys := C.nativeModuleSystem
  let K : CompatibleStageEndomorphism sys :=
    { map := fun n => (clockAxis (E := C.Base n)).toLinearMap
      commute := by
        intro m n h
        exact congrArg (fun f => f.toLinearMap)
          (C.bondMap_phaseLinear m n h) }
  exact K.colimitMap

/-- The comparison from the actual module colimit to the cone target
intertwines the descended real Hestenes axis with the cone's axis. This is a
compatibility statement; it does not identify the two carriers or assert that
the comparison is invertible. -/
theorem nativeColimitToLimitBase_phaseIntertwines :
    C.nativeClockAxis ≫ C.nativeColimitToLimitBase =
      C.nativeColimitToLimitBase ≫
        ModuleCat.ofHom ((clockAxis (E := C.LimitBase)).toLinearMap) := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hStageAxis :
      C.nativeClockAxis.hom
          ((colimit.ι (Native.moduleDiagram C.nativeModuleSystem) n).hom x) =
        (colimit.ι (Native.moduleDiagram C.nativeModuleSystem) n).hom
          ((clockAxis (E := C.Base n)).toLinearMap x) := by
    let sys := C.nativeModuleSystem
    let K : CompatibleStageEndomorphism sys :=
      { map := fun i => (clockAxis (E := C.Base i)).toLinearMap
        commute := by
          intro i j h
          exact congrArg (fun f => f.toLinearMap)
            (C.bondMap_phaseLinear i j h) }
    have h := congrArg (fun f => f.hom)
      (CompatibleStageEndomorphism.colimitMap_stage
        (sys := sys) K n)
    exact LinearMap.congr_fun h x
  have hComparison (y : DoubledSpace (C.Base n)) :
      C.nativeColimitToLimitBase.hom
          ((colimit.ι (Native.moduleDiagram C.nativeModuleSystem) n).hom y) =
        C.ι n y := by
    have h := congrArg (fun f => f.hom)
      (C.nativeColimitToLimitBase_stage n)
    change _ = _ at h
    exact LinearMap.congr_fun h y
  let xStage : DoubledSpace (C.Base n) := x
  change C.nativeColimitToLimitBase.hom
      (C.nativeClockAxis.hom
        ((colimit.ι (Native.moduleDiagram C.nativeModuleSystem) n).hom x)) =
    (clockAxis (E := C.LimitBase)).toLinearMap
      (C.nativeColimitToLimitBase.hom
        ((colimit.ι (Native.moduleDiagram C.nativeModuleSystem) n).hom x))
  calc
    _ = C.ι n ((clockAxis (E := C.Base n)).toLinearMap xStage) := by
      rw [hStageAxis, hComparison]
    _ = clockAxis (E := C.LimitBase) (C.ι n xStage) :=
      PhaseStructure.phaseLinear_apply
        (C.toFilteredPhaseCone.include_isPhaseLinearMap n) xStage
    _ = _ := by
      rw [← hComparison xStage]
      rfl

/-- The real Hestenes phase axis on the stage colimit has square `-1`. -/
theorem nativeColimit_clockAxis_sq :
    let sys := C.nativeModuleSystem
    let K : CompatibleStageEndomorphism sys :=
      { map := fun n => (clockAxis (E := C.Base n)).toLinearMap
        commute := by
          intro m n h
          exact congrArg (fun f => f.toLinearMap)
            (C.bondMap_phaseLinear m n h) }
    K.colimitMap ≫ K.colimitMap = -𝟙 (nativeColimitModule sys) := by
  exact clockAxisColimit_square_eq_neg_id C.nativeModuleSystem (by
      intro m n h
      exact congrArg (fun f => f.toLinearMap)
        (C.bondMap_phaseLinear m n h))

end HestenesKreinCone

end InfoGeometry.Canonical.FilteredHestenesKreinColimit
