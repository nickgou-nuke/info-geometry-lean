import InfoGeometry.Canonical.Cl11CuntzStageComplexificationTopologicalBridge
import InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-!
# Coherent finite-index realization of the Cl(1,1) tower

The generic `Fintype.equivFinOfCardEq` indexing used by the older matrix
owners is intentionally opaque.  This owner supplies a recursive indexing
equivalence whose successor is exactly the tensor-product indexing used by
the UHF/Cuntz successor map.  The resulting complexification is therefore a
genuine finite-stage natural transformation, with no coherence hypothesis.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.Cl11CuntzStageComplexificationTopologicalBridge
open InfoGeometry.Canonical.JordanWignerCantorRepresentation
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge

/-! The topological trace owners are parameterized by a successor family.
Expose the native concrete successor as that family once, so every colimit
readout below uses the same `Data` witness as `concrete_trace_compatible`. -/
abbrev concreteData : CuntzMatrixTraceTower.Data :=
  fun n => CuntzMatrixTraceTower.concreteStep n

abbrev ClStage (n : ℕ) : Type := MatStage n
abbrev CoherentComplexStage (n : ℕ) : Type :=
  Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

noncomputable def coherentIdxEquivFinPowTwo :
    (n : ℕ) → Idx n ≃ Fin (2 ^ n)
  | 0 => Equiv.refl (Fin 1)
  | n + 1 =>
      ((coherentIdxEquivFinPowTwo n).prodCongr (Equiv.refl (Fin 2))).trans
        (finProdFinEquiv.trans (finCongr (by
          simp [pow_succ, Nat.mul_comm])))

@[simp] theorem coherentIdxEquivFinPowTwo_zero :
    coherentIdxEquivFinPowTwo 0 = Equiv.refl (Fin 1) :=
  rfl

theorem coherentIdxEquivFinPowTwo_succ (n : ℕ) :
    coherentIdxEquivFinPowTwo (Nat.succ n) =
      ((coherentIdxEquivFinPowTwo n).prodCongr (Equiv.refl (Fin 2))).trans
        (finProdFinEquiv.trans (finCongr (by
          simp [pow_succ, Nat.mul_comm]))) :=
  rfl

noncomputable def coherentComplexifyClStage (n : ℕ) :
    ClStage n →ₐ[ℝ] CoherentComplexStage n :=
  (Matrix.reindexAlgEquiv ℝ ℂ (coherentIdxEquivFinPowTwo n)).toAlgHom.comp
    (complexifyMatrixAlgHom n)

def coherentComplexifyClStageTopCatHom (n : ℕ) :
    TopCat.of (ClStage n) ⟶ TopCat.of (CoherentComplexStage n) :=
  TopCat.ofHom
    { toFun := coherentComplexifyClStage n
      continuous_toFun :=
        (coherentComplexifyClStage n).toLinearMap.continuous_of_finiteDimensional }

def coherentConcreteStepTopCatHom (n : ℕ) :
    TopCat.of (CoherentComplexStage n) ⟶
      TopCat.of (CoherentComplexStage (Nat.succ n)) :=
  TopCat.ofHom
    { toFun := concreteStep n
      continuous_toFun :=
        (concreteStep n).toAlgHom.toLinearMap.continuous_of_finiteDimensional }

theorem coherentComplexifyClStage_naturality (n : ℕ) (A : ClStage n) :
    coherentComplexifyClStage (Nat.succ n) (stageEmbed n A) =
      concreteStep n (coherentComplexifyClStage n A) := by
  ext i j
  simp [coherentIdxEquivFinPowTwo, coherentComplexifyClStage,
    complexifyMatrixAlgHom, concreteStep, Matrix.reindexAlgEquiv,
    Matrix.kroneckerMap_apply, stageIndexEquiv, matStageEmbed,
    Equiv.prodCongr]
  apply Or.inl
  change ↑((1 : Matrix (Fin 2) (Fin 2) ℝ)
      (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2) =
    (1 : Matrix (Fin 2) (Fin 2) ℂ)
      (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases h : (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2 <;>
    simp only [h]
  all_goals
    by_cases hij : i.modNat = j.modNat <;> simp

theorem coherentComplexifyClStage_stageEmbedMap_naturality
    {m n : ℕ} (hmn : m ≤ n) (A : ClStage m) :
    coherentComplexifyClStage n (stageEmbedMap hmn A) =
      concreteMap hmn (coherentComplexifyClStage m A) := by
  induction hmn with
  | refl =>
      simp [stageEmbedMap_refl, concreteMap_id]
  | @step n h ih =>
      rw [stageEmbedMap_succ h]
      change coherentComplexifyClStage (Nat.succ n)
          (stageEmbed n (stageEmbedMap h A)) =
        map concreteData (Nat.le.step h)
          (coherentComplexifyClStage m A)
      rw [map_succ concreteData h]
      change coherentComplexifyClStage (Nat.succ n)
          (stageEmbed n (stageEmbedMap h A)) =
        concreteStep n (concreteMap h (coherentComplexifyClStage m A))
      rw [coherentComplexifyClStage_naturality]
      exact congrArg (concreteStep n) ih

theorem coherentComplexifyClStageTopCatHom_naturality
    (n : ℕ) (A : ClStage n) :
    coherentComplexifyClStageTopCatHom (Nat.succ n) (stageEmbed n A) =
      coherentConcreteStepTopCatHom n
        (coherentComplexifyClStageTopCatHom n A) := by
  change coherentComplexifyClStage (Nat.succ n) (stageEmbed n A) =
    concreteStep n (coherentComplexifyClStage n A)
  exact coherentComplexifyClStage_naturality n A

theorem coherentComplexifyClStage_trace (n : ℕ) (A : ClStage n) :
    Matrix.trace (coherentComplexifyClStage n A) =
      Complex.ofReal (Matrix.trace A) := by
  unfold coherentComplexifyClStage
  change Matrix.trace
      ((Matrix.reindexAlgEquiv ℝ ℂ (coherentIdxEquivFinPowTwo n))
        (complexifyMatrixAlgHom n A)) = _
  simp only [Matrix.reindexAlgEquiv, Matrix.trace]
  dsimp [complexifyMatrixAlgHom]
  rw [Complex.ofReal_sum]
  exact Equiv.sum_comp (coherentIdxEquivFinPowTwo n).symm
    (fun i => Complex.ofReal (A i i))

theorem coherentComplexifyClStage_normalizedTrace (n : ℕ) (A : ClStage n) :
    matrixTraceFunctional n (coherentComplexifyClStage n A) =
      Complex.ofReal (normalizedTrace n A) := by
  rw [matrixTraceFunctional_apply, coherentComplexifyClStage_trace]
  unfold normalizedTrace
  rw [Complex.ofReal_div]
  simp [div_eq_mul_inv, mul_comm]

theorem coherentComplexifyClStage_star (n : ℕ) (A : ClStage n) :
    coherentComplexifyClStage n (star A) =
      star (coherentComplexifyClStage n A) := by
  ext i j
  simp [coherentComplexifyClStage, Matrix.reindexAlgEquiv,
    complexifyMatrixAlgHom, Matrix.star_apply]

theorem coherentComplexifyClStage_topological_star_readback
    (n : ℕ) (A : ClStage n) :
    CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n
        (coherentComplexifyClStage n (star A)) =
      CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n
        (Matrix.conjTranspose (coherentComplexifyClStage n A)) := by
  simpa only [Matrix.star_eq_conjTranspose] using congrArg
    (CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n)
    (coherentComplexifyClStage_star n A)

def coherentComplexificationNatTrans :
    Cl11MarkovJonesTopologicalColimit.topologicalDiagram ⟶
      CuntzMatrixTraceTopologicalColimit.topologicalDiagram concreteData where
  app n := coherentComplexifyClStageTopCatHom n
  naturality := by
    intro m n f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    rw [TopCat.comp_app, TopCat.comp_app]
    change coherentComplexifyClStage n (stageEmbedMap (leOfHom f) A) =
      concreteMap (leOfHom f) (coherentComplexifyClStage m A)
    exact coherentComplexifyClStage_stageEmbedMap_naturality (leOfHom f) A

def coherentComplexificationColimitCocone :
    Cocone Cl11MarkovJonesTopologicalColimit.topologicalDiagram where
  pt := CuntzMatrixTraceTopologicalColimit.topologicalColimitObject concreteData
  ι :=
    { app := fun n => coherentComplexifyClStageTopCatHom n ≫
        CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro A
        rw [TopCat.comp_app, TopCat.comp_app]
        change CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n
            (coherentComplexifyClStage n (stageEmbedMap (leOfHom f) A)) =
          CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData m
            (coherentComplexifyClStage m A)
        rw [coherentComplexifyClStage_stageEmbedMap_naturality]
        change colimit.ι (CuntzMatrixTraceTopologicalColimit.topologicalDiagram concreteData) n
            ((CuntzMatrixTraceTopologicalColimit.topologicalDiagram concreteData).map f
              (coherentComplexifyClStage m A)) =
          colimit.ι (CuntzMatrixTraceTopologicalColimit.topologicalDiagram concreteData) m
            (coherentComplexifyClStage m A)
        exact congrArg (fun g => g (coherentComplexifyClStage m A))
          (colimit.w
            (CuntzMatrixTraceTopologicalColimit.topologicalDiagram concreteData)
            f) }

noncomputable def coherentComplexificationColimitMap :
    Cl11MarkovJonesTopologicalColimit.topologicalColimitObject ⟶
      CuntzMatrixTraceTopologicalColimit.topologicalColimitObject concreteData :=
  colimit.desc
    Cl11MarkovJonesTopologicalColimit.topologicalDiagram
    coherentComplexificationColimitCocone

theorem coherentComplexificationColimitMap_stage (n : ℕ) (A : ClStage n) :
    coherentComplexificationColimitMap
        (Cl11MarkovJonesTopologicalColimit.topologicalInclusion n A) =
      CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n
        (coherentComplexifyClStage n A) := by
  have h := FilteredColimit.Native.Topological.topologicalDirectDescend_stage
    Cl11MarkovJonesTopologicalColimit.topologicalDiagram
    coherentComplexificationColimitCocone n
  exact congrArg (fun f => f A) h

theorem coherentComplexificationColimit_star_readback
    (n : ℕ) (A : ClStage n) :
    coherentComplexificationColimitMap
        (Cl11MarkovJonesTopologicalColimit.topologicalInclusion n
          (Matrix.conjTranspose A)) =
      CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n
        (Matrix.conjTranspose (coherentComplexifyClStage n A)) := by
  rw [coherentComplexificationColimitMap_stage]
  have hstar :
      coherentComplexifyClStage n (Matrix.conjTranspose A) =
        Matrix.conjTranspose (coherentComplexifyClStage n A) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      coherentComplexifyClStage_star n A
  exact congrArg
    (CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n)
    hstar

theorem coherentComplexificationColimit_trace_factorization :
    Cl11MarkovJonesTopologicalColimit.traceTopologicalColimitMap =
      coherentComplexificationColimitMap ≫
        CuntzMatrixTraceTopologicalColimit.traceTopologicalColimitMap concreteData
          concrete_trace_compatible ≫
          complexTraceToRealTopCatHom := by
  symm
  apply FilteredColimit.Native.Topological.topologicalDirectDescend_unique
    Cl11MarkovJonesTopologicalColimit.topologicalDiagram
    Cl11MarkovJonesTopologicalColimit.traceTopologicalCocone
    (coherentComplexificationColimitMap ≫
      CuntzMatrixTraceTopologicalColimit.traceTopologicalColimitMap concreteData
        concrete_trace_compatible ≫
        complexTraceToRealTopCatHom)
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  rw [TopCat.comp_app, TopCat.comp_app]
  change Complex.re
      (CuntzMatrixTraceTopologicalColimit.traceTopologicalColimitMap concreteData
        concrete_trace_compatible
        (coherentComplexificationColimitMap
          (Cl11MarkovJonesTopologicalColimit.topologicalInclusion n A))) =
    normalizedTrace n A
  rw [coherentComplexificationColimitMap_stage,
    CuntzMatrixTraceTopologicalColimit.traceTopologicalColimitMap_inclusion,
    coherentComplexifyClStage_normalizedTrace]
  rfl

theorem coherentComplexificationColimit_realTrace_factorization :
    Cl11MarkovJonesTopologicalColimit.traceTopologicalColimitMap =
      coherentComplexificationColimitMap ≫
        CuntzMatrixTraceTopologicalGNSBridge.realTraceTopologicalColimitMap
          concreteData concrete_trace_compatible := by
  rw [CuntzMatrixTraceTopologicalGNSBridge.realTraceTopologicalColimitMap_factorization]
  exact coherentComplexificationColimit_trace_factorization

theorem coherentComplexificationColimit_realTrace_stage (n : ℕ) (A : ClStage n) :
    CuntzMatrixTraceTopologicalGNSBridge.realTraceTopologicalColimitMap
      concreteData concrete_trace_compatible
      (coherentComplexificationColimitMap
        (Cl11MarkovJonesTopologicalColimit.topologicalInclusion n A)) =
      normalizedTrace n A := by
  rw [CuntzMatrixTraceTopologicalGNSBridge.realTraceTopologicalColimitMap_factorization,
    coherentComplexificationColimitMap_stage, TopCat.comp_app,
    CuntzMatrixTraceTopologicalColimit.traceTopologicalColimitMap_inclusion,
    coherentComplexifyClStage_normalizedTrace]
  rfl

/-! The coherent complexification preserves the finite cyclic Markov readout.
The statement remains stagewise because the target `TopCat` colimit carries
no multiplication supplied by this comparison map. -/

theorem coherentComplexificationColimit_realTrace_stage_cyclic
    (n : ℕ) (A B : ClStage n) :
    CuntzMatrixTraceTopologicalGNSBridge.realTraceTopologicalColimitMap
        concreteData concrete_trace_compatible
        (coherentComplexificationColimitMap
          (Cl11MarkovJonesTopologicalColimit.topologicalInclusion n (A * B))) =
      CuntzMatrixTraceTopologicalGNSBridge.realTraceTopologicalColimitMap
        concreteData concrete_trace_compatible
        (coherentComplexificationColimitMap
          (Cl11MarkovJonesTopologicalColimit.topologicalInclusion n (B * A))) := by
  rw [coherentComplexificationColimit_realTrace_stage,
    coherentComplexificationColimit_realTrace_stage]
  unfold normalizedTrace
  rw [Matrix.trace_mul_comm]

theorem coherentComplexificationColimit_realTrace_stage_commutator
    (n : ℕ) (A B : ClStage n) :
    CuntzMatrixTraceTopologicalGNSBridge.realTraceTopologicalColimitMap
        concreteData concrete_trace_compatible
        (coherentComplexificationColimitMap
          (Cl11MarkovJonesTopologicalColimit.topologicalInclusion n
            (A * B - B * A))) = 0 := by
  rw [coherentComplexificationColimit_realTrace_stage]
  unfold normalizedTrace
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, zero_div]

theorem coherentComplexificationColimit_realTrace_unique
    (f : Cl11MarkovJonesTopologicalColimit.topologicalColimitObject ⟶ TopCat.of ℝ)
    (h : ∀ (n : ℕ) (A : ClStage n),
      f (Cl11MarkovJonesTopologicalColimit.topologicalInclusion n A) =
        normalizedTrace n A) :
    f = coherentComplexificationColimitMap ≫
      CuntzMatrixTraceTopologicalGNSBridge.realTraceTopologicalColimitMap
        concreteData concrete_trace_compatible := by
  rw [Cl11MarkovJonesTopologicalColimit.traceTopologicalColimitMap_unique f h,
    coherentComplexificationColimit_realTrace_factorization]

/-- The algebraic direct limit has a canonical representative map into the
    coherent `TopCat` colimit.  This is a comparison map only: no topology is
    put on the algebraic quotient. -/
theorem coherentStageEmbedMap_eq_bondMap
    {m n : ℕ} (hmn : m ≤ n) (A : ClStage m) :
    Cl11MarkovJonesTopologicalColimit.stageEmbedMap hmn A =
      bondMap stageBond m n hmn A := by
  induction hmn with
  | refl =>
      simp [Cl11MarkovJonesTopologicalColimit.stageEmbedMap_refl,
        bondMap_refl]
  | @step n h ih =>
      rw [Cl11MarkovJonesTopologicalColimit.stageEmbedMap_succ h,
        bondMap_succ stageBond m n h]
      simp [stageBond, ih]

noncomputable def coherentAlgebraicToTopological :
    Limit → Cl11MarkovJonesTopologicalColimit.topologicalColimitObject :=
  DirectLimit.lift
    (f := fun m n h => bondMap stageBond m n h)
    (fun n (A : ClStage n) =>
      Cl11MarkovJonesTopologicalColimit.topologicalInclusion n A)
    (by
      intro m n h A
      rw [← coherentStageEmbedMap_eq_bondMap h A]
      change colimit.ι Cl11MarkovJonesTopologicalColimit.topologicalDiagram m A =
        colimit.ι Cl11MarkovJonesTopologicalColimit.topologicalDiagram n
          (Cl11MarkovJonesTopologicalColimit.topologicalDiagram.map (homOfLE h) A)
      exact (FilteredColimit.Native.Topological.topologicalDirectInjection_naturality_apply
        Cl11MarkovJonesTopologicalColimit.topologicalDiagram
        (f := homOfLE h) A).symm)

@[simp] theorem coherentAlgebraicToTopological_ofStage
    (n : ℕ) (A : ClStage n) :
    coherentAlgebraicToTopological (ofStage n A) =
      Cl11MarkovJonesTopologicalColimit.topologicalInclusion n A := by
  rfl

@[simp] theorem coherentAlgebraicToTopological_ofStage_transition
    (n : ℕ) (A : ClStage n) :
    coherentAlgebraicToTopological
        (ofStage (n + 1) (stageEmbed n A)) =
      coherentAlgebraicToTopological (ofStage n A) := by
  change coherentAlgebraicToTopological
      (directLimitOf stageBond (n + 1) (stageBond n A)) =
    coherentAlgebraicToTopological (directLimitOf stageBond n A)
  rw [directLimitOf_bond]

theorem coherentComplexificationColimit_stageStarMap
    (n : ℕ) (A : ClStage n) :
    coherentComplexificationColimitMap
        (coherentAlgebraicToTopological (stageStarMap n A)) =
      CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n
        (coherentComplexifyClStage n (star A)) := by
  rw [show stageStarMap n A = ofStage n (star A) by rfl,
    coherentAlgebraicToTopological_ofStage,
    coherentComplexificationColimitMap_stage]

theorem coherentComplexificationColimit_stageStarMap_conjTranspose
    (n : ℕ) (A : ClStage n) :
    coherentComplexificationColimitMap
        (coherentAlgebraicToTopological (stageStarMap n A)) =
      CuntzMatrixTraceTopologicalColimit.topologicalInclusion concreteData n
        (Matrix.conjTranspose (coherentComplexifyClStage n A)) := by
  rw [coherentComplexificationColimit_stageStarMap]
  simpa only [Matrix.star_eq_conjTranspose] using
    coherentComplexifyClStage_topological_star_readback n A

/-- The two `TopCat` realizations use the same finite stages.  This morphism
    transports the older CAR presentation to the Markov--Jones presentation
    by the identity on every finite stage. -/
noncomputable def cliffordCARToCl11MarkovCocone :
    Cocone CliffordCARTopologicalColimit.topologicalDiagram where
  pt := Cl11MarkovJonesTopologicalColimit.topologicalColimitObject
  ι :=
    { app := fun n => Cl11MarkovJonesTopologicalColimit.topologicalInclusion n
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro A
        rw [TopCat.comp_app]
        change Cl11MarkovJonesTopologicalColimit.topologicalInclusion n
            (CliffordCARTopologicalColimit.bondCLM _ _ (leOfHom f) A) =
          Cl11MarkovJonesTopologicalColimit.topologicalInclusion m A
        rw [CliffordCARTopologicalColimit.bondCLM_apply,
          CliffordCARAlgebraicTopologicalComparison.bondAlgHom_eq_bondMap,
          ← coherentStageEmbedMap_eq_bondMap (leOfHom f) A]
        change colimit.ι Cl11MarkovJonesTopologicalColimit.topologicalDiagram n
            (Cl11MarkovJonesTopologicalColimit.topologicalDiagram.map f A) =
          colimit.ι Cl11MarkovJonesTopologicalColimit.topologicalDiagram m A
        exact FilteredColimit.Native.Topological.topologicalDirectInjection_naturality_apply
          Cl11MarkovJonesTopologicalColimit.topologicalDiagram (f := f) A }

noncomputable def cliffordCARToCl11MarkovTopological :
    CliffordCARTopologicalColimit.topologicalColimit ⟶
      Cl11MarkovJonesTopologicalColimit.topologicalColimitObject :=
  colimit.desc
    CliffordCARTopologicalColimit.topologicalDiagram
    cliffordCARToCl11MarkovCocone

theorem cliffordCARToCl11MarkovTopological_stage (n : ℕ) (A : ClStage n) :
    cliffordCARToCl11MarkovTopological
        (CliffordCARTopologicalColimit.topologicalInjection n A) =
      Cl11MarkovJonesTopologicalColimit.topologicalInclusion n A := by
  have h := FilteredColimit.Native.Topological.topologicalDirectDescend_stage
    CliffordCARTopologicalColimit.topologicalDiagram
    cliffordCARToCl11MarkovCocone n
  exact congrArg (fun g => g A) h

theorem coherentAlgebraicToTopological_factorization :
    (fun x => cliffordCARToCl11MarkovTopological
      (CliffordCARAlgebraicTopologicalComparison.algebraicToTopological x)) =
      coherentAlgebraicToTopological := by
  funext x
  induction x using DirectLimit.induction with
  | _ n A =>
      change cliffordCARToCl11MarkovTopological
          (CliffordCARAlgebraicTopologicalComparison.algebraicToTopological
            (ofStage n A)) =
        coherentAlgebraicToTopological (ofStage n A)
      rw [CliffordCARAlgebraicTopologicalComparison.algebraicToTopological_ofStage]
      rw [coherentAlgebraicToTopological_ofStage]
      exact cliffordCARToCl11MarkovTopological_stage n A

/-- The finite normalized Markov trace also descends through the algebraic
    direct limit as a real-linear map. -/
theorem normalizedTraceLimit_compatible
    (m n : ℕ) (h : m ≤ n) (A : ClStage m) :
    InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n
        (bondMap stageBond m n h A) =
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear m A := by
  rw [← coherentStageEmbedMap_eq_bondMap h A]
  simpa [InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear] using
    (Cl11MarkovJonesTopologicalColimit.normalizedTrace_stageEmbedMap h A)

noncomputable def normalizedTraceLimit :
    Limit →+ ℝ :=
  { toFun :=
      _root_.DirectLimit.lift
        (fun m n h => bondMap stageBond m n h)
        (fun n => InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n)
        (by
          intro m n h A
          exact (normalizedTraceLimit_compatible m n h A).symm)
    map_add' := by
      intro x y
      induction x, y using DirectLimit.induction₂ with
      | _ n A B =>
          rw [DirectLimit.add_def, DirectLimit.lift_def]
          change InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n
              (A + B) =
            InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n A +
              InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n B
          exact map_add _ A B
    map_zero' := by
      rw [DirectLimit.zero_def 0, DirectLimit.lift_def]
      exact map_zero _ }

@[simp] theorem normalizedTraceLimit_ofStage (n : ℕ) (A : ClStage n) :
    normalizedTraceLimit (ofStage n A) =
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n A := by
  rfl

theorem normalizedTraceLimit_factorization :
    (fun x =>
      Cl11MarkovJonesTopologicalColimit.traceTopologicalColimitMap
        (coherentAlgebraicToTopological x)) =
      normalizedTraceLimit := by
  funext x
  induction x using DirectLimit.induction with
  | _ n A =>
      change Cl11MarkovJonesTopologicalColimit.traceTopologicalColimitMap
          (coherentAlgebraicToTopological (ofStage n A)) =
        normalizedTraceLimit (ofStage n A)
      rw [coherentAlgebraicToTopological_ofStage,
        Cl11MarkovJonesTopologicalColimit.traceTopologicalColimitMap_inclusion,
        normalizedTraceLimit_ofStage]
      rfl

/-- The stagewise involution readout descends to an additive endomorphism of
    the concrete algebraic direct limit. -/
noncomputable def limitStarAddHom : Limit →+ Limit where
  toFun :=
    _root_.DirectLimit.lift
      (fun m n h => bondMap stageBond m n h)
      (fun n => stageStarMap n)
      (by
        intro m n h A
        exact (stageStarMap_compat m n h A).symm)
  map_add' := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ n A B =>
        rw [DirectLimit.add_def, DirectLimit.lift_def]
        change stageStarMap n (A + B) =
          stageStarMap n A + stageStarMap n B
        exact map_add _ A B
  map_zero' := by
    have hzero :
        (0 : Limit) =
          (⟦(⟨0, (0 : ClStage 0)⟩ : Σ n, ClStage n)⟧ : Limit) :=
      DirectLimit.zero_def
        (G := fun n => ClStage n)
        (f := fun m n h => bondMap stageBond m n h) 0
    conv_lhs => rw [hzero]
    rw [DirectLimit.lift_def]
    exact map_zero (stageStarMap 0)

@[simp] theorem limitStarAddHom_ofStage (n : ℕ) (A : ClStage n) :
    limitStarAddHom (ofStage n A) = stageStarMap n A := by
  rfl

theorem limitStarAddHom_involutive (x : Limit) :
    limitStarAddHom (limitStarAddHom x) = x := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change stageStarMap n (star A) = ofStage n A
      rfl

end InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
