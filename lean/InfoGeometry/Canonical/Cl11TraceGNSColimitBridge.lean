import InfoGeometry.Cosmology.Cl11ParabolicVacuumQuotientBridge
import InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
import InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
import InfoGeometry.Canonical.CuntzMatrixAlgebraicGNSBridge

/-!
# The finite `Cl(1,1)` trace-GNS carrier and the native colimit

The stage-one normalized-trace GNS quotient has a canonical map to the
algebraic direct limit of the `Cl(1,1)` matrix tower.  Its normalized-trace
readout agrees with the existing `TopCat` colimit trace cocone.  These are
maps and readout identities on the repository's actual carriers; this file
does not identify the algebraic quotient with a completion or with the whole
topological colimit.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11TraceGNSColimitBridge

open InfoGeometry.Canonical.Cl11FiniteTraceGNSAction
open InfoGeometry.Canonical.Cl11FiniteTraceGNSReadout
open InfoGeometry.Canonical.Cl11FiniteNormalizedTraceState
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Canonical.JordanWignerCantorRepresentation
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge
open InfoGeometry.Canonical.CuntzMatrixAlgebraicGNSBridge
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Cosmology.Cl11ParabolicVacuumQuotientBridge
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Prequantum.GNSBridge.AbstractGNSState

/-- The class of a finite stage-one trace-GNS representative in the
algebraic direct limit of the Clifford matrix tower. -/
noncomputable def traceGNS_to_algebraicLimit :
    cl11RepresentationQuotient 1 → Limit :=
  Quotient.lift (fun X : MatStage 1 => ofStage 1 X) (by
    intro X Y hXY
    have hEq := cl11TraceGNS_stageOne_setoid_eq hXY
    exact congrArg (ofStage 1) hEq)

@[simp] theorem traceGNS_to_algebraicLimit_mk (X : MatStage 1) :
    traceGNS_to_algebraicLimit
      (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state) X) =
        ofStage 1 X := rfl

/-- The stage-one map into the algebraic Clifford tower is injective because
each tensor-with-identity bond is injective. -/
theorem ofStage_stageOne_injective : Function.Injective (ofStage 1) := by
  apply directLimitOf_injective stageBond
  intro n
  change Function.Injective (matStageEmbed n)
  exact matStageEmbed_injective n

/-- Every transition of the Cuntz matrix tower is injective: it is a finite
composition of the injective successor map `A ↦ A ⊗ 1`. -/
theorem cuntzConcreteMap_injective {i j : ℕ} (hij : i ≤ j) :
    Function.Injective (concreteMap hij) := by
  change Function.Injective (map concreteData hij)
  induction hij with
  | refl =>
      rw [map_id]
      exact Function.injective_id
  | @step j hij ih =>
      rw [map_succ concreteData hij]
      exact (concreteStep j).injective.comp ih

/-- The canonical algebraic Cuntz direct-limit stage map is injective. -/
theorem cuntzStageInjection_injective (n : ℕ) :
    Function.Injective (stageInjection n) := by
  change Function.Injective (fun x : MatrixStage n =>
    (⟦⟨n, x⟩⟧ : Carrier))
  exact DirectLimit.mk_injective
    (f := fun i j hij => rawMap hij)
    (fun i j hij => by
      change Function.Injective (concreteMap hij)
      exact cuntzConcreteMap_injective hij) n

/-- Entrywise real-to-complex scalar extension is injective at the coherent
finite stage, since `Complex.ofReal` is injective and reindexing is an
equivalence. -/
theorem coherentComplexifyClStage_injective (n : ℕ) :
    Function.Injective (coherentComplexifyClStage n) := by
  intro A B hAB
  have hComplexify : complexifyMatrixAlgHom n A = complexifyMatrixAlgHom n B :=
    (Matrix.reindexAlgEquiv ℝ ℂ (coherentIdxEquivFinPowTwo n)).injective hAB
  ext i j
  have hEntry := congrArg (fun M => M i j) hComplexify
  have hEntry : Complex.ofReal (A i j) = Complex.ofReal (B i j) := by
    simpa [complexifyMatrixAlgHom, RingHom.mapMatrix_apply] using hEntry
  exact Complex.ofReal_injective hEntry

/-- The faithful finite trace-GNS quotient embeds into the algebraic
Clifford tower.  Faithfulness identifies equivalent GNS representatives,
and injectivity of the tower inclusions reflects equality back to stage one.
-/
theorem traceGNS_to_algebraicLimit_injective :
    Function.Injective traceGNS_to_algebraicLimit := by
  intro q r h
  revert h
  refine Quotient.inductionOn₂ q r ?_
  intro X Y h
  have hColimit : ofStage 1 X = ofStage 1 Y := by
    simpa only [traceGNS_to_algebraicLimit_mk] using h
  have hStage : X = Y := ofStage_stageOne_injective hColimit
  subst Y
  rfl

/-- The raising-root class remains nonzero in the algebraic tower image,
although the distinct vacuum-column quotient annihilates that class. This
exhibits the concrete kernel difference between the faithful trace-GNS lane
and the vacuum-state quotient lane. -/
theorem traceRoot_survives_colimit_but_vanishes_vacuum :
    ofStage 1 (matrixToCl11StageOne
      InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus) ≠ 0 ∧
      cl11TraceGNS_to_vacuumNullQuotient
        (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state)
          (matrixToCl11StageOne
            InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus)) = 0 := by
  constructor
  · intro hzero
    apply cl11TraceGNS_rootPlus_nonzero_in_kernel.1
    apply traceGNS_to_algebraicLimit_injective
    simpa only [traceGNS_to_algebraicLimit_mk, map_zero] using hzero
  · exact cl11TraceGNS_rootPlus_nonzero_in_kernel.2

/-- The native finite GNS left action is carried to multiplication in the
algebraic direct limit. This is the representation-action compatibility for
the actual stage-one quotient and tower inclusion. -/
theorem traceGNS_to_algebraicLimit_left_action
    (A : MatStage 1) (q : cl11RepresentationQuotient 1) :
    traceGNS_to_algebraicLimit (cl11Action 1 A q) =
      ofStage 1 A * traceGNS_to_algebraicLimit q := by
  refine Quotient.inductionOn q ?_
  intro X
  rw [cl11Action_mk, traceGNS_to_algebraicLimit_mk,
    traceGNS_to_algebraicLimit_mk]
  exact map_mul (ofStage 1) A X

/-- Composition of finite GNS actions agrees with multiplication in the
colimit, as a consequence of the action intertwiner. -/
theorem traceGNS_to_algebraicLimit_action_mul
    (A B : MatStage 1) (q : cl11RepresentationQuotient 1) :
    traceGNS_to_algebraicLimit (cl11Action 1 (A * B) q) =
      ofStage 1 A * ofStage 1 B * traceGNS_to_algebraicLimit q := by
  rw [cl11Action_mul, traceGNS_to_algebraicLimit_left_action,
    traceGNS_to_algebraicLimit_left_action, mul_assoc]

/-- The normalized trace descends to the stage-one trace-GNS quotient.
Faithfulness makes the GNS equivalence relation equality of representatives,
so this descended scalar readout is well-defined. -/
noncomputable def traceGNS_eval : cl11RepresentationQuotient 1 → ℝ :=
  Quotient.lift (normalizedTrace 1) (by
    intro X Y hXY
    have hEq := cl11TraceGNS_stageOne_setoid_eq hXY
    rw [hEq])

@[simp] theorem traceGNS_eval_mk (X : MatStage 1) :
    traceGNS_eval
      (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state) X) =
        normalizedTrace 1 X := rfl

/-- The direct-limit trace evaluated on the image of a GNS class is its
descended finite-state value. -/
theorem topologicalTrace_comp_classMap (q : cl11RepresentationQuotient 1) :
    normalizedTraceTopologicalColimitMap
      (algebraicToTopological (traceGNS_to_algebraicLimit q)) =
        traceGNS_eval q := by
  refine Quotient.inductionOn q ?_
  intro X
  rw [traceGNS_to_algebraicLimit_mk, traceGNS_eval_mk]
  exact normalizedTraceTopologicalColimitMap_algebraic_stage 1 X

/-- Under the standard `2 × 2` matrix coordinates, the colimit readout of
the stage-one class is the ordinary matrix trace divided by two. -/
theorem topologicalTrace_stageOne_matrix (A : RealMatrix2) :
    normalizedTraceTopologicalColimitMap
      (algebraicToTopological
        (traceGNS_to_algebraicLimit
          (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state)
            (matrixToCl11StageOne A)))) =
        Matrix.trace A / 2 := by
  rw [topologicalTrace_comp_classMap, traceGNS_eval_mk,
    normalizedTrace_stageOne_matrixToCl11]

/-- Send a stage-one trace-GNS class through the algebraic Clifford limit,
the coherent real-to-complex tower map, and into the existing Cuntz matrix
`TopCat` colimit. -/
noncomputable def traceGNS_to_CuntzTopologicalColimit
    (q : cl11RepresentationQuotient 1) :
    topologicalColimitObject concreteData :=
  coherentComplexificationColimitMap
    (coherentAlgebraicToTopological (traceGNS_to_algebraicLimit q))

/-- The Cuntz-colimit real-trace readout of a trace-GNS class is exactly its
descended finite normalized-trace value. This is the readout compatibility
for the composite map from the finite GNS carrier into the coherent Cuntz
colimit. -/
theorem traceGNS_CuntzColimit_realTrace (q : cl11RepresentationQuotient 1) :
    realTraceTopologicalColimitMap concreteData
      (traceGNS_to_CuntzTopologicalColimit q) = traceGNS_eval q := by
  refine Quotient.inductionOn q ?_
  intro X
  rw [traceGNS_to_CuntzTopologicalColimit,
    traceGNS_to_algebraicLimit_mk,
    coherentAlgebraicToTopological_ofStage,
    traceGNS_eval_mk]
  exact coherentComplexificationColimit_realTrace_stage 1 X

/-- In standard matrix coordinates, the real trace on the Cuntz colimit
recovers half the ordinary trace of the stage-one representative. -/
theorem traceGNS_CuntzColimit_stageOne_matrix (A : RealMatrix2) :
    realTraceTopologicalColimitMap concreteData
      (traceGNS_to_CuntzTopologicalColimit
        (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state)
          (matrixToCl11StageOne A))) = Matrix.trace A / 2 := by
  rw [traceGNS_CuntzColimit_realTrace, traceGNS_eval_mk,
    normalizedTrace_stageOne_matrixToCl11]

/-! ## Algebraic GNS quotient bridge -/

/-- The stage-one Clifford trace-GNS class maps to the GNS class of the
coherently complexified matrix in the algebraic Cuntz matrix direct limit.
The target is the repository's algebraic GNS quotient, whose underlying
setoid is proved to be equality by `algebraicTraceGNSQuotient_is_exact_carrier`.
This map is constructed on quotient classes, not inferred from a scalar trace
identity. -/
noncomputable def traceGNS_to_CuntzAlgebraicGNS
    (q : cl11RepresentationQuotient 1) :
    algebraicTraceGNSQuotient :=
  Quotient.lift
    (fun X : MatStage 1 =>
      (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState)
        (stageInjection 1 (coherentComplexifyClStage 1 X)) :
          algebraicTraceGNSQuotient))
    (by
      intro X Y hXY
      have hEq := cl11TraceGNS_stageOne_setoid_eq hXY
      exact congrArg
        (fun Z : MatStage 1 =>
          (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState)
            (stageInjection 1 (coherentComplexifyClStage 1 Z)) :
              algebraicTraceGNSQuotient)) hEq)
    q

@[simp] theorem traceGNS_to_CuntzAlgebraicGNS_mk (X : MatStage 1) :
    traceGNS_to_CuntzAlgebraicGNS
      (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state) X) =
        (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState)
          (stageInjection 1 (coherentComplexifyClStage 1 X)) :
            algebraicTraceGNSQuotient) := rfl

/-- The normalized trace descends to the algebraic Cuntz GNS quotient.  The
GNS relation identifies elements whose difference is null; pairing that
difference with the unit and using symmetry of the trace shows their state
values agree. -/
noncomputable def CuntzAlgebraicGNS_eval : algebraicTraceGNSQuotient → ℝ :=
  Quotient.lift (fun x : Carrier => realTraceState.eval x) (by
    intro x y hxy
    have hnull : x - y ∈ realTraceState.gnsNullSet := hxy
    have hpair := RealAlgebraicState.state_null_product_zero
      realTraceState (1 : Carrier) (x - y) hnull
    have hpair' : realTraceState.eval (star (x - y)) = 0 := by
      simpa [RealAlgebraicState.eval] using hpair
    have hsymmetric : realTraceState.eval (x - y) =
        realTraceState.eval (star (x - y)) := by
      simpa [RealAlgebraicState.eval] using
        realTraceState.symmetric (x - y) (1 : Carrier)
    have hdiff : realTraceState.eval (x - y) = 0 := hsymmetric.trans hpair'
    have hmap := realTraceState.toLinearMap.map_sub x y
    change realTraceState.eval (x - y) =
      realTraceState.eval x - realTraceState.eval y at hmap
    rw [hdiff] at hmap
    linarith)

@[simp] theorem CuntzAlgebraicGNS_eval_mk (x : Carrier) :
    CuntzAlgebraicGNS_eval
      (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState) x) =
        realTraceState.eval x := rfl

/-- Left multiplication on the algebraic Cuntz GNS quotient. Faithfulness
identifies its quotient relation with equality, so multiplication descends
without adding a separate ideal hypothesis. -/
def CuntzAlgebraicGNSAction (a : Carrier)
    (q : algebraicTraceGNSQuotient) : algebraicTraceGNSQuotient :=
  Quotient.liftOn q
    (fun x =>
      (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState) (a * x) :
        algebraicTraceGNSQuotient))
    (by
      intro x y hxy
      have hEq : x = y := by
        rw [algebraicTraceGNSQuotient_is_exact_carrier] at hxy
        exact hxy
      subst y
      rfl)

@[simp] theorem CuntzAlgebraicGNSAction_mk (a x : Carrier) :
    CuntzAlgebraicGNSAction a
      (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState) x) =
        (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState) (a * x) :
          algebraicTraceGNSQuotient) := rfl

theorem CuntzAlgebraicGNSAction_one (q : algebraicTraceGNSQuotient) :
    CuntzAlgebraicGNSAction 1 q = q := by
  refine Quotient.inductionOn q ?_
  intro x
  simp [CuntzAlgebraicGNSAction]

theorem CuntzAlgebraicGNSAction_mul (a b : Carrier)
    (q : algebraicTraceGNSQuotient) :
    CuntzAlgebraicGNSAction (a * b) q =
      CuntzAlgebraicGNSAction a (CuntzAlgebraicGNSAction b q) := by
  refine Quotient.inductionOn q ?_
  intro x
  simp [CuntzAlgebraicGNSAction, mul_assoc]

/-- The class map preserves the GNS state readout: the finite normalized
Clifford trace agrees with the real part of the coherent complex matrix trace
in the Cuntz algebraic GNS carrier. -/
theorem traceGNS_CuntzAlgebraicGNS_eval (q : cl11RepresentationQuotient 1) :
    CuntzAlgebraicGNS_eval (traceGNS_to_CuntzAlgebraicGNS q) = traceGNS_eval q := by
  refine Quotient.inductionOn q ?_
  intro X
  rw [traceGNS_to_CuntzAlgebraicGNS_mk, CuntzAlgebraicGNS_eval_mk,
    traceGNS_eval_mk]
  rw [realTraceState_stage]
  change (matrixTraceFunctional 1 (coherentComplexifyClStage 1 X)).re = _
  rw [coherentComplexifyClStage_normalizedTrace]
  simp

/-- The finite GNS representation action intertwines with left multiplication
in the algebraic Cuntz GNS representation under the quotient embedding. -/
theorem traceGNS_CuntzAlgebraicGNS_action
    (A : MatStage 1) (q : cl11RepresentationQuotient 1) :
    traceGNS_to_CuntzAlgebraicGNS (cl11Action 1 A q) =
      CuntzAlgebraicGNSAction
        (stageInjection 1 (coherentComplexifyClStage 1 A))
        (traceGNS_to_CuntzAlgebraicGNS q) := by
  refine Quotient.inductionOn q ?_
  intro X
  simp only [cl11Action_mk, traceGNS_to_CuntzAlgebraicGNS_mk,
    CuntzAlgebraicGNSAction_mk]
  congr 1
  rw [map_mul, map_mul]

/-- The finite trace-GNS cyclic vector maps to the algebraic Cuntz trace-GNS
vacuum class. -/
theorem traceGNS_to_CuntzAlgebraicGNS_vacuum :
    traceGNS_to_CuntzAlgebraicGNS
      (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state) (1 : MatStage 1)) =
      algebraicTraceGNSVacuum := by
  change Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState)
      (stageInjection 1 (coherentComplexifyClStage 1 (1 : MatStage 1))) =
    Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState) (1 : Carrier)
  apply congrArg (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState))
  simp only [map_one]

/-- On the standard real matrix representative, the algebraic Cuntz GNS
class is represented by its ordinary entrywise complexification. -/
theorem traceGNS_to_CuntzAlgebraicGNS_stageOne_matrix (A : RealMatrix2) :
    traceGNS_to_CuntzAlgebraicGNS
      (Quotient.mk (gnsSetoid (cl11RepresentationState 1).state)
        (matrixToCl11StageOne A)) =
      (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState)
        (stageInjection 1
          (coherentComplexifyClStage 1 (matrixToCl11StageOne A)) : Carrier) :
            algebraicTraceGNSQuotient) := by
  rfl

/-- The quotient map into the algebraic Cuntz GNS carrier is injective.
The target GNS relation is equality by trace faithfulness, the Cuntz stage
map is injective by the direct-limit embedding theorem, and coherent
complexification is entrywise injective. -/
theorem traceGNS_to_CuntzAlgebraicGNS_injective :
    Function.Injective traceGNS_to_CuntzAlgebraicGNS := by
  intro q r hqr
  revert hqr
  refine Quotient.inductionOn₂ q r ?_
  intro X Y hXY
  have hCarrier := Quotient.exact hXY
  rw [algebraicTraceGNSQuotient_is_exact_carrier] at hCarrier
  have hStage :
      stageInjection 1 (coherentComplexifyClStage 1 X) =
        stageInjection 1 (coherentComplexifyClStage 1 Y) := hCarrier
  have hComplex : coherentComplexifyClStage 1 X =
      coherentComplexifyClStage 1 Y := cuntzStageInjection_injective 1 hStage
  have hEqual : X = Y := coherentComplexifyClStage_injective 1 hComplex
  subst Y
  rfl

/-! ## Algebraic Cuntz GNS to topological colimit comparison -/

/-- The algebraic Cuntz matrix direct limit maps to its native `TopCat`
colimit by sending each finite-stage representative to the canonical
topological injection. -/
noncomputable def CuntzAlgebraicToTopologicalColimit :
    Carrier → topologicalColimitObject concreteData :=
  DirectLimit.lift
    (f := fun i j hij => rawMap hij)
    (fun n A => topologicalInclusion concreteData n A)
    (by
      intro i j hij A
      simpa [rawMap, concreteMap] using
        (topologicalInclusion_transition concreteData hij A).symm)

@[simp] theorem CuntzAlgebraicToTopologicalColimit_stage
    (n : ℕ) (A : MatrixStage n) :
    CuntzAlgebraicToTopologicalColimit (stageInjection n A) =
      topologicalInclusion concreteData n A := rfl

/-- The algebraic Cuntz GNS quotient maps to the topological colimit because
its trace-faithful GNS relation is equality on the algebraic carrier. -/
noncomputable def CuntzAlgebraicGNS_to_TopologicalColimit
    (q : algebraicTraceGNSQuotient) :
    topologicalColimitObject concreteData :=
  Quotient.lift
    (fun x : Carrier => CuntzAlgebraicToTopologicalColimit x)
    (by
      intro x y hxy
      have hEq : x = y := by
        rw [algebraicTraceGNSQuotient_is_exact_carrier] at hxy
        exact hxy
      exact congrArg CuntzAlgebraicToTopologicalColimit hEq)
    q

@[simp] theorem CuntzAlgebraicGNS_to_TopologicalColimit_mk (x : Carrier) :
    CuntzAlgebraicGNS_to_TopologicalColimit
      (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState) x) =
        CuntzAlgebraicToTopologicalColimit x := rfl

/-- Triangle compatibility: the direct algebraic-Cuntz route and the
coherent Clifford-to-Cuntz-topological route send every finite trace-GNS
class to the same topological-colimit point. -/
theorem traceGNS_topological_routes_agree
    (q : cl11RepresentationQuotient 1) :
    CuntzAlgebraicGNS_to_TopologicalColimit
        (traceGNS_to_CuntzAlgebraicGNS q) =
      traceGNS_to_CuntzTopologicalColimit q := by
  refine Quotient.inductionOn q ?_
  intro X
  rw [traceGNS_to_CuntzAlgebraicGNS_mk,
    CuntzAlgebraicGNS_to_TopologicalColimit_mk,
    CuntzAlgebraicToTopologicalColimit_stage]
  rw [traceGNS_to_CuntzTopologicalColimit,
    traceGNS_to_algebraicLimit_mk,
    coherentAlgebraicToTopological_ofStage,
    coherentComplexificationColimitMap_stage]

end InfoGeometry.Canonical.Cl11TraceGNSColimitBridge
