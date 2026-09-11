import InfoGeometry.Canonical.CARCCRFockCuntzParameterTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
import InfoGeometry.Canonical.CuntzStarInductiveSystem
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological readouts for CAR, CCR, and Cuntz witnesses

The algebraic CAR/CCR/Fock/Cuntz relations are owned by
`CARCCRFockCuntzBridge`.  This file only packages the already verified CAR,
CCR, and Cuntz endpoint witnesses as continuous maps into the common
noncommutative q-CCR zero locus.  The Fock left-regular q = 0 identity remains
an operator identity on its native algebraic carrier; no discrete topology or
finite matrix surrogate is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout

universe u

open CategoryTheory
open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.CARCCRFockCuntzParameterTopology
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Physics.CStarCuntzTensorQuotient
open CStarStateColimit.Native
open InfoGeometry.Canonical.CuntzStarInductiveSystem

variable {A : Type*} [CStarAlgebra A]

def carParameterPoint (c cstar : A) : QCCRParameterSpace A :=
  (c, (cstar, (-1 : A)))

def ccrParameterPoint (c cstar : A) : QCCRParameterSpace A :=
  (c, (cstar, (1 : A)))

def carParameterPointTopCatHom
    (c cstar : A) (h : c * cstar + cstar * c = 1) :
    TopCat.of PUnit ⟶
      TopCat.of (qCcrParameterZeroLocus (A := A)) :=
  TopCat.ofHom
    { toFun := fun _ =>
        ⟨carParameterPoint c cstar,
          by
            change qCcrParameterResidualContinuousMap (A := A)
                (c, (cstar, (-1 : A))) = 0
            simpa [qCcrParameterResidualContinuousMap] using
              (car_is_neg_one_qccr c cstar h)⟩
      continuous_toFun := continuous_const }

def ccrParameterPointTopCatHom
    (c cstar : A) (h : c * cstar - cstar * c = 1) :
    TopCat.of PUnit ⟶
      TopCat.of (qCcrParameterZeroLocus (A := A)) :=
  TopCat.ofHom
    { toFun := fun _ =>
        ⟨ccrParameterPoint c cstar,
          by
            change qCcrParameterResidualContinuousMap (A := A)
                (c, (cstar, (1 : A))) = 0
            simpa [qCcrParameterResidualContinuousMap] using
              (ccr_is_plus_one_qccr c cstar h)⟩
      continuous_toFun := continuous_const }

@[simp] theorem carParameterPointTopCatHom_apply
    (c cstar : A) (h : c * cstar + cstar * c = 1) (u : PUnit) :
    carParameterPointTopCatHom c cstar h u =
      (⟨carParameterPoint c cstar,
        by
          change qCcrParameterResidualContinuousMap (A := A)
              (c, (cstar, (-1 : A))) = 0
          simpa [qCcrParameterResidualContinuousMap] using
            (car_is_neg_one_qccr c cstar h)⟩ :
        qCcrParameterZeroLocus (A := A)) :=
  rfl

@[simp] theorem ccrParameterPointTopCatHom_apply
    (c cstar : A) (h : c * cstar - cstar * c = 1) (u : PUnit) :
    ccrParameterPointTopCatHom c cstar h u =
      (⟨ccrParameterPoint c cstar,
        by
          change qCcrParameterResidualContinuousMap (A := A)
              (c, (cstar, (1 : A))) = 0
          simpa [qCcrParameterResidualContinuousMap] using
            (ccr_is_plus_one_qccr c cstar h)⟩ :
        qCcrParameterZeroLocus (A := A)) :=
  rfl

def cstarCuntzParameterPoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : CStarCuntzFamily A ι) (i : ι) : QCCRParameterSpace A :=
  (star (F.S i), (F.S i, (0 : A)))

def cstarCuntzParameterPointTopCatHom
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : CStarCuntzFamily A ι) (i : ι) :
    TopCat.of PUnit ⟶
      TopCat.of (qCcrParameterZeroLocus (A := A)) :=
  TopCat.ofHom
    { toFun := fun _ =>
        ⟨cstarCuntzParameterPoint F i,
          by
            change qCcrParameterResidualContinuousMap (A := A)
                (star (F.S i), (F.S i, (0 : A))) = 0
            simpa [qCcrParameterResidualContinuousMap] using
              (cstar_cuntz_generator_qccr_zero F i)⟩
      continuous_toFun := continuous_const }

@[simp] theorem cstarCuntzParameterPointTopCatHom_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : CStarCuntzFamily A ι) (i : ι) (u : PUnit) :
    cstarCuntzParameterPointTopCatHom F i u =
      (⟨cstarCuntzParameterPoint F i,
        by
          change qCcrParameterResidualContinuousMap (A := A)
              (star (F.S i), (F.S i, (0 : A))) = 0
          simpa [qCcrParameterResidualContinuousMap] using
            (cstar_cuntz_generator_qccr_zero F i)⟩ :
        qCcrParameterZeroLocus (A := A)) :=
  rfl

/-! ### Naturality through a filtered star-algebra system -/

theorem carParameterPointTopCatHom_transition_natural
    {I : Type u} [Preorder I]
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)]
    [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    {i j : I} (hij : i ≤ j)
    (c cstar : Stage i) (h : c * cstar + cstar * c = 1) :
    carParameterPointTopCatHom c cstar h ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage sys hij =
      carParameterPointTopCatHom (sys.map hij c) (sys.map hij cstar) (by
        calc
          sys.map hij c * sys.map hij cstar +
              sys.map hij cstar * sys.map hij c =
            sys.map hij (c * cstar + cstar * c) := by simp
          _ = sys.map hij 1 := by rw [h]
          _ = 1 := map_one (sys.map hij)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change qCcrParameterTransitionMap Stage sys hij
      (carParameterPoint c cstar) =
    carParameterPoint (sys.map hij c) (sys.map hij cstar)
  simp [qCcrParameterTransitionMap, carParameterPoint]

theorem ccrParameterPointTopCatHom_transition_natural
    {I : Type u} [Preorder I]
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)]
    [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    {i j : I} (hij : i ≤ j)
    (c cstar : Stage i) (h : c * cstar - cstar * c = 1) :
    ccrParameterPointTopCatHom c cstar h ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage sys hij =
      ccrParameterPointTopCatHom (sys.map hij c) (sys.map hij cstar) (by
        calc
          sys.map hij c * sys.map hij cstar -
              sys.map hij cstar * sys.map hij c =
            sys.map hij (c * cstar - cstar * c) := by simp
          _ = sys.map hij 1 := by rw [h]
          _ = 1 := map_one (sys.map hij)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change qCcrParameterTransitionMap Stage sys hij
      (ccrParameterPoint c cstar) =
    ccrParameterPoint (sys.map hij c) (sys.map hij cstar)
  simp [qCcrParameterTransitionMap, ccrParameterPoint]

theorem cstarCuntzParameterPointTopCatHom_transition_natural
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (T : CuntzStarTower Stage) {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    cstarCuntzParameterPointTopCatHom (T.family m) i ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage
          T.toContinuousStarInductiveSystem hmn =
      cstarCuntzParameterPointTopCatHom (T.family n) (Fin.castLE hmn i) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change qCcrParameterTransitionMap Stage
      T.toContinuousStarInductiveSystem hmn
      (cstarCuntzParameterPoint (T.family m) i) =
    cstarCuntzParameterPoint (T.family n) (Fin.castLE hmn i)
  simp [qCcrParameterTransitionMap, cstarCuntzParameterPoint,
    T.map_generator, map_star]

/-! ### Colimit readout of a Cuntz generator parameter point

The point attached to an old generator may be represented at any later stage.
The following definitions keep that stagewise representative bundled in the
closed q-CCR fiber diagram, and the transition theorem records that its image
in the topological colimit is independent of the chosen later stage.
-/

def cstarCuntzParameterZeroFiberPoint
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (T : CuntzStarTower Stage) (m : ℕ) (i : Fin m) :
    {p : QCCRParameterSpace (Stage m) //
      p ∈ qCcrParameterZeroLocus (A := Stage m)} :=
  cstarCuntzParameterPointTopCatHom (T.family m) i PUnit.unit

def cstarCuntzParameterColimitPoint
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (T : CuntzStarTower Stage) (m : ℕ) (i : Fin m) :
    qCcrParameterZeroFiberTopologicalColimit Stage
      T.toContinuousStarInductiveSystem :=
  qCcrParameterZeroFiberTopologicalInjection Stage
    T.toContinuousStarInductiveSystem m
    (cstarCuntzParameterZeroFiberPoint T m i)

theorem cstarCuntzParameterColimitPoint_stage_independent
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (T : CuntzStarTower Stage) {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    cstarCuntzParameterColimitPoint T n (Fin.castLE hmn i) =
      cstarCuntzParameterColimitPoint T m i := by
  have hpoint := congrArg (fun f => f PUnit.unit)
    (cstarCuntzParameterPointTopCatHom_transition_natural
      T hmn i)
  calc
    cstarCuntzParameterColimitPoint T n (Fin.castLE hmn i) =
      qCcrParameterZeroFiberTopologicalInjection Stage
          T.toContinuousStarInductiveSystem n
            (qCcrParameterZeroFiberTransitionMap Stage
              T.toContinuousStarInductiveSystem hmn
              (cstarCuntzParameterZeroFiberPoint T m i)) := by
      have hp : cstarCuntzParameterZeroFiberPoint T n (Fin.castLE hmn i) =
          qCcrParameterZeroFiberTransitionMap Stage
            T.toContinuousStarInductiveSystem hmn
            (cstarCuntzParameterZeroFiberPoint T m i) := by
        simpa [cstarCuntzParameterZeroFiberPoint,
          qCcrParameterZeroFiberTransitionTopCatHom] using hpoint.symm
      exact congrArg
        (fun p => qCcrParameterZeroFiberTopologicalInjection Stage
          T.toContinuousStarInductiveSystem n p) hp
    _ = cstarCuntzParameterColimitPoint T m i := by
      exact qCcrParameterZeroFiberTopologicalInjection_transition
        Stage T.toContinuousStarInductiveSystem hmn
        (cstarCuntzParameterZeroFiberPoint T m i)

theorem cstarCuntzParameterColimitPoint_ambient
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (T : CuntzStarTower Stage) (m : ℕ) (i : Fin m) :
    qCcrParameterZeroFiberToParameterColimit Stage
        T.toContinuousStarInductiveSystem
        (cstarCuntzParameterColimitPoint T m i) =
      qCcrParameterTopologicalInjection Stage
        T.toContinuousStarInductiveSystem m
        (cstarCuntzParameterZeroFiberPoint T m i).1 := by
  have h := qCcrParameterZeroFiberToParameterColimit_stage
    Stage T.toContinuousStarInductiveSystem m
  have hp := congrArg
    (fun f => f (cstarCuntzParameterZeroFiberPoint T m i)) h
  simpa [cstarCuntzParameterColimitPoint,
    qCcrParameterZeroFiberToParameterNatTrans] using hp

def carParameterZeroFiberPoint
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    (m : ℕ) (c cstar : Stage m)
    (h : c * cstar + cstar * c = 1) :
    {p : QCCRParameterSpace (Stage m) //
      p ∈ qCcrParameterZeroLocus (A := Stage m)} :=
  carParameterPointTopCatHom c cstar h PUnit.unit

def carParameterColimitPoint
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (sys : ContinuousStarInductiveSystem Stage)
    (m : ℕ) (c cstar : Stage m)
    (h : c * cstar + cstar * c = 1) :
    qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  qCcrParameterZeroFiberTopologicalInjection Stage sys m
    (carParameterZeroFiberPoint m c cstar h)

theorem carParameterColimitPoint_transition
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (sys : ContinuousStarInductiveSystem Stage)
    {m n : ℕ} (hmn : m ≤ n) (c cstar : Stage m)
    (h : c * cstar + cstar * c = 1) :
    qCcrParameterZeroFiberTopologicalInjection Stage sys n
        (qCcrParameterZeroFiberTransitionMap Stage sys hmn
          (carParameterZeroFiberPoint m c cstar h)) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys m
        (carParameterZeroFiberPoint m c cstar h) :=
  qCcrParameterZeroFiberTopologicalInjection_transition Stage sys hmn
    (carParameterZeroFiberPoint m c cstar h)

theorem carParameterColimitPoint_stage_independent
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (T : CuntzStarTower Stage) {m n : ℕ} (hmn : m ≤ n)
    (c cstar : Stage m) (h : c * cstar + cstar * c = 1)
    (h' : T.map hmn c * T.map hmn cstar +
      T.map hmn cstar * T.map hmn c = 1) :
    qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem n
        (carParameterZeroFiberPoint n (T.map hmn c) (T.map hmn cstar) h') =
      qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem m
        (carParameterZeroFiberPoint m c cstar h) := by
  have hpoint := congrArg (fun f => f PUnit.unit)
    (carParameterPointTopCatHom_transition_natural
      T.toContinuousStarInductiveSystem hmn c cstar h)
  have hp : carParameterZeroFiberPoint n (T.map hmn c) (T.map hmn cstar) h' =
      qCcrParameterZeroFiberTransitionMap Stage
        T.toContinuousStarInductiveSystem hmn
        (carParameterZeroFiberPoint m c cstar h) := by
    apply Subtype.ext
    simpa [carParameterZeroFiberPoint,
      qCcrParameterZeroFiberTransitionTopCatHom] using
      congrArg Subtype.val hpoint.symm
  calc
    qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem n
        (carParameterZeroFiberPoint n (T.map hmn c) (T.map hmn cstar) h') =
      qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem n
        (qCcrParameterZeroFiberTransitionMap Stage
          T.toContinuousStarInductiveSystem hmn
          (carParameterZeroFiberPoint m c cstar h)) :=
      congrArg (fun p => qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem n p) hp
    _ = qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem m
        (carParameterZeroFiberPoint m c cstar h) :=
      qCcrParameterZeroFiberTopologicalInjection_transition Stage
        T.toContinuousStarInductiveSystem hmn
        (carParameterZeroFiberPoint m c cstar h)

theorem carParameterColimitPoint_ambient
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (sys : ContinuousStarInductiveSystem Stage)
    (m : ℕ) (c cstar : Stage m) (h : c * cstar + cstar * c = 1) :
    qCcrParameterZeroFiberToParameterColimit Stage sys
        (qCcrParameterZeroFiberTopologicalInjection Stage sys m
          (carParameterZeroFiberPoint m c cstar h)) =
      qCcrParameterTopologicalInjection Stage sys m
        (carParameterZeroFiberPoint m c cstar h).1 := by
  have hstage := qCcrParameterZeroFiberToParameterColimit_stage Stage sys m
  exact congrArg (fun f => f (carParameterZeroFiberPoint m c cstar h)) hstage

def ccrParameterZeroFiberPoint
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    (m : ℕ) (c cstar : Stage m)
    (h : c * cstar - cstar * c = 1) :
    {p : QCCRParameterSpace (Stage m) //
      p ∈ qCcrParameterZeroLocus (A := Stage m)} :=
  ccrParameterPointTopCatHom c cstar h PUnit.unit

def ccrParameterColimitPoint
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (sys : ContinuousStarInductiveSystem Stage)
    (m : ℕ) (c cstar : Stage m)
    (h : c * cstar - cstar * c = 1) :
    qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  qCcrParameterZeroFiberTopologicalInjection Stage sys m
    (ccrParameterZeroFiberPoint m c cstar h)

theorem ccrParameterColimitPoint_transition
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (sys : ContinuousStarInductiveSystem Stage)
    {m n : ℕ} (hmn : m ≤ n) (c cstar : Stage m)
    (h : c * cstar - cstar * c = 1) :
    qCcrParameterZeroFiberTopologicalInjection Stage sys n
        (qCcrParameterZeroFiberTransitionMap Stage sys hmn
          (ccrParameterZeroFiberPoint m c cstar h)) =
      qCcrParameterZeroFiberTopologicalInjection Stage sys m
        (ccrParameterZeroFiberPoint m c cstar h) :=
  qCcrParameterZeroFiberTopologicalInjection_transition Stage sys hmn
    (ccrParameterZeroFiberPoint m c cstar h)

theorem ccrParameterColimitPoint_stage_independent
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (T : CuntzStarTower Stage) {m n : ℕ} (hmn : m ≤ n)
    (c cstar : Stage m) (h : c * cstar - cstar * c = 1)
    (h' : T.map hmn c * T.map hmn cstar -
      T.map hmn cstar * T.map hmn c = 1) :
    qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem n
        (ccrParameterZeroFiberPoint n (T.map hmn c) (T.map hmn cstar) h') =
      qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem m
        (ccrParameterZeroFiberPoint m c cstar h) := by
  have hpoint := congrArg (fun f => f PUnit.unit)
    (ccrParameterPointTopCatHom_transition_natural
      T.toContinuousStarInductiveSystem hmn c cstar h)
  have hp : ccrParameterZeroFiberPoint n (T.map hmn c) (T.map hmn cstar) h' =
      qCcrParameterZeroFiberTransitionMap Stage
        T.toContinuousStarInductiveSystem hmn
        (ccrParameterZeroFiberPoint m c cstar h) := by
    apply Subtype.ext
    simpa [ccrParameterZeroFiberPoint,
      qCcrParameterZeroFiberTransitionTopCatHom] using
      congrArg Subtype.val hpoint.symm
  calc
    qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem n
        (ccrParameterZeroFiberPoint n (T.map hmn c) (T.map hmn cstar) h') =
      qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem n
        (qCcrParameterZeroFiberTransitionMap Stage
          T.toContinuousStarInductiveSystem hmn
          (ccrParameterZeroFiberPoint m c cstar h)) :=
      congrArg (fun p => qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem n p) hp
    _ = qCcrParameterZeroFiberTopologicalInjection Stage
        T.toContinuousStarInductiveSystem m
        (ccrParameterZeroFiberPoint m c cstar h) :=
      qCcrParameterZeroFiberTopologicalInjection_transition Stage
        T.toContinuousStarInductiveSystem hmn
        (ccrParameterZeroFiberPoint m c cstar h)

theorem ccrParameterColimitPoint_ambient
    {Stage : ℕ → Type}
    [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)]
    [∀ n, StarOrderedRing (Stage n)]
    (sys : ContinuousStarInductiveSystem Stage)
    (m : ℕ) (c cstar : Stage m) (h : c * cstar - cstar * c = 1) :
    qCcrParameterZeroFiberToParameterColimit Stage sys
        (qCcrParameterZeroFiberTopologicalInjection Stage sys m
          (ccrParameterZeroFiberPoint m c cstar h)) =
      qCcrParameterTopologicalInjection Stage sys m
        (ccrParameterZeroFiberPoint m c cstar h).1 := by
  have hstage := qCcrParameterZeroFiberToParameterColimit_stage Stage sys m
  exact congrArg (fun f => f (ccrParameterZeroFiberPoint m c cstar h)) hstage

end InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
