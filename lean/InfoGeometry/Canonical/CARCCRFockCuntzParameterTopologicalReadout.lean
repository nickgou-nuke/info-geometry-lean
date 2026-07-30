import InfoGeometry.Canonical.CARCCRFockCuntzParameterTopology
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

end InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
