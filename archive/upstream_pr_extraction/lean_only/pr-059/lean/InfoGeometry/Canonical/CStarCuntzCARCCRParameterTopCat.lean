import InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge
import InfoGeometry.OperatorAlgebra.QCCRResidual
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological parameter space for the CAR/CCR/Cuntz `q`-relation

The relation is kept in the noncommutative form
`qCcrRelation c c* q = c * cstar - q * cstar * c - 1`. This module adds its
parameter-space topology and q-fiber specialization maps as TopCat/readout maps.
-/

noncomputable section

namespace InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat

set_option linter.unusedSectionVars false

open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge
open CategoryTheory

variable {A : Type*} [CStarAlgebra A]
  [TopologicalSpace A] [T1Space A] [ContinuousMul A] [ContinuousSub A]

abbrev QCCRParameterSpace (A : Type*) := A × (A × A)

/-- Residual relation map on the 3-parameter q-CCR space. -/
def qCcrParameterResidualContinuousMap :
    ContinuousMap (QCCRParameterSpace A) A :=
  { toFun := fun p => qCcrRelation p.1 p.2.1 p.2.2
    continuous_toFun := by
      have hc : Continuous (fun p : QCCRParameterSpace A => p.1) := continuous_fst
      have hcs : Continuous (fun p : QCCRParameterSpace A => p.2.1) :=
        continuous_fst.comp continuous_snd
      have hq : Continuous (fun p : QCCRParameterSpace A => p.2.2) :=
        continuous_snd.comp continuous_snd
      exact ((hc.mul hcs).sub ((hq.mul hcs).mul hc)).sub continuous_const }

/-- Closed zero-locus of the q-CCR residual relation. -/
def qCcrParameterZeroLocus : Set (QCCRParameterSpace A) :=
  (qCcrParameterResidualContinuousMap (A := A)) ⁻¹' ({0} : Set A)


def qCcrParameterTopCatHom :
    TopCat.of (QCCRParameterSpace A) ⟶ TopCat.of A :=
  TopCat.ofHom (qCcrParameterResidualContinuousMap (A := A))

theorem qCcrParameterZeroLocus_closed :
    IsClosed (qCcrParameterZeroLocus (A := A)) := by
  exact isClosed_singleton.preimage
    (qCcrParameterResidualContinuousMap (A := A)).continuous_toFun

/-- Embed a fixed `q`-value fiber into the ambient 3-parameter space. -/
def qCcrSpecializationMap (q : A) :
    ContinuousMap (A × A) (QCCRParameterSpace A) :=
  { toFun := fun p => (p.1, (p.2, q))
    continuous_toFun := by
      simpa [Function.comp] using
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const :
          Continuous fun p : A × A => (p.2, (q : A)))) }


def qCcrSpecializationTopCatHom (q : A) :
    TopCat.of (A × A) ⟶ TopCat.of (QCCRParameterSpace A) :=
  TopCat.ofHom (qCcrSpecializationMap (A := A) q)

/-- Fixed-q ambient points are exactly those in the parameter zero-locus with third coordinate = q. -/
def qCcrParameterZeroLocusFiber (q : A) : Set (QCCRParameterSpace A) :=
  {p | p ∈ qCcrParameterZeroLocus (A := A) ∧ p.2.2 = q}

/-- Fiber as a topological subtype of fixed-`q` points satisfying the residual relation. -/
def qCcrParameterZeroLocusFiberType (q : A) :
    Type _ :=
  {p : QCCRParameterSpace A // p ∈ qCcrParameterZeroLocus (A := A) ∧ p.2.2 = q}

/-- Topology is inherited from the ambient product topology via subtype restriction. -/
instance (q : A) : TopologicalSpace (qCcrParameterZeroLocusFiberType (A := A) q) := by
  change TopologicalSpace {p : QCCRParameterSpace A // p ∈ qCcrParameterZeroLocus (A := A) ∧ p.2.2 = q}
  infer_instance

/- Specialization map from the q-fiber to the parameter zero-locus. -/
omit [T1Space A] in
theorem qCcr_specialization_zero_preimage (q : A) :
    (qCcrSpecializationMap (A := A) q) ⁻¹' qCcrParameterZeroLocus =
    qCcrZeroLocus q := by
  ext p
  rfl

def qCcrSpecializationZeroLocusMap (q : A) :
    {p : A × A // p ∈ qCcrZeroLocus (A := A) q} →
      qCcrParameterZeroLocusFiberType (A := A) q :=
  fun p =>
    ⟨qCcrSpecializationMap (A := A) q p.1, by
      constructor
      ·
        have hx : p.1 ∈ (qCcrSpecializationMap (A := A) q) ⁻¹' qCcrParameterZeroLocus := by
          rw [qCcr_specialization_zero_preimage (A := A) q]
          exact p.2
        exact (Set.mem_preimage.mp hx)
      · rfl⟩


omit [T1Space A] in
theorem continuous_qCcrSpecializationZeroLocusMap (q : A) :
    Continuous (qCcrSpecializationZeroLocusMap (A := A) q) := by
  exact Continuous.subtype_mk
    ((qCcrSpecializationMap (A := A) q).continuous_toFun.comp continuous_subtype_val)
    (fun x => (qCcrSpecializationZeroLocusMap (A := A) q x).property)


def qCcrSpecializationZeroLocusTopCatHom (q : A) :
    TopCat.of {p : A × A // p ∈ qCcrZeroLocus q} ⟶
      TopCat.of (qCcrParameterZeroLocusFiberType (A := A) q) :=
  TopCat.ofHom
    { toFun := qCcrSpecializationZeroLocusMap (A := A) q
      continuous_toFun := continuous_qCcrSpecializationZeroLocusMap (A := A) q }

def qCcrSpecializationZeroLocusFiberMap (q : A) :
    qCcrParameterZeroLocusFiberType (A := A) q →
    {p : A × A // p ∈ qCcrZeroLocus (A := A) q} :=
  fun p =>
    let cp : A × A := (p.1.1, p.1.2.1)
    have hzero : qCcrRelation p.1.1 p.1.2.1 q = 0 := by
      have hraw : qCcrRelation p.1.1 p.1.2.1 p.1.2.2 = 0 := p.2.1
      simpa [p.2.2] using hraw
    ⟨cp, by
      simpa [qCcrZeroLocus, qCcrResidualContinuousMap] using hzero⟩

/-- Right inverse: `specialization ∘ fiberMap = id` on the fixed-q ambient fiber. -/
theorem qCcrSpecializationZeroLocusMap_rightInverse (q : A) :
    Function.RightInverse (qCcrSpecializationZeroLocusFiberMap (A := A) q)
    (qCcrSpecializationZeroLocusMap (A := A) q) := by
  rintro ⟨x, hx⟩
  apply Subtype.ext
  ext <;> simp [qCcrSpecializationZeroLocusMap, qCcrSpecializationZeroLocusFiberMap,
    qCcrSpecializationMap, qCcrZeroLocus, hx.2]

 /-- Left inverse: `fiberMap ∘ specialization = id` on `qCcrZeroLocus q`. -/
theorem qCcrSpecializationZeroLocusMap_leftInverse (q : A) :
    Function.LeftInverse (qCcrSpecializationZeroLocusFiberMap (A := A) q)
    (qCcrSpecializationZeroLocusMap (A := A) q) := by
  rintro ⟨x, hx⟩
  apply Subtype.ext
  ext <;> simp [qCcrSpecializationZeroLocusMap, qCcrSpecializationZeroLocusFiberMap,
    qCcrSpecializationMap]

/-- The fixed-q ambient image is exactly the specialization image of `qCcrZeroLocus q`. -/
theorem qCcrSpecializationZeroLocusMap_range_eq (qq : A) :
    Set.range (qCcrSpecializationZeroLocusMap (A := A) qq) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ _
  · intro _
    refine ⟨qCcrSpecializationZeroLocusFiberMap (A := A) qq x, ?_⟩
    exact qCcrSpecializationZeroLocusMap_rightInverse (A := A) qq x

/-- Fixed-`q` specialization on the zero-locus is injective. -/
theorem qCcrSpecializationZeroLocusMap_injective (qq : A) :
    Function.Injective (qCcrSpecializationZeroLocusMap (A := A) qq) :=
  (qCcrSpecializationZeroLocusMap_leftInverse (A := A) qq).injective

theorem continuous_qCcrSpecializationZeroLocusFiberMap (q : A) :
    Continuous (qCcrSpecializationZeroLocusFiberMap (A := A) q) := by
  apply Continuous.subtype_mk
  · change Continuous (fun p : qCcrParameterZeroLocusFiberType (A := A) q =>
      (p.1.1, p.1.2.1))
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_fst.comp continuous_snd).comp continuous_subtype_val)

def qCcrSpecializationZeroLocusTopCatIso (q : A) :
    TopCat.of {p : A × A // p ∈ qCcrZeroLocus (A := A) q} ≅
      TopCat.of (qCcrParameterZeroLocusFiberType (A := A) q) where
  hom := qCcrSpecializationZeroLocusTopCatHom (A := A) q
  inv := TopCat.ofHom
    { toFun := qCcrSpecializationZeroLocusFiberMap (A := A) q
      continuous_toFun := continuous_qCcrSpecializationZeroLocusFiberMap (A := A) q }
  hom_inv_id := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact qCcrSpecializationZeroLocusMap_leftInverse (A := A) q x
  inv_hom_id := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact qCcrSpecializationZeroLocusMap_rightInverse (A := A) q x

@[simp] theorem qCcrSpecializationZeroLocusTopCatIso_hom_apply
    (q : A) (x : {p : A × A // p ∈ qCcrZeroLocus (A := A) q}) :
    (qCcrSpecializationZeroLocusTopCatIso (A := A) q).hom x =
      qCcrSpecializationZeroLocusMap (A := A) q x :=
  rfl

@[simp] theorem qCcrSpecializationZeroLocusTopCatIso_inv_apply
    (q : A) (x : qCcrParameterZeroLocusFiberType (A := A) q) :
    (qCcrSpecializationZeroLocusTopCatIso (A := A) q).inv x =
      qCcrSpecializationZeroLocusFiberMap (A := A) q x :=
  rfl

end InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
