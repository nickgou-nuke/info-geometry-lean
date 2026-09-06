import InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
import Mathlib.Topology.Maps.Basic

/-!
# Separation of the CAR and CCR parameter fibres

The q-coordinate is part of the ambient noncommutative parameter space.  Thus
the fermionic (`q = -1`) and bosonic (`q = 1`) zero fibres are disjoint before
any representation or completion is chosen.  This is a small but useful
topological readout of the CAR/CCR distinction.
-/

namespace InfoGeometry.Canonical.CARCCRParameterFiberSeparation

open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge
open InfoGeometry.OperatorAlgebra.QCCRResidual

variable {A : Type*} [CStarAlgebra A]

theorem qCcrParameterZeroLocusFiber_disjoint
    (q₁ q₂ : A) (h : q₁ ≠ q₂) :
    Disjoint (qCcrParameterZeroLocusFiber (A := A) q₁)
      (qCcrParameterZeroLocusFiber (A := A) q₂) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  exact h (hp₁.2.symm.trans hp₂.2)

theorem car_ccr_parameter_fibres_disjoint
    [CharZero A] :
    Disjoint (qCcrParameterZeroLocusFiber (A := A) (-1))
      (qCcrParameterZeroLocusFiber (A := A) 1) := by
  apply qCcrParameterZeroLocusFiber_disjoint
  intro h
  have htwo : (2 : A) = 0 := by
    calc
      (2 : A) = 1 + 1 := by norm_num
      _ = 1 + (-1) := by rw [h]
      _ = 0 := by simp
  have htwoNat : (2 : ℕ) = 0 := by exact_mod_cast htwo
  omega

theorem cuntz_car_parameter_fibres_disjoint
    [CharZero A] :
    Disjoint (qCcrParameterZeroLocusFiber (A := A) 0)
      (qCcrParameterZeroLocusFiber (A := A) (-1)) := by
  apply qCcrParameterZeroLocusFiber_disjoint
  norm_num

theorem cuntz_ccr_parameter_fibres_disjoint
    [CharZero A] :
    Disjoint (qCcrParameterZeroLocusFiber (A := A) 0)
      (qCcrParameterZeroLocusFiber (A := A) 1) := by
  apply qCcrParameterZeroLocusFiber_disjoint
  norm_num

theorem qCcrParameterZeroLocusFiber_closed
    [TopologicalSpace A] [T1Space A] [ContinuousMul A] [ContinuousSub A]
    (q : A) :
    IsClosed (qCcrParameterZeroLocusFiber (A := A) q) := by
  rw [show qCcrParameterZeroLocusFiber (A := A) q =
      qCcrParameterZeroLocus (A := A) ∩
        (fun p : QCCRParameterSpace A => p.2.2) ⁻¹' ({q} : Set A) by
    ext p
    rfl]
  exact (qCcrParameterZeroLocus_closed (A := A)).inter
    (isClosed_singleton.preimage
      (continuous_snd.comp continuous_snd))

theorem qCcrParameterZeroLocusFiber_isClosedEmbedding
    [TopologicalSpace A] [T1Space A] [ContinuousMul A] [ContinuousSub A]
    (q : A) :
    Topology.IsClosedEmbedding
      (fun p : qCcrParameterZeroLocusFiberType (A := A) q => p.1) := by
  exact (qCcrParameterZeroLocusFiber_closed (A := A) q).isClosedEmbedding_subtypeVal

theorem qCcrParameterZeroLocusFiber_inclusion_isClosedEmbedding
    [TopologicalSpace A] [T1Space A] [ContinuousMul A] [ContinuousSub A]
    (q : A) :
    Topology.IsClosedEmbedding
      (Set.inclusion (show
        qCcrParameterZeroLocusFiber (A := A) q ⊆
          qCcrParameterZeroLocus (A := A) from fun _ hp => hp.1)) := by
  have hclosed := qCcrParameterZeroLocusFiber_closed (A := A) q
  exact Topology.IsClosedEmbedding.inclusion (fun _ hp => hp.1)
    (hclosed.preimage continuous_subtype_val)

theorem qCcrSpecializationZeroLocusMap_isClosedEmbedding
    [TopologicalSpace A] [T1Space A] [ContinuousMul A] [ContinuousSub A]
    (q : A) :
    Topology.IsClosedEmbedding
      (qCcrSpecializationZeroLocusMap (A := A) q) := by
  let e :
      {p : A × A // p ∈ qCcrZeroLocus (A := A) q} ≃ₜ
        qCcrParameterZeroLocusFiberType (A := A) q :=
    { toFun := qCcrSpecializationZeroLocusMap (A := A) q
      invFun := qCcrSpecializationZeroLocusFiberMap (A := A) q
      left_inv := qCcrSpecializationZeroLocusMap_leftInverse (A := A) q
      right_inv := qCcrSpecializationZeroLocusMap_rightInverse (A := A) q
      continuous_toFun := continuous_qCcrSpecializationZeroLocusMap (A := A) q
      continuous_invFun := continuous_qCcrSpecializationZeroLocusFiberMap (A := A) q }
  exact e.isClosedEmbedding

theorem qCcrSpecializationZeroLocusTopCatHom_isClosedEmbedding
    [TopologicalSpace A] [T1Space A] [ContinuousMul A] [ContinuousSub A]
    (q : A) :
    Topology.IsClosedEmbedding
      (qCcrSpecializationZeroLocusTopCatHom (A := A) q) := by
  simpa [qCcrSpecializationZeroLocusTopCatHom] using
    qCcrSpecializationZeroLocusMap_isClosedEmbedding (A := A) q

theorem qCcrSpecializationZeroLocusTopCatHom_surjective
    (q : A) :
    Function.Surjective (qCcrSpecializationZeroLocusTopCatHom (A := A) q) := by
  intro y
  have hy : y ∈ (Set.univ : Set
      (qCcrParameterZeroLocusFiberType (A := A) q)) := Set.mem_univ y
  rw [← qCcrSpecializationZeroLocusMap_range_eq (A := A) q] at hy
  simpa [qCcrSpecializationZeroLocusTopCatHom] using hy

theorem qCcrSpecializationZeroLocusTopCatHom_bijective
    (q : A) :
    Function.Bijective (qCcrSpecializationZeroLocusTopCatHom (A := A) q) := by
  refine ⟨(qCcrSpecializationZeroLocusMap_leftInverse (A := A) q).injective, ?_⟩
  exact qCcrSpecializationZeroLocusTopCatHom_surjective (A := A) q

theorem cuntz_car_parameter_fibres_closed_disjoint
    [CharZero A] [TopologicalSpace A] [T1Space A]
    [ContinuousMul A] [ContinuousSub A] :
    IsClosed (qCcrParameterZeroLocusFiber (A := A) 0) ∧
      IsClosed (qCcrParameterZeroLocusFiber (A := A) (-1)) ∧
        Disjoint (qCcrParameterZeroLocusFiber (A := A) 0)
          (qCcrParameterZeroLocusFiber (A := A) (-1)) := by
  exact ⟨qCcrParameterZeroLocusFiber_closed (A := A) 0,
    qCcrParameterZeroLocusFiber_closed (A := A) (-1),
    cuntz_car_parameter_fibres_disjoint (A := A)⟩

theorem cuntz_ccr_parameter_fibres_closed_disjoint
    [CharZero A] [TopologicalSpace A] [T1Space A]
    [ContinuousMul A] [ContinuousSub A] :
    IsClosed (qCcrParameterZeroLocusFiber (A := A) 0) ∧
      IsClosed (qCcrParameterZeroLocusFiber (A := A) 1) ∧
        Disjoint (qCcrParameterZeroLocusFiber (A := A) 0)
          (qCcrParameterZeroLocusFiber (A := A) 1) := by
  exact ⟨qCcrParameterZeroLocusFiber_closed (A := A) 0,
    qCcrParameterZeroLocusFiber_closed (A := A) 1,
    cuntz_ccr_parameter_fibres_disjoint (A := A)⟩

theorem car_ccr_parameter_fibres_closed_disjoint
    [CharZero A] [TopologicalSpace A] [T1Space A]
    [ContinuousMul A] [ContinuousSub A] :
    IsClosed (qCcrParameterZeroLocusFiber (A := A) (-1)) ∧
      IsClosed (qCcrParameterZeroLocusFiber (A := A) 1) ∧
        Disjoint (qCcrParameterZeroLocusFiber (A := A) (-1))
          (qCcrParameterZeroLocusFiber (A := A) 1) := by
  exact ⟨qCcrParameterZeroLocusFiber_closed (A := A) (-1),
    qCcrParameterZeroLocusFiber_closed (A := A) 1,
    car_ccr_parameter_fibres_disjoint (A := A)⟩

theorem qCcrSpecializationZeroLocusMap_range_disjoint
    (q₁ q₂ : A) (h : q₁ ≠ q₂) :
    Disjoint
      (Set.range (fun p : {p : A × A //
        p ∈ qCcrZeroLocus (A := A) q₁} =>
        (qCcrSpecializationZeroLocusMap (A := A) q₁ p).1))
      (Set.range (fun p : {p : A × A //
        p ∈ qCcrZeroLocus (A := A) q₂} =>
        (qCcrSpecializationZeroLocusMap (A := A) q₂ p).1)) := by
  have hleft :
      Set.range (fun p : {p : A × A //
        p ∈ qCcrZeroLocus (A := A) q₁} =>
        (qCcrSpecializationZeroLocusMap (A := A) q₁ p).1) ⊆
        qCcrParameterZeroLocusFiber (A := A) q₁ := by
    rintro _ ⟨p, rfl⟩
    exact (qCcrSpecializationZeroLocusMap (A := A) q₁ p).property
  have hright :
      Set.range (fun p : {p : A × A //
        p ∈ qCcrZeroLocus (A := A) q₂} =>
        (qCcrSpecializationZeroLocusMap (A := A) q₂ p).1) ⊆
        qCcrParameterZeroLocusFiber (A := A) q₂ := by
    rintro _ ⟨p, rfl⟩
    exact (qCcrSpecializationZeroLocusMap (A := A) q₂ p).property
  exact (qCcrParameterZeroLocusFiber_disjoint (A := A) q₁ q₂ h).mono
    hleft hright

theorem qCcrSpecializationZeroLocusMap_ambient_range_eq_fiber
    (q : A) :
    Set.range (fun p : {p : A × A //
      p ∈ qCcrZeroLocus (A := A) q} =>
      (qCcrSpecializationZeroLocusMap (A := A) q p).1) =
      qCcrParameterZeroLocusFiber (A := A) q := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact (qCcrSpecializationZeroLocusMap (A := A) q p).property
  · intro hx
    let x' : qCcrParameterZeroLocusFiberType (A := A) q := ⟨x, hx⟩
    have hx' : x' ∈ (Set.univ : Set
        (qCcrParameterZeroLocusFiberType (A := A) q)) := Set.mem_univ x'
    obtain ⟨p, hp⟩ := (qCcrSpecializationZeroLocusMap_range_eq
      (A := A) q) ▸ hx'
    refine ⟨p, ?_⟩
    exact congrArg Subtype.val hp

theorem qCcrSpecializationZeroLocusMap_ambient_range_closed
    [TopologicalSpace A] [T1Space A] [ContinuousMul A] [ContinuousSub A]
    (q : A) :
    IsClosed (Set.range (fun p : {p : A × A //
      p ∈ qCcrZeroLocus (A := A) q} =>
      (qCcrSpecializationZeroLocusMap (A := A) q p).1)) := by
  exact (qCcrSpecializationZeroLocusMap_ambient_range_eq_fiber (A := A) q).symm ▸
    qCcrParameterZeroLocusFiber_closed (A := A) q

theorem qCcrSpecializationZeroLocusMap_ranges_closed_disjoint
    [TopologicalSpace A] [T1Space A] [ContinuousMul A] [ContinuousSub A]
    (q₁ q₂ : A) (h : q₁ ≠ q₂) :
    IsClosed (Set.range (fun p : {p : A × A //
      p ∈ qCcrZeroLocus (A := A) q₁} =>
      (qCcrSpecializationZeroLocusMap (A := A) q₁ p).1)) ∧
      IsClosed (Set.range (fun p : {p : A × A //
        p ∈ qCcrZeroLocus (A := A) q₂} =>
        (qCcrSpecializationZeroLocusMap (A := A) q₂ p).1)) ∧
        Disjoint
          (Set.range (fun p : {p : A × A //
            p ∈ qCcrZeroLocus (A := A) q₁} =>
            (qCcrSpecializationZeroLocusMap (A := A) q₁ p).1))
          (Set.range (fun p : {p : A × A //
            p ∈ qCcrZeroLocus (A := A) q₂} =>
            (qCcrSpecializationZeroLocusMap (A := A) q₂ p).1)) := by
  exact ⟨qCcrSpecializationZeroLocusMap_ambient_range_closed (A := A) q₁,
    qCcrSpecializationZeroLocusMap_ambient_range_closed (A := A) q₂,
    qCcrSpecializationZeroLocusMap_range_disjoint (A := A) q₁ q₂ h⟩

end InfoGeometry.Canonical.CARCCRParameterFiberSeparation
