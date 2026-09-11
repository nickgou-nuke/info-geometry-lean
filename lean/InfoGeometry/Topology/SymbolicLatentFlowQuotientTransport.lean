import InfoGeometry.Topology.SymbolicLatentQuotientHomeomorph
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Transport of symbolic flows to the observational quotient and range

The quotient action is induced by the existing observationally preserving
flow.  The range action is its conjugate through the compact observational
homeomorphism.
-/

namespace InfoGeometry.Topology

open SymbolicLatentMorphism

def flowMorphism
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) :
    SymbolicLatentMorphism S S where
  toFun := F.act t
  continuous_toFun := F.continuous_time t
  intertwines := by
    intro i x
    exact congrFun (F.preserves_observation t x) i

def quotientFlowAct
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) :
    _root_.Quotient (symbolicObservationalSetoid S) →
      _root_.Quotient (symbolicObservationalSetoid S) :=
  (flowMorphism F t).quotientMap

theorem continuous_quotientFlowAct
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) :
    Continuous (quotientFlowAct F t) :=
  continuous_quotientMap (flowMorphism F t)

@[simp] theorem quotientFlowAct_mk
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) (x : X) :
    quotientFlowAct F t
        (_root_.Quotient.mk (symbolicObservationalSetoid S) x) =
      _root_.Quotient.mk (symbolicObservationalSetoid S) (F.act t x) :=
  rfl

theorem quotientFlowAct_zero
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    quotientFlowAct F 0 q = q := by
  refine _root_.Quotient.inductionOn q ?_
  intro x
  simp [quotientFlowAct, flowMorphism, F.zero_apply]

theorem quotientFlowAct_add
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (s t : ℝ)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    quotientFlowAct F (s + t) q =
      quotientFlowAct F s (quotientFlowAct F t q) := by
  refine _root_.Quotient.inductionOn q ?_
  intro x
  simp [quotientFlowAct, flowMorphism, F.add_apply]

noncomputable def rangeFlowAct
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) :
    Set.range (symbolicObservationQuotientMap S) →
      Set.range (symbolicObservationQuotientMap S) :=
  fun y =>
    symbolicObservationQuotientHomeomorphRange S
      (quotientFlowAct F t
        ((symbolicObservationQuotientHomeomorphRange S).symm y))

theorem continuous_rangeFlowAct
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) :
    Continuous (rangeFlowAct F t) := by
  exact (symbolicObservationQuotientHomeomorphRange S).continuous.comp
    ((continuous_quotientFlowAct F t).comp
      (symbolicObservationQuotientHomeomorphRange S).symm.continuous)

theorem rangeFlowAct_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowAct F 0 y = y := by
  unfold rangeFlowAct
  rw [quotientFlowAct_zero]
  simp

theorem rangeFlowAct_add
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (s t : ℝ)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowAct F (s + t) y =
      rangeFlowAct F s (rangeFlowAct F t y) := by
  unfold rangeFlowAct
  rw [quotientFlowAct_add]
  simp

theorem rangeFlowAct_natural
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    rangeFlowAct F t
        (symbolicObservationQuotientHomeomorphRange S q) =
      symbolicObservationQuotientHomeomorphRange S
        (quotientFlowAct F t q) := by
  unfold rangeFlowAct
  simp

noncomputable def rangeFlowHomeomorph
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ) :
    Set.range (symbolicObservationQuotientMap S) ≃ₜ
      Set.range (symbolicObservationQuotientMap S) where
  toFun := rangeFlowAct F t
  invFun := rangeFlowAct F (-t)
  left_inv y := by
    rw [← rangeFlowAct_add]
    rw [neg_add_cancel]
    exact rangeFlowAct_zero F y
  right_inv y := by
    rw [← rangeFlowAct_add]
    rw [add_neg_cancel]
    exact rangeFlowAct_zero F y
  continuous_toFun := continuous_rangeFlowAct F t
  continuous_invFun := by
    simpa using continuous_rangeFlowAct F (-t)

@[simp] theorem rangeFlowHomeomorph_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentFlow S) (t : ℝ)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    rangeFlowHomeomorph F t y = rangeFlowAct F t y :=
  rfl

end InfoGeometry.Topology
