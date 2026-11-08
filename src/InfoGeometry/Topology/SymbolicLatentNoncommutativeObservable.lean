import InfoGeometry.Topology.SymbolicLatentCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Operator-valued symbolic-latent observables

The scalar readout layer is retained only as a continuous post-processing
map.  The primary observables take values in a normed (possibly genuinely
noncommutative) algebra, so multiplication and commutators remain visible
before a real-valued feature is extracted.
-/

namespace InfoGeometry.Topology

def operatorCommutator {A : Type*} [Ring A] (a b : A) : A := a * b - b * a

theorem operatorCommutator_eq_zero_iff
    {A : Type*} [Ring A] (a b : A) :
    operatorCommutator a b = 0 ↔ a * b = b * a := by
  simp [operatorCommutator, sub_eq_zero]

abbrev NoncommutativeObservable
    (X A : Type*) [TopologicalSpace X] [NormedRing A] := C(X, A)

namespace NoncommutativeObservable

abbrev eval
    {X A : Type*} [TopologicalSpace X] [NormedRing A]
    (f : NoncommutativeObservable X A) : X → A := f

abbrev continuous_eval
    {X A : Type*} [TopologicalSpace X] [NormedRing A]
    (f : NoncommutativeObservable X A) : Continuous f := f.continuous

end NoncommutativeObservable

abbrev NoncommutativeObservableSystem
    (X A : Type*) [TopologicalSpace X] [NormedRing A]
    (ι : Type*) [Fintype ι] :=
  (ι → NoncommutativeObservable X A) × C(A, ℝ)

namespace NoncommutativeObservableSystem

abbrev observable
    {X A : Type*} [TopologicalSpace X] [NormedRing A]
    {ι : Type*} [Fintype ι]
    (S : NoncommutativeObservableSystem X A ι) :
    ι → NoncommutativeObservable X A := S.1

abbrev readout
    {X A : Type*} [TopologicalSpace X] [NormedRing A]
    {ι : Type*} [Fintype ι]
    (S : NoncommutativeObservableSystem X A ι) : C(A, ℝ) := S.2

abbrev continuous_readout
    {X A : Type*} [TopologicalSpace X] [NormedRing A]
    {ι : Type*} [Fintype ι]
    (S : NoncommutativeObservableSystem X A ι) : Continuous S.readout :=
  S.readout.continuous

def scalarized
    {X A : Type*} [TopologicalSpace X] [NormedRing A]
    {ι : Type*} [Fintype ι]
    (S : NoncommutativeObservableSystem X A ι) :
  FiniteContinuousObservableSystem X ι :=
  fun i =>
    ContinuousMap.mk (S.readout ∘ (S.observable i).eval)
      (S.continuous_readout.comp (S.observable i).continuous_eval)

end NoncommutativeObservableSystem

theorem NoncommutativeObservableSystem.scalarized_observationMap
    {X A : Type*} [TopologicalSpace X] [NormedRing A]
    {ι : Type*} [Fintype ι]
    (S : NoncommutativeObservableSystem X A ι) (x : X) (i : ι) :
    S.scalarized.observationMap x i =
      S.readout ((S.observable i).eval x) := by
  change (S.scalarized i) x = S.readout ((S.observable i).eval x)
  rfl

def pointwiseOperatorCommutator
    {X A : Type*} [TopologicalSpace X] [NormedRing A]
    (a b : X → A) : X → A :=
  fun x => operatorCommutator (a x) (b x)

theorem pointwiseOperatorCommutator_eq_zero_iff
    {X A : Type*} [TopologicalSpace X] [NormedRing A]
    (a b : X → A) :
    pointwiseOperatorCommutator a b = 0 ↔
      ∀ x, a x * b x = b x * a x := by
  constructor
  · intro h x
    have hx := congrFun h x
    exact (operatorCommutator_eq_zero_iff (a x) (b x)).mp hx
  · intro h
    funext x
    exact (operatorCommutator_eq_zero_iff (a x) (b x)).mpr (h x)

end InfoGeometry.Topology
