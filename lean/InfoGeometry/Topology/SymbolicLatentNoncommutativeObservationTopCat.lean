import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservable

/-!
# Topological quotient of operator-valued symbolic-latent observations

This is the genuinely noncommutative observation lane.  The quotient readout
lands in a finite product of a `NormedRing A`, so multiplication and
commutators remain visible; no scalar diagonal replacement is introduced.
-/

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u} [TopologicalSpace X] [NormedRing A] [Fintype ι]

def NoncommutativeObservableSystem.operatorObservationMap
    (S : NoncommutativeObservableSystem X A ι) : X → (ι → A) :=
  fun x i => (S.observable i).eval x

theorem continuous_operatorObservationMap
    (S : NoncommutativeObservableSystem X A ι) :
    Continuous S.operatorObservationMap := by
  unfold NoncommutativeObservableSystem.operatorObservationMap
  apply continuous_pi
  intro i
  exact (S.observable i).continuous_eval

def operatorObservationalSetoid
    (S : NoncommutativeObservableSystem X A ι) : Setoid X where
  r x y := S.operatorObservationMap x = S.operatorObservationMap y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

abbrev OperatorObservationalQuotient
    (S : NoncommutativeObservableSystem X A ι) :=
  Quotient (operatorObservationalSetoid S)

def operatorObservationQuotientMap
    (S : NoncommutativeObservableSystem X A ι) :
    X → OperatorObservationalQuotient S :=
  Quotient.mk (operatorObservationalSetoid S)

def operatorObservationQuotientReadout
    (S : NoncommutativeObservableSystem X A ι) :
    OperatorObservationalQuotient S → (ι → A) :=
  Quotient.lift (s := operatorObservationalSetoid S)
    S.operatorObservationMap (fun _ _ h => h)

theorem continuous_operatorObservationQuotientMap
    (S : NoncommutativeObservableSystem X A ι) :
    Continuous (operatorObservationQuotientMap S) := by
  exact continuous_quot_mk

theorem isQuotientMap_operatorObservationQuotientMap
    (S : NoncommutativeObservableSystem X A ι) :
    Topology.IsQuotientMap (operatorObservationQuotientMap S) := by
  exact isQuotientMap_quot_mk

theorem continuous_operatorObservationQuotientReadout
    (S : NoncommutativeObservableSystem X A ι) :
    Continuous (operatorObservationQuotientReadout S) := by
  exact Continuous.quotient_lift (continuous_operatorObservationMap S)
    (fun _ _ h => h)

theorem operatorObservationQuotientReadout_mk
    (S : NoncommutativeObservableSystem X A ι) (x : X) :
    operatorObservationQuotientReadout S (operatorObservationQuotientMap S x) =
      S.operatorObservationMap x := by
  simpa [operatorObservationQuotientReadout, operatorObservationQuotientMap] using
    (Quotient.lift_mk (s := operatorObservationalSetoid S)
      S.operatorObservationMap (fun _ _ h => h) x)

def operatorObservationQuotientMapTopCatHom
    (S : NoncommutativeObservableSystem X A ι) :
    TopCat.of X ⟶ TopCat.of (OperatorObservationalQuotient S) :=
  TopCat.ofHom
    { toFun := operatorObservationQuotientMap S
      continuous_toFun := continuous_operatorObservationQuotientMap S }

def operatorObservationQuotientTopCatHom
    (S : NoncommutativeObservableSystem X A ι) :
    TopCat.of (OperatorObservationalQuotient S) ⟶ TopCat.of (ι → A) :=
  TopCat.ofHom
    { toFun := operatorObservationQuotientReadout S
      continuous_toFun := continuous_operatorObservationQuotientReadout S }

theorem operatorObservationQuotientTopCatHom_comp_map
    (S : NoncommutativeObservableSystem X A ι) :
    operatorObservationQuotientMapTopCatHom S ≫
        operatorObservationQuotientTopCatHom S =
      TopCat.ofHom
        { toFun := S.operatorObservationMap
          continuous_toFun := continuous_operatorObservationMap S } := by
  ext x i
  rfl

theorem continuous_pointwiseOperatorCommutator
    (S : NoncommutativeObservableSystem X A ι) (i j : ι) :
    Continuous (fun x => operatorCommutator
      ((S.observable i).eval x) ((S.observable j).eval x)) := by
  exact ((S.observable i).continuous_eval.mul (S.observable j).continuous_eval).sub
    ((S.observable j).continuous_eval.mul (S.observable i).continuous_eval)

def operatorCommutatorProfile
    (S : NoncommutativeObservableSystem X A ι) : X → (ι → ι → A) :=
  fun x i j => operatorCommutator
    ((S.observable i).eval x) ((S.observable j).eval x)

theorem continuous_operatorCommutatorProfile
    (S : NoncommutativeObservableSystem X A ι) :
    Continuous (operatorCommutatorProfile S) := by
  unfold operatorCommutatorProfile
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_pointwiseOperatorCommutator S i j

def operatorCommutatorProfileTopCatHom
    (S : NoncommutativeObservableSystem X A ι) :
    TopCat.of X ⟶ TopCat.of (ι → ι → A) :=
  TopCat.ofHom
    { toFun := operatorCommutatorProfile S
      continuous_toFun := continuous_operatorCommutatorProfile S }

@[simp] theorem operatorCommutatorProfileTopCatHom_apply
    (S : NoncommutativeObservableSystem X A ι) (x : X) (i j : ι) :
    operatorCommutatorProfileTopCatHom S x i j =
      operatorCommutator ((S.observable i).eval x) ((S.observable j).eval x) :=
  by
    change operatorCommutatorProfile S x i j = _
    rfl

def operatorCommutatorProfileQuotientReadout
    (S : NoncommutativeObservableSystem X A ι) :
    OperatorObservationalQuotient S → (ι → ι → A) :=
  Quotient.lift (s := operatorObservationalSetoid S)
    (operatorCommutatorProfile S)
    (by
      intro x y hxy
      funext i j
      exact congrArg
        (fun v : ι → A => operatorCommutator (v i) (v j)) hxy)

theorem continuous_operatorCommutatorProfileQuotientReadout
    (S : NoncommutativeObservableSystem X A ι) :
    Continuous (operatorCommutatorProfileQuotientReadout S) := by
  apply Continuous.quotient_lift (continuous_operatorCommutatorProfile S)

theorem operatorCommutatorProfileQuotientReadout_mk
    (S : NoncommutativeObservableSystem X A ι) (x : X) :
    operatorCommutatorProfileQuotientReadout S
        (operatorObservationQuotientMap S x) =
      operatorCommutatorProfile S x := by
  rfl

def operatorCommutatorProfileQuotientTopCatHom
    (S : NoncommutativeObservableSystem X A ι) :
    TopCat.of (OperatorObservationalQuotient S) ⟶
      TopCat.of (ι → ι → A) :=
  TopCat.ofHom
    { toFun := operatorCommutatorProfileQuotientReadout S
      continuous_toFun := continuous_operatorCommutatorProfileQuotientReadout S }

theorem operatorCommutatorProfileQuotientTopCatHom_comp_map
    (S : NoncommutativeObservableSystem X A ι) :
    operatorObservationQuotientMapTopCatHom S ≫
        operatorCommutatorProfileQuotientTopCatHom S =
      operatorCommutatorProfileTopCatHom S := by
  ext x i j
  rfl

def operatorCommutingLocus
    (S : NoncommutativeObservableSystem X A ι) : Set X :=
  {x | operatorCommutatorProfile S x = 0}

theorem isClosed_operatorCommutingLocus
    (S : NoncommutativeObservableSystem X A ι) :
    IsClosed (operatorCommutingLocus S) := by
  unfold operatorCommutingLocus
  exact isClosed_singleton.preimage (continuous_operatorCommutatorProfile S)

def operatorCommutingLocusQuotient
    (S : NoncommutativeObservableSystem X A ι) :
    Set (OperatorObservationalQuotient S) :=
  {q | operatorCommutatorProfileQuotientReadout S q = 0}

theorem isClosed_operatorCommutingLocusQuotient
    (S : NoncommutativeObservableSystem X A ι) :
    IsClosed (operatorCommutingLocusQuotient S) := by
  unfold operatorCommutingLocusQuotient
  exact isClosed_singleton.preimage
    (continuous_operatorCommutatorProfileQuotientReadout S)

theorem operatorCommutingLocusQuotient_preimage
    (S : NoncommutativeObservableSystem X A ι) :
    (operatorObservationQuotientMap S) ⁻¹'
        operatorCommutingLocusQuotient S =
      operatorCommutingLocus S := by
  ext x
  rfl

end InfoGeometry.Topology
