import InfoGeometry.Topology.D4StarObservableExtensionality

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-!
## The two-point Boolean observable spectrum

This is a finite evaluation spectrum, not a claim about a C*-algebraic
Gelfand spectrum.
-/

def booleanObservableSpectrumMap :
    C(D4StarQuotient, Bool) → Bool × Bool :=
  fun f =>
    (f (starQuotientMap centralVertex),
      f (starQuotientMap (outerVertex ColorChannel.red)))

theorem booleanObservableSpectrumMap_injective :
    Function.Injective booleanObservableSpectrumMap := by
  intro f g h
  apply continuousMap_ext_by_two_classes f g
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

def booleanSpectrumCentreCharacter :
    C(D4StarQuotient, Bool) → Bool :=
  fun f => f (starQuotientMap centralVertex)

def booleanSpectrumOuterCharacter :
    C(D4StarQuotient, Bool) → Bool :=
  fun f => f (starQuotientMap (outerVertex ColorChannel.red))

theorem booleanObservableSpectrumMap_eq_characters
    (f : C(D4StarQuotient, Bool)) :
    booleanObservableSpectrumMap f =
      (booleanSpectrumCentreCharacter f,
        booleanSpectrumOuterCharacter f) := rfl

def booleanSpectrumRealizingObservable
    (p : Bool × Bool) : ContinuousOrbitObservable Bool :=
  ⟨{ toFun := fun v =>
      match v with
      | Sum.inr _ => p.1
      | Sum.inl _ => p.2,
      continuous_toFun := continuous_of_discreteTopology }, by
      intro v w h
      cases v with
      | inl c =>
          cases w with
          | inl d => rfl
          | inr u => exact False.elim h
      | inr u =>
          cases w with
          | inl c => exact False.elim h
          | inr v => rfl⟩

def booleanSpectrumRealize (p : Bool × Bool) :
    C(D4StarQuotient, Bool) :=
  descendedContinuousMap (booleanSpectrumRealizingObservable p)

theorem booleanObservableSpectrumMap_realize
    (p : Bool × Bool) :
    booleanObservableSpectrumMap (booleanSpectrumRealize p) = p := by
  apply Prod.ext
  · exact descendedContinuousMap_comp_projection
      (booleanSpectrumRealizingObservable p) centralVertex
  · exact descendedContinuousMap_comp_projection
      (booleanSpectrumRealizingObservable p)
      (outerVertex ColorChannel.red)

theorem booleanObservableSpectrumMap_surjective :
    Function.Surjective booleanObservableSpectrumMap := by
  intro p
  exact ⟨booleanSpectrumRealize p,
    booleanObservableSpectrumMap_realize p⟩

noncomputable def booleanObservableSpectrumEquiv :
    C(D4StarQuotient, Bool) ≃ Bool × Bool :=
  Equiv.ofBijective booleanObservableSpectrumMap
    ⟨booleanObservableSpectrumMap_injective,
      booleanObservableSpectrumMap_surjective⟩

end InfoGeometry.Topology.PauliJungD4Star
