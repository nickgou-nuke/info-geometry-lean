import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ChiralOperatorTopologicalBridge
import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationTopCat

/-!
# Operator-valued Sage latent chart

The eight Sage slots are treated as genuinely operator-valued observables in
the order
`(u₊, s₊₀, s₊₁, s₊₂, u₋, s₋₀, s₋₁, s₋₂)`.

The observation target is a finite product of the coefficient algebra.  This
keeps noncommutative multiplication and commutators visible; the scalar norm
readout below is only an optional secondary observation required by the
generic observable-system interface.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

abbrev OperatorSageFeatureSpace A := Fin 8 → A

def operatorSageFeature
    (i : Fin 8) : OperatorSageTopologicalCarrier A → A :=
  ![
    fun X => X.1,
    fun X => X.2.2.1 0,
    fun X => X.2.2.1 1,
    fun X => X.2.2.1 2,
    fun X => X.2.1,
    fun X => X.2.2.2 0,
    fun X => X.2.2.2 1,
    fun X => X.2.2.2 2] i

def operatorSageObservationMap :
    OperatorSageTopologicalCarrier A → OperatorSageFeatureSpace A :=
  fun X i => operatorSageFeature i X

@[continuity, fun_prop]
theorem continuous_operatorSageFeature (i : Fin 8) :
    Continuous (operatorSageFeature (A := A) i) := by
  fin_cases i
  · exact continuous_operatorSage_nPlus
  · exact (continuous_apply (0 : Fin 3)).comp continuous_operatorSage_sigmaPlus
  · exact (continuous_apply (1 : Fin 3)).comp continuous_operatorSage_sigmaPlus
  · exact (continuous_apply (2 : Fin 3)).comp continuous_operatorSage_sigmaPlus
  · exact continuous_operatorSage_nMinus
  · exact (continuous_apply (0 : Fin 3)).comp continuous_operatorSage_sigmaMinus
  · exact (continuous_apply (1 : Fin 3)).comp continuous_operatorSage_sigmaMinus
  · exact (continuous_apply (2 : Fin 3)).comp continuous_operatorSage_sigmaMinus

theorem continuous_operatorSageObservationMap :
    Continuous (operatorSageObservationMap (A := A)) := by
  exact continuous_pi (fun i => continuous_operatorSageFeature i)

def operatorSageObservationInverse
    (f : OperatorSageFeatureSpace A) :
    OperatorSageTopologicalCarrier A :=
  (f 0, f 4, ![f 1, f 2, f 3], ![f 5, f 6, f 7])

def operatorSageFeatureHomeomorph :
    OperatorSageTopologicalCarrier A ≃ₜ OperatorSageFeatureSpace A where
  toFun := operatorSageObservationMap
  invFun := operatorSageObservationInverse
  left_inv := by
    intro X
    rcases X with ⟨nPlus, nMinus, sigmaPlus, sigmaMinus⟩
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  right_inv := by
    intro f
    funext i
    fin_cases i <;> rfl
  continuous_toFun := continuous_operatorSageObservationMap
  continuous_invFun := by
    change Continuous (fun f : OperatorSageFeatureSpace A =>
      (f 0, f 4, ![f 1, f 2, f 3], ![f 5, f 6, f 7]))
    refine (continuous_apply (0 : Fin 8)).prodMk ?_
    refine (continuous_apply (4 : Fin 8)).prodMk ?_
    refine (continuous_pi ?_).prodMk (continuous_pi ?_)
    · intro i
      fin_cases i <;> exact continuous_apply _
    · intro i
      fin_cases i <;> exact continuous_apply _

@[simp] theorem operatorSageFeatureHomeomorph_apply
    (X : OperatorSageTopologicalCarrier A) :
    operatorSageFeatureHomeomorph (A := A) X =
      operatorSageObservationMap X := rfl

def operatorSageLatentSystem :
    NoncommutativeObservableSystem
      (OperatorSageTopologicalCarrier A) A (Fin 8) :=
  (fun i => ContinuousMap.mk (operatorSageFeature i)
      (continuous_operatorSageFeature i),
    ContinuousMap.mk norm continuous_norm)

@[simp] theorem operatorSageLatentSystem_observationMap
    (X : OperatorSageTopologicalCarrier A) (i : Fin 8) :
    (operatorSageLatentSystem (A := A)).operatorObservationMap X i =
      operatorSageFeature i X := rfl

theorem operatorSageLatentSystem_observationMap_eq_homeomorph
    (X : OperatorSageTopologicalCarrier A) :
    (operatorSageLatentSystem (A := A)).operatorObservationMap X =
      operatorSageFeatureHomeomorph (A := A) X := by
  rfl

theorem operatorSageLatentSystem_observation_isEmbedding :
    Topology.IsEmbedding
      (operatorSageLatentSystem (A := A)).operatorObservationMap := by
  rw [show (operatorSageLatentSystem (A := A)).operatorObservationMap =
      operatorSageFeatureHomeomorph (A := A) by
    funext X
    exact operatorSageLatentSystem_observationMap_eq_homeomorph X]
  exact operatorSageFeatureHomeomorph.isEmbedding

theorem operatorSageLatentSystem_observation_injective :
    Function.Injective
      (operatorSageLatentSystem (A := A)).operatorObservationMap := by
  exact operatorSageFeatureHomeomorph.injective

theorem operatorSageLatentSystem_observation_fiber_singleton
    (X : OperatorSageTopologicalCarrier A) :
    {Y | (operatorSageLatentSystem (A := A)).operatorObservationMap Y =
      (operatorSageLatentSystem (A := A)).operatorObservationMap X} = {X} := by
  ext Y
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr
      (operatorSageLatentSystem_observation_injective h)
  · intro h
    rcases Set.mem_singleton_iff.mp h with rfl
    rfl

end
end InfoGeometry.Topology
