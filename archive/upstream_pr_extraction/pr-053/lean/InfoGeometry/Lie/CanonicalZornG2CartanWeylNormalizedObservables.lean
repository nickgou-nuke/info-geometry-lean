import InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariantEnsemble

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanWeylNormalizedObservables

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariantEnsemble
open scoped BigOperators

variable {State W Y : Type*} [Fintype State] [Nonempty State] [Group W]

def gibbsExpectation
    (D : WeylEquivariantEnsembleDatum (State := State) (W := W))
    (beta : Fin 2 → ℝ) (f : State → Y) (g : Y → ℝ) : ℝ :=
  ∑ m : State, realGibbsWeight D.base beta m * g (f m)

def directionalCharge
    (D : WeylEquivariantEnsembleDatum (State := State) (W := W))
    (v : Fin 2 → ℝ) (m : State) : ℝ :=
  ∑ i : Fin 2, v i * D.base.momentMap m i

theorem directionalCharge_apply
    (D : WeylEquivariantEnsembleDatum (State := State) (W := W))
    (v : Fin 2 → ℝ) (m : State) :
    directionalCharge D v m = ∑ i : Fin 2, v i * D.base.momentMap m i := rfl

theorem gibbsExpectation_parameterLeftAction
    (D : WeylEquivariantEnsembleDatum (State := State) (W := W))
    (w : W) (beta : Fin 2 → ℝ) (f : State → Y) (g : Y → ℝ) :
    gibbsExpectation D (parameterLeftAction (D := D) w beta) f g =
      gibbsExpectation D beta (fun m => f (w • m)) g := by
  unfold gibbsExpectation
  rw [← Equiv.sum_comp (D.stateAction w)]
  apply Finset.sum_congr rfl
  intro m _
  have hp : realGibbsWeight D.base (parameterLeftAction (D := D) w beta)
      (D.stateAction w m) = realGibbsWeight D.base beta m := by
    simpa using probability_diagonal_invariant (D := D) w beta m
  rw [hp]
  rfl

end InfoGeometry.Lie.CanonicalZornG2CartanWeylNormalizedObservables
