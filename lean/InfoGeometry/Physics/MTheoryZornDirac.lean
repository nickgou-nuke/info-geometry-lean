import InfoGeometry.Physics.BdGValuedZornCarrier

namespace InfoGeometry.Physics.Supergravity

open InfoGeometry.Physics

/-!
This owner instantiates the existing 32-dimensional matrix-valued Zorn-shaped
carrier with a finite family of off-diagonal BdG blocks.  It does not add a
Zorn product or identify the carrier with a Clifford or supergravity algebra.
-/

abbrev MTheoryZornCarrier := BdGValuedZornCarrier

def gaugeMultiplet (Delta : Fin 3 → ℚ) : MTheoryZornCarrier where
  alpha := 0
  beta := 0
  vecX := fun i => !![0, Delta i; Delta i, 0]
  vecY := fun i => !![0, Delta i; Delta i, 0]

@[simp] theorem gaugeMultiplet_vecX
    (Delta : Fin 3 → ℚ) (i : Fin 3) :
    (gaugeMultiplet Delta).vecX i = !![0, Delta i; Delta i, 0] :=
  rfl

@[simp] theorem gaugeMultiplet_vecY
    (Delta : Fin 3 → ℚ) (i : Fin 3) :
    (gaugeMultiplet Delta).vecY i = !![0, Delta i; Delta i, 0] :=
  rfl

theorem gaugeMultiplet_component_anticommutes_chiral
    (Delta : Fin 3 → ℚ) (i : Fin 3) :
    (gaugeMultiplet Delta).vecX i *
          (chiralGrading : BdGBlock ℚ) +
        (chiralGrading : BdGBlock ℚ) * (gaugeMultiplet Delta).vecX i =
      (0 : BdGBlock ℚ) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [gaugeMultiplet, chiralGrading, Matrix.mul_apply, Fin.sum_univ_two]

theorem gaugeMultiplet_vecY_anticommutes_chiral
    (Delta : Fin 3 → ℚ) (i : Fin 3) :
    (gaugeMultiplet Delta).vecY i *
          (chiralGrading : BdGBlock ℚ) +
        (chiralGrading : BdGBlock ℚ) * (gaugeMultiplet Delta).vecY i =
      (0 : BdGBlock ℚ) := by
  simpa using gaugeMultiplet_component_anticommutes_chiral Delta i

end InfoGeometry.Physics.Supergravity
