import InfoGeometry.Physics.BdGChiralBlockMatrix
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace InfoGeometry.Physics

/-!
This file defines only a matrix-valued Zorn-shaped data record.
It is a 32-dimensional rational vector-space candidate when `A = BdGBlock ℚ`.
No Zorn multiplication, ring instance, octonion tensor product, or physical
representation theorem is asserted here.
-/

structure MatrixValuedZornData (A : Type*) where
  alpha : A
  beta : A
  vecX : Fin 3 → A
  vecY : Fin 3 → A

def matrixValuedZornCarrierEquiv (A : Type*) :
    MatrixValuedZornData A ≃
      A × A × (Fin 3 → A) × (Fin 3 → A) where
  toFun x := (x.alpha, x.beta, x.vecX, x.vecY)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

abbrev BdGValuedZornData :=
  MatrixValuedZornData (BdGBlock ℚ)

/-!
The vector-space version uses products directly, so the additive and scalar
structures are inherited from Mathlib rather than reconstructed on the
four-field carrier above.
-/

abbrev BdGValuedZornVectorCarrier :=
  BdGBlock ℚ × BdGBlock ℚ ×
    (Fin 3 → BdGBlock ℚ) ×
    (Fin 3 → BdGBlock ℚ)

theorem finrank_bdgValuedZornVectorCarrier :
    Module.finrank ℚ BdGValuedZornVectorCarrier = 32 := by
  classical
  have h : Module.finrank ℚ (BdGBlock ℚ) = 4 := by
    simp [BdGBlock, Module.finrank_matrix]
  have hp : Module.finrank ℚ (Fin 3 → BdGBlock ℚ) = 12 := by
    rw [Module.finrank_pi_fintype]
    simp [h]
  simp [BdGValuedZornVectorCarrier, Module.finrank_prod, h, hp]

@[simp] theorem finrank_bdgBlock :
    Module.finrank ℚ (BdGBlock ℚ) = 4 := by
  simp [BdGBlock, Module.finrank_matrix]


def localDiracMultiplet (Delta : Fin 3 → ℚ) : BdGValuedZornData where
  alpha := 0
  beta := 0
  vecX := fun i => diracOperator (Delta i)
  vecY := fun i => diracOperator (Delta i)

@[simp] theorem localDiracMultiplet_vecX
    (Delta : Fin 3 → ℚ) (i : Fin 3) :
    (localDiracMultiplet Delta).vecX i = diracOperator (Delta i) :=
  rfl

@[simp] theorem localDiracMultiplet_vecY
    (Delta : Fin 3 → ℚ) (i : Fin 3) :
    (localDiracMultiplet Delta).vecY i = diracOperator (Delta i) :=
  rfl

theorem localDiracMultiplet_component_odd
    (Delta : Fin 3 → ℚ) (i : Fin 3) :
    (localDiracMultiplet Delta).vecX i *
          (chiralGrading : BdGBlock ℚ) +
        (chiralGrading : BdGBlock ℚ) *
          (localDiracMultiplet Delta).vecX i = 0 := by
  simpa using
    (dirac_anticommutes_with_chirality (A := ℚ) (Delta i))

theorem localDiracMultiplet_component_odd_vecY
    (Delta : Fin 3 → ℚ) (i : Fin 3) :
    (localDiracMultiplet Delta).vecY i *
          (chiralGrading : BdGBlock ℚ) +
        (chiralGrading : BdGBlock ℚ) *
          (localDiracMultiplet Delta).vecY i = 0 := by
  simpa using
    (dirac_anticommutes_with_chirality (A := ℚ) (Delta i))

end InfoGeometry.Physics
