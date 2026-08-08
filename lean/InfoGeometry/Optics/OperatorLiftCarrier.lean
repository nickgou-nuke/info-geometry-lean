/-
InfoGeometry/Optics/OperatorLiftCarrier.lean

The finite doubled carrier for operator-valued polarization matrices.

An entry matrix acts on `Fin 2 → W` by summing the two internal operators in
each sheet row.  This is the concrete carrier realization of the operator lift;
an inverse equivalence is intentionally not asserted here without the
corresponding reconstruction proof.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Optics.OperatorLiftCarrier

variable {R W : Type*}
variable [CommSemiring R] [AddCommMonoid W] [Module R W]

/-- Matrices whose entries are endomorphisms of the internal carrier. -/
abbrev OperatorMatrix := Matrix (Fin 2) (Fin 2) (Module.End R W)

/-! ## The operator-entry reconstruction complement -/

/-- The `(i,j)` internal operator read from an endomorphism of the doubled carrier. -/
def matrixEntry (T : Module.End R (Fin 2 → W)) (i j : Fin 2) : Module.End R W where
  toFun x := T (Pi.single j x) i
  map_add' x y := by
    simpa [Pi.single_add] using
      congrFun (T.map_add (Pi.single j x) (Pi.single j y)) i
  map_smul' r x := by
    simpa [Pi.single_smul] using
      congrFun (T.map_smul r (Pi.single j x)) i

/-- The operator-entry matrix associated to an endomorphism of the doubled carrier. -/
def matrixOfAction (T : Module.End R (Fin 2 → W)) : OperatorMatrix (R := R) (W := W) :=
  fun i j => matrixEntry T i j

/-- The action of an operator-entry matrix on the doubled carrier. -/
def matrixAction (A : OperatorMatrix (R := R) (W := W)) :
    Module.End R (Fin 2 → W) :=
  LinearMap.pi (fun i =>
    ∑ j : Fin 2, (A i j).comp (LinearMap.proj j))

@[simp]
theorem matrixAction_apply
    (A : OperatorMatrix (R := R) (W := W))
    (v : Fin 2 → W) (i : Fin 2) :
    matrixAction A v i = ∑ j : Fin 2, A i j (v j) := by
  simp [matrixAction, LinearMap.sum_apply, Finset.sum_apply]

@[simp]
theorem matrixAction_zero
    (v : Fin 2 → W) :
    matrixAction (0 : OperatorMatrix (R := R) (W := W)) v = 0 := by
  ext i
  simp

theorem matrixAction_add
    (A B : OperatorMatrix (R := R) (W := W)) :
    matrixAction (A + B) = matrixAction A + matrixAction B := by
  ext v i
  simp [matrixAction_apply]
  abel

section AdditiveGroup

variable {R W : Type*}
variable [CommSemiring R] [Ring R] [AddCommGroup W] [Module R W]

theorem matrixAction_neg
    (A : OperatorMatrix (R := R) (W := W)) :
    matrixAction (-A) = -matrixAction A := by
  ext v i
  simp [matrixAction_apply]

theorem matrixAction_sub
    (A B : OperatorMatrix (R := R) (W := W)) :
    matrixAction (A - B) = matrixAction A - matrixAction B := by
  rw [sub_eq_add_neg, matrixAction_add, matrixAction_neg]
  simp only [sub_eq_add_neg]

end AdditiveGroup

theorem matrixAction_smul
    (r : R) (A : OperatorMatrix (R := R) (W := W)) :
    matrixAction (r • A) = r • matrixAction A := by
  ext v i
  simp [matrixAction_apply, Matrix.smul_apply, LinearMap.smul_apply,
    Pi.smul_apply, Finset.smul_sum]

@[simp]
theorem matrixAction_one
    (v : Fin 2 → W) :
    matrixAction (1 : OperatorMatrix (R := R) (W := W)) v = v := by
  ext i
  fin_cases i <;>
    simp [matrixAction_apply, Matrix.one_apply, Fin.sum_univ_two]

theorem matrixAction_mul
    (A B : OperatorMatrix (R := R) (W := W)) (v : Fin 2 → W) :
    matrixAction (A * B) v = matrixAction A (matrixAction B v) := by
  ext i
  simp only [matrixAction_apply, Matrix.mul_apply, Module.End.mul_apply]
  change
    (∑ x : Fin 2, ∑ j : Fin 2, A i j (B j x (v x))) =
      ∑ j : Fin 2, A i j (∑ x : Fin 2, B j x (v x))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Fin.sum_univ_two]

@[simp]
theorem matrixAction_mul_end
    (A B : OperatorMatrix (R := R) (W := W)) :
    matrixAction (A * B) = matrixAction A * matrixAction B := by
  apply LinearMap.ext
  intro v
  funext i
  exact congrFun (matrixAction_mul A B v) i

theorem matrixAction_injective :
    Function.Injective (matrixAction (R := R) (W := W)) := by
  intro A B h
  funext i j
  apply LinearMap.ext
  intro x
  fin_cases j
  · have hxy := congrFun
      (congrArg (fun T : Module.End R (Fin 2 → W) => T (Pi.single 0 x)) h) i
    simpa [matrixAction_apply, Pi.single_apply] using hxy
  · have hxy := congrFun
      (congrArg (fun T : Module.End R (Fin 2 → W) => T (Pi.single 1 x)) h) i
    simpa [matrixAction_apply, Pi.single_apply] using hxy

theorem matrixAction_matrixOfAction
    (T : Module.End R (Fin 2 → W)) :
    matrixAction (matrixOfAction T) = T := by
  apply LinearMap.ext
  intro v
  funext i
  have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
    funext j
    fin_cases j <;> simp [Pi.single_apply]
  rw [hv, map_add]
  fin_cases i <;>
    simp [matrixAction_apply, matrixOfAction, matrixEntry, Pi.single_apply]

/-- The operator-valued `2 × 2` matrix/action equivalence. -/
noncomputable def matrixActionEquiv :
    OperatorMatrix (R := R) (W := W) ≃ Module.End R (Fin 2 → W) :=
  Equiv.ofBijective (matrixAction (R := R) (W := W))
    ⟨matrixAction_injective (R := R) (W := W), fun T =>
      ⟨matrixOfAction T, matrixAction_matrixOfAction T⟩⟩

@[simp]
theorem matrixActionEquiv_apply
    (A : OperatorMatrix (R := R) (W := W)) :
    matrixActionEquiv (R := R) (W := W) A = matrixAction A :=
  rfl

@[simp]
theorem matrixActionEquiv_symm_apply
    (T : Module.End R (Fin 2 → W)) :
    (matrixActionEquiv (R := R) (W := W)).symm T = matrixOfAction T := by
  apply matrixAction_injective (R := R) (W := W)
  change
    matrixActionEquiv (R := R) (W := W)
        ((matrixActionEquiv (R := R) (W := W)).symm T) =
      matrixAction (matrixOfAction T)
  rw [(matrixActionEquiv (R := R) (W := W)).apply_symm_apply]
  exact (matrixAction_matrixOfAction T).symm

end InfoGeometry.Optics.OperatorLiftCarrier
