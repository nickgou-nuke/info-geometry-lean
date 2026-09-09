import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Physics.ParabolicClock

/-!
# Native `M₂(ℝ)` action on the doubled real clock carrier

This file constructs the standard real `2 × 2` matrix representation on
`DoubledSpace E = WithLp 2 (E × E)`.  It identifies three distinct matrices
with the native doubled-space operators:

* `matrixJ` with `modular_j`;
* `matrixEpsilon` with `spectral_epsilon`;
* `matrixClockAxis = matrixJ * matrixEpsilon` with `clockAxis`.

The square-zero generator `InfoGeometry.Physics.K` remains a separate
parabolic direction.  Its action is `(x, ξ) ↦ (ξ, 0)`, not the elliptic clock
action `(x, ξ) ↦ (-ξ, x)`.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledMatrixClockBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

abbrev H₂ (E : Type*) := DoubledSpace E
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev End₂ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  Module.End ℝ (DoubledSpace E)

/--
The standard action of a real `2 × 2` matrix on the doubled carrier `E ⊕ E`.
-/
noncomputable def matrixAction (A : Mat2) : End₂ E where
  toFun u :=
    to_doubled
      (A 0 0 • WithLp.fst u + A 0 1 • WithLp.snd u)
      (A 1 0 • WithLp.fst u + A 1 1 • WithLp.snd u)
  map_add' u v := by
    apply DoubledSpace.ext <;>
      simp [WithLp.add_fst, WithLp.add_snd, smul_add] <;>
      abel
  map_smul' r u := by
    apply DoubledSpace.ext <;>
      simp [WithLp.smul_fst, WithLp.smul_snd, smul_add, smul_smul,
        mul_comm]

@[simp]
theorem matrixAction_to_doubled (A : Mat2) (x ξ : E) :
    matrixAction (E := E) A (to_doubled x ξ : H₂ E) =
      to_doubled
        (A 0 0 • x + A 0 1 • ξ)
        (A 1 0 • x + A 1 1 • ξ) := by
  rfl

/-- The full real-linear `M₂(ℝ)` representation on `DoubledSpace E`. -/
noncomputable def ρclock : Mat2 →ₗ[ℝ] End₂ E where
  toFun := matrixAction (E := E)
  map_add' A B := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;>
      simp [matrixAction, add_smul] <;>
      module
  map_smul' r A := by
    apply LinearMap.ext
    intro u
    apply DoubledSpace.ext <;>
      simp [matrixAction, smul_add, smul_smul]

/-- Matrix multiplication is transported to composition of doubled operators. -/
theorem ρclock_mul (A B : Mat2) :
    ρclock (E := E) (A * B) =
      (ρclock (E := E) A).comp (ρclock (E := E) B) := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ρclock, matrixAction, Matrix.mul_apply, Fin.sum_univ_two,
      smul_add, add_smul, mul_smul] <;>
    module

@[simp]
theorem ρclock_one :
    ρclock (E := E) (1 : Mat2) = LinearMap.id := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ρclock, matrixAction]

/-- The representation packaged as an algebra homomorphism. -/
noncomputable def ρclockAlg : Mat2 →ₐ[ℝ] End₂ E :=
  { toFun := ρclock (E := E)
    map_one' := ρclock_one (E := E)
    map_mul' := ρclock_mul (E := E)
    map_zero' := (ρclock (E := E)).map_zero
    map_add' := (ρclock (E := E)).map_add
    commutes' := by
      intro r
      apply LinearMap.ext
      intro u
      apply DoubledSpace.ext <;>
      simp [ρclock, matrixAction, Matrix.algebraMap_matrix_apply,
        Algebra.smul_def] }

/-- Matrix of the modular swap. -/
def matrixJ : Mat2 :=
  !![0, 1;
     1, 0]

/-- Matrix of the Krein fundamental symmetry. -/
def matrixEpsilon : Mat2 :=
  !![1,  0;
     0, -1]

/-- Matrix of the elliptic doubled clock axis `J ε`. -/
def matrixClockAxis : Mat2 :=
  !![0, -1;
     1,  0]

@[simp]
theorem matrixJ_sq :
    matrixJ * matrixJ = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem matrixEpsilon_sq :
    matrixEpsilon * matrixEpsilon = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixEpsilon, Matrix.mul_apply, Fin.sum_univ_two]

theorem matrixJ_mul_epsilon :
    matrixJ * matrixEpsilon = matrixClockAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixJ, matrixEpsilon, matrixClockAxis,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem matrixClockAxis_sq :
    matrixClockAxis * matrixClockAxis = -(1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixClockAxis, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix swap is exactly the native modular swap. -/
theorem ρclock_matrixJ :
    ρclock (E := E) matrixJ =
      (modular_j (E := E)).toLinearMap := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ρclock, matrixAction, matrixJ, modular_j]

/-- The diagonal matrix is exactly the native spectral involution. -/
theorem ρclock_matrixEpsilon :
    ρclock (E := E) matrixEpsilon =
      (spectral_epsilon (E := E)).toLinearMap := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ρclock, matrixAction, matrixEpsilon, spectral_epsilon]

/-- The product matrix `J ε` is exactly the native elliptic clock axis. -/
theorem ρclock_matrixClockAxis :
    ρclock (E := E) matrixClockAxis =
      (clockAxis (E := E)).toLinearMap := by
  apply LinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ρclock, matrixAction, matrixClockAxis, clockAxis, complex_i,
      modular_j, spectral_epsilon]

@[simp]
theorem ρclock_parabolicK_apply (x ξ : E) :
    ρclock (E := E) (InfoGeometry.Physics.K (R := ℝ))
        (to_doubled x ξ : H₂ E) =
      to_doubled ξ 0 := by
  apply DoubledSpace.ext <;>
    simp [ρclock, matrixAction, InfoGeometry.Physics.K]

/-- The represented parabolic generator remains square-zero. -/
theorem ρclock_parabolicK_sq :
    (ρclock (E := E) (InfoGeometry.Physics.K (R := ℝ))).comp
        (ρclock (E := E) (InfoGeometry.Physics.K (R := ℝ))) = 0 := by
  calc
    (ρclock (E := E) (InfoGeometry.Physics.K (R := ℝ))).comp
          (ρclock (E := E) (InfoGeometry.Physics.K (R := ℝ))) =
        ρclock (E := E)
          (InfoGeometry.Physics.K (R := ℝ) *
            InfoGeometry.Physics.K (R := ℝ)) :=
      (ρclock_mul (E := E)
        (InfoGeometry.Physics.K (R := ℝ))
        (InfoGeometry.Physics.K (R := ℝ))).symm
    _ = ρclock (E := E) 0 := by
      rw [InfoGeometry.Physics.K_sq_eq_zero]
    _ = 0 := by
      exact (ρclock (E := E)).map_zero

/-- The parabolic matrix is not the elliptic clock-axis matrix. -/
theorem parabolicK_ne_matrixClockAxis :
    InfoGeometry.Physics.K (R := ℝ) ≠ matrixClockAxis := by
  intro h
  have hentry := congrArg (fun A : Mat2 => A 1 0) h
  norm_num [InfoGeometry.Physics.K, matrixClockAxis] at hentry

/-- On every nonzero doubled carrier, the represented parabolic and elliptic
clock operators are distinct. -/
theorem ρclock_parabolicK_ne_clockAxis [Nontrivial E] :
    ρclock (E := E) (InfoGeometry.Physics.K (R := ℝ)) ≠
      (clockAxis (E := E)).toLinearMap := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have h_apply := congrArg
    (fun T : Module.End ℝ (DoubledSpace E) =>
      T (to_doubled x 0 : DoubledSpace E)) h
  have h_snd := congrArg WithLp.snd h_apply
  have hzero : (0 : E) = x := by
    simpa using h_snd
  exact hx hzero.symm

end InfoGeometry.Krein.DoubledMatrixClockBridge
