import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Physics.ParabolicClock

/-!
# Matrix action on the native doubled carrier

This owner relates the real `2 × 2` matrix carrier to the existing
`DoubledSpace E`.  It keeps the parabolic nilpotent generator distinct from
the elliptic clock axis: both are represented on the same carrier, but they
are different matrices.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

abbrev H₂ (E : Type*) := DoubledSpace E

/-- The standard component action of a real `2 × 2` matrix on `E ⊕ E`. -/
noncomputable def matrixAction (A : Matrix (Fin 2) (Fin 2) ℝ) :
    DoubledSpace E →L[ℝ] DoubledSpace E where
  toFun u :=
    to_doubled
      (A 0 0 • WithLp.fst u + A 0 1 • WithLp.snd u)
      (A 1 0 • WithLp.fst u + A 1 1 • WithLp.snd u)
  map_add' u v := by
    apply DoubledSpace.ext <;>
      simp [smul_add, add_assoc, add_left_comm]
  map_smul' r u := by
    apply DoubledSpace.ext <;>
      simp [WithLp.smul_fst, WithLp.smul_snd, smul_add,
        smul_smul, mul_comm]
  cont := by
    let f : H₂ E →L[ℝ] E :=
      (A 0 0) • fst_L (E := E) + (A 0 1) • snd_L (E := E)
    let g : H₂ E →L[ℝ] E :=
      (A 1 0) • fst_L (E := E) + (A 1 1) • snd_L (E := E)
    simpa [f, g] using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal))
        (α := E) (β := E)).comp (f.prod g).continuous

omit [CompleteSpace E] in
@[simp]
theorem matrixAction_to_doubled
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x ξ : E) :
    matrixAction A (to_doubled x ξ : H₂ E) =
      to_doubled
        (A 0 0 • x + A 0 1 • ξ)
        (A 1 0 • x + A 1 1 • ξ) := by
  rfl

/-- The induced linear map from matrix coefficients to doubled endomorphisms. -/
noncomputable def ρclock :
    Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ]
      (DoubledSpace E →L[ℝ] DoubledSpace E) where
  toFun := matrixAction
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;>
      simp [matrixAction, add_smul, add_assoc]
      <;> abel
  map_smul' r A := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;>
      simp [matrixAction, WithLp.smul_fst, WithLp.smul_snd,
        smul_add, smul_smul]

omit [CompleteSpace E] in
@[simp]
theorem ρclock_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (u : H₂ E) :
    ρclock A u = matrixAction A u := rfl

omit [CompleteSpace E] in
theorem ρclock_mul
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    ρclock (E := E) (A * B) =
      (ρclock (E := E) A).comp (ρclock (E := E) B) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext
  · simp [ρclock, matrixAction, Matrix.mul_apply, Fin.sum_univ_two]
    module
  · simp [ρclock, matrixAction, Matrix.mul_apply, Fin.sum_univ_two]
    module

omit [CompleteSpace E] in
@[simp]
theorem ρclock_one :
    ρclock (E := E) (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [ρclock, matrixAction]

def matrixJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

def matrixEpsilon : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def matrixClockAxis : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

@[simp]
theorem matrixJ_sq :
    matrixJ * matrixJ = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem matrixEpsilon_sq :
    matrixEpsilon * matrixEpsilon =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
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
    matrixClockAxis * matrixClockAxis =
      -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixClockAxis, Matrix.mul_apply, Fin.sum_univ_two]

omit [CompleteSpace E] in
theorem ρclock_matrixJ :
    ρclock (E := E) matrixJ = modular_j (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [ρclock, matrixAction, matrixJ, modular_j]

omit [CompleteSpace E] in
theorem ρclock_matrixEpsilon :
    ρclock (E := E) matrixEpsilon =
      spectral_epsilon (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ρclock, matrixAction, matrixEpsilon, spectral_epsilon]

omit [CompleteSpace E] in
theorem ρclock_matrixClockAxis :
    ρclock (E := E) matrixClockAxis =
      clockAxis (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ρclock, matrixAction, matrixClockAxis]

/-! The algebra-valued form of the same representation. -/

noncomputable def ρclockEnd :
    Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Module.End ℝ (DoubledSpace E) where
  toFun A := (ρclock (E := E) A).toLinearMap
  map_add' A B := by
    exact congrArg ContinuousLinearMap.toLinearMap
      (map_add (ρclock (E := E)) A B)
  map_smul' r A := by
    exact congrArg ContinuousLinearMap.toLinearMap
      (map_smul (ρclock (E := E)) r A)

noncomputable def ρclockAlg :
    Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] Module.End ℝ (DoubledSpace E) :=
  AlgHom.ofLinearMap (ρclockEnd (E := E)) (by
    change (ρclock (E := E) (1 : Matrix (Fin 2) (Fin 2) ℝ)).toLinearMap =
      (ContinuousLinearMap.id ℝ (DoubledSpace E)).toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap (ρclock_one (E := E))) (by
    intro A B
    change (ρclock (E := E) (A * B)).toLinearMap =
      ((ρclock (E := E) A).toLinearMap).comp
        (ρclock (E := E) B).toLinearMap
    rw [ρclock_mul]
    rfl)

omit [CompleteSpace E] in
@[simp]
theorem ρclockAlg_apply
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ρclockAlg (E := E) A = (ρclock (E := E) A).toLinearMap := rfl

omit [CompleteSpace E] in
@[simp]
theorem ρclockAlg_matrixJ :
    ρclockAlg (E := E) matrixJ = (modular_j (E := E)).toLinearMap := by
  rw [ρclockAlg_apply, ρclock_matrixJ]

omit [CompleteSpace E] in
@[simp]
theorem ρclockAlg_matrixEpsilon :
    ρclockAlg (E := E) matrixEpsilon =
      (spectral_epsilon (E := E)).toLinearMap := by
  rw [ρclockAlg_apply, ρclock_matrixEpsilon]

omit [CompleteSpace E] in
@[simp]
theorem ρclockAlg_matrixClockAxis :
    ρclockAlg (E := E) matrixClockAxis =
      (clockAxis (E := E)).toLinearMap := by
  rw [ρclockAlg_apply, ρclock_matrixClockAxis]

omit [CompleteSpace E] in
theorem ρclock_parabolicK_apply (x ξ : E) :
    ρclock (E := E) (InfoGeometry.Physics.K (R := ℝ))
        (to_doubled x ξ : H₂ E) = to_doubled ξ 0 := by
  apply DoubledSpace.ext <;>
    simp [ρclock, matrixAction, InfoGeometry.Physics.K]

omit [CompleteSpace E] in
theorem ρclock_parabolicK_sq :
    (ρclock (E := E) (InfoGeometry.Physics.K (R := ℝ))).comp
        (ρclock (E := E) (InfoGeometry.Physics.K (R := ℝ))) = 0 := by
  rw [← ρclock_mul]
  rw [InfoGeometry.Physics.K_sq_eq_zero]
  simp

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
