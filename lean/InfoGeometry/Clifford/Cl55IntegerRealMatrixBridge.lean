import InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Scalar extension of the finite split `O(5,5)` matrix readout

The finite Pin readout is stored over `ℤ`, while the native Clifford carrier
`V55` and its quadratic form are real.  This owner performs only the honest
coefficient extension from the former matrix carrier to the latter scalar
field.  It does not identify the resulting coordinate basis with `V55`; that
requires a separate, explicit coordinate equivalence.
-/

namespace InfoGeometry.Clifford.Cl55IntegerRealMatrixBridge

open InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws
open Matrix

abbrev M10R := Matrix (Fin 10) (Fin 10) ℝ
abbrev V10R := InfoGeometry.Algebra.FiniteSpin.Vec10R

/-- Entrywise coefficient extension from integer to real matrices. -/
def intMatrixToReal (A : M10Z) : M10R := fun i j => (A i j : ℝ)

def intVectorToReal (v : V10Z) : V10R := fun i => (v i : ℝ)

@[simp] theorem intMatrixToReal_apply (A : M10Z) (i j : Fin 10) :
    intMatrixToReal A i j = (A i j : ℝ) := rfl

@[simp] theorem intVectorToReal_apply (v : V10Z) (i : Fin 10) :
    intVectorToReal v i = (v i : ℝ) := rfl

theorem intMatrixToReal_mulVec (A : M10Z) (v : V10Z) :
    (intMatrixToReal A).mulVec (intVectorToReal v) =
      intVectorToReal (A.mulVec v) := by
  ext i
  simp [intMatrixToReal, intVectorToReal, Matrix.mulVec, dotProduct]

theorem intMatrixToReal_mul (A B : M10Z) :
    intMatrixToReal (A * B) = intMatrixToReal A * intMatrixToReal B := by
  ext i j
  simp [intMatrixToReal, Matrix.mul_apply]

theorem intMatrixToReal_transpose (A : M10Z) :
    intMatrixToReal Aᵀ = (intMatrixToReal A)ᵀ := by
  rfl

theorem intMatrixToReal_one :
    intMatrixToReal (1 : M10Z) = (1 : M10R) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [intMatrixToReal]
  · simp [intMatrixToReal, h]

/-- The diagonal split metric after scalar extension. -/
def etaReal : M10R := intMatrixToReal eta

/-- Real orthogonality for the scalar-extended finite matrix readout. -/
def IsO55Real (A : M10R) : Prop := Aᵀ * etaReal * A = etaReal

theorem intMatrixToReal_isO55 {A : M10Z} (hA : IsO55 A) :
    IsO55Real (intMatrixToReal A) := by
  unfold IsO55Real etaReal
  change intMatrixToReal Aᵀ * intMatrixToReal eta * intMatrixToReal A =
    intMatrixToReal eta
  calc
    intMatrixToReal Aᵀ * intMatrixToReal eta * intMatrixToReal A =
        intMatrixToReal (Aᵀ * eta) * intMatrixToReal A := by
      exact congrArg (fun X => X * intMatrixToReal A)
        (intMatrixToReal_mul Aᵀ eta).symm
    _ = intMatrixToReal ((Aᵀ * eta) * A) := by
      exact (intMatrixToReal_mul (Aᵀ * eta) A).symm
    _ = intMatrixToReal eta := congrArg intMatrixToReal hA

theorem pinReflectReal_isO55 (k : Fin 10) :
    IsO55Real (intMatrixToReal (pinReflect k)) :=
  intMatrixToReal_isO55 (pinReflect_all_o55 k)

theorem pinReflectReal_involutive (k : Fin 10) :
    intMatrixToReal (pinReflect k) * intMatrixToReal (pinReflect k) =
      (1 : M10R) := by
  rw [← intMatrixToReal_mul]
  simpa only [intMatrixToReal_one] using
    congrArg intMatrixToReal (pinReflect_all_involutive k)

end InfoGeometry.Clifford.Cl55IntegerRealMatrixBridge
