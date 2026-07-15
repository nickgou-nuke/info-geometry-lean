import InfoGeometry.Canonical.FiniteFibonacciFourPointBlocks
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.FiniteFibonacciFourPointDualBasis

Finite dual-basis and fusion-matrix interface for the four-point Fibonacci
sector.

This file captures the algebraic content of the `Φ`/`Θ` basis change at
`n = 4` without formalizing hypergeometric functions or analytic continuation.

The owner surface is purely finite:

* a symbolic fusion matrix with entries `τ` and `s = √τ`;
* the dual basis vectors obtained by applying that fusion map to the `Φ` basis;
* involutivity of the fusion transform under the algebraic relations
  `τ² + τ = 1` and `s² = τ`.

No conformal-block derivation.
No complex-analytic continuation.
No non-diagonal braid matrix.
-/

namespace FiniteFibonacciFourPointDualBasis

open FiniteFibonacciFourPointBlocks

/--
Symbolic fusion data for the `n = 4` Fibonacci sector.

`tau` is the inverse golden ratio parameter and `s` is a square root of `tau`.
-/
structure FusionData where
  tau : ℂ
  s : ℂ
  tau_sq_add_tau : tau * tau + tau = 1
  s_sq : s * s = tau

namespace FusionData

/-- The symbolic dual-basis transformation matrix. -/
def fusionMatrix (D : FusionData) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![D.tau, D.s; D.s, -D.tau]

@[simp]
theorem fusionMatrix_apply_fst_fst (D : FusionData) :
    D.fusionMatrix 0 0 = D.tau := by
  rfl

@[simp]
theorem fusionMatrix_apply_fst_snd (D : FusionData) :
    D.fusionMatrix 0 1 = D.s := by
  rfl

@[simp]
theorem fusionMatrix_apply_snd_fst (D : FusionData) :
    D.fusionMatrix 1 0 = D.s := by
  rfl

@[simp]
theorem fusionMatrix_apply_snd_snd (D : FusionData) :
    D.fusionMatrix 1 1 = -D.tau := by
  rfl

/--
The symbolic fusion matrix is involutive under the golden-ratio relations.

This is the finite matrix shadow of the paper's `F² = 1` identity.
-/
theorem fusionMatrix_mul_self (D : FusionData) :
    D.fusionMatrix * D.fusionMatrix = 1 := by
  rcases D with ⟨tau, s, htau, hs⟩
  have hsum : tau + tau * tau = 1 := by
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using htau
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fusionMatrix, hsum, hs, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- The finite `Φ`-to-`Θ` basis change on coordinate pairs. -/
def fusionTransform (D : FusionData) : PhiBasis → PhiBasis
  | (x, y) => (D.tau * x + D.s * y, D.s * x - D.tau * y)

/-- The first `Θ` basis vector in the symbolic fusion basis. -/
def theta0 (D : FusionData) : PhiBasis :=
  fusionTransform D phi0

/-- The second `Θ` basis vector in the symbolic fusion basis. -/
def theta1 (D : FusionData) : PhiBasis :=
  fusionTransform D phi1

@[simp]
theorem fusionTransform_phi0 (D : FusionData) :
    fusionTransform D phi0 = (D.tau, D.s) := by
  simp [fusionTransform, phi0]

@[simp]
theorem fusionTransform_phi1 (D : FusionData) :
    fusionTransform D phi1 = (D.s, -D.tau) := by
  simp [fusionTransform, phi1]

@[simp]
theorem theta0_eq (D : FusionData) :
    theta0 D = (D.tau, D.s) := by
  simp [theta0, fusionTransform, phi0]

@[simp]
theorem theta1_eq (D : FusionData) :
    theta1 D = (D.s, -D.tau) := by
  simp [theta1, fusionTransform, phi1]

/--
The symbolic fusion transform is involutive under the golden-ratio relations.

This is the finite algebraic shadow of the `Φ ↔ Θ` basis change.
-/
theorem fusionTransform_involutive (D : FusionData) (v : PhiBasis) :
    fusionTransform D (fusionTransform D v) = v := by
  rcases D with ⟨tau, s, htau, hs⟩
  have hsum : tau * tau + s * s = 1 := by
    rw [hs, htau]
  cases v with
  | mk x y =>
      ext
      · calc
          tau * (tau * x + s * y) + s * (s * x - tau * y)
              = tau * (tau * x) + tau * (s * y) + s * (s * x) - s * (tau * y) := by ring
          _ = tau * (tau * x) + s * (s * x) := by ring
          _ = (tau * tau + s * s) * x := by ring
          _ = x := by simp [hsum]
      · calc
          s * (tau * x + s * y) - tau * (s * x - tau * y)
              = s * (tau * x) + s * (s * y) - tau * (s * x) + tau * (tau * y) := by ring
          _ = s * (s * y) + tau * (tau * y) := by ring
          _ = (tau * tau + s * s) * y := by ring
          _ = y := by simp [hsum]

/--
The `Φ` basis is recovered from the `Θ` basis by the same involutive transform.
-/
theorem phi_to_theta_to_phi (D : FusionData) (v : PhiBasis) :
    fusionTransform D (fusionTransform D v) = v :=
  fusionTransform_involutive D v

/--
The dual basis vectors are exchanged back by the same fusion transform.
-/
theorem phi_theta_exchange (D : FusionData) :
    fusionTransform D (theta0 D) = phi0 ∧ fusionTransform D (theta1 D) = phi1 := by
  constructor
  · simpa [theta0] using fusionTransform_involutive D phi0
  · simpa [theta1] using fusionTransform_involutive D phi1

end FusionData

end FiniteFibonacciFourPointDualBasis
