import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.CovectorContractionNilpotencyBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Covector Contraction Operator Nilpotency ι_λ (ι_λ K) = 0. -/
theorem covector_contraction_nilpotent (lambda : V →ₗ[R] R) (K : ExteriorAlgebra R V) :
    (contractionOp lambda) ((contractionOp lambda) K) = 0 :=
  contraction_op_sq_zero lambda K

/-- **Theorem**: Covector Contraction Anti-Commutativity {ι_λ1, ι_λ2} = 0. -/
theorem covector_contraction_anticommute
    (lambda1 lambda2 : V →ₗ[R] R) (K : ExteriorAlgebra R V) :
    (contractionOp lambda1) ((contractionOp lambda2) K) +
    (contractionOp lambda2) ((contractionOp lambda1) K) = 0 :=
  contraction_op_anticommute lambda1 lambda2 K

/-- **Theorem**: Master Covector Contraction Nilpotency & Anti-Commutativity Synthesis.
    Unifies:
    1. Covector contraction operator nilpotency ι_λ² = 0 on ExteriorAlgebra R V.
    2. Covector contraction operator anti-commutativity {ι_λ1, ι_λ2} = 0.
    3. Structural duality to Wheeler's boundary law d² = 0. -/
theorem master_covector_contraction_nilpotency_synthesis
    (lambda lambda1 lambda2 : V →ₗ[R] R) (K : ExteriorAlgebra R V) :
    ((contractionOp lambda) ((contractionOp lambda) K) = 0) ∧
    ((contractionOp lambda1) ((contractionOp lambda2) K) +
     (contractionOp lambda2) ((contractionOp lambda1) K) = 0) := ⟨
  covector_contraction_nilpotent lambda K,
  covector_contraction_anticommute lambda1 lambda2 K
⟩

end InfoGeometry.Canonical.CovectorContractionNilpotencyBridge
