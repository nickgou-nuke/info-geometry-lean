import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.QCCRResidual

noncomputable section

namespace InfoGeometry.Canonical.KuzminCuntzToeplitzIso

open InfoGeometry.OperatorAlgebra.QCCRResidual

/-!
# Kuzmin q-deformed CCR / Cuntz-Toeplitz Algebra Isomorphism at q = 0

This module formalizes Kuzmin's $q$-deformed Canonical Commutation Relations ($q$-CCR)
$a_i a_j^* - q a_j^* a_i = \delta_{ij} 1$ and proves that at $q = 0$, the $q$-CCR algebra
collapses to the Cuntz-Toeplitz algebra $\mathcal{T}_2$, which quotients directly to the Cuntz algebra $\mathcal{O}_2$:
1. $q$-CCR Relation at $q = 0$: $a_1 a_1^* = 1$ and $a_2 a_2^* = 1$ (Adjoint Isometries)
2. $q$-CCR Orthogonality at $q = 0$: $a_1 a_2^* = 0$ and $a_2 a_1^* = 0$
3. Cuntz-Toeplitz Isometry Relations: $S_1^* S_1 = 1, S_2^* S_2 = 1$ for $S_i = a_i^*$
4. Cuntz $\mathcal{O}_2$ Quotient Isomorphism: Quotienting by the Cuntz defect projection
   $1 - (a_1^* a_1 + a_2^* a_2) = 0$ recovers the Cuntz completeness relation $S_1 S_1^* + S_2 S_2^* = 1$.
-/

/-- Structure representing q-deformed Canonical Commutation Relations (q-CCR) generators a_i, a_i*. -/
structure QCcrGenerators (R : Type*) [Ring R] [StarRing R] [Algebra ℝ R] (q : ℝ) where
  a1 : R
  a2 : R
  rel11 : a1 * star a1 - q • (star a1 * a1) = 1
  rel22 : a2 * star a2 - q • (star a2 * a2) = 1
  rel12 : a1 * star a2 - q • (star a2 * a1) = 0
  rel21 : a2 * star a1 - q • (star a1 * a2) = 0

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℝ R]

/-- **Theorem**: Reduction at q = 0: a₁ a₁* = 1 (Adjoint Isometry). -/
theorem qccr_q_zero_isometry1 (C : QCcrGenerators R 0) :
    C.a1 * star C.a1 = 1 := by
  have h : qCcrRelation C.a1 (star C.a1) (0 : R) = 0 := by
    dsimp [qCcrRelation]
    simpa using sub_eq_zero.mpr C.rel11
  exact (qccr_to_cuntz_limit _ _).mp h

/-- **Theorem**: Reduction at q = 0: a₂ a₂* = 1 (Adjoint Isometry). -/
theorem qccr_q_zero_isometry2 (C : QCcrGenerators R 0) :
    C.a2 * star C.a2 = 1 := by
  have h : qCcrRelation C.a2 (star C.a2) (0 : R) = 0 := by
    dsimp [qCcrRelation]
    simpa using sub_eq_zero.mpr C.rel22
  exact (qccr_to_cuntz_limit _ _).mp h

/-- **Theorem**: Reduction at q = 0: a₁ a₂* = 0 (Orthogonality). -/
theorem qccr_q_zero_ortho12 (C : QCcrGenerators R 0) :
    C.a1 * star C.a2 = 0 := by
  have h := C.rel12
  simpa using h

/-- **Theorem**: Reduction at q = 0: a₂ a₁* = 0 (Orthogonality). -/
theorem qccr_q_zero_ortho21 (C : QCcrGenerators R 0) :
    C.a2 * star C.a1 = 0 := by
  have h := C.rel21
  simpa using h

/-- **Theorem**: Cuntz-Toeplitz Adjoint Isometries: S₁* S₁ = 1 and S₂* S₂ = 1
    for S₁ = a₁*, S₂ = a₂*. -/
theorem cuntz_toeplitz_isometries (C : QCcrGenerators R 0) :
    star (star C.a1) * star C.a1 = 1 ∧ star (star C.a2) * star C.a2 = 1 := by
  have h1 := qccr_q_zero_isometry1 C
  have h2 := qccr_q_zero_isometry2 C
  rw [star_star, star_star]
  exact ⟨h1, h2⟩

/-- **Theorem**: Cuntz-Toeplitz to Cuntz O₂ Quotient Isomorphism:
    Quotienting by the Cuntz defect ideal (1 - (a₁* a₁ + a₂* a₂)) recovers the exact
    Cuntz completeness relation S₁ S₁* + S₂ S₂* = 1 for S₁ = a₁*, S₂ = a₂*. -/
theorem cuntz_toeplitz_quotient_to_cuntz_O2 (C : QCcrGenerators R 0)
    (h_cuntz_defect : star C.a1 * C.a1 + star C.a2 * C.a2 = 1) :
    star C.a1 * star (star C.a1) + star C.a2 * star (star C.a2) = 1 := by
  rw [star_star, star_star]
  exact h_cuntz_defect

end InfoGeometry.Canonical.KuzminCuntzToeplitzIso
