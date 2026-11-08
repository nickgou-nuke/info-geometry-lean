import Mathlib.Algebra.Category.Ring.FilteredColimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Star.StarAlgHom
import InfoGeometry.Canonical.CuntzMatrixRingColimitHestenesBridge
import InfoGeometry.Canonical.CuntzMatrixTraceTower

/-!
# Algebraic *-Colimit Bridge for the Matrix Tower

This module packages the native algebraic star involution on the `RingCat` colimit
$$A_\infty^{\rm ring} = \operatorname{colim}_{n} M_{2^n}(\mathbb{C}).$$

Since each finite matrix stage $M_{2^n}(\mathbb{C})$ carries the canonical conjugate-transpose
star involution $A \mapsto A^*$, and the successor maps $\iota_{m,n} : M_{2^m}(\mathbb{C}) \to M_{2^n}(\mathbb{C})$
are `StarAlgHom`s (preserving $A^*$), the star operation descends canonically to the filtered colimit.

## Key Theorems:
- `concreteMap_star`: Stage transition preserves the matrix star operation:
  $\iota_{m,n}(A^*) = (\iota_{m,n}(A))^*$.
- `ringColimitInclusion_star_stage_transition`: Stage inclusion of conjugate transpose is
  strictly coherent with stage refinement.
- `concreteMap_preserves_projection`: Self-adjoint idempotents ($P^* = P, P^2 = P$) are preserved
  under all stage transitions $\iota_{m,n}$.
- `isColimitProjection_idempotent`: Any colimit element represented by a stage projection satisfies $p^2 = p$.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixStarColimitBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixRingColimitHestenesBridge

/-- Matrix star involution on each stage is preserved by stage transitions. -/
theorem concreteMap_star {m n : ℕ} (hmn : m ≤ n) (A : MatrixStage m) :
    concreteMap hmn (star A) = star (concreteMap hmn A) := by
  exact map_star (concreteMap hmn) A

/-- Stage inclusion of conjugate transpose is well-defined under stage refinement. -/
theorem ringColimitInclusion_star_stage_transition {m n : ℕ} (hmn : m ≤ n) (A : MatrixStage m) :
    ringColimitInclusion n (star (concreteMap hmn A)) =
      ringColimitInclusion m (star A) := by
  rw [← concreteMap_star hmn A]
  exact ringColimit_stage_transition hmn (star A)

/-- Stage transitions preserve self-adjoint idempotents (projections). -/
theorem concreteMap_preserves_projection {m n : ℕ} (hmn : m ≤ n) (P : MatrixStage m)
    (hP_sa : star P = P) (hP_idem : P * P = P) :
    star (concreteMap hmn P) = concreteMap hmn P ∧
      concreteMap hmn P * concreteMap hmn P = concreteMap hmn P := by
  constructor
  · rw [← concreteMap_star hmn P, hP_sa]
  · rw [← map_mul (concreteMap hmn) P P, hP_idem]

/-- An algebraic projection in the matrix colimit is a self-adjoint idempotent representative. -/
def IsColimitProjection (p : RingColimit) (n : ℕ) (P : MatrixStage n) : Prop :=
  p = ringColimitInclusion n P ∧ star P = P ∧ P * P = P

theorem isColimitProjection_idempotent {p : RingColimit} {n : ℕ} {P : MatrixStage n}
    (hp : IsColimitProjection p n P) : p * p = p := by
  rcases hp with ⟨rfl, _, hP_idem⟩
  rw [← ringColimitInclusion_mul, hP_idem]

theorem isColimitProjection_stage_transition {p : RingColimit} {m n : ℕ} (hmn : m ≤ n)
    {P : MatrixStage m} (hp : IsColimitProjection p m P) :
    IsColimitProjection p n (concreteMap hmn P) := by
  rcases hp with ⟨rfl, hP_sa, hP_idem⟩
  have hproj := concreteMap_preserves_projection hmn P hP_sa hP_idem
  refine ⟨(ringColimit_stage_transition hmn P).symm, hproj.1, hproj.2⟩

end InfoGeometry.Canonical.CuntzMatrixStarColimitBridge
