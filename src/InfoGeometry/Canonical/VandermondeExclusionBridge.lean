import Mathlib.LinearAlgebra.Vandermonde
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.VandermondeExclusionBridge

\[
V(v)=\mathrm{Matrix.vandermonde}(v),\qquad
\det V(v)=\prod_i\prod_{j\in Ioi(i)}(v_j-v_i).
\]

\[
\det V(v)=0 \iff \exists i\neq j,\ v_i=v_j,
\qquad
\det V(v)\neq 0 \iff v \text{ injective}.
\]
-/

namespace InfoGeometry.Canonical.VandermondeExclusionBridge

open scoped Matrix

universe u

section CommRing

variable {R : Type u} [CommRing R] {n : ℕ}

namespace FiniteVandermondeExclusionWitness

variable (W : Fin n → R)

/-- `V(v)`. -/
@[rep_depth thermo]
def matrix (W : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.vandermonde W

/-- `\det V(v)`. -/
@[rep_depth thermo]
def determinant (W : Fin n → R) : R :=
  (matrix W).det

/-- `\det V(v)=\prod_i\prod_{j\in Ioi(i)}(v_j-v_i)`. -/
@[rep_depth thermo]
theorem determinant_eq_pairwise_separation :
    determinant W = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (W j - W i) := by
  unfold determinant matrix
  simpa using Matrix.det_vandermonde W

end FiniteVandermondeExclusionWitness

end CommRing

section Domain

variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

namespace FiniteVandermondeExclusionWitness

variable (W : Fin n → R)

/-- `\det V(v)=0 \iff` collision. -/
@[rep_depth thermo]
theorem determinant_eq_zero_iff_collision :
    determinant W = 0 ↔ ∃ i j : Fin n, W i = W j ∧ i ≠ j := by
  unfold determinant matrix
  simpa using (Matrix.det_vandermonde_eq_zero_iff (v := W))

/-- `\det V(v)\neq 0 \iff` injective. -/
@[rep_depth thermo]
theorem determinant_ne_zero_iff_injective :
    determinant W ≠ 0 ↔ Function.Injective W := by
  unfold determinant matrix
  simpa using (Matrix.det_vandermonde_ne_zero_iff (v := W))

/-- `i\neq j \wedge v_i=v_j \to \det V(v)=0`. -/
@[rep_depth thermo]
theorem collision_forces_determinant_zero
    {i j : Fin n} (hij : i ≠ j) (hEq : W i = W j) :
    determinant W = 0 := by
  rw [determinant_eq_zero_iff_collision W]
  exact ⟨i, j, hEq, hij⟩

/-- `\det V(v)\neq 0 \to v_i=v_j \to i=j`. -/
@[rep_depth thermo]
theorem determinant_ne_zero_forbids_collision
    (hdet : determinant W ≠ 0) {i j : Fin n} (hEq : W i = W j) :
    i = j := by
  exact (determinant_ne_zero_iff_injective W).mp hdet hEq

/-- `\det V(v)\neq0 \leftrightarrow \mathrm{Injective}(v)` and `\det V(v)=0 \leftrightarrow` collision. -/
@[rep_depth thermo]
theorem exclusion_packet :
    (determinant W ≠ 0 ↔ Function.Injective W) ∧
      (determinant W = 0 ↔ ∃ i j : Fin n, W i = W j ∧ i ≠ j) := by
  exact ⟨determinant_ne_zero_iff_injective W, determinant_eq_zero_iff_collision W⟩

end FiniteVandermondeExclusionWitness

end Domain

end InfoGeometry.Canonical.VandermondeExclusionBridge
