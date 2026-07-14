import Mathlib.LinearAlgebra.Vandermonde
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

namespace VandermondeExclusionBridge

open scoped Matrix

universe u

section CommRing

variable {R : Type u} [CommRing R] {n : ℕ}

/-- `v : Fin n → R`. -/
@[rep_depth thermo]
structure FiniteVandermondeExclusionWitness where
  nodes : Fin n → R

namespace FiniteVandermondeExclusionWitness

variable (W : FiniteVandermondeExclusionWitness (R := R) (n := n))

/-- `V(v)`. -/
@[rep_depth thermo]
def matrix : Matrix (Fin n) (Fin n) R :=
  Matrix.vandermonde W.nodes

/-- `\det V(v)`. -/
@[rep_depth thermo]
def determinant : R :=
  W.matrix.det

/-- `\det V(v)=\prod_i\prod_{j\in Ioi(i)}(v_j-v_i)`. -/
@[rep_depth thermo]
theorem determinant_eq_pairwise_separation :
    W.determinant = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (W.nodes j - W.nodes i) := by
  unfold determinant matrix
  simpa using Matrix.det_vandermonde W.nodes

end FiniteVandermondeExclusionWitness

end CommRing

section Domain

variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

namespace FiniteVandermondeExclusionWitness

variable (W : FiniteVandermondeExclusionWitness (R := R) (n := n))

/-- `\det V(v)=0 \iff` collision. -/
@[rep_depth thermo]
theorem determinant_eq_zero_iff_collision :
    W.determinant = 0 ↔ ∃ i j : Fin n, W.nodes i = W.nodes j ∧ i ≠ j := by
  unfold determinant matrix
  simpa using (Matrix.det_vandermonde_eq_zero_iff (v := W.nodes))

/-- `\det V(v)\neq 0 \iff` injective. -/
@[rep_depth thermo]
theorem determinant_ne_zero_iff_injective :
    W.determinant ≠ 0 ↔ Function.Injective W.nodes := by
  unfold determinant matrix
  simpa using (Matrix.det_vandermonde_ne_zero_iff (v := W.nodes))

/-- `i\neq j \wedge v_i=v_j \to \det V(v)=0`. -/
@[rep_depth thermo]
theorem collision_forces_determinant_zero
    {i j : Fin n} (hij : i ≠ j) (hEq : W.nodes i = W.nodes j) :
    W.determinant = 0 := by
  rw [W.determinant_eq_zero_iff_collision]
  exact ⟨i, j, hEq, hij⟩

/-- `\det V(v)\neq 0 \to v_i=v_j \to i=j`. -/
@[rep_depth thermo]
theorem determinant_ne_zero_forbids_collision
    (hdet : W.determinant ≠ 0) {i j : Fin n} (hEq : W.nodes i = W.nodes j) :
    i = j := by
  exact (W.determinant_ne_zero_iff_injective.mp hdet) hEq

/-- `\det V(v)\neq0 \leftrightarrow \mathrm{Injective}(v)` and `\det V(v)=0 \leftrightarrow` collision. -/
@[rep_depth thermo]
theorem exclusion_packet :
    (W.determinant ≠ 0 ↔ Function.Injective W.nodes) ∧
      (W.determinant = 0 ↔ ∃ i j : Fin n, W.nodes i = W.nodes j ∧ i ≠ j) := by
  exact ⟨W.determinant_ne_zero_iff_injective, W.determinant_eq_zero_iff_collision⟩

end FiniteVandermondeExclusionWitness

end Domain

end VandermondeExclusionBridge
