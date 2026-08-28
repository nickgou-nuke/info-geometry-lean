import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

noncomputable section

open Matrix

namespace InfoGeometry.OperatorAlgebra.CommutantDuality

abbrev Dim32 := Fin 32
abbrev Mat32 := Matrix Dim32 Dim32 ℝ

/-!
# Finite Matrix Commutant and Modular-Reflection Calculus

This module formalizes a finite matrix-level algebraic fragment:
1. **The Commutant $\mathcal{M}'$**:
    $\mathcal{M}' = \{ B' \in B(\mathcal{H}) \mid [A, B'] = 0, \; \forall A \in \mathcal{M} \}$.
2. **A conditional commutator identity**:
    $[A, B'] = A B' - B' A = 0$ identically for $A \in \mathcal{M}, B' \in \mathcal{M}'$.
3. **A concrete matrix involution $J$**:
    $J = \operatorname{diag}(I_{16}, -I_{16})$ with $J^2 = 1$.
4. **Conjugation by this involution**:
    $\pi_J(A) = J A J$, satisfying $(\pi_J \circ \pi_J)(A) = A$.
5. **A trace pairing identity**:
    $\langle A, B' \rangle_\rho = \operatorname{Tr}(\rho A B')$, satisfying $\operatorname{Tr}(\rho A B') = \operatorname{Tr}(\rho B' A)$ when $[A, B'] = 0$.

This file does not establish von Neumann closure, the double-commutant theorem,
standard-form Tomita--Takesaki theory, or an identification
$J\mathcal{M}J=\mathcal{M}'$.
-/

/-! ### 1. The Von Neumann Commutant Predicate & Microcausality -/

/-- The Commutant $\mathcal{M}'$ of a subset $\mathcal{M} \subset \operatorname{Mat}_{32}(\mathbb{R})$. -/
def IsInCommutant (M : Mat32 → Prop) (B' : Mat32) : Prop :=
  ∀ A, M A → A * B' = B' * A

/-- **THE MICROCAUSALITY THEOREM**:
    The commutator between any local observable $A \in \mathcal{M}$ and any commutant operator $B' \in \mathcal{M}'$ vanishes identically. -/
theorem microcausality (M : Mat32 → Prop) (A B' : Mat32) 
    (hA : M A) (hB' : IsInCommutant M B') :
    A * B' - B' * A = 0 := by
  rw [hB' A hA, sub_self]

/-! ### 2. The Tomita-Takesaki Modular Conjugation J (J² = I) -/

/-- The Krein-Tomita Modular Conjugation operator $J = \operatorname{diag}(I_{16}, -I_{16})$. -/
def modularJ : Mat32 :=
  Matrix.diagonal (fun i => if i.val < 16 then (1 : ℝ) else -1)

/-- **Theorem**: $J$ is an involution: $J^2 = 1$. -/
theorem modularJ_involution : modularJ * modularJ = 1 := by
  dsimp [modularJ]
  rw [Matrix.diagonal_mul_diagonal]
  have h_diag : (fun i : Dim32 => (if i.val < 16 then (1 : ℝ) else -1) * (if i.val < 16 then (1 : ℝ) else -1)) = fun _ => 1 := by
    ext i
    split_ifs <;> ring
  rw [h_diag]
  exact diagonal_one

/-- The Tomita Modular Reflection: $A \mapsto J A J$. -/
def tomitaReflect (A : Mat32) : Mat32 :=
  modularJ * A * modularJ

/-- **Theorem**: Tomita modular reflection is an involution on operators: $\pi_J(\pi_J(A)) = A$. -/
theorem tomitaReflect_involution (A : Mat32) :
    tomitaReflect (tomitaReflect A) = A := by
  dsimp [tomitaReflect]
  have hJ := modularJ_involution
  calc
    modularJ * (modularJ * A * modularJ) * modularJ
      = (modularJ * modularJ) * A * (modularJ * modularJ) := by
          simp only [Matrix.mul_assoc]
    _ = 1 * A * 1 := by rw [hJ]
    _ = A := by rw [Matrix.one_mul, Matrix.mul_one]

/-! ### 3. Entanglement State Bilinear Pairing Across the Horizon -/

/-- The expectation value / state pairing across the horizon: $\langle A, B' \rangle_\rho = \operatorname{Tr}(\rho A B')$. -/
def modularBilinearPairing (rho A B' : Mat32) : ℝ :=
  Matrix.trace (rho * A * B')

/-- **Theorem**: Commutation under the trace for commuting subsystems: $\operatorname{Tr}(\rho A B') = \operatorname{Tr}(\rho B' A)$. -/
theorem pairing_commutes (rho A B' : Mat32) (h_comm : A * B' = B' * A) :
    modularBilinearPairing rho A B' = Matrix.trace (rho * B' * A) := by
  dsimp [modularBilinearPairing]
  have h := congrArg (fun X : Mat32 => Matrix.trace (rho * X)) h_comm
  simpa only [Matrix.mul_assoc] using h

/-! ### 4. Grand Commutant Duality Synthesis -/

/--
🏆 **GRAND SYNTHESIS: Von Neumann Algebra Commutant Duality & Tomita Modular Reflection**

Unifies:
1. Exact microcausality: $[A, B'] = 0$ for $A \in \mathcal{M}, B' \in \mathcal{M}'$.
2. Modular involution: $J^2 = 1$.
3. Modular reflection involution: $\pi_J(\pi_J(A)) = A$.
4. Trace pairing cyclic commutativity: $\operatorname{Tr}(\rho A B') = \operatorname{Tr}(\rho B' A)$.
-/
theorem grand_commutant_duality_synthesis
    (M : Mat32 → Prop) (rho A B' : Mat32)
    (hA : M A) (hB' : IsInCommutant M B') :
    (A * B' - B' * A = 0) ∧
    (modularJ * modularJ = 1) ∧
    (tomitaReflect (tomitaReflect A) = A) ∧
    (modularBilinearPairing rho A B' = Matrix.trace (rho * B' * A)) :=
  ⟨microcausality M A B' hA hB',
   modularJ_involution,
   tomitaReflect_involution A,
   pairing_commutes rho A B' (hB' A hA)⟩

end InfoGeometry.OperatorAlgebra.CommutantDuality
