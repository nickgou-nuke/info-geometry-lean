import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

/-!
# Çelik's Cantor-Set Clifford Representation

From Derya Çelik, "A new approach to matrix isomorphisms of complex Clifford
algebras via Cantor set", Turkish Journal of Mathematics 47 (2023), 75-86.

The repo's `FractalCantorFockWitness.lean` already formalizes Lemma 2.2
(tilt/switch commutation). This file records Theorem 3.1 — the Clifford
representation — delegating all commutation proofs to the existing owner.

## Lemma 2.2 → Already proved in FractalCantorFockWitness

  tilt_sq (j)              → Tⱼ² = I           (Çelik Lemma 2.2, proved)
  switch_sq (j)            → Sⱼ² = I           (Çelik Lemma 2.2, proved)
  tilt_switch_anticomm (j) → TⱼSⱼ = -SⱼTⱼ     (Çelik Lemma 2.2.iv, proved)
  tilt_switch_comm_of_ne   → TⱼSₖ = SₖTⱼ (j≠k) (Çelik Lemma 2.2.iii, proved)
  tilt_comm                → TⱼTₖ = TₖTⱼ       (Çelik Lemma 2.2.i, proved)
  switch_comm              → SⱼSₖ = SₖSⱼ (j≠k) (Çelik Lemma 2.2.ii, proved)

## Theorem 3.1 / 3.2 — Formalization target

The paper's finite-rank theorem says that the representation
`ψ₂ₙ : Cl₂ₙ → End(Fₙ)` is an algebra homomorphism:
  ψ(eᵢ)² = I
  ψ(eᵢ)ψ(eⱼ) = -ψ(eⱼ)ψ(eᵢ)  (i ≠ j)

where Fₙ is the Cantor boundary function space and the representation
uses the tilt/switch operators.  The repo owns the base Pauli relations below
and the tilt/switch commutation lemmas in `FractalCantorFockWitness`.  The
arbitrary-depth finite homomorphism is now constructed in
`CelikKocakPaperCliffordLift` using Mathlib's native `CliffordAlgebra.lift`;
the stronger matrix/tensor-product isomorphism remains separate proof debt.

## Theorem 3.2 target — Matrix = Tensor product of Pauli matrices

  ψ₂ₙ(e₁) = I₂ ⊗ ⋯ ⊗ I₂ ⊗ U    (U = diag(1,-1))
  ψ₂ₙ(e₂) = I₂ ⊗ ⋯ ⊗ I₂ ⊗ V    (V = [[0,1],[1,0]])
  ψ₂ₙ(e_{2k-1}) = −I₂ ⊗ ⋯ ⊗ U ⊗ J ⊗ ⋯ ⊗ J
  ψ₂ₙ(e_{2k})   = −I₂ ⊗ ⋯ ⊗ V ⊗ J ⊗ ⋯ ⊗ J   (J = [[0,i],[-i,0]])

That matrix isomorphism is the target.  This file does not claim the full
finite-rank isomorphism as proved.
-/

set_option linter.unusedVariables false

open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

noncomputable section

namespace InfoGeometry.Canonical.CelikCantorClifford

/-! ### 1. Lemma 2.2 — Already proved in FractalCantorFockWitness -/

-- All six commutation relations are proved:
--   tilt_sq j             : Tⱼ² = I           (Lemma 2.2, Čelik)
--   switch_sq j           : Sⱼ² = I           (Lemma 2.2, Čelik)
--   tilt_switch_anticomm j: TⱼSⱼ = -SⱼTⱼ     (Lemma 2.2.iv, Čelik)
--   tilt_switch_comm_of_ne hij : TᵢSⱼ = SⱼTᵢ (i≠j) (Lemma 2.2.iii, Čelik)
--   tilt_comm (i:=j) (j:=k)  : TⱼTₖ = TₖTⱼ     (Lemma 2.2.i, Čelik)
--   switch_comm (i:=j) (j:=k) hij : SⱼSₖ = SₖSⱼ (j≠k) (Lemma 2.2.ii, Čelik)

/-! ### 2. Rank-one Pauli realization of the Clifford relations -/

/--
The Pauli matrices:
  U = σ_z = diag(1, -1)   — tilt matrix (sign flip)
  V = σ_x = [[0,1],[1,0]]  — switch matrix (bit flip)
  J = [[0,i],[-i,0]]      — the coupling matrix

These satisfy the defining two-generator complex Clifford relations:
  U² = V² = I,  UV = -VU.

The coupling matrix `J` is treated only as a further concrete Pauli matrix
below.  Tensor embeddings and Bott-periodicity statements require a separate
recursive tensor-stage owner.
-/
def U : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def V : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def J : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; -Complex.I, 0]

/-- U² = I. -/
theorem U_sq : U * U = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [U, Matrix.mul_apply]

/-- V² = I. -/
theorem V_sq : V * V = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [V, Matrix.mul_apply]

/-- UV = -VU — the Pauli anticommutation (the Clifford relation). -/
theorem UV_anticomm : U * V = -(V * U) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [U, V, Matrix.mul_apply]

def celikPauliFiniteBridge : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![U, V]

theorem celikPauliFiniteBridge_sq (i : Fin 2) :
    celikPauliFiniteBridge i * celikPauliFiniteBridge i = 1 := by
  fin_cases i
  · simpa [celikPauliFiniteBridge] using U_sq
  · simpa [celikPauliFiniteBridge] using V_sq

theorem celikPauliFiniteBridge_anticomm
    {i j : Fin 2} (hij : i ≠ j) :
    celikPauliFiniteBridge i * celikPauliFiniteBridge j =
      -(celikPauliFiniteBridge j * celikPauliFiniteBridge i) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · simpa [celikPauliFiniteBridge] using UV_anticomm
  · apply eq_neg_of_add_eq_zero_right
    have h : U * V + V * U = 0 := by
      rw [UV_anticomm]
      simp
    simpa [celikPauliFiniteBridge, add_comm] using h
  · exact False.elim (hij rfl)

theorem celikPauliFiniteBridge_gamma_zero :
    celikPauliFiniteBridge 0 = U := by
  rfl

theorem celikPauliFiniteBridge_gamma_one :
    celikPauliFiniteBridge 1 = V := by
  rfl

/-! ### 3. Base Pauli Clifford Relations -/

/--
Base Pauli Clifford packet.

This is the closed finite matrix fragment used by the Çelik dictionary:
`U² = 1`, `V² = 1`, and `UV = -VU`.

It does not assert the full finite-rank map `Cl₂ₙ → End(Fₙ)`, the tensor
product formula for every generator, or the matrix-algebra isomorphism
`Cl₂ₙ ≃ M_{2ⁿ}(ℂ)`.
-/
theorem celik_pauli_clifford_base :
    U * U = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      V * V = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      U * V = -(V * U) := by
  exact ⟨U_sq, V_sq, UV_anticomm⟩

/-! ### 4. Explicit rank-one matrix closure -/

def matrixUnit : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | ⟨0, _⟩ => !![1, 0; 0, 0]
  | ⟨1, _⟩ => !![0, 1; 0, 0]
  | ⟨2, _⟩ => !![0, 0; 1, 0]
  | ⟨3, _⟩ => !![0, 0; 0, 1]
  | _ => 0

theorem matrix_unit_decomposition
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A = A 0 0 • matrixUnit 0 +
      A 0 1 • matrixUnit 1 +
      A 1 0 • matrixUnit 2 +
      A 1 1 • matrixUnit 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixUnit]

theorem matrix_units_span_eq_top :
    Submodule.span ℂ (Set.range matrixUnit) = ⊤ := by
  apply top_unique
  intro A hA
  rw [matrix_unit_decomposition A]
  repeat' apply Submodule.add_mem
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self (0 : Fin 4)))
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self (1 : Fin 4)))
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self (2 : Fin 4)))
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self (3 : Fin 4)))

/-!
#### BUCKET 3: OPEN ISOMORPHISM DEBT

- Prove the tensor-product matrix formulas for every generator.
- Prove surjectivity and injectivity of the finite-rank lift.
- Package the resulting matrix isomorphism only after the inverse laws are
  explicit Lean objects.
-/

end InfoGeometry.Canonical.CelikCantorClifford
