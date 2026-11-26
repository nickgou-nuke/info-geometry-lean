/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge

/-!
# Concrete finite-stage tower for doubled-Minkowski BdG gap persistence

This module instantiates the abstract directed-tower theorem of
`DoubledMinkowskiBdGColimitBridge` with a concrete refinement of doubled BdG
state spaces by padding one zero particle/hole component per stage. It proves
that Euclidean norm and sheet-Krein pairing are preserved, that the zero-kinetic
BdG quadratic form is exactly `m² * ‖ψ‖²`, and that the abstract colimit theorem
therefore yields a projective limit quadratic form with the same lower bound.

No continuum 4D Yang–Mills existence, Wightman/OS axioms, or physical spectral
mass-gap theorem is claimed.
-/

namespace InfoGeometry.Canonical.DoubledMinkowskiConcreteTowerGap

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open scoped BigOperators
open Filter

/-- Non-commutativity witness inherited from the concrete BdG block carrier. -/
theorem concreteTower_noncommWitness :
    ∃ A B : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ, A * B ≠ B * A :=
  exists_noncomm_bdg_mat

/-- Pad a finite vector by one zero component at the last index. -/
def pad {n : ℕ} (u : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.lastCases 0 u

/-- Lift the padding to a doubled particle/hole state. -/
def padSum {n : ℕ} (ψ : Fin n ⊕ Fin n → ℝ) : Fin (n + 1) ⊕ Fin (n + 1) → ℝ :=
  Sum.elim (fun i => pad (fun j => ψ (Sum.inl j)) i)
           (fun i => pad (fun j => ψ (Sum.inr j)) i)

/-- Padding preserves the Euclidean dot product. -/
theorem pad_dotProduct {n : ℕ} (u v : Fin n → ℝ) :
    dotProduct (pad u) (pad v) = dotProduct u v := by
  simp [dotProduct, pad, Fin.sum_univ_castSucc]

/-- Padding preserves the doubled-state dot product. -/
theorem padSum_dotProduct {n : ℕ} (ψ φ : Fin n ⊕ Fin n → ℝ) :
    dotProduct (padSum ψ) (padSum φ) = dotProduct ψ φ := by
  simp [dotProduct, padSum, pad, Fin.sum_univ_castSucc, Fintype.sum_sum_type]

/-- Sheet Krein involution `diag(1, -1)` on a finite BdG stage. -/
def sheetKrein (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Sheet-Krein pairing on a finite BdG stage. -/
def bdgKreinPair {n : ℕ} (ψ φ : Fin n ⊕ Fin n → ℝ) : ℝ :=
  dotProduct ψ ((sheetKrein n).mulVec φ)

/-- Padding preserves the sheet-Krein pairing. -/
theorem padSum_bdgKreinPair {n : ℕ} (ψ φ : Fin n ⊕ Fin n → ℝ) :
    bdgKreinPair (padSum ψ) (padSum φ) = bdgKreinPair ψ φ := by
  simp [bdgKreinPair, sheetKrein, Matrix.mulVec, Matrix.one_apply, dotProduct,
    padSum, pad, Fin.sum_univ_castSucc, Fintype.sum_sum_type]

/-- BdG quadratic form for the zero-kinetic stage with pairing gap `m`. -/
def stageBdgQuad {n : ℕ} (m : ℝ) (ψ : Fin n ⊕ Fin n → ℝ) : ℝ :=
  let H := bdgHamiltonian (0 : Matrix (Fin n) (Fin n) ℝ) m
  dotProduct ψ ((H * H).mulVec ψ)

/-- The zero-kinetic BdG quadratic form is exactly `m² * ‖ψ‖²`. -/
theorem stageBdgQuad_eq {n : ℕ} (m : ℝ) (ψ : Fin n ⊕ Fin n → ℝ) :
    stageBdgQuad m ψ = m ^ 2 * dotProduct ψ ψ := by
  have h := bdg_gapped_spectrum_and_particle_hole_symmetry
    (0 : Matrix (Fin n) (Fin n) ℝ) (by simp) m ψ
  dsimp [stageBdgQuad]
  rw [h.2.2.1]
  simp [Matrix.mulVec, Matrix.one_apply, dotProduct, Fintype.sum_sum_type,
    mul_add, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Uniform gap bound at every concrete finite stage. -/
theorem stageBdgQuad_gap {n : ℕ} (m : ℝ) (ψ : Fin n ⊕ Fin n → ℝ) :
    m ^ 2 * dotProduct ψ ψ ≤ stageBdgQuad m ψ := by
  rw [stageBdgQuad_eq]

/-- The concrete BdG quadratic form is invariant under stage padding. -/
theorem stageBdgQuad_pad {n : ℕ} (m : ℝ) (ψ : Fin n ⊕ Fin n → ℝ) :
    stageBdgQuad m (padSum ψ) = stageBdgQuad m ψ := by
  rw [stageBdgQuad_eq, stageBdgQuad_eq, padSum_dotProduct]

/-- Euclidean norm is strictly invariant along the concrete padding tower. -/
theorem seqVal_normSq_pad :
    ∀ n (ψ : Fin n ⊕ Fin n → ℝ) (k : ℕ),
      seqVal (fun n => padSum (n := n)) (fun n ψ => dotProduct ψ ψ) n ψ k =
        dotProduct ψ ψ := by
  intro n ψ k
  induction k generalizing n ψ with
  | zero => rfl
  | succ k ih =>
    change seqVal (fun n => padSum (n := n)) (fun n ψ => dotProduct ψ ψ) (n + 1)
      (padSum ψ) k = dotProduct ψ ψ
    rw [ih, padSum_dotProduct]

/-- Concrete instance of the abstract doubled-Minkowski BdG colimit gap theorem.
The resulting `Q_inf` is a projective limit quadratic form with the same
`m²`-lower bound; it is not a continuum Yang–Mills measure. -/
theorem concrete_tower_gap (m : ℝ) :
    ∃ Q_inf : (n : ℕ) → (Fin n ⊕ Fin n → ℝ) → ℝ,
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        Tendsto (seqVal (fun n => padSum (n := n)) (fun n ψ => stageBdgQuad m ψ) n ψ) atTop
          (nhds (Q_inf n ψ))) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        m ^ 2 * dotProduct ψ ψ ≤ Q_inf n ψ) := by
  have h := continuum_colimit_doubled_minkowski_and_bdg_mass_gap
    (V := fun n => Fin n ⊕ Fin n → ℝ)
    (ι := fun n => padSum (n := n))
    (normSq := fun n ψ => dotProduct ψ ψ)
    (kreinPair := fun n ψ φ => bdgKreinPair ψ φ)
    (bdgQuad := fun n ψ => stageBdgQuad m ψ)
    (ε := fun _ => 0) m
    (by intro n ψ; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (ψ i))
    (by intro n ψ; exact padSum_dotProduct ψ ψ)
    (by intro n ψ φ; exact padSum_bdgKreinPair ψ φ)
    (by intro n ψ; exact stageBdgQuad_gap m ψ)
    (by simp)
    (by intro n ψ; simp [stageBdgQuad_pad])
  rcases h with ⟨hKrein, Q_inf, hTendsto, hProj, hGap, hNN⟩
  exact ⟨Q_inf, hTendsto, hGap⟩

end InfoGeometry.Canonical.DoubledMinkowskiConcreteTowerGap
