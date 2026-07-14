import Mathlib
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.ConcreteHilbertCommutation
import InfoGeometry.Canonical.CayleyBregmanBridge

/-!
# Souriau-Bost-Connes Crystallization: Closure Proofs

This module keeps the capstone closure debt honest by delegating already-closed
finite/algebraic/limit facts to their current owner files, and by proving the
remaining finite V4 sewing anomaly statement from concrete Pauli matrices.

The statements here are not the full analytic Bost-Connes theorem and do not
construct the Cantor-state accumulation functor.  Those remain separate
construction debt in `SouriauBostConnesTransition.lean`.
-/

open scoped Topology TensorProduct

noncomputable section

namespace SouriauBostConnesClosureProofs

open InfoGeometry.Canonical.FormalPrimeRootSystem
open Matrix Complex

/-! ## 1. Finite primon product and Weyl denominator -/

/--
Finite cutoff partition identity: the repository-owned finite primon product is
the reciprocal of the evaluated Boolean prime Weyl denominator.
-/
@[rep_depth thermo, capstone]
theorem finite_primon_partition_eq_inverse_evaluated_denominator
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finitePrimonPartition L β = (evaluatedWeylDenominator L β)⁻¹ :=
  finitePrimonPartition_eq_evaluatedWeylDenominator_inv L β

/-- Same finite identity in conventional `p ^ (-β)` variables. -/
@[rep_depth thermo, capstone]
theorem finite_primon_partition_eq_rpow_product
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finitePrimonPartition L β = ∏ p ∈ L.primes, (1 - (p : ℝ) ^ (-β))⁻¹ :=
  finitePrimonPartition_eq_rpowProduct L β

/-! ## 2. Algebraic tensor-factor separation -/

/--
Algebraic tensor-factor separation:
`(S ⊗ id) (id ⊗ K) = (id ⊗ K) (S ⊗ id)`.

This is the theorem-safe algebraic core of the Cuntz-base/fiber separation.
The bounded Hilbert-completion lift remains separate analytic debt.
-/
@[rep_depth thermo, capstone]
theorem tensor_factor_separation
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (S : V →ₗ[ℝ] V) (K : W →ₗ[ℝ] W) :
    (TensorProduct.map S (LinearMap.id : W →ₗ[ℝ] W)).comp
        (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) K) =
      (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) K).comp
        (TensorProduct.map S (LinearMap.id : W →ₗ[ℝ] W)) :=
  ConcreteHilbertCommutation.tensorFactorSeparation S K

/-! ## 3. Real thermal Cayley compactification -/

/--
The real thermal-ray Cayley coordinate tends to the disk boundary point `1` as
`β -> +∞`.

This proves only the scalar compactification coordinate.  Identifying the
zero-temperature state accumulation set with the Cantor boundary is not claimed
here.
-/
@[rep_depth thermo, capstone]
theorem thermal_cayley_tendsto_boundary_one :
    Filter.Tendsto Cayley.thermalCayley Filter.atTop (𝓝 (1 : ℝ)) :=
  Cayley.thermalCayley_tendsto_atTop_one

/-! ## 4. Concrete V4 sewing anomaly cancellation -/

/-- Concrete chirality operator, Pauli Z. -/
@[rep_depth thermo, capstone]
def concreteChirality : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Concrete V4 sewing involution, Pauli X. -/
@[rep_depth thermo, capstone]
def concreteSwitch : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- `Γ ^ 2 = 1` for the concrete chirality matrix. -/
@[simp, rep_depth thermo, capstone]
theorem concreteChirality_sq :
    concreteChirality ^ 2 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [concreteChirality, Matrix.mul_apply, Fin.sum_univ_two, pow_two]

/-- `S ^ 2 = 1` for the concrete sewing involution. -/
@[simp, rep_depth thermo, capstone]
theorem concreteSwitch_sq :
    concreteSwitch ^ 2 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [concreteSwitch, Matrix.mul_apply, Fin.sum_univ_two, pow_two]

/-- The concrete chirality and sewing involution anticommute. -/
@[rep_depth thermo, capstone]
theorem concreteChirality_switch_anticomm :
    concreteChirality * concreteSwitch = -(concreteSwitch * concreteChirality) := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [concreteChirality, concreteSwitch, Matrix.mul_apply, Fin.sum_univ_two]

/-- The product `ΓS` is traceless. -/
@[rep_depth thermo, capstone]
theorem concreteChirality_mul_switch_trace_zero :
    Matrix.trace (concreteChirality * concreteSwitch) = (0 : ℂ) := by
  simp [concreteChirality, concreteSwitch, Matrix.trace, Fin.sum_univ_two]

/-- A concrete 2x2 boundary state invariant under the V4 sewing involution. -/
@[rep_depth thermo, capstone]
structure SewnBoundaryState where
  rho : Matrix (Fin 2) (Fin 2) ℂ
  is_hermitian : rhoᴴ = rho
  trace_one : Matrix.trace rho = (1 : ℂ)
  sewing_invariant : concreteSwitch * rho * concreteSwitch = rho

/-- Canonical V4-sewn boundary state: the maximally mixed 2x2 density matrix. -/
@[rep_depth thermo, capstone]
def canonicalSewnBoundaryState : SewnBoundaryState where
  rho := (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  is_hermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  trace_one := by
    simp [Matrix.trace]
  sewing_invariant := by
    ext i j
    fin_cases i <;> fin_cases j
      <;> simp [concreteSwitch, Matrix.mul_apply, Fin.sum_univ_two]

/-- Chiral index of a concrete sewn boundary state: `χ = Tr(Γρ)`. -/
@[rep_depth thermo, capstone]
noncomputable def sewnChiralIndex (s : SewnBoundaryState) : ℂ :=
  Matrix.trace (concreteChirality * s.rho)

/--
Every concrete V4-sewn boundary state has zero chiral index.

The proof uses only the concrete Pauli matrices, their anticommutation, the
involution law `S ^ 2 = 1`, and cyclicity of the matrix trace.
-/
@[rep_depth thermo, capstone]
theorem sewn_boundary_chiral_index_vanishes (s : SewnBoundaryState) :
    sewnChiralIndex s = 0 := by
  unfold sewnChiralIndex
  have h_anticomm_sw_chir :
      concreteSwitch * concreteChirality = -(concreteChirality * concreteSwitch) := by
    calc
      concreteSwitch * concreteChirality = -(-(concreteSwitch * concreteChirality)) := by
        simp
      _ = -(concreteChirality * concreteSwitch) := by
        rw [concreteChirality_switch_anticomm]
  have h_sewn : concreteSwitch * s.rho * concreteSwitch = s.rho :=
    s.sewing_invariant
  have h_switch_sq : concreteSwitch ^ 2 = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    concreteSwitch_sq
  have h_trace_neg :
      Matrix.trace (concreteChirality * s.rho) =
        -Matrix.trace (concreteChirality * s.rho) := by
    calc
      Matrix.trace (concreteChirality * s.rho)
          = Matrix.trace (concreteChirality * (concreteSwitch * s.rho * concreteSwitch)) := by
            rw [h_sewn]
      _ = Matrix.trace (concreteChirality * concreteSwitch * s.rho * concreteSwitch) := by
            simp [mul_assoc]
      _ = Matrix.trace (concreteSwitch * (concreteChirality * concreteSwitch * s.rho)) := by
            rw [Matrix.trace_mul_comm
              (concreteChirality * concreteSwitch * s.rho) concreteSwitch]
      _ = Matrix.trace (concreteSwitch * concreteChirality * concreteSwitch * s.rho) := by
            simp [mul_assoc]
      _ = Matrix.trace ((-(concreteChirality * concreteSwitch)) * concreteSwitch * s.rho) := by
            rw [h_anticomm_sw_chir]
      _ = Matrix.trace (-(concreteChirality * concreteSwitch * concreteSwitch) * s.rho) := by
            simp [mul_assoc]
      _ = Matrix.trace (-(concreteChirality * (concreteSwitch ^ 2)) * s.rho) := by
            simp [mul_assoc, pow_two]
      _ = Matrix.trace (-(concreteChirality * (1 : Matrix (Fin 2) (Fin 2) ℂ)) * s.rho) := by
            rw [h_switch_sq]
      _ = Matrix.trace (-concreteChirality * s.rho) := by
            simp
      _ = Matrix.trace (-(concreteChirality * s.rho)) := by
            simp
      _ = -Matrix.trace (concreteChirality * s.rho) := by
            simp
  have h_sum_zero :
      Matrix.trace (concreteChirality * s.rho) +
          Matrix.trace (concreteChirality * s.rho) = 0 := by
    calc
      Matrix.trace (concreteChirality * s.rho) +
          Matrix.trace (concreteChirality * s.rho)
          = Matrix.trace (concreteChirality * s.rho) +
              (-Matrix.trace (concreteChirality * s.rho)) := by
                nth_rw 2 [h_trace_neg]
      _ = 0 := by
            simp
  have h_two_mul : (2 : ℂ) * Matrix.trace (concreteChirality * s.rho) = 0 := by
    calc
      (2 : ℂ) * Matrix.trace (concreteChirality * s.rho)
          = Matrix.trace (concreteChirality * s.rho) +
              Matrix.trace (concreteChirality * s.rho) := by
                ring
      _ = 0 := h_sum_zero
  rcases mul_eq_zero.mp h_two_mul with (h2z | htr)
  · have h2_nz : (2 : ℂ) ≠ 0 := by
      norm_num
    exact absurd h2z h2_nz
  · exact htr

/-- The canonical sewn boundary state has zero chiral index. -/
@[rep_depth thermo, capstone]
theorem canonical_sewn_boundary_chiral_index_vanishes :
    sewnChiralIndex canonicalSewnBoundaryState = 0 :=
  sewn_boundary_chiral_index_vanishes canonicalSewnBoundaryState

end SouriauBostConnesClosureProofs
