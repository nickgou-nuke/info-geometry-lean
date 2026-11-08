import InfoGeometry.Thermo.FiniteDiagonal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring

open scoped BigOperators

/-!
# Thermodynamic Identities (Finite Diagonal Model)

State-function layer over `InfoGeometry.Thermo.FiniteDiagonal`:

- internal energy
- entropy
- Massieu potential
- free energy
- canonical identities `S = βU + log Z` and `βF = -log Z`
-/

namespace InfoGeometry.Thermo.FiniteDiagonal

section Identities

variable {n : ℕ} [Nonempty (Fin n)]

/-- Internal energy `U(β) = ∑ᵢ ρᵢ(β) Hᵢ`. -/
noncomputable def internalEnergy (H : Fin n → ℝ) (β : ℝ) : ℝ :=
  ∑ i, gibbsWeight H β i * H i

/-- Gibbs entropy `S(β) = -∑ᵢ ρᵢ(β) log ρᵢ(β)`. -/
noncomputable def entropy (H : Fin n → ℝ) (β : ℝ) : ℝ :=
  -∑ i, gibbsWeight H β i * Real.log (gibbsWeight H β i)

/-- Massieu potential `ψ(β) = log Z(β)`. -/
noncomputable def massieu (H : Fin n → ℝ) (β : ℝ) : ℝ :=
  Real.log (partition H β)

/-- Helmholtz free energy (finite diagonal convention). -/
noncomputable def freeEnergy (H : Fin n → ℝ) (β : ℝ) : ℝ :=
  -(1 / β) * massieu H β

omit [Nonempty (Fin n)] in
lemma internalEnergy_eq_gibbsState_hamiltonian (H : Fin n → ℝ) (β : ℝ) :
    internalEnergy H β = gibbsState H β (hamiltonianOp H) := by
  unfold internalEnergy gibbsState hamiltonianOp
  simp

lemma log_gibbsWeight (H : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    Real.log (gibbsWeight H β i) = logDensityEntry H β i := by
  rw [gibbsWeight_eq_exp_logDensity (H := H) (β := β) (i := i)]
  simp

lemma entropy_eq_beta_internal_plus_massieu (H : Fin n → ℝ) (β : ℝ) :
    entropy H β = β * internalEnergy H β + massieu H β := by
  unfold entropy internalEnergy massieu
  have hsum : ∑ i, gibbsWeight H β i = 1 := gibbsWeight_sum_one H β
  have hsplit :
      ∑ i, gibbsWeight H β i * (-β * H i - Real.log (partition H β))
        = (-β) * (∑ i, gibbsWeight H β i * H i)
          + (-Real.log (partition H β)) * (∑ i, gibbsWeight H β i) := by
    calc
      ∑ i, gibbsWeight H β i * (-β * H i - Real.log (partition H β))
          = ∑ i, (gibbsWeight H β i * (-β * H i)
              + gibbsWeight H β i * (-Real.log (partition H β))) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
      _ = (∑ i, gibbsWeight H β i * (-β * H i))
            + (∑ i, gibbsWeight H β i * (-Real.log (partition H β))) := by
              rw [Finset.sum_add_distrib]
      _ = ((-β) * (∑ i, gibbsWeight H β i * H i))
            + ((-Real.log (partition H β)) * (∑ i, gibbsWeight H β i)) := by
              congr
              · calc
                  ∑ i, gibbsWeight H β i * (-β * H i)
                      = ∑ i, (-β) * (gibbsWeight H β i * H i) := by
                          refine Finset.sum_congr rfl ?_
                          intro i hi
                          ring
                  _ = (-β) * (∑ i, gibbsWeight H β i * H i) := by
                        simpa using
                          (Finset.mul_sum (s := Finset.univ) (a := -β)
                            (f := fun i => gibbsWeight H β i * H i)).symm
              · calc
                  ∑ i, gibbsWeight H β i * (-Real.log (partition H β))
                      = ∑ i, (-Real.log (partition H β)) * gibbsWeight H β i := by
                          refine Finset.sum_congr rfl ?_
                          intro i hi
                          ring
                  _ = (-Real.log (partition H β)) * (∑ i, gibbsWeight H β i) := by
                        simpa using
                          (Finset.mul_sum (s := Finset.univ)
                            (a := -Real.log (partition H β)) (f := fun i => gibbsWeight H β i)).symm
  calc
    -∑ i, gibbsWeight H β i * Real.log (gibbsWeight H β i)
        = -∑ i, gibbsWeight H β i * logDensityEntry H β i := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [log_gibbsWeight (H := H) (β := β) (i := i)]
    _ = -∑ i, gibbsWeight H β i * (-β * H i - Real.log (partition H β)) := by
          rfl
    _ = -(((-β) * (∑ i, gibbsWeight H β i * H i))
          + ((-Real.log (partition H β)) * (∑ i, gibbsWeight H β i))) := by
            rw [hsplit]
    _ = β * (∑ i, gibbsWeight H β i * H i) + Real.log (partition H β) := by
          rw [hsum]
          ring

omit [Nonempty (Fin n)] in
lemma beta_mul_freeEnergy (H : Fin n → ℝ) (β : ℝ) (hβ : β ≠ 0) :
    β * freeEnergy H β = -massieu H β := by
  unfold freeEnergy
  have hβ' : 1 / β = β⁻¹ := by rw [one_div]
  rw [hβ']
  calc
    β * (-(β⁻¹) * massieu H β) = -((β * β⁻¹) * massieu H β) := by ring
    _ = -((1 : ℝ) * massieu H β) := by rw [mul_inv_cancel₀ hβ]
    _ = -massieu H β := by ring

end Identities

end InfoGeometry.Thermo.FiniteDiagonal
