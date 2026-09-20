import InfoGeometry.Clifford.Tower
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section

namespace InfoGeometry.CliffordWeyl.SplitCliffordGrades

open InfoGeometry.CliffordTower

instance splitSpace_finiteDimensional : (stages : ℕ) →
    FiniteDimensional ℝ (SplitSpace stages)
  | 0 => by
      change FiniteDimensional ℝ (Fin 0 → ℝ × ℝ)
      infer_instance
  | stages + 1 => by
      letI := splitSpace_finiteDimensional stages
      change FiniteDimensional ℝ ((ℝ × ℝ) × SplitSpace stages)
      infer_instance

theorem splitSpace_finrank (stages : ℕ) :
    Module.finrank ℝ (SplitSpace stages) = 2 * stages := by
  induction stages with
  | zero => simp [SplitSpace]
  | succ stages induction_hypothesis =>
      change Module.finrank ℝ ((ℝ × ℝ) × SplitSpace stages) = 2 * (stages + 1)
      rw [Module.finrank_prod, Module.finrank_prod, induction_hypothesis]
      simp only [Module.finrank_self]
      omega

def vectorBasis (stages : ℕ) : Module.Basis (Fin (2 * stages)) ℝ (SplitSpace stages) :=
  Module.finBasisOfFinrankEq ℝ (SplitSpace stages) (splitSpace_finrank stages)

def degreeBasis (stages degree : ℕ) :
    Module.Basis (Set.powersetCard (Fin (2 * stages)) degree) ℝ
      (⋀[ℝ]^degree (SplitSpace stages)) :=
  (vectorBasis stages).exteriorPower degree

theorem degree_finrank (stages degree : ℕ) :
    Module.finrank ℝ (⋀[ℝ]^degree (SplitSpace stages)) =
      Nat.choose (2 * stages) degree := by
  rw [exteriorPower.finrank_eq, splitSpace_finrank]

theorem degree_finrank_above_dimension (stages degree : ℕ)
    (above : 2 * stages < degree) :
    Module.finrank ℝ (⋀[ℝ]^degree (SplitSpace stages)) = 0 := by
  rw [degree_finrank, Nat.choose_eq_zero_of_lt above]

def exteriorBasis (stages : ℕ) :
    Module.Basis (Finset (Fin (2 * stages))) ℝ (ExteriorAlgebra ℝ (SplitSpace stages)) := by
  let basis := (DirectSum.Decomposition.isInternal
    (ℳ := fun degree : ℕ => ⋀[ℝ]^degree (SplitSpace stages))).collectedBasis
      (degreeBasis stages)
  exact basis.reindex (Equiv.sigmaFiberEquiv Finset.card)

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

def cliffordBasis (stages : ℕ) :
    Module.Basis (Finset (Fin (2 * stages))) ℝ (Clsplit stages) :=
  (exteriorBasis stages).map (CliffordAlgebra.equivExterior (Qsplit stages)).symm

instance clifford_finiteDimensional (stages : ℕ) : FiniteDimensional ℝ (Clsplit stages) :=
  Module.Basis.finiteDimensional_of_finite (cliffordBasis stages)

theorem clifford_finrank (stages : ℕ) :
    Module.finrank ℝ (Clsplit stages) = 2 ^ (2 * stages) := by
  rw [Module.finrank_eq_card_basis (cliffordBasis stages)]
  simp

theorem clifford_reconstruction (stages : ℕ) (operator : Clsplit stages) :
    ∑ blade, (cliffordBasis stages).repr operator blade • cliffordBasis stages blade =
      operator :=
  (cliffordBasis stages).sum_repr operator

end InfoGeometry.CliffordWeyl.SplitCliffordGrades
