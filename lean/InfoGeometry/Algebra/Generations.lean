import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Basis-indexed fermion quantum-number table

This file assigns the eight named basis elements of the concrete integral
split-octonion carrier to eight fermion quantum-number labels.  It proves that
the assignment is injective and records the table's count and charge sum.
It does not map arbitrary split-octonions (linear combinations of basis
elements) to particle lists, nor does it prove an Albert-algebra realization
of a fermion generation.  Those require additional representation data.
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

namespace InfoGeometry.Algebra.Generations

/-- Color label in the finite one-generation table. -/
inductive Color where
  | singlet : Color
  | red : Color
  | green : Color
  | blue : Color
  deriving DecidableEq, Repr

/-- Quantum-number tuple assigned to a named split-octonion basis vector. -/
structure FermionQuantumNumbers where
  electricCharge : ℚ
  weakIsospin : ℚ
  hypercharge : ℚ
  color : Color
  deriving DecidableEq, Repr

/-- Explicit basis-indexed assignment.  `Basis8` is the basis of the concrete
integral Zorn split-octonion carrier, not a space of arbitrary states. -/
def basisFermion : Basis8 → FermionQuantumNumbers
  | .ePlus  => ⟨0, 1 / 2, -1, Color.singlet⟩
  | .eMinus => ⟨-1, -1 / 2, -1, Color.singlet⟩
  | .up0    => ⟨2 / 3, 1 / 2, 1 / 3, Color.red⟩
  | .up1    => ⟨2 / 3, 1 / 2, 1 / 3, Color.green⟩
  | .up2    => ⟨2 / 3, 1 / 2, 1 / 3, Color.blue⟩
  | .down0  => ⟨-1 / 3, -1 / 2, 1 / 3, Color.red⟩
  | .down1  => ⟨-1 / 3, -1 / 2, 1 / 3, Color.green⟩
  | .down2  => ⟨-1 / 3, -1 / 2, 1 / 3, Color.blue⟩

/-- Distinct split-octonion basis labels remain distinct under the assignment. -/
theorem basisFermion_injective : Function.Injective basisFermion := by
  intro x y h
  cases x <;> cases y <;> simp [basisFermion] at h ⊢ <;> norm_num at h

/-- The eight indexed basis vectors are distinct in the actual eight-coordinate
split-octonion carrier. -/
theorem basisElem_injective : Function.Injective basisElem := by
  intro x y h
  cases x <;> cases y <;>
    simp [basisElem, ePlus, eMinus, up0, up1, up2, down0, down1, down2] at h ⊢

/-- The eight labels, in the declared basis order. -/
def singleGenerationFermions : List FermionQuantumNumbers :=
  [basisFermion .ePlus, basisFermion .eMinus, basisFermion .up0,
   basisFermion .up1, basisFermion .up2, basisFermion .down0,
   basisFermion .down1, basisFermion .down2]

/-- The sum of electric charges in the explicitly declared basis table is zero. -/
theorem single_generation_charge_sum_zero :
    (singleGenerationFermions.map FermionQuantumNumbers.electricCharge).sum = 0 := by
  norm_num [singleGenerationFermions, basisFermion]

/-- Three copies of the finite basis-label table.  This is a list construction;
it does not identify three arbitrary Albert slots with physical generations. -/
def threeGenerationTable : List FermionQuantumNumbers :=
  singleGenerationFermions ++ singleGenerationFermions ++ singleGenerationFermions

/-- Charge sum of the three-copy table, derived from the one-copy charge sum. -/
theorem three_generation_table_charge_sum_zero :
    (threeGenerationTable.map FermionQuantumNumbers.electricCharge).sum = 0 := by
  simp only [threeGenerationTable, List.map_append, List.sum_append,
    single_generation_charge_sum_zero, add_zero]

end InfoGeometry.Algebra.Generations
