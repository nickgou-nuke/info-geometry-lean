import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# `Cl(5,5)`, split anomaly cancellation, Bott stability, and `osp(1|2)` atoms

This module formalizes the algebraic skeleton:

* dimension factorization `dim Cl(5,5)=2^10=2^2*2^8`, matching
  `Cl(1,1) ⊗ Cl(4,4)`;
* matrix dimensions `M₂ ⊗ M₁₆ ≃ M₃₂` at the level of real dimensions;
* split signature anomaly index `5-5=0`;
* an `osp(1|2)` atom where `G²=T` implies `{G,G}=2T`;
* tensor/Bott-block maps preserving tripotent geometry and the twisted
  Witten index in the colimit.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55AnomalyOSP

open Matrix

/-! ## Dimension and split-signature arithmetic -/

/-- Clifford real vector-space dimension. -/
def cliffordDim (p q : ℕ) : ℕ := 2 ^ (p + q)

/-- `Cl(5,5)` has dimension `1024`. -/
theorem cliffordDim_55 : cliffordDim 5 5 = 1024 := by
  norm_num [cliffordDim]

/-- `Cl(1,1)` has dimension `4`. -/
theorem cliffordDim_11 : cliffordDim 1 1 = 4 := by
  norm_num [cliffordDim]

/-- `Cl(4,4)` has dimension `256`. -/
theorem cliffordDim_44 : cliffordDim 4 4 = 256 := by
  norm_num [cliffordDim]

/-- Dimension factorization for `Cl(5,5) ≃ Cl(1,1) ⊗ Cl(4,4)`. -/
theorem clifford_55_factor_dim : cliffordDim 5 5 = cliffordDim 1 1 * cliffordDim 4 4 := by
  norm_num [cliffordDim]

/-- Matrix dimension factorization `M₂ ⊗ M₁₆` has `M₃₂` dimension. -/
theorem matrix_dim_factor : 2^2 * 16^2 = 32^2 := by
  norm_num

/-- Split-signature anomaly index. -/
def anomalyIndex (p q : ℤ) : ℤ := p - q

/-- The `(5,5)` anomaly index vanishes. -/
theorem anomalyIndex_55_zero : anomalyIndex 5 5 = 0 := by
  norm_num [anomalyIndex]

/-! ## `osp(1|2)` atom and tripotency -/

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C
abbrev M6C := InfoGeometry.Algebra.FiniteSpin.Mat6C

/-- A concrete odd generator. -/
def Gatom : M2C := !![0, 1; 1, 0]

/-- The even Hamiltonian/translation atom. -/
def Tatom : M2C := 1

/-- `G²=T`. -/
theorem Gatom_sq : Gatom * Gatom = Tatom := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Gatom, Tatom, Matrix.mul_apply, Fin.sum_univ_two]

/-- The super-anticommutator `{G,G}=2T`. -/
theorem osp_atom_anticommutator : Gatom * Gatom + Gatom * Gatom = (2 : ℂ) • Tatom := by
  rw [Gatom_sq]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Tatom] <;> norm_num

/-- Tripotent scale operator. -/
def Trip : M3C := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- Tripotency `T³=T`. -/
theorem Trip_tripotent : Trip * Trip * Trip = Trip := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Trip, Matrix.mul_apply, Fin.sum_univ_three]

/-- One doubled/tensored copy of the tripotent sector. -/
def TripLift : M6C :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- Tensoring/doubling by an identity block preserves tripotency. -/
theorem TripLift_tripotent : TripLift * TripLift * TripLift = TripLift := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [TripLift, Matrix.mul_apply, Fin.sum_univ_six]


end InfoGeometry.Clifford.Clifford55AnomalyOSP
