import Mathlib
import proofs.Cl11SheetDiracMatrices

noncomputable section

open Cl11SheetDiracMatrices

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The total Hilbert space operator algebra is M₂(End(W)) -/
abbrev OperatorValuedMatrix (W : Type) := Matrix (Fin 2 × W) (Fin 2 × W) ℂ

/-- Tensor product of a 2x2 matrix and a WxW matrix -/
def kronecker (A : M2C) (B : Matrix W W ℂ) : OperatorValuedMatrix W :=
  fun ⟨i1, j1⟩ ⟨i2, j2⟩ => A i1 i2 * B j1 j2

/-- Extract the A_0 component from the decomposition -/
def extract_I (M : OperatorValuedMatrix W) : Matrix W W ℂ :=
  fun j1 j2 => (M ⟨0, j1⟩ ⟨0, j2⟩ + M ⟨1, j1⟩ ⟨1, j2⟩) / 2

/-- Extract the A_3 component (associated with Γ) -/
def extract_Gamma (M : OperatorValuedMatrix W) : Matrix W W ℂ :=
  fun j1 j2 => (M ⟨0, j1⟩ ⟨0, j2⟩ - M ⟨1, j1⟩ ⟨1, j2⟩) / 2

/-- Extract the A_1 component (associated with J) -/
def extract_J (M : OperatorValuedMatrix W) : Matrix W W ℂ :=
  fun j1 j2 => (M ⟨0, j1⟩ ⟨1, j2⟩ + M ⟨1, j1⟩ ⟨0, j2⟩) / 2

/-- Extract the A_2 component (associated with K) -/
def extract_K (M : OperatorValuedMatrix W) : Matrix W W ℂ :=
  fun j1 j2 => (M ⟨1, j1⟩ ⟨0, j2⟩ - M ⟨0, j1⟩ ⟨1, j2⟩) / 2

/-- The fundamental theorem of operator-valued polarization:
    Every operator has a unique decomposition into the chiral/sheet basis. -/
theorem operator_valued_polarization (M : OperatorValuedMatrix W) :
    M = kronecker 1 (extract_I M) +
        kronecker Gamma (extract_Gamma M) +
        kronecker J (extract_J M) +
        kronecker K (extract_K M) := by
  ext ⟨i1, j1⟩ ⟨i2, j2⟩
  fin_cases i1 <;> fin_cases i2 <;>
    simp [kronecker, extract_I, extract_Gamma, extract_J, extract_K,
          Gamma, J, K, Matrix.add_apply, Matrix.mul_apply] <;>
    ring
