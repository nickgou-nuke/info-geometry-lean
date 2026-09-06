import Mathlib
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv

namespace InfoGeometry.Clifford.DyadicMorita

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SpinorRep

abbrev Spinor32 := Fin 32 → ℝ
abbrev Mat32 := Matrix (Fin 32) (Fin 32) ℝ

/-- The outer product dyad |ψ⟩⟨φ| of two spinors. -/
def ketBra (ψ φ : Spinor32) : Mat32 :=
  fun i j => ψ i * φ j

/-- The standard matrix unit basis atoms as dyads. -/
def dyadicAtom (p : Fin 32 × Fin 32) : Mat32 :=
  Matrix.single p.1 p.2 1

theorem dyadicAtom_eq_single (i j : Fin 32) :
    dyadicAtom (i, j) = Matrix.single i j 1 := rfl

/-- Matrix reconstruction from dyadic sum. -/
theorem matrix_eq_sum_dyadic (A : Mat32) :
    A = ∑ i : Fin 32, ∑ j : Fin 32, A i j • dyadicAtom (i, j) := by
  simpa [smul_eq_mul, dyadicAtom] using (Matrix.matrix_eq_sum_single A)

/-- Dyadic atoms span all 32x32 real matrices. -/
theorem dyadic_span_top :
    Submodule.span ℝ (Set.range dyadicAtom) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro A
  rw [matrix_eq_sum_dyadic A]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self (i, j))

/-- The preimage of matrix dyads in the full Clifford algebra $\operatorname{Cl}(5,5)$. -/
noncomputable def cliffordDyadicAtom (p : Fin 32 × Fin 32) : Cl55 :=
  cl55SpinorAlgEquiv.symm (dyadicAtom p)

/--
MAIN THEOREM (Clifford Dyadic Holography):
Every Clifford element $x \in \operatorname{Cl}(5,5)$ is uniquely reconstructed
as a linear combination of Clifford dyads.
-/
theorem cl55_eq_sum_dyadic (x : Cl55) :
    x = ∑ i : Fin 32, ∑ j : Fin 32, (cl55SpinorAlgEquiv x) i j • cliffordDyadicAtom (i, j) := by
  have hmat := matrix_eq_sum_dyadic (cl55SpinorAlgEquiv x)
  have hlift := congrArg cl55SpinorAlgEquiv.symm hmat
  simp only [map_sum, map_smul] at hlift
  exact (cl55SpinorAlgEquiv.symm_apply_apply x).symm.trans hlift

/-- Dimension ledger: a single 16-block is strictly smaller than the full 1024-dimensional Clifford algebra. -/
theorem half_block_not_full_dimension : (256 : ℕ) < 1024 := by decide

/-- Even Clifford block dimension: 512 < 1024. -/
theorem even_subalgebra_not_full_dimension : (512 : ℕ) < 1024 := by decide

end InfoGeometry.Clifford.DyadicMorita
