import Mathlib
import InfoGeometry.Algebra.HypercomplexTriad

/-!
# InfoGeometry.Canonical.SuperAlgebraEquilibrium

Concrete `2×2` superalgebra equilibrium identities from split-Clifford atoms.
-/

namespace InfoGeometry.Canonical.SuperAlgebraEquilibrium

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Odd generator `Q`. -/
noncomputable def Q : M2R := N

/-- Conjugate odd generator `Q†`. -/
def Q_dag : M2R := !![0, 0; 1, 0]

/-- Even generator `H`. -/
def H : M2R := (1 : M2R)

/-- Fermionic nilpotency in anticommutator form: `{Q,Q}=0`. -/
theorem super_odd_nilpotent :
    Q * Q + Q * Q = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Q, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Odd pairing generates the even Hamiltonian: `{Q,Q†}=H`. -/
theorem super_odd_pairing_generates_even :
    Q * Q_dag + Q_dag * Q = H := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Q, Q_dag, N, H, Matrix.mul_apply, Fin.sum_univ_two]

/-- Even/odd commutator vanishes: `[H,Q]=0`. -/
theorem super_even_odd_commute :
    H * Q - Q * H = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [H, Q, N, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.SuperAlgebraEquilibrium
