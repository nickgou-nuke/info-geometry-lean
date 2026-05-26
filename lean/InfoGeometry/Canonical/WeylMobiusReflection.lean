import Mathlib
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.ModularLorentzBoost

/-!
# InfoGeometry.Canonical.WeylMobiusReflection

Concrete Weyl/Möbius reflection identities in the current `M₂(ℝ)` basis.

This module is intentionally aligned with existing repository definitions:
* `E` (hyperbolic generator) is diagonal;
* `K` is defined as `E`;
* `N` is nilpotent and `Nᵀ` is its transpose.

So the conjugation action by `E` is a sign flip on the boundary lanes
(`N`, `Nᵀ`), while fixing the Cartan generator `K`.
-/

namespace InfoGeometry.Canonical.WeylMobiusReflection

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.ModularLorentzBoost

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Reflection operator chosen compatibly with existing basis (`W = E = K`). -/
noncomputable def W : M2R := K

@[simp] theorem W_eq_K : W = K := rfl
@[simp] theorem W_eq_E : W = E := by rfl

/-- Weyl involution (`W² = 1`). -/
theorem weyl_involution : W * W = (1 : M2R) := by
  simpa [W, K] using (E_sq : E * E = (1 : M2R))

/-- Cartan generator is fixed by conjugation with `W`. -/
theorem weyl_conj_K :
    W * K * W = K := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [W, K, E, Matrix.mul_apply, Fin.sum_univ_two]

/-- Left nilpotent lane flips sign under Weyl conjugation. -/
theorem weyl_conj_N :
    W * N * W = -N := by
  ext i j <;> (fin_cases i <;> fin_cases j) <;>
    norm_num [W, K, E, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Right nilpotent lane (`Nt`) flips sign under Weyl conjugation. -/
theorem weyl_conj_Nt :
    W * Nt * W = -Nt := by
  ext i j <;> (fin_cases i <;> fin_cases j) <;>
    norm_num [W, K, E, Nt, Matrix.mul_apply, Fin.sum_univ_two]

/-- Transpose-lane version, normalized through existing `Nt = Nᵀ`. -/
theorem weyl_conj_N_transpose :
    W * Nᵀ * W = -Nᵀ := by
  simpa [Nt_eq_transpose] using weyl_conj_Nt

end InfoGeometry.Canonical.WeylMobiusReflection
