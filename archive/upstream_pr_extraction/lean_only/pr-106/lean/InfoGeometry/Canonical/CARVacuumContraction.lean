import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.CARVacuumContraction

Concrete CAR vacuum contraction lemmas on a state `v`.

This file proves:

* single-mode contraction:
  if `A ∘ C + C ∘ A = c • id` and `A v = 0`, then `A (C v) = c • v`;
* bounded finite-sum lift over a `Finset` of modes.
-/

namespace InfoGeometry.Canonical.CARVacuumContraction

open scoped BigOperators

set_option linter.unusedSimpArgs false

variable {𝕜 V ι : Type*}
variable [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

/--
Single-mode CAR vacuum contraction.
-/
theorem car_vacuum_contraction
    (A C : V →ₗ[𝕜] V)
    (c : 𝕜)
    (h_car : A.comp C + C.comp A = c • (LinearMap.id : V →ₗ[𝕜] V))
    (v : V)
    (h_vac : A v = 0) :
    A (C v) = c • v := by
  have h_eval : (A.comp C + C.comp A) v = (c • (LinearMap.id : V →ₗ[𝕜] V)) v := by
    simpa using congrArg (fun F : V →ₗ[𝕜] V => F v) h_car
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply] at h_eval
  rw [LinearMap.smul_apply, LinearMap.id_apply] at h_eval
  rw [h_vac, LinearMap.map_zero, add_zero] at h_eval
  exact h_eval

/--
Bounded finite-sum CAR contraction on a vacuum state.

Each mode `i` contributes `c i • v` provided:
* modewise CAR: `(A i) ∘ (C i) + (C i) ∘ (A i) = c i • id`;
* vacuum annihilation: `(A i) v = 0`.
-/
theorem car_vacuum_contraction_sum
    [DecidableEq ι]
    (S : Finset ι)
    (A C : ι → V →ₗ[𝕜] V)
    (c : ι → 𝕜)
    (v : V)
    (h_car :
      ∀ i ∈ S,
        (A i).comp (C i) + (C i).comp (A i) = (c i) • (LinearMap.id : V →ₗ[𝕜] V))
    (h_vac : ∀ i ∈ S, A i v = 0) :
    (Finset.sum S (fun i => (A i).comp (C i))) v = (Finset.sum S c) • v := by
  calc
    (Finset.sum S (fun i => (A i).comp (C i))) v
        = Finset.sum S (fun i => ((A i).comp (C i)) v) := by
            simp
    _ = Finset.sum S (fun i => (c i) • v) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using
            car_vacuum_contraction (A i) (C i) (c i) (h_car i hi) v (h_vac i hi)
    _ = (Finset.sum S c) • v := by
          simpa using (Finset.sum_smul (s := S) (f := c) (x := v)).symm

/-! ### Constructive 2×2 Matrix CAR Fermion Fock Model -/

open Matrix

/-- Fermionic annihilation operator: $a = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. -/
def carAnnihilate (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1;
     0, 0]

/-- Fermionic creation operator: $a^\dagger = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$. -/
def carCreate (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0;
     1, 0]

/-- Vacuum state column vector: $v_0 = \begin{pmatrix} 1 \\ 0 \end{pmatrix}$. -/
def carVacuumCol (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 1) R :=
  !![1;
     0]

/-- 🏆 THEOREM 1 (Constructive Vacuum Annihilation):
    $a \cdot v_0 = 0$. -/
theorem car_vacuum_annihilate_exact (R : Type*) [CommRing R] :
    carAnnihilate R * carVacuumCol R = 0 := by
  dsimp [carAnnihilate, carVacuumCol]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- 🏆 THEOREM 2 (Constructive Canonical Anticommutation Relation):
    $\{a, a^\dagger\} = a a^\dagger + a^\dagger a = I_2$. -/
theorem car_anticommutation_exact (R : Type*) [CommRing R] :
    carAnnihilate R * carCreate R + carCreate R * carAnnihilate R = 1 := by
  dsimp [carAnnihilate, carCreate]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- 🏆 THEOREM 3 (Constructive Single-Mode Fock Contraction):
    $a (a^\dagger v_0) = v_0$. -/
theorem car_vacuum_contraction_matrix_exact (R : Type*) [CommRing R] :
    carAnnihilate R * (carCreate R * carVacuumCol R) = carVacuumCol R := by
  dsimp [carAnnihilate, carCreate, carVacuumCol]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.CARVacuumContraction
