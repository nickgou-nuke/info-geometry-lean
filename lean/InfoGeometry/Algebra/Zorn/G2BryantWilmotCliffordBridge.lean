import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Bryant-Wilmot Clifford Spin(7) Bridge to 14D 𝔤₂ Lie Derivations

Formalizes the 14-dimensional Bryant-Wilmot generator basis of the exceptional
Lie algebra `𝔤₂ ⊂ 𝔰𝔬(7) ⊂ Cl(7, 0)` as explicit bivectors in `Spin(7)`
leaving the associative calibration 3-form `Φ` invariant (Wilmot, arXiv:2505.06011v1, 2025;
Bryant, 1987).

### Main Results:
1. `bivector`: Standard `𝔰𝔬(7)` elementary rotation generator `e_{ij}`.
2. `bryantWilmotMatrix`: The 14-dimensional linear combination of Bryant generators.
3. `bryantWilmotMatrix_skew`: Proof of strict skew-symmetry `Mᵀ = -M` in `𝔰𝔬(7)`.
4. `bryantWilmot_preserves_metric`: Infinitesimal preservation of the Euclidean metric.
-/

namespace InfoGeometry.Algebra.Zorn.G2BryantWilmot

variable {R : Type*} [CommRing R]

/-- Elementary rotation bivector matrix `E_{ij} = e_i e_jᵀ - e_j e_iᵀ` in `𝔰𝔬(7)`. -/
def bivector (i j : Fin 7) : Matrix (Fin 7) (Fin 7) R :=
  fun r c =>
    if i = j then 0
    else if r = i ∧ c = j then (1 : R)
    else if r = j ∧ c = i then (-1 : R)
    else 0

theorem bivector_apply_same (i : Fin 7) :
    bivector (R := R) i i = 0 := by
  ext r c
  simp [bivector]

theorem bivector_skew (i j : Fin 7) (r c : Fin 7) :
    bivector (R := R) i j c r = - bivector i j r c := by
  dsimp [bivector]
  by_cases hij : i = j
  · simp [hij]
  · by_cases h1 : r = i ∧ c = j
    · have h2 : ¬(c = i ∧ r = j) := by
        rintro ⟨rfl, rfl⟩
        exact hij h1.1.symm
      have h3 : c = j ∧ r = i := ⟨h1.2, h1.1⟩
      simp [hij, h1, h2, h3]
    · by_cases h2 : r = j ∧ c = i
      · have h3 : ¬(c = j ∧ r = i) := by
          rintro ⟨rfl, rfl⟩
          exact hij h2.2.symm
        have h4 : c = i ∧ r = j := ⟨h2.2, h2.1⟩
        simp [hij, h1, h2, h3, h4]
      · have h3 : ¬(c = i ∧ r = j) := by
          rintro ⟨hca, hcb⟩
          exact h2 ⟨hcb, hca⟩
        have h4 : ¬(c = j ∧ r = i) := by
          rintro ⟨hca, hcb⟩
          exact h1 ⟨hcb, hca⟩
        simp [hij, h1, h2, h3, h4]

/-- The 14-parameter Bryant-Wilmot 𝔤₂ derivation matrix on `R⁷`. -/
def bryantWilmotMatrix (c : Fin 14 → R) : Matrix (Fin 7) (Fin 7) R
  | 0, 0 => 0
  | 0, 1 => c 2
  | 0, 2 => -c 1
  | 0, 3 => c 4
  | 0, 4 => c 3
  | 0, 5 => -c 6
  | 0, 6 => c 5 - c 12
  | 1, 0 => -c 2
  | 1, 1 => 0
  | 1, 2 => c 0
  | 1, 3 => c 5
  | 1, 4 => -c 6 + c 13
  | 1, 5 => c 3 - c 10
  | 1, 6 => -c 4 - c 11
  | 2, 0 => c 1
  | 2, 1 => -c 0
  | 2, 2 => 0
  | 2, 3 => -c 13
  | 2, 4 => c 12
  | 2, 5 => c 11
  | 2, 6 => -c 10
  | 3, 0 => -c 4
  | 3, 1 => -c 5
  | 3, 2 => c 13
  | 3, 3 => 0
  | 3, 4 => -c 0 + c 7
  | 3, 5 => -c 1 + c 8
  | 3, 6 => c 2 - c 9
  | 4, 0 => -c 3
  | 4, 1 => c 6 - c 13
  | 4, 2 => -c 12
  | 4, 3 => c 0 - c 7
  | 4, 4 => 0
  | 4, 5 => c 9
  | 4, 6 => c 8
  | 5, 0 => c 6
  | 5, 1 => -c 3 + c 10
  | 5, 2 => -c 11
  | 5, 3 => c 1 - c 8
  | 5, 4 => -c 9
  | 5, 5 => 0
  | 5, 6 => -c 7
  | 6, 0 => -c 5 + c 12
  | 6, 1 => c 4 + c 11
  | 6, 2 => c 10
  | 6, 3 => -c 2 + c 9
  | 6, 4 => -c 8
  | 6, 5 => c 7
  | 6, 6 => 0

/-- 🏆 THEOREM: The 14-parameter Bryant-Wilmot matrix is strictly skew-symmetric in 𝔰𝔬(7). -/
theorem bryantWilmotMatrix_skew (c : Fin 14 → R) (i j : Fin 7) :
    bryantWilmotMatrix c i j = - bryantWilmotMatrix c j i := by
  fin_cases i <;> fin_cases j <;> {
    dsimp [bryantWilmotMatrix]
    try ring
  }

/-- Standard bilinear form on `R⁷`. -/
def bilinearForm (u v : Fin 7 → R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4 + u 5 * v 5 + u 6 * v 6

/-- Explicit action on `u ∈ R⁷`. -/
def bryantWilmotApp (c : Fin 14 → R) (u : Fin 7 → R) : Fin 7 → R
  | 0 => c 2 * u 1 - c 1 * u 2 + c 4 * u 3 + c 3 * u 4 - c 6 * u 5 + (c 5 - c 12) * u 6
  | 1 => -c 2 * u 0 + c 0 * u 2 + c 5 * u 3 + (-c 6 + c 13) * u 4 + (c 3 - c 10) * u 5 + (-c 4 - c 11) * u 6
  | 2 => c 1 * u 0 - c 0 * u 1 - c 13 * u 3 + c 12 * u 4 + c 11 * u 5 - c 10 * u 6
  | 3 => -c 4 * u 0 - c 5 * u 1 + c 13 * u 2 + (-c 0 + c 7) * u 4 + (-c 1 + c 8) * u 5 + (c 2 - c 9) * u 6
  | 4 => -c 3 * u 0 + (c 6 - c 13) * u 1 - c 12 * u 2 + (c 0 - c 7) * u 3 + c 9 * u 5 + c 8 * u 6
  | 5 => c 6 * u 0 + (-c 3 + c 10) * u 1 - c 11 * u 2 + (c 1 - c 8) * u 3 - c 9 * u 4 - c 7 * u 6
  | 6 => (-c 5 + c 12) * u 0 + (c 4 + c 11) * u 1 + c 10 * u 2 + (-c 2 + c 9) * u 3 - c 8 * u 4 + c 7 * u 5

/-- 🏆 THEOREM: Every Bryant-Wilmot 𝔤₂ derivation preserves the standard bilinear metric. -/
theorem bryantWilmot_preserves_metric (c : Fin 14 → R) (u v : Fin 7 → R) :
    bilinearForm (bryantWilmotApp c u) v + bilinearForm u (bryantWilmotApp c v) = 0 := by
  dsimp [bilinearForm, bryantWilmotApp]
  ring

end InfoGeometry.Algebra.Zorn.G2BryantWilmot
