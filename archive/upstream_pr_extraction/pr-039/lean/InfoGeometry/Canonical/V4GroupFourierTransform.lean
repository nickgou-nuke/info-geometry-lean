import Mathlib.Tactic
import InfoGeometry.Topology.V4RootSystem

/-!
# Finite Fourier transform on the native Klein four group

The four coefficients are indexed by the repository's actual `V4Group`, and
the four sign functions are its four real one-dimensional characters.  This
owner proves the finite character law and the corresponding Walsh inversion.
It does not assign thermodynamic or geometric meanings to the coefficients.
-/

noncomputable section

namespace InfoGeometry.Canonical.V4GroupFourierTransform

open scoped BigOperators
open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Topology.V4RootSystem.V4Group

instance : Fintype V4Group where
  elems := {I, W1, W2, W12}
  complete := by
    intro g
    cases g <;> simp

/-- The four real sign characters of the native Klein four group. -/
def v4Character : Fin 4 → V4Group → ℝ
  | 0, _ => 1
  | 1, I => 1
  | 1, W1 => 1
  | 1, W2 => -1
  | 1, W12 => -1
  | 2, I => 1
  | 2, W1 => -1
  | 2, W2 => 1
  | 2, W12 => -1
  | 3, I => 1
  | 3, W1 => -1
  | 3, W2 => -1
  | 3, W12 => 1

@[simp] theorem v4Character_one (k : Fin 4) :
    v4Character k 1 = 1 := by
  fin_cases k <;> rfl

theorem v4Character_mul (k : Fin 4) (g h : V4Group) :
    v4Character k (g * h) = v4Character k g * v4Character k h := by
  change v4Character k (v4_mul g h) = v4Character k g * v4Character k h
  fin_cases k <;> cases g <;> cases h <;>
    norm_num [v4Character, v4_mul]

def v4EquivFin : Fin 4 ≃ V4Group where
  toFun
    | 0 => I
    | 1 => W1
    | 2 => W2
    | 3 => W12
  invFun
    | I => 0
    | W1 => 1
    | W2 => 2
    | W12 => 3
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro g
    cases g <;> rfl

/-! ## Character orthogonality -/

theorem v4Character_pairwise_orthogonality (k l : Fin 4) :
    (∑ g : V4Group, v4Character k g * v4Character l g) =
      if k = l then 4 else 0 := by
  classical
  rw [← Equiv.sum_comp v4EquivFin
    (fun g => v4Character k g * v4Character l g)]
  fin_cases k <;> fin_cases l <;>
    simp [v4EquivFin, v4Character, Fin.sum_univ_succ] <;> norm_num

/-- Fourier evaluation of a coefficient function on the native `V₄`. -/
def v4Fourier (k : Fin 4) (z : V4Group → ℝ) : ℝ :=
  ∑ g : V4Group, v4Character k g * z g

theorem v4Fourier_expansion (k : Fin 4) (z : V4Group → ℝ) :
    v4Fourier k z =
      v4Character k I * z I +
        v4Character k W1 * z W1 +
        v4Character k W2 * z W2 +
        v4Character k W12 * z W12 := by
  classical
  unfold v4Fourier
  rw [← Equiv.sum_comp v4EquivFin (fun g => v4Character k g * z g)]
  fin_cases k <;>
    simp [v4EquivFin, v4Character, Fin.sum_univ_succ] <;> ring

theorem v4Fourier_inversion (z : V4Group → ℝ) (g : V4Group) :
    (1 / 4 : ℝ) *
        ∑ k : Fin 4, v4Character k g * v4Fourier k z = z g := by
  classical
  cases g <;>
    simp [v4Fourier_expansion, v4Character, Fin.sum_univ_succ] <;>
    ring

theorem v4Fourier_inversion_function (z : V4Group → ℝ) :
    (fun g => (1 / 4 : ℝ) *
        ∑ k : Fin 4, v4Character k g * v4Fourier k z) = z := by
  funext g
  exact v4Fourier_inversion z g

end InfoGeometry.Canonical.V4GroupFourierTransform
