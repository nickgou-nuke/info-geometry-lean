import Mathlib
import InfoGeometry.Canonical.FiniteHeisenbergCore
import InfoGeometry.Quantum.PauliSoldering

open InfoGeometry.Canonical.FiniteHeisenbergCore
open InfoGeometry.Quantum.PauliSoldering
open Matrix

namespace InfoGeometry.Sandbox.UncertaintyAnomalySwarm

/-- 
We embed the finite Heisenberg group generators into 4-momentum space 
so they can be soldered into Pauli matrices.
The Heisenberg coordinates (x, y) map to σ1, σ2.
The central cocycle z maps to σ3.
-/
def heisenbergVector {n : ℕ} (h : Heisenberg n) : ℂ × ℂ × ℂ × ℂ :=
  (0, (h.1.1.val : ℂ), (h.1.2.val : ℂ), (h.2.val : ℂ))

/-- 
The Maurer-Cartan 3-form on the Lie algebra / soldered operators.
ω(X, Y, Z) = Tr(X [Y, Z]).
-/
noncomputable def maurerCartan3Form (P1 P2 P3 : ℂ × ℂ × ℂ × ℂ) : ℂ :=
  Matrix.trace (solder P1 * (solder P2 * solder P3 - solder P3 * solder P2))

lemma maurerCartan3Form_center_explicit (u1 u2 u3 v1 v2 v3 w3 : ℂ) :
  maurerCartan3Form (0, 0, 0, w3) (0, u1, u2, u3) (0, v1, v2, v3) =
  4 * Complex.I * w3 * (u1 * v2 - u2 * v1) := by
  dsimp [maurerCartan3Form]
  rw [solder_explicit, solder_explicit, solder_explicit]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  ring

lemma zmod_val_cross_ne_zero {n : ℕ} [Fact (2 ≤ n)] (u1 u2 v1 v2 : ZMod n)
    (h : u1 * v2 - v1 * u2 ≠ 0) :
    (u1.val : ℂ) * (v2.val : ℂ) - (u2.val : ℂ) * (v1.val : ℂ) ≠ 0 := by
  intro h0
  have h1 : (u1.val : ℤ) * (v2.val : ℤ) - (u2.val : ℤ) * (v1.val : ℤ) = 0 := by exact_mod_cast h0
  have h2 : ((u1.val : ℤ) * (v2.val : ℤ) - (u2.val : ℤ) * (v1.val : ℤ) : ZMod n) = 0 := by rw [h1, Int.cast_zero]
  have hn : NeZero n := ⟨by
    have h2n : 2 ≤ n := Fact.out
    omega⟩
  have h3 : u1 * v2 - u2 * v1 = 0 := by
    calc u1 * v2 - u2 * v1
      _ = (u1.val : ZMod n) * (v2.val : ZMod n) - (u2.val : ZMod n) * (v1.val : ZMod n) := by
        congr 1
        · congr 1 <;> exact (ZMod.natCast_zmod_val _).symm
        · congr 1 <;> exact (ZMod.natCast_zmod_val _).symm
      _ = ((u1.val : ℤ) : ZMod n) * ((v2.val : ℤ) : ZMod n) - ((u2.val : ℤ) : ZMod n) * ((v1.val : ℤ) : ZMod n) := by push_cast; rfl
      _ = 0 := h2
  have h4 : u1 * v2 - v1 * u2 = 0 := by
    calc u1 * v2 - v1 * u2
      _ = u1 * v2 - u2 * v1 := by ring
      _ = 0 := h3
  exact h h4

/-- 
The Uncertainty Principle (non-zero commutator of Heisenberg generators) 
forces the Chiral Anomaly (Maurer-Cartan 3-form) to be non-zero. 
-/
theorem heisenberg_anomaly_nonzero {n : ℕ} [Fact (2 ≤ n)] 
    (u v : Heisenberg n)
    (h_uncert : heisenberg_cocycle_defect u v ≠ 0) :
    ∃ (w : Heisenberg n), maurerCartan3Form (heisenbergVector w) (heisenbergVector u) (heisenbergVector v) ≠ 0 := by
  use heisenbergCenterElement 1
  have hC : ((1 : ZMod n).val : ℂ) ≠ 0 := by
    have hn : NeZero n := ⟨by
      have h2n : 2 ≤ n := Fact.out
      omega⟩
    have h_one : (1 : ZMod n).val = 1 := ZMod.val_one n
    rw [h_one]
    exact one_ne_zero
  dsimp [heisenbergCenterElement, heisenbergVector]
  rw [maurerCartan3Form_center_explicit]
  intro h_zero
  simp only [mul_eq_zero] at h_zero
  rcases h_zero with h4 | h_zero
  · rcases h4 with h4 | h4
    · rcases h4 with h4 | h4
      · norm_num at h4
      · exact Complex.I_ne_zero h4
    · exact hC h4
  · exact zmod_val_cross_ne_zero u.1.1 u.1.2 v.1.1 v.1.2 h_uncert h_zero

end InfoGeometry.Sandbox.UncertaintyAnomalySwarm
