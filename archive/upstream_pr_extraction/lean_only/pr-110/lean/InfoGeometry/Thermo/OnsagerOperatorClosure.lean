import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Thermo.OnsagerClosure

variable {V: Type*} [AddCommGroup V] [Module ℝ V]

/-- The total Onsager-Casimir non-equilibrium generator W = L + Ω. -/
structure OnsagerCasimirSystem (V: Type*) [AddCommGroup V] [Module ℝ V] where
  dissipative : LinearMap.BilinForm ℝ V
  reversible : LinearMap.BilinForm ℝ V
  dissipative_symm : ∀ x y, dissipative x y = dissipative y x
  reversible_skew : ∀ x y, reversible x y = - reversible y x
  dissipative_nonneg : ∀ x, 0 ≤ dissipative x x

namespace OnsagerCasimirSystem

variable (S: OnsagerCasimirSystem V)

/-- The total generator W = L + Ω. -/
def totalGenerator : LinearMap.BilinForm ℝ V :=
  S.dissipative + S.reversible

/-- THEOREM 1 (Pure Dissipation): The reversible skew bracket contributes zero dissipation. -/
@[simp]
theorem reversible_diag_zero (x: V) : S.reversible x x = 0 := by -- uses x
  have h := S.reversible_skew x x
  linarith

/-- THEOREM 2 (Entropy Production Identity): Total entropy production W(x, x) = L(x, x) ≥ 0. -/
theorem entropy_production_eq (x: V) :
    S.totalGenerator x x = S.dissipative x x := by -- uses x
  dsimp [totalGenerator]
  rw [S.reversible_diag_zero x, add_zero]

/-- THEOREM 3 (Second Law of Thermodynamics): Entropy production is unconditionally non-negative. -/
theorem entropy_production_nonneg (x: V) :
    0 ≤ S.totalGenerator x x := by -- uses x
  rw [S.entropy_production_eq x]
  exact S.dissipative_nonneg x

/-- THEOREM 4 (Onsager Reciprocity Decomposition):
    The symmetric part of W is L, and the skew part is Ω. -/
theorem totalGenerator_symm_part (x y: V) :
    (1 / 2 : ℝ) * (S.totalGenerator x y + S.totalGenerator y x) = S.dissipative x y := by -- uses x y
  dsimp [totalGenerator]
  have hL := S.dissipative_symm x y
  have hΩ := S.reversible_skew y x
  calc
    (1 / 2 : ℝ) * (S.dissipative x y + S.reversible x y + (S.dissipative y x + S.reversible y x))
      = (1 / 2 : ℝ) * (S.dissipative x y + S.dissipative y x + (S.reversible x y + S.reversible y x)) := by ring
    _ = (1 / 2 : ℝ) * (S.dissipative x y + S.dissipative x y + (S.reversible x y + - S.reversible x y)) := by rw [← hL, ← hΩ]
    _ = (1 / 2 : ℝ) * (2 * S.dissipative x y + 0) := by ring
    _ = S.dissipative x y := by ring

theorem totalGenerator_skew_part (x y: V) :
    (1 / 2 : ℝ) * (S.totalGenerator x y - S.totalGenerator y x) = S.reversible x y := by -- uses x y
  dsimp [totalGenerator]
  have hL := S.dissipative_symm y x
  have hΩ := S.reversible_skew y x
  calc
    (1 / 2 : ℝ) * (S.dissipative x y + S.reversible x y - (S.dissipative y x + S.reversible y x))
      = (1 / 2 : ℝ) * (S.dissipative x y - S.dissipative y x + (S.reversible x y - S.reversible y x)) := by ring
    _ = (1 / 2 : ℝ) * (S.dissipative x y - S.dissipative x y + (S.reversible x y - - S.reversible x y)) := by rw [hL, ← hΩ]
    _ = (1 / 2 : ℝ) * (0 + 2 * S.reversible x y) := by ring
    _ = S.reversible x y := by ring

/-!
=============================================================================
PART 2: Time-Reversal Involution and the Onsager–Casimir Reciprocal Relations
=============================================================================
-/

structure TimeReversal (V: Type*) [AddCommGroup V] [Module ℝ V] where
  op : V →ₗ[ℝ] V
  involutive : ∀ x, op (op x) = x

/-- A system with time-reversal parity structure. -/
structure ParityOnsagerSystem (V: Type*) [AddCommGroup V] [Module ℝ V] extends OnsagerCasimirSystem V where
  T : TimeReversal V
  dissipative_T_even : ∀ x y, dissipative (T.op x) (T.op y) = dissipative x y
  reversible_T_odd : ∀ x y, reversible (T.op x) (T.op y) = - reversible x y

namespace ParityOnsagerSystem

variable (PS: ParityOnsagerSystem V)

/-- 
  THEOREM 5 (The Master Onsager–Casimir Reciprocity Law):
  Under time reversal T, the total generator satisfies:
    W(T x, T y) = W(y, x)
  (i.e., transposition is equivalent to time-reversal reflection).
-/
theorem onsager_casimir_master_reciprocity (x y: V) :
    PS.totalGenerator (PS.T.op x) (PS.T.op y) = PS.totalGenerator y x := by -- uses x y
  dsimp [totalGenerator]
  rw [PS.dissipative_T_even, PS.reversible_T_odd]
  have hL := PS.dissipative_symm x y
  have hΩ := PS.reversible_skew x y
  rw [hL, hΩ, neg_neg]

/-- THEOREM 6: Entropy production is invariant under time reversal. -/
theorem entropy_production_T_invariant (x: V) :
    PS.totalGenerator (PS.T.op x) (PS.T.op x) = PS.totalGenerator x x := by -- uses x
  rw [PS.entropy_production_eq, PS.entropy_production_eq]
  exact PS.dissipative_T_even x x

end ParityOnsagerSystem

end OnsagerCasimirSystem

end InfoGeometry.Thermo.OnsagerClosure

end noncomputable section
