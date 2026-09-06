import Mathlib.LinearAlgebra.ExteriorPower.Basis
import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

/-!
# Finite dimensions of the exterior degrees

The Fock carrier is graded by exterior powers.  This owner records the native
Mathlib dimension theorem for each degree; it does not replace the exterior
algebra by a hand-enumerated `Fin 32` carrier.
-/

namespace InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

theorem exteriorPower_finrank (k : ℕ) :
    Module.finrank ℝ (⋀[ℝ]^k V5) = Nat.choose 5 k := by
  rw [exteriorPower.finrank_eq]
  simp [V5]

theorem exteriorPower_eq_bot_of_five_lt {k : ℕ} (hk : 5 < k) :
    (⋀[ℝ]^k V5) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hfin : Module.finrank ℝ (⋀[ℝ]^k V5) = 0 := by
    rw [exteriorPower_finrank]
    exact Nat.choose_eq_zero_of_lt hk
  have hx0 : (⟨x, hx⟩ : (⋀[ℝ]^k V5)) = 0 :=
    (finrank_zero_iff_forall_zero.mp hfin) ⟨x, hx⟩
  exact congrArg Subtype.val hx0

theorem exteriorPower_subsingleton_of_five_lt {k : ℕ} (hk : 5 < k) :
    Subsingleton (⋀[ℝ]^k V5) := by
  rw [exteriorPower_eq_bot_of_five_lt hk]
  infer_instance

end InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
