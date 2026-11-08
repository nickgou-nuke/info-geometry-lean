import InfoGeometry.Canonical.RelativeModularBerezinianBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BerezinianTrace

/-!
# Common and relative Weyl modes in the diagonal Berezinian model

The relative-modular owner supplies the sheet-level Berezinian shadow.  This
file records the elementary two-sheet scalar consequence: equal Weyl scaling
on both sheets is invisible to the Berezinian, while the difference of the
sheet scales remains visible.
-/

namespace InfoGeometry.Quantum.ChiralRelativeModularBerezinianBridge

noncomputable section

open InfoGeometry.Canonical.BerezinianTrace

def commonScale (kPlus kMinus : ℝ) : ℝ := (kPlus + kMinus) / 2

def relativeScale (kPlus kMinus : ℝ) : ℝ := (kPlus - kMinus) / 2

theorem commonScale_add_relativeScale (kPlus kMinus : ℝ) :
    commonScale kPlus kMinus + relativeScale kPlus kMinus = kPlus := by
  dsimp [commonScale, relativeScale]
  ring

theorem commonScale_sub_relativeScale (kPlus kMinus : ℝ) :
    commonScale kPlus kMinus - relativeScale kPlus kMinus = kMinus := by
  dsimp [commonScale, relativeScale]
  ring

theorem common_weyl_berezinian_neutral (κ : ℝ) :
    berezinian (Real.exp κ * Real.exp κ) (Real.exp κ * Real.exp κ)
      (mul_ne_zero (Real.exp_ne_zero κ) (Real.exp_ne_zero κ)) = 1 := by
  apply ber_eq_one

theorem relative_weyl_berezinian (kPlus kMinus : ℝ) :
    berezinian (Real.exp kPlus * Real.exp kPlus)
      (Real.exp kMinus * Real.exp kMinus)
      (mul_ne_zero (Real.exp_ne_zero kMinus) (Real.exp_ne_zero kMinus)) =
      Real.exp (2 * (kPlus - kMinus)) := by
  rw [ber_exp_eq_exp_str]
  congr 1
  dsimp [supertrace]
  ring

theorem common_relative_reconstruction (kPlus kMinus : ℝ) :
    (commonScale kPlus kMinus + relativeScale kPlus kMinus,
      commonScale kPlus kMinus - relativeScale kPlus kMinus) = (kPlus, kMinus) := by
  simp [commonScale_add_relativeScale, commonScale_sub_relativeScale]

end
end InfoGeometry.Quantum.ChiralRelativeModularBerezinianBridge
