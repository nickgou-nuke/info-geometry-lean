import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.OperatorAlgebra.IwasawaKANLocalAlgebra

abbrev AlgMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-! A deliberately local algebraic owner.  No Iwasawa, Laplace, or physical
interpretation is asserted here: the theorem below is only the consequence of
the two square laws and anticommutation. -/
structure CliffordPair (n : ℕ) where
  B : AlgMat n
  K : AlgMat n
  B_sq : B * B = -1
  K_sq : K * K = 1
  anticomm : B * K = -(K * B)

def nilpotentCombination (p : CliffordPair n) : AlgMat n := p.B + p.K

theorem nilpotentCombination_sq (p : CliffordPair n) :
    nilpotentCombination p * nilpotentCombination p = 0 := by
  dsimp [nilpotentCombination]
  calc
    (p.B + p.K) * (p.B + p.K) =
        p.B * p.B + p.B * p.K + p.K * p.B + p.K * p.K := by
      noncomm_ring
    _ = -1 + p.B * p.K + p.K * p.B + 1 := by
      rw [p.B_sq, p.K_sq]
    _ = 0 := by
      rw [p.anticomm]
      abel

end InfoGeometry.OperatorAlgebra.IwasawaKANLocalAlgebra
