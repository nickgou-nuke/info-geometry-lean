import InfoGeometry.Quantum.MajoranaPfaffianBridge
import Mathlib.Tactic

/-!
# Finite Majorana pairing blocks

This is the next finite layer above the local `2 × 2` Pfaffian owner.  It
packages a finite family of canonical skew pairing blocks and their product
invariant.  It does not claim a general matrix Pfaffian expansion or a
perfect-matching theorem.
-/

namespace InfoGeometry.Quantum.FiniteMajoranaPairingBlocks

open InfoGeometry.Quantum.MajoranaPfaffianBridge

/-- The canonical skew block for one Majorana pair with coupling `a`. -/
def pairingBlock (a : ℝ) : M2R :=
  !![0, a; -a, 0]

theorem pairingBlock_isSkew (a : ℝ) :
    IsSkew (pairingBlock a) := by
  unfold IsSkew pairingBlock
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem pairingBlock_det (a : ℝ) :
    (pairingBlock a).det = a ^ 2 := by
  rw [det_eq_pfaffian2_sq (pairingBlock_isSkew a)]
  rfl

/-- Product Pfaffian invariant of a finite family of Majorana pair blocks. -/
def finitePairingPfaffian {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  ∏ k, a k

/-- Product of the determinants of the canonical pair blocks. -/
def finitePairingDeterminant {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  ∏ k, (pairingBlock (a k)).det

theorem finitePairingDeterminant_eq_square {N : ℕ} (a : Fin N → ℝ) :
    finitePairingDeterminant a = (finitePairingPfaffian a) ^ 2 := by
  unfold finitePairingDeterminant finitePairingPfaffian
  simp_rw [pairingBlock_det]
  rw [← Finset.prod_pow]

end InfoGeometry.Quantum.FiniteMajoranaPairingBlocks
