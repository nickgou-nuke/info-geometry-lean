import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace DiscreteGaussBonnetKleinBridge

/-- Hexagonal Lattice with 5-6-7 Polygonal Defects. -/
structure HexagonalLatticeWithDefects where
  N5 : ℕ
  N6 : ℕ
  N7 : ℕ

namespace HexagonalLatticeWithDefects

/-- Total Discrete Gauss-Bonnet Curvature: Σ (6 - n) N_n. -/
def totalDiscreteCurvature (L : HexagonalLatticeWithDefects) : ℤ :=
  (1 : ℤ) * (L.N5 : ℤ) + (0 : ℤ) * (L.N6 : ℤ) + (-1 : ℤ) * (L.N7 : ℤ)

/-- Euler Characteristic of the Klein Bottle χ(K²) = 0. -/
def eulerCharacteristicKleinBottle : ℤ := 0

@[simp] theorem totalDiscreteCurvature_eq_sub (L : HexagonalLatticeWithDefects) :
    totalDiscreteCurvature L = (L.N5 : ℤ) - (L.N7 : ℤ) := by
  dsimp [totalDiscreteCurvature]
  ring

/-! Finite Gauss--Bonnet readout for the Klein carrier. -/
theorem gauss_bonnet_constraint_iff_defect_balance
    (L : HexagonalLatticeWithDefects) :
    totalDiscreteCurvature L = 6 * eulerCharacteristicKleinBottle ↔
      L.N5 = L.N7 := by
  rw [totalDiscreteCurvature_eq_sub, eulerCharacteristicKleinBottle]
  constructor
  · intro h
    exact Int.ofNat_inj.mp (sub_eq_zero.mp (by simpa using h))
  · intro h
    simp [h]

/-! The finite curvature readout is unchanged by a map preserving the two
defect sectors.  This is the invariant form needed for later colimit
transport. -/
theorem totalDiscreteCurvature_invariant_of_defect_preserving
    (L L' : HexagonalLatticeWithDefects)
    (h5 : L.N5 = L'.N5)
    (h7 : L.N7 = L'.N7) :
    totalDiscreteCurvature L = totalDiscreteCurvature L' := by
  simp [totalDiscreteCurvature, h5, h7]

/-- **Theorem**: 5-7 Dipole Pairing Law on the Klein Bottle:
    Gauss-Bonnet curvature constraint N₅ - N₇ = 6 χ(K²) = 0 forces N₅ = N₇. -/
theorem klein_bottle_forces_5_7_dipole_pairing
    (L : HexagonalLatticeWithDefects)
    (h_gauss_bonnet : totalDiscreteCurvature L = 6 * eulerCharacteristicKleinBottle) :
    L.N5 = L.N7 := by
  dsimp [totalDiscreteCurvature, eulerCharacteristicKleinBottle] at h_gauss_bonnet
  have h_sub : (L.N5 : ℤ) - (L.N7 : ℤ) = 0 := by
    calc (L.N5 : ℤ) - (L.N7 : ℤ)
      _ = (1 : ℤ) * (L.N5 : ℤ) + (0 : ℤ) * (L.N6 : ℤ) + (-1 : ℤ) * (L.N7 : ℤ) := by ring
      _ = 6 * 0 := h_gauss_bonnet
      _ = 0 := by ring
  exact Int.ofNat_inj.mp (sub_eq_zero.mp h_sub)

end HexagonalLatticeWithDefects

end DiscreteGaussBonnetKleinBridge
