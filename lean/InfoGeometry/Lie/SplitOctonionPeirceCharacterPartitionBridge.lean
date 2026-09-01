import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge

/-!
# Finite Peirce character and degree-parity readouts

This owner packages the finite `1 + 3 + 3 + 1` coordinate carrier as a
character calculation. `peirceGrading` is the existing sheet involution;
`exteriorDegreeParity` is a separate diagonal operator with signs determined
by the literal exterior degrees `0, 1, 1, 1, 3, 2, 2, 2` in the established
Peirce ordering.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionPeirceCharacterPartitionBridge

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge

abbrev Carrier := PeirceCarrier
abbrev CarrierEnd := Module.End ℝ Carrier

/-- Exterior-degree parity `(-1)^k` in the established Peirce coordinate order
`0,1,1,1,3,2,2,2`.  Thus the signs are `+,-,-,-,-,+,+,+`. -/
def exteriorDegreeParity : CarrierEnd where
  toFun x i :=
    if i.val = 0 then x i
    else if i.val ≤ 4 then -x i
    else x i
  map_add' x y := by
    ext i
    dsimp
    split_ifs <;> ring
  map_smul' c x := by
    ext i
    dsimp
    split_ifs <;> ring

def peirceSheetParity : CarrierEnd := peirceGrading

def peirceCharacterProduct : CarrierEnd :=
  peirceSheetParity * exteriorDegreeParity

theorem exteriorDegreeParity_sq :
    exteriorDegreeParity * exteriorDegreeParity = (1 : CarrierEnd) := by
  apply LinearMap.ext
  intro x
  ext i
  dsimp [exteriorDegreeParity, Module.End.mul_apply]
  split_ifs <;> ring

def peirceDegreeGeneratingPolynomial (q : ℝ) : ℝ :=
  1 + 3 * q + 3 * q ^ 2 + q ^ 3

def peirceSignedGeneratingPolynomial (q : ℝ) : ℝ :=
  1 + 3 * q - 3 * q ^ 2 - q ^ 3

def peirceProductGeneratingPolynomial (q : ℝ) : ℝ :=
  (1 - q) ^ 3

def peirceOppositeGeneratingPolynomial (q : ℝ) : ℝ :=
  1 - 3 * q - 3 * q ^ 2 + q ^ 3

theorem peirceDegreeGeneratingPolynomial_eq_binomial (q : ℝ) :
    peirceDegreeGeneratingPolynomial q = (1 + q) ^ 3 := by
  dsimp [peirceDegreeGeneratingPolynomial]
  ring

theorem peirceProductGeneratingPolynomial_eq_binomial (q : ℝ) :
    peirceProductGeneratingPolynomial q = (1 - q) ^ 3 := rfl

def peirceCarrierDim : ℝ := 8

/-! The following is the trace in the displayed coordinate basis.  We keep the
coordinate definition explicit: the carrier is `Fin 8 → ℝ`, so this is the
sum of the eight diagonal matrix coefficients, not a supplied trace value. -/
def coordinateBasisVector (i : Fin 8) : Carrier :=
  fun j => if j = i then 1 else 0

def peirceCoordinateTrace (T : CarrierEnd) : ℝ :=
  ∑ i : Fin 8, (T (coordinateBasisVector i)) i

def peirceSheetParityTrace : ℝ := peirceCoordinateTrace peirceSheetParity
def exteriorDegreeParityTrace : ℝ := peirceCoordinateTrace exteriorDegreeParity
def peirceCharacterProductTrace : ℝ := peirceCoordinateTrace peirceCharacterProduct

theorem peirceSheetParityTrace_eq :
    peirceSheetParityTrace = 0 := by
  classical
  have hdiag : ∀ i : Fin 8,
      (peirceSheetParity (coordinateBasisVector i)) i =
        if i.val < 4 then 1 else -1 := by
    intro i
    fin_cases i <;> simp [coordinateBasisVector, peirceSheetParity,
      peirceGrading]
  simp only [peirceSheetParityTrace, peirceCoordinateTrace, hdiag]
  norm_num [Fin.sum_univ_succ]

theorem exteriorDegreeParityTrace_eq :
    exteriorDegreeParityTrace = 0 := by
  classical
  have hdiag : ∀ i : Fin 8,
      (exteriorDegreeParity (coordinateBasisVector i)) i =
        if i.val = 0 then 1 else if i.val ≤ 4 then -1 else 1 := by
    intro i
    fin_cases i <;> simp [coordinateBasisVector, exteriorDegreeParity]
  simp only [exteriorDegreeParityTrace, peirceCoordinateTrace, hdiag]
  norm_num [Fin.sum_univ_succ]

theorem peirceCharacterProductTrace_eq :
    peirceCharacterProductTrace = -4 := by
  classical
  have hdiag : ∀ i : Fin 8,
      (peirceCharacterProduct (coordinateBasisVector i)) i =
        if i.val = 0 then 1 else if i.val < 4 then -1
          else if i.val = 4 then 1 else -1 := by
    intro i
    fin_cases i <;> simp [coordinateBasisVector, peirceCharacterProduct,
      peirceSheetParity, peirceGrading, exteriorDegreeParity,
      Module.End.mul_apply]
  simp only [peirceCharacterProductTrace, peirceCoordinateTrace, hdiag]
  norm_num [Fin.sum_univ_succ]

theorem peirceCharacterTrace_packet :
    (peirceCarrierDim,
      peirceSheetParityTrace,
      exteriorDegreeParityTrace,
      peirceCharacterProductTrace) =
      (8, 0, 0, -4) := by
  rw [peirceSheetParityTrace_eq, exteriorDegreeParityTrace_eq,
    peirceCharacterProductTrace_eq]
  rfl

end InfoGeometry.Lie.SplitOctonionPeirceCharacterPartitionBridge
