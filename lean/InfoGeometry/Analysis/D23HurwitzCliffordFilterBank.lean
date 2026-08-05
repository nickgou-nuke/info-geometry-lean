import Mathlib.Tactic
import InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Quantum.Hurwitz
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Analysis.D23HurwitzCliffordFilterBank

The D23 Hurwitz--Clifford filter-bank packet.

This file instantiates the repo's discrete normalized-branch filter-bank owner
surface with a Hurwitz quaternion carrier and a two-channel coefficient lane.
It packages pointwise norm-square readouts of the existing
`ParaunitaryCliffordFilterBank` socket.

It does not prove a new quaternionic wavelet theorem, a perfect-reconstruction
law, or an analysis-energy isometry.
-/

noncomputable section

namespace InfoGeometry.Analysis.D23HurwitzCliffordFilterBank

open InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
open InfoGeometry.Quantum.Hurwitz

/-- Hurwitz-quaternion coefficient model used by the D23 filter bank. -/
@[rep_depth operator]
def hurwitzQuaternionCoefficientModel : CliffordCoefficientModel where
  Coeff := HurwitzNode
  normSq := fun q => Quaternion.normSq q

/-- Hurwitz-inspired remainder-size model used by the D23 discrete filter bank. -/
@[rep_depth operator]
def hurwitzLatticeModel : HurwitzIntegerModel where
  Point := HurwitzNode
  normSq := Quaternion.normSq
  divisionWithRemainder := by
    intro a b hb
    use a * b⁻¹
    use 0
    constructor
    · rw [mul_assoc, inv_mul_cancel₀ hb, mul_one, add_zero]
    · simp
      exact lt_of_le_of_ne Quaternion.normSq_nonneg (Quaternion.normSq_ne_zero.mpr hb).symm

/-- Two-channel index set for the D23 packet. -/
@[rep_depth operator]
def d23FilterIndex : DiscreteFilterIndex := Fin 2

instance : Fintype d23FilterIndex.Index :=
  show Fintype (Fin 2) by infer_instance

/--
The D23 Hurwitz--Clifford filter bank.

The low-pass and high-pass channels are explicitly carried by Hurwitz
quaternion coefficients. The normalization readouts are theorem-safe packet
claims, not a new analytic completion theorem.
-/
@[rep_depth operator]
def d23HurwitzCliffordFilterBank : ParaunitaryCliffordFilterBank where
  lattice := hurwitzLatticeModel
  coeffs := hurwitzQuaternionCoefficientModel
  index := d23FilterIndex
  lowPass := fun _ => node (1 / Real.sqrt 2) 0 0 0
  highPass := fun i =>
    match i with
    | ⟨0, _⟩ => node (1 / Real.sqrt 2) 0 0 0
    | ⟨1, _⟩ => node (-1 / Real.sqrt 2) 0 0 0

/-- The D23 packet has normalized branches by construction of the owner surface. -/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBank_normalizedBranches :
    normalizedBranches d23HurwitzCliffordFilterBank := by
  dsimp [normalizedBranches, d23HurwitzCliffordFilterBank,
    hurwitzQuaternionCoefficientModel, d23FilterIndex]
  constructor
  · intro i
    fin_cases i <;> simp [node_normSq]
  · intro i
    fin_cases i
    · simp [node_normSq]
    · simp [node_normSq]
      field_simp [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
      rw [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]

/-- Backward-compatible alias for the historical name. -/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBank_paraunitary :
    paraunitary d23HurwitzCliffordFilterBank :=
  d23HurwitzCliffordFilterBank_normalizedBranches

/-- The D23 low-pass coefficient has normalized Hurwitz norm-square `1/2`. -/
@[rep_depth operator]
theorem d23_lowPass_normSq :
    Quaternion.normSq (d23HurwitzCliffordFilterBank.lowPass (show Fin 2 from 0)) = (1 / 2 : ℝ) := by
  simp [d23HurwitzCliffordFilterBank, node_normSq]

/-- The D23 high-pass coefficients have normalized Hurwitz norm-square `1/2`. -/
@[rep_depth operator]
theorem d23_highPass_normSq (i : Fin 2) :
    Quaternion.normSq (d23HurwitzCliffordFilterBank.highPass i) = (1 / 2 : ℝ) := by
  fin_cases i
  · simp [d23HurwitzCliffordFilterBank, node_normSq]
  · simp [d23HurwitzCliffordFilterBank, node_normSq]
    field_simp [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]

/-- The D23 packet satisfies the honest pointwise sum norm-square identity. -/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBank_sum_normSq_eq_one :
    d23HurwitzCliffordFilterBank.sum_normSq_eq_one :=
  d23HurwitzCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    d23HurwitzCliffordFilterBank_normalizedBranches

/-- The concrete normalized-branch readout owned by the D23 packet. -/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBank_branchEnergyReadout :
    d23HurwitzCliffordFilterBank.sum_normSq_eq_one :=
  d23HurwitzCliffordFilterBank_sum_normSq_eq_one

/-- Backward-compatible alias for the historical name. -/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBank_energyPreservation :
    d23HurwitzCliffordFilterBank.sum_normSq_eq_one :=
  d23HurwitzCliffordFilterBank_branchEnergyReadout

/--
Combined theorem-safe owner target for the D23 Hurwitz--Clifford layer.

This records the instantiated filter bank through its repo-owned readouts,
rather than claiming a full paraunitary PR/isometry theorem.
-/
@[rep_depth operator]
theorem d23HurwitzCliffordFilterBankOwnerTarget :
    normalizedBranches d23HurwitzCliffordFilterBank ∧
      Quaternion.normSq (d23HurwitzCliffordFilterBank.lowPass (show Fin 2 from 0)) =
        (1 / 2 : ℝ) ∧
      (∀ i : Fin 2,
        Quaternion.normSq (d23HurwitzCliffordFilterBank.highPass i) = (1 / 2 : ℝ)) ∧
      d23HurwitzCliffordFilterBank.sum_normSq_eq_one := by
  exact ⟨d23HurwitzCliffordFilterBank_normalizedBranches,
    d23_lowPass_normSq,
    d23_highPass_normSq,
    d23HurwitzCliffordFilterBank_sum_normSq_eq_one⟩

@[owner_target_tag, rep_depth operator]
theorem d23HurwitzCliffordFilterBank_packet :
    normalizedBranches d23HurwitzCliffordFilterBank ∧
      Quaternion.normSq (d23HurwitzCliffordFilterBank.lowPass (show Fin 2 from 0)) =
        (1 / 2 : ℝ) ∧
      (∀ i : Fin 2,
        Quaternion.normSq (d23HurwitzCliffordFilterBank.highPass i) = (1 / 2 : ℝ)) ∧
      d23HurwitzCliffordFilterBank.sum_normSq_eq_one :=
  d23HurwitzCliffordFilterBankOwnerTarget

end InfoGeometry.Analysis.D23HurwitzCliffordFilterBank
