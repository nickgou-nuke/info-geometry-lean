/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.CircularChiralCausalConeBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

/-!
# The `ZMod 2` grading of the circular chiral basis

This owner records only the grading carried by the existing eight-element
chiral carrier.  It does not assert that the Zorn multiplication is closed on
the basis indices: mixed products generally produce idempotent components.
-/

namespace InfoGeometry.Algebra.CircularChiralGrading

open InfoGeometry.Algebra.CircularChiralCausalConeBasis
open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
open InfoGeometry.Algebra.ZornMatrix

abbrev Vec := InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace.Vec

noncomputable def chiralPairingBilin : LinearMap.BilinForm ℝ Vec :=
  { toFun := fun q =>
      { toFun := fun p => chiralPairing q p
        map_add' := by
          intro p r
          simp [chiralPairing, Vec3.dot]
          ring
        map_smul' := by
          intro c p
          simp [chiralPairing, Vec3.dot]
          ring }
    map_add' := by
      intro q r
      ext p
      simp [chiralPairing, Vec3.dot]
      ring
    map_smul' := by
      intro c q
      ext p
      simp [chiralPairing, Vec3.dot]
      ring }

@[simp] theorem chiralPairingBilin_apply (q p : Vec) :
    chiralPairingBilin q p = chiralPairing q p := rfl

theorem chiralPairingBilin_nondegenerate_left
    (q : Vec) (hq : ∀ p : Vec, chiralPairingBilin q p = 0) : q = 0 := by
  funext i
  fin_cases i
  · simpa [chiralPairingBilin, chiralPairing, Vec3.dot, Vec3.basis] using
      hq (Vec3.basis 0)
  · simpa [chiralPairingBilin, chiralPairing, Vec3.dot, Vec3.basis] using
      hq (Vec3.basis 1)
  · simpa [chiralPairingBilin, chiralPairing, Vec3.dot, Vec3.basis] using
      hq (Vec3.basis 2)

/-! ## Full-carrier Peirce projectors -/

def peircePlus (Z : ZornMatrix ℝ) : ZornMatrix ℝ :=
  (E11 : ZornMatrix ℝ) * Z * E22

def peirceMinus (Z : ZornMatrix ℝ) : ZornMatrix ℝ :=
  (E22 : ZornMatrix ℝ) * Z * E11

theorem peircePlus_coordinates (Z : ZornMatrix ℝ) :
    peircePlus Z =
      { a := 0, v := Z.v, w := 0, b := 0 } := by
  apply ZornMatrix.ext <;>
    simp [peircePlus, ZornMatrix.mul, E11, E22, Vec3.dot,
      Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem peirceMinus_coordinates (Z : ZornMatrix ℝ) :
    peirceMinus Z =
      { a := 0, v := 0, w := Z.w, b := 0 } := by
  apply ZornMatrix.ext <;>
    simp [peirceMinus, ZornMatrix.mul, E11, E22, Vec3.dot,
      Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

theorem peircePlus_idempotent (Z : ZornMatrix ℝ) :
    peircePlus (peircePlus Z) = peircePlus Z := by
  rw [peircePlus_coordinates, peircePlus_coordinates]

theorem peirceMinus_idempotent (Z : ZornMatrix ℝ) :
    peirceMinus (peirceMinus Z) = peirceMinus Z := by
  rw [peirceMinus_coordinates, peirceMinus_coordinates]

theorem peircePlus_after_peirceMinus (Z : ZornMatrix ℝ) :
    peircePlus (peirceMinus Z) = 0 := by
  rw [peirceMinus_coordinates, peircePlus_coordinates]
  simp [ZornMatrix.zero]

theorem peirceMinus_after_peircePlus (Z : ZornMatrix ℝ) :
    peirceMinus (peircePlus Z) = 0 := by
  rw [peircePlus_coordinates, peirceMinus_coordinates]
  simp [ZornMatrix.zero]


theorem peircePlus_upperZorn (q : Vec) :
    peircePlus (upperZorn q) = upperZorn q := by
  rw [peircePlus_coordinates]
  rfl

theorem peirceMinus_lowerZorn (p : Vec) :
    peirceMinus (lowerZorn p) = lowerZorn p := by
  rw [peirceMinus_coordinates]
  rfl

theorem peircePlus_lowerZorn (p : Vec) :
    peircePlus (lowerZorn p) = 0 := by
  rw [peircePlus_coordinates]
  simp [lowerZorn, ZornMatrix.zero]

theorem peirceMinus_upperZorn (q : Vec) :
    peirceMinus (upperZorn q) = 0 := by
  rw [peirceMinus_coordinates]
  simp [upperZorn, ZornMatrix.zero]

theorem peircePlus_add_peirceMinus_of_diagonal_zero
    (Z : ZornMatrix ℝ) (ha : Z.a = 0) (hb : Z.b = 0) :
    peircePlus Z + peirceMinus Z = Z := by
  rw [peircePlus_coordinates, peirceMinus_coordinates]
  apply ZornMatrix.ext <;>
    simp [ZornMatrix.add, ha, hb, Vec3.add]

theorem peircePlus_add_peirceMinus_upper_lower (q p : Vec) :
    peircePlus (upperZorn q + lowerZorn p) +
        peirceMinus (upperZorn q + lowerZorn p) =
      upperZorn q + lowerZorn p := by
  apply peircePlus_add_peirceMinus_of_diagonal_zero
  · change (0 : ℝ) + 0 = 0
    ring
  · change (0 : ℝ) + 0 = 0
    ring

theorem peirce_cross_sector_annihilation (q p : Vec) :
    peircePlus (lowerZorn p) = 0 ∧ peirceMinus (upperZorn q) = 0 := by
  exact ⟨peircePlus_lowerZorn p, peirceMinus_upperZorn q⟩

/-- The two idempotent basis vectors are even; the six vector directions are
odd. -/
def chiralParity : ChiralBasis → ZMod 2
  | .uPlus => 0
  | .uMinus => 0
  | .up _ => 1
  | .down _ => 1

@[simp] theorem chiralParity_uPlus :
    chiralParity ChiralBasis.uPlus = 0 := rfl

@[simp] theorem chiralParity_uMinus :
    chiralParity ChiralBasis.uMinus = 0 := rfl

@[simp] theorem chiralParity_up (i : Fin 3) :
    chiralParity (ChiralBasis.up i) = 1 := rfl

@[simp] theorem chiralParity_down (i : Fin 3) :
    chiralParity (ChiralBasis.down i) = 1 := rfl

theorem chiralParity_eq_zero_iff (b : ChiralBasis) :
    chiralParity b = 0 ↔
      b = ChiralBasis.uPlus ∨ b = ChiralBasis.uMinus := by
  cases b with
  | uPlus => simp
  | uMinus => simp
  | up i => simp
  | down i => simp

theorem chiralParity_eq_one_iff (b : ChiralBasis) :
    chiralParity b = 1 ↔
      (∃ i : Fin 3, b = ChiralBasis.up i) ∨
        (∃ i : Fin 3, b = ChiralBasis.down i) := by
  cases b with
  | uPlus => simp
  | uMinus => simp
  | up i => simp
  | down i => simp

theorem chiralParity_add_two (b : ChiralBasis) :
    chiralParity b + chiralParity b = 0 := by
  cases b with
  | uPlus => rfl
  | uMinus => rfl
  | up i => change (1 : ZMod 2) + 1 = 0; decide
  | down i => change (1 : ZMod 2) + 1 = 0; decide

/-- The phase-space involution acts trivially on the upper sheet and by the
sign character on the lower sheet. -/
theorem paraJ_plusPhase (q : Vec) :
    paraJ (plusPhase q) = plusPhase q := by
  simp [paraJ, plusPhase]

theorem paraJ_minusPhase (p : Vec) :
    paraJ (minusPhase p) = (0, -p) := by
  simp [paraJ, minusPhase]

theorem paraJ_circular_plus (i : Fin 3) :
    paraJ (plusPhase (Vec3.basis i)) = plusPhase (Vec3.basis i) := by
  exact paraJ_plusPhase _

theorem paraJ_circular_minus (i : Fin 3) :
    paraJ (minusPhase (Vec3.basis i)) = (0, -Vec3.basis i) := by
  exact paraJ_minusPhase _

end InfoGeometry.Algebra.CircularChiralGrading
