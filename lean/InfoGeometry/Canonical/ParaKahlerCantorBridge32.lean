import Mathlib
import InfoGeometry.Canonical.PositiveGrassmannianExteriorCantor
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge

/-!
# Depth-five Cantor channels for the positive `Gr(2,4)` Plücker state

The depth-five address set is the existing `BitWord 5` owner, whose cardinality
is 32 and whose canonical finite index is supplied by
`CliffordBitWordEquivalence`.  Prefix operators, matrix units, vacuum and the
five-mode CAR relations are reused from their owners.

The Plücker-weighted vector below is an actual finite linear combination of
normalized depth-five cylinder vectors in Cantor `L²`.  This module proves its
norm formula and positivity on the six active channels.  It deliberately does
not identify that vector with the action of the Clifford blade on the Fock
vacuum; that intertwining equation requires a separate matrix-action readback.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.Canonical.ParaKahlerCantorBridge32

open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.Projective.MatrixPluckerPositiveBridge

/-- Five-bit addresses for depth-five cylinders. -/
abbrev Word5 := BitWord 5

/-- The recursive tower's canonical enumeration of `BitWord 5`; this is
separate from the little-endian natural address map proved for the six
Plücker channels below. -/
noncomputable def word5Fin32 : Word5 ≃ Fin 32 := by
  simpa using InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordFinPowTwoEquiv 5

@[simp] theorem word5_card : Fintype.card Word5 = 32 := by
  simp [Word5, Fintype.card_fin, Fintype.card_bool]

/-- The actual normalized depth-five Cuntz prefix vector in Bernoulli Cantor
`L²`. -/
def cylinderVector5 (w : Word5) : L2Boundary :=
  operatorWord (List.ofFn w) vacuumL2

/-- Equal-depth prefix vectors are orthonormal by the owner's word-cancellation
law and normalized-vacuum readout. -/
theorem cylinderVector5_inner (u v : Word5) :
    inner ℂ (cylinderVector5 u) (cylinderVector5 v) =
      if u = v then 1 else 0 := by
  by_cases huv : u = v
  · subst v
    have hcancel :
        (operatorWordDag (List.ofFn u))
          (operatorWord (List.ofFn u) vacuumL2) = vacuumL2 := by
      exact ContinuousLinearMap.ext_iff.mp
        (operatorWordDag_comp_operatorWord (List.ofFn u)) vacuumL2
    simpa using (calc
      inner ℂ (cylinderVector5 u) (cylinderVector5 u) =
          inner ℂ vacuumL2 vacuumL2 := by
            calc
              inner ℂ (cylinderVector5 u) (cylinderVector5 u) =
                  inner ℂ vacuumL2
                    ((ContinuousLinearMap.adjoint (operatorWord (List.ofFn u)))
                      (operatorWord (List.ofFn u) vacuumL2)) := by
                exact (ContinuousLinearMap.adjoint_inner_right
                  (operatorWord (List.ofFn u)) vacuumL2
                  (operatorWord (List.ofFn u) vacuumL2)).symm
              _ = inner ℂ vacuumL2 vacuumL2 := by
                rw [← ContinuousLinearMap.star_eq_adjoint,
                  ← operatorWordDag_eq_star, hcancel]
      _ = 1 := vacuumL2_inner_self)
  · have hlen : (List.ofFn u).length = (List.ofFn v).length := by simp
    have hwords : List.ofFn u ≠ List.ofFn v := by
      intro h
      apply huv
      exact List.ofFn_injective h
    have hcancel := operatorWordDag_comp_operatorWord_of_length_eq hlen hwords
    have hzero :
        (operatorWordDag (List.ofFn u)) (operatorWord (List.ofFn v) vacuumL2) = 0 := by
      have h := congrArg (fun T => T vacuumL2) hcancel
      simpa using h
    calc
      inner ℂ (cylinderVector5 u) (cylinderVector5 v) =
          inner ℂ vacuumL2
            ((ContinuousLinearMap.adjoint (operatorWord (List.ofFn u)))
              (operatorWord (List.ofFn v) vacuumL2)) := by
        exact (ContinuousLinearMap.adjoint_inner_right (operatorWord (List.ofFn u))
          vacuumL2 (operatorWord (List.ofFn v) vacuumL2)).symm
      _ = 0 := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← operatorWordDag_eq_star, hzero]
        simp
      _ = if u = v then 1 else 0 := by simp [huv]

/-- Depth-five matrix units are the existing Cantor matrix units, reindexed by
the canonical five-bit address equivalence. -/
def cylinderMatrixUnit5 (u v : Word5) : BoundedL2Operator :=
  bitWordUnit 5 u v

theorem cylinderMatrixUnit5_mul (u v x y : Word5) :
    (cylinderMatrixUnit5 u v).comp (cylinderMatrixUnit5 x y) =
      if v = x then cylinderMatrixUnit5 u y else 0 :=
  bitWordUnit_mul 5 u v x y

theorem cylinderMatrixUnit5_resolution :
    ∑ w : Word5, cylinderMatrixUnit5 w w =
      ContinuousLinearMap.id ℂ L2Boundary := by
  exact bitWordUnit_level_sum_one 5

theorem cylinderMatrixUnit5_apply_basis (u v : Word5) :
    cylinderMatrixUnit5 u v (cylinderVector5 v) = cylinderVector5 u := by
  change operatorMatrixUnit (List.ofFn u) (List.ofFn v)
      (operatorWord (List.ofFn v) vacuumL2) = _
  change operatorWord (List.ofFn u)
      (operatorWordDag (List.ofFn v)
        (operatorWord (List.ofFn v) vacuumL2)) = _
  rw [show (operatorWordDag (List.ofFn v))
      (operatorWord (List.ofFn v) vacuumL2) = vacuumL2 by
    exact ContinuousLinearMap.ext_iff.mp
      (operatorWordDag_comp_operatorWord (List.ofFn v)) vacuumL2]
  rfl

/-- The six Plücker channels are the weight-two words in the first four modes;
the fifth mode is fixed to zero. -/
def pluckerAddress (i : Fin 6) : Word5 :=
  match i.val with
  | 0 => ![true, true, false, false, false]
  | 1 => ![true, false, true, false, false]
  | 2 => ![true, false, false, true, false]
  | 3 => ![false, true, true, false, false]
  | 4 => ![false, true, false, true, false]
  | 5 => ![false, false, true, true, false]
  | _ => ![false, false, false, false, false]

/-- Little-endian natural-number address, with bit zero having weight one. -/
def word5BinaryValue (w : Word5) : ℕ :=
  (if w 0 then 1 else 0) + (if w 1 then 2 else 0) +
  (if w 2 then 4 else 0) + (if w 3 then 8 else 0) +
  (if w 4 then 16 else 0)

theorem word5BinaryValue_lt (w : Word5) : word5BinaryValue w < 32 := by
  unfold word5BinaryValue
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;>
    cases h3 : w 3 <;> cases h4 : w 4 <;>
    norm_num [h0, h1, h2, h3, h4]

/-- The specified low-bit-first `Fin 32` address of a five-bit word. -/
def word5LittleEndianIndex (w : Word5) : Fin 32 :=
  ⟨word5BinaryValue w, word5BinaryValue_lt w⟩

def pluckerSectorIndex (i : Fin 6) : Fin 32 :=
  match i.val with
  | 0 => 3
  | 1 => 5
  | 2 => 9
  | 3 => 6
  | 4 => 10
  | 5 => 12
  | _ => 0

theorem pluckerAddress_index (i : Fin 6) :
    word5LittleEndianIndex (pluckerAddress i) = pluckerSectorIndex i := by
  fin_cases i <;>
    norm_num [word5LittleEndianIndex, word5BinaryValue, pluckerSectorIndex, pluckerAddress]

theorem pluckerAddress_injective : Function.Injective pluckerAddress := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [pluckerAddress] at h ⊢

/-- The fifth occupation bit is zero in each of the six Grassmannian
channels: this is a property of the chosen four-mode blade, not an
annihilation law for the fifth creation operator. -/
theorem pluckerAddress_fifthBit (i : Fin 6) : pluckerAddress i 4 = false := by
  fin_cases i <;> rfl

/-- Each Grassmannian address has exactly two occupied modes. -/
theorem pluckerAddress_weight (i : Fin 6) :
    (Finset.univ.filter (fun k : Fin 5 => pluckerAddress i k = true)).card = 2 := by
  fin_cases i <;> decide

/-- The positive Grassmannian Plücker vector, realized as a step-function
vector in the actual depth-five Cantor `L²` space. -/
def pluckerCantorState (M : Matrix2x4) : L2Boundary :=
  ∑ i : Fin 6, (matrixPluckerCoords M i : ℂ) • cylinderVector5 (pluckerAddress i)

theorem pluckerCantorState_inner (M : Matrix2x4) :
    inner ℂ (pluckerCantorState M) (pluckerCantorState M) =
      (∑ i : Fin 6, ((matrixPluckerCoords M i) ^ 2 : ℝ) : ℂ) := by
  classical
  unfold pluckerCantorState
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  simp_rw [inner_smul_left, inner_smul_right, cylinderVector5_inner,
    Complex.conj_ofReal]
  rw [Finset.sum_eq_single i]
  · simp [pow_two, Complex.ofReal_mul]
  · intro j _ hji
    have haddr : pluckerAddress i ≠ pluckerAddress j := fun h =>
      hji (pluckerAddress_injective h.symm)
    simp [haddr]
  · simp

/-- Reading a Plücker state in one of its six orthonormal cylinder channels
recovers exactly the corresponding Plücker coordinate. -/
theorem pluckerCantorState_channel_coefficient (M : Matrix2x4) (i : Fin 6) :
    inner ℂ (cylinderVector5 (pluckerAddress i)) (pluckerCantorState M) =
      (matrixPluckerCoords M i : ℂ) := by
  classical
  unfold pluckerCantorState
  rw [inner_sum]
  simp_rw [inner_smul_right, cylinderVector5_inner]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have haddr : pluckerAddress i ≠ pluckerAddress j := fun h =>
      hji (pluckerAddress_injective h.symm)
    simp [haddr]
  · simp

/-- A cylinder outside the six Plücker addresses is orthogonal to the
Grassmannian state. -/
theorem pluckerCantorState_off_channel (M : Matrix2x4) (w : Word5)
    (hw : ∀ i : Fin 6, pluckerAddress i ≠ w) :
    inner ℂ (cylinderVector5 w) (pluckerCantorState M) = 0 := by
  classical
  unfold pluckerCantorState
  rw [inner_sum]
  simp_rw [inner_smul_right, cylinderVector5_inner]
  have hne : ∀ i : Fin 6, w ≠ pluckerAddress i := fun i => Ne.symm (hw i)
  simp [hne]

/-- On a strictly positive chart, the support of the depth-five state is
exactly the six weight-two addresses. -/
theorem pluckerCantorState_support_iff
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4))
    (w : Word5) :
    inner ℂ (cylinderVector5 w) (pluckerCantorState M) ≠ 0 ↔
      ∃ i : Fin 6, pluckerAddress i = w := by
  constructor
  · intro h
    by_contra hnot
    apply h
    exact pluckerCantorState_off_channel M w (by
      intro i hi
      exact hnot ⟨i, hi⟩)
  · rintro ⟨i, rfl⟩
    rw [pluckerCantorState_channel_coefficient]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (positiveGrassmannianInterior_mem_matrixPluckerPositive M hM i))

theorem pluckerCantorState_norm_sq (M : Matrix2x4) :
    ‖pluckerCantorState M‖ ^ 2 =
      ∑ i : Fin 6, (matrixPluckerCoords M i) ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), pluckerCantorState_inner]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact Complex.ofReal_re _

theorem positiveChart_cantor_sectors_positive
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∀ i : Fin 6, 0 < matrixPluckerCoords M i :=
  positiveGrassmannianInterior_mem_matrixPluckerPositive M hM

/-- The six Cantor-channel coefficients inherit the Klein quadratic relation
from the matrix Plücker minors. -/
theorem pluckerCantorState_klein_relation (M : Matrix2x4) :
    matrixPluckerCoords M 0 * matrixPluckerCoords M 5 -
      matrixPluckerCoords M 1 * matrixPluckerCoords M 4 +
      matrixPluckerCoords M 2 * matrixPluckerCoords M 3 = 0 :=
  matrixPluckerCoords_klein_relation M

/-- The actual five-mode creation/annihilation CAR are read back from the
existing native spinor owner, rather than reproved with a second ad-hoc model. -/
theorem spinorCAR_same_site (i : Fin 5) :
    InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorAnnihilation55 i *
        InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorCreation55 i +
      InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorCreation55 i *
        InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorAnnihilation55 i = 1 :=
  InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorCAR_same_site i

theorem spinorCAR_mixed_sites (i j : Fin 5) :
    InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorAnnihilation55 i *
        InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorCreation55 j +
      InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorCreation55 j *
        InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorAnnihilation55 i =
      if i = j then 1 else 0 :=
  InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.spinorCAR_mixed_sites i j

end InfoGeometry.Canonical.ParaKahlerCantorBridge32

end noncomputable section
