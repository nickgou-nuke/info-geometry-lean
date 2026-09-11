import InfoGeometry.Algebra.Zorn.CanonicalKantorOperators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionEllCrossChannel

/-!
# Same-color canonical `V` computations

The theorems below evaluate the concrete polynomial `V` operator on one
paired split-octonion root channel.  Every proof unfolds to the native Zorn
coordinates.  No Kantor identity or closure structure is assumed.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Lie.SplitOctonionEllKantorRankOne

open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.CanonicalKantorOperators
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

@[simp] theorem canonicalConj_rootPlus (a : Fin 3) :
    canonicalConj (rootPlus a) = -rootPlus a := by
  fin_cases a <;>
    ext i <;>
    simp [canonicalConj, canonicalVectorEquiv, rootPlus, chiralNull,
      ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit, lUnit,
      zMul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVectorMatrix.conj]
  all_goals (try fin_cases i) <;> norm_num

@[simp] theorem canonicalConj_rootMinus (a : Fin 3) :
    canonicalConj (rootMinus a) = -rootMinus a := by
  fin_cases a <;>
    ext i <;>
    simp [canonicalConj, canonicalVectorEquiv, rootMinus, chiralNull,
      ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit, lUnit,
      zMul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVectorMatrix.conj]
  all_goals (try fin_cases i) <;> norm_num

/-- Direct same-color value `V(N⁺,N⁻,N⁺) = -2 N⁺`. -/
theorem V_rootPlus_rootMinus_rootPlus (a : Fin 3) :
    V (rootPlus a) (rootMinus a) (rootPlus a) =
      (-2 : ℝ) • rootPlus a := by
  fin_cases a <;>
    ext i <;>
    simp [V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/-- Direct same-color value `V(N⁻,N⁺,N⁻) = -2 N⁻`. -/
theorem V_rootMinus_rootPlus_rootMinus (a : Fin 3) :
    V (rootMinus a) (rootPlus a) (rootMinus a) =
      (-2 : ℝ) • rootMinus a := by
  fin_cases a <;>
    ext i <;>
    simp [V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/-- Direct same-color Kantor value on the positive root channel.  This is a
native computation of `K(E,F)E`, not an assumed Kantor-pair relation. -/
theorem K_rootPlus_rootMinus_rootPlus (a : Fin 3) :
    K (rootPlus a) (rootMinus a) (rootPlus a) =
      -rootPlus a := by
  fin_cases a <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/-- The companion same-color value `K(E,F)F = F` on the negative channel. -/
theorem K_rootPlus_rootMinus_rootMinus (a : Fin 3) :
    K (rootPlus a) (rootMinus a) (rootMinus a) =
      rootMinus a := by
  fin_cases a <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/-! ## First cross-color closure computation -/

/- The mixed channel vanishes for distinct root labels.  These concrete
instances are intentionally kept finite: they expose the cross-color
calculation without introducing a contract or a symbolic delta wrapper. -/
theorem K_rootPlus_zero_rootMinus_one_rootPlus (c : Fin 3) :
    K (rootPlus 0) (rootMinus 1) (rootPlus c) = 0 := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num
theorem K_rootMinus_zero_rootPlus_one_rootMinus (c : Fin 3) :
    K (rootMinus 0) (rootPlus 1) (rootMinus c) = 0 := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/- The mixed same-polarity tails vanish for the same distinct labels. -/
theorem K_rootPlus_zero_rootMinus_one_rootMinus (c : Fin 3) :
    K (rootPlus 0) (rootMinus 1) (rootMinus c) = 0 := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
theorem K_rootMinus_zero_rootPlus_one_rootPlus (c : Fin 3) :
    K (rootMinus 0) (rootPlus 1) (rootPlus c) = 0 := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/- For equal first two labels the mixed tails reproduce the third root
channel, as predicted by the same-color matrix-unit atom. -/
theorem K_rootPlus_zero_rootMinus_zero_rootMinus (c : Fin 3) :
    K (rootPlus 0) (rootMinus 0) (rootMinus c) = rootMinus c := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem K_rootMinus_zero_rootPlus_zero_rootPlus (c : Fin 3) :
    K (rootMinus 0) (rootPlus 0) (rootPlus c) = rootPlus c := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

private theorem K_rootPlus_one_rootMinus_one_rootMinus (c : Fin 3) :
    K (rootPlus 1) (rootMinus 1) (rootMinus c) = rootMinus c := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

private theorem K_rootPlus_two_rootMinus_two_rootMinus (c : Fin 3) :
    K (rootPlus 2) (rootMinus 2) (rootMinus c) = rootMinus c := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/- The same-color tail identity for every quaternionic root label. -/
theorem K_rootPlus_rootMinus_rootMinus_all (a c : Fin 3) :
    K (rootPlus a) (rootMinus a) (rootMinus c) = rootMinus c := by
  fin_cases a
  · exact K_rootPlus_zero_rootMinus_zero_rootMinus c
  · exact K_rootPlus_one_rootMinus_one_rootMinus c
  · exact K_rootPlus_two_rootMinus_two_rootMinus c

private theorem K_rootMinus_one_rootPlus_one_rootPlus (c : Fin 3) :
    K (rootMinus 1) (rootPlus 1) (rootPlus c) = rootPlus c := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

private theorem K_rootMinus_two_rootPlus_two_rootPlus (c : Fin 3) :
    K (rootMinus 2) (rootPlus 2) (rootPlus c) = rootPlus c := by
  fin_cases c <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem K_rootMinus_rootPlus_rootPlus_all (a c : Fin 3) :
    K (rootMinus a) (rootPlus a) (rootPlus c) = rootPlus c := by
  fin_cases a
  · exact K_rootMinus_zero_rootPlus_zero_rootPlus c
  · exact K_rootMinus_one_rootPlus_one_rootPlus c
  · exact K_rootMinus_two_rootPlus_two_rootPlus c

private theorem V_rootPlus_zero_rootMinus_rootPlus (b : Fin 3) :
    V (rootPlus 0) (rootMinus b) (rootPlus b) =
      (-2 : ℝ) • rootPlus 0 := by
  fin_cases b <;>
    ext i <;>
    simp [V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

private theorem V_rootPlus_one_rootMinus_rootPlus (b : Fin 3) :
    V (rootPlus 1) (rootMinus b) (rootPlus b) =
      (-2 : ℝ) • rootPlus 1 := by
  fin_cases b <;>
    ext i <;>
    simp [V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

private theorem V_rootPlus_two_rootMinus_rootPlus (b : Fin 3) :
    V (rootPlus 2) (rootMinus b) (rootPlus b) =
      (-2 : ℝ) • rootPlus 2 := by
  fin_cases b <;>
    ext i <;>
    simp [V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem V_rootPlus_rootMinus_rootPlus_channel (a b : Fin 3) :
    V (rootPlus a) (rootMinus b) (rootPlus b) =
      (-2 : ℝ) • rootPlus a := by
  fin_cases a
  · exact V_rootPlus_zero_rootMinus_rootPlus b
  · exact V_rootPlus_one_rootMinus_rootPlus b
  · exact V_rootPlus_two_rootMinus_rootPlus b

private theorem V_rootMinus_zero_rootPlus_rootMinus (b : Fin 3) :
    V (rootMinus 0) (rootPlus b) (rootMinus b) =
      (-2 : ℝ) • rootMinus 0 := by
  fin_cases b <;>
    ext i <;>
    simp [V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVectorMatrix.conj]
  all_goals (try fin_cases i) <;> norm_num

private theorem V_rootMinus_one_rootPlus_rootMinus (b : Fin 3) :
    V (rootMinus 1) (rootPlus b) (rootMinus b) =
      (-2 : ℝ) • rootMinus 1 := by
  fin_cases b <;>
    ext i <;>
    simp [V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVectorMatrix.conj]
  all_goals (try fin_cases i) <;> norm_num

private theorem V_rootMinus_two_rootPlus_rootMinus (b : Fin 3) :
    V (rootMinus 2) (rootPlus b) (rootMinus b) =
      (-2 : ℝ) • rootMinus 2 := by
  fin_cases b <;>
    ext i <;>
    simp [V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVectorMatrix.conj]
  all_goals (try fin_cases i) <;> norm_num

theorem V_rootMinus_rootPlus_rootMinus_channel (a b : Fin 3) :
    V (rootMinus a) (rootPlus b) (rootMinus b) =
      (-2 : ℝ) • rootMinus a := by
  fin_cases a
  · exact V_rootMinus_zero_rootPlus_rootMinus b
  · exact V_rootMinus_one_rootPlus_rootMinus b
  · exact V_rootMinus_two_rootPlus_rootMinus b

/- The native `V` channel identities are homogeneous for the axial
commutator grading. -/
theorem ellCommutator_V_rootPlus_rootMinus_rootPlus_channel
    (a b : Fin 3) :
    ellCommutator (V (rootPlus a) (rootMinus b) (rootPlus b)) =
      (2 : ℝ) • V (rootPlus a) (rootMinus b) (rootPlus b) := by
  rw [V_rootPlus_rootMinus_rootPlus_channel]
  rw [map_smul, ellCommutator_rootPlus]
  module

theorem ellCommutator_V_rootMinus_rootPlus_rootMinus_channel
    (a b : Fin 3) :
    ellCommutator (V (rootMinus a) (rootPlus b) (rootMinus b)) =
      (-2 : ℝ) • V (rootMinus a) (rootPlus b) (rootMinus b) := by
  rw [V_rootMinus_rootPlus_rootMinus_channel]
  rw [map_smul, ellCommutator_rootMinus]

theorem ellCommutator_K_rootPlus_rootMinus_rootMinus_all
    (a c : Fin 3) :
    ellCommutator (K (rootPlus a) (rootMinus a) (rootMinus c)) =
      (-2 : ℝ) • K (rootPlus a) (rootMinus a) (rootMinus c) := by
  rw [K_rootPlus_rootMinus_rootMinus_all]
  rw [ellCommutator_rootMinus]

theorem ellCommutator_K_rootMinus_rootPlus_rootPlus_all
    (a c : Fin 3) :
    ellCommutator (K (rootMinus a) (rootPlus a) (rootPlus c)) =
      (2 : ℝ) • K (rootMinus a) (rootPlus a) (rootPlus c) := by
  rw [K_rootMinus_rootPlus_rootPlus_all]
  rw [ellCommutator_rootPlus]

/- The rank-one `K(E,F)` operator also acts diagonally on the two Peirce
idempotents. -/
theorem K_rootPlus_rootMinus_uPlus (a : Fin 3) :
    K (rootPlus a) (rootMinus a) uPlus = -uPlus := by
  fin_cases a <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      uPlus, chiralNull, ellBasis, quaternionBasis, iUnit, jUnit,
      kQuaternionUnit, lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem K_rootPlus_rootMinus_uMinus (a : Fin 3) :
    K (rootPlus a) (rootMinus a) uMinus = uMinus := by
  fin_cases a <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      uMinus, chiralNull, ellBasis, quaternionBasis, iUnit, jUnit,
      kQuaternionUnit, lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem K_rootPlus_rootMinus_one (a : Fin 3) :
    K (rootPlus a) (rootMinus a) (1 : CZ) = -lUnit := by
  fin_cases a <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem K_rootPlus_rootMinus_ell (a : Fin 3) :
    K (rootPlus a) (rootMinus a) lUnit = -(1 : CZ) := by
  fin_cases a <;>
    ext i <;>
    simp [K, V, canonicalConj, canonicalVectorEquiv, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Algebra.ZornVectorMatrix.conj,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem ellCommutator_K_rootPlus_rootMinus_one (a : Fin 3) :
    ellCommutator (K (rootPlus a) (rootMinus a) (1 : CZ)) = 0 := by
  rw [K_rootPlus_rootMinus_one]
  fin_cases a <;>
    ext i <;>
    simp [ellCommutator, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem ellCommutator_K_rootPlus_rootMinus_ell (a : Fin 3) :
    ellCommutator (K (rootPlus a) (rootMinus a) lUnit) = 0 := by
  rw [K_rootPlus_rootMinus_ell]
  fin_cases a <;>
    ext i <;>
    simp [ellCommutator, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

end InfoGeometry.Lie.SplitOctonionEllKantorRankOne
