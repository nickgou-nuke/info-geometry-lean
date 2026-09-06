import Mathlib.Tactic
import InfoGeometry.Algebra.Zorn.RegularActionAssociator
import InfoGeometry.Algebra.KingdonSplitOctonion
import InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionEllCircularCAR

/-!
# Native right-regular circular CAR bridge

The literal exterior creation operator raises the established Peirce/exterior
order `0 → 1 → 2 → 3`.  On the genuine `uPlus/uMinus` circular split-octonion
carrier that endpoint pattern is carried by right regular multiplication, not
by left regular multiplication.

This owner proves the full three-mode CAR relations for the right-regular
circular roots.  The proof is intrinsic: right alternativity makes the two
associator corrections in the symmetrized regular product cancel.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllCircularCAR
open InfoGeometry.Physics

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

def rightRegular (x : CZ) : EndCZ :=
  rightMultiplication x

@[simp] theorem rightRegular_apply (x y : CZ) :
    rightRegular x y = y * x :=
  rfl

private theorem zorn_right_alt (x y : CZ) :
    (y * x) * x = y * (x * x) :=
  InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.zorn_right_alternative x y

theorem rightRegular_anticommutator (a b : CZ) :
    rightRegular a * rightRegular b + rightRegular b * rightRegular a =
      rightRegular (a * b + b * a) := by
  apply LinearMap.ext
  intro y
  change (y * b) * a + (y * a) * b = y * (a * b + b * a)
  rw [mul_add]
  have hskew :=
    InfoGeometry.Algebra.alternative_associator_swap23 zorn_right_alt y b a
  change
    (y * b) * a - y * (b * a) =
      -((y * a) * b - y * (a * b)) at hskew
  abel

theorem rightRegular_sq_zero_of_sq_zero
    (x : CZ) (hx : x * x = 0) :
    rightRegular x * rightRegular x = 0 := by
  apply LinearMap.ext
  intro y
  change (y * x) * x = 0
  rw [zorn_right_alt x y, hx]
  simp

@[simp] theorem rightRegular_rootPlus_sq (i : Fin 3) :
    rightRegular (rootPlus i) * rightRegular (rootPlus i) = 0 :=
  rightRegular_sq_zero_of_sq_zero (rootPlus i) (rootPlus_sq_zero i)

@[simp] theorem rightRegular_rootMinus_sq (i : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootMinus i) = 0 :=
  rightRegular_sq_zero_of_sq_zero (rootMinus i) (rootMinus_sq_zero i)

theorem rootPlus_same_anticommutator_zero (i j : Fin 3) :
    rootPlus i * rootPlus j + rootPlus j * rootPlus i = (0 : CZ) := by
  fin_cases i <;> fin_cases j <;>
    ext k <;>
    simp [rootPlus, chiralNull, ellBasis, quaternionBasis,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.jUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.kQuaternionUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases k) <;> norm_num

theorem rootMinus_same_anticommutator_zero (i j : Fin 3) :
    rootMinus i * rootMinus j + rootMinus j * rootMinus i = (0 : CZ) := by
  fin_cases i <;> fin_cases j <;>
    ext k <;>
    simp [rootMinus, chiralNull, ellBasis, quaternionBasis,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.jUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.kQuaternionUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases k) <;> norm_num

theorem rightRegular_root_mixed_CAR (i j : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootPlus j) +
        rightRegular (rootPlus j) * rightRegular (rootMinus i) =
      (if i = j then (1 : ℝ) else 0) • (1 : EndCZ) := by
  rw [rightRegular_anticommutator]
  have hanti :
      rootMinus i * rootPlus j + rootPlus j * rootMinus i =
        (if i = j then (1 : CZ) else 0) := by
    have h := rootPlus_mul_rootMinus_anticommutator j i
    by_cases hij : i = j
    · subst j
      simpa [add_comm] using h
    · have hji : j ≠ i := Ne.symm hij
      simpa [hij, hji, add_comm] using h
  rw [hanti]
  by_cases hij : i = j
  · subst j
    simp
    apply LinearMap.ext
    intro y
    change y * (1 : CZ) = y
    exact zMul_one y
  · simp [hij, rightRegular]

theorem rightRegular_rootPlus_same_CAR (i j : Fin 3) :
    rightRegular (rootPlus i) * rightRegular (rootPlus j) +
        rightRegular (rootPlus j) * rightRegular (rootPlus i) = 0 := by
  rw [rightRegular_anticommutator, rootPlus_same_anticommutator_zero]
  apply LinearMap.ext
  intro y
  rfl

theorem rightRegular_rootMinus_same_CAR (i j : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootMinus j) +
        rightRegular (rootMinus j) * rightRegular (rootMinus i) = 0 := by
  rw [rightRegular_anticommutator, rootMinus_same_anticommutator_zero]
  apply LinearMap.ext
  intro y
  rfl

theorem rightRegular_root_CAR (i : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootPlus i) +
        rightRegular (rootPlus i) * rightRegular (rootMinus i) =
      (1 : EndCZ) := by
  simpa using rightRegular_root_mixed_CAR i i

def rightRegularCARPair (i : Fin 3) : SplitClifford.CARPair EndCZ where
  ann := rightRegular (rootMinus i)
  cre := rightRegular (rootPlus i)
  ann_sq := rightRegular_rootMinus_sq i
  cre_sq := rightRegular_rootPlus_sq i
  anti := rightRegular_root_CAR i

@[simp] theorem rightRegular_rootPlus_uPlus (i : Fin 3) :
    rightRegular (rootPlus i) uPlus = rootPlus i := by
  change uPlus * rootPlus i = rootPlus i
  exact uPlus_mul_rootPlus i

@[simp] theorem rightRegular_rootPlus_uMinus (i : Fin 3) :
    rightRegular (rootPlus i) uMinus = 0 := by
  change uMinus * rootPlus i = 0
  exact uMinus_mul_rootPlus i

@[simp] theorem rightRegular_rootMinus_uPlus (i : Fin 3) :
    rightRegular (rootMinus i) uPlus = 0 := by
  change uPlus * rootMinus i = 0
  exact uPlus_mul_rootMinus i

@[simp] theorem rightRegular_rootMinus_uMinus (i : Fin 3) :
    rightRegular (rootMinus i) uMinus = rootMinus i := by
  change uMinus * rootMinus i = rootMinus i
  exact uMinus_mul_rootMinus i

theorem rightRegular_creation_endpoint_packet (i : Fin 3) :
    rightRegular (rootPlus i) uPlus = rootPlus i ∧
      rightRegular (rootPlus i) uMinus = 0 :=
  ⟨rightRegular_rootPlus_uPlus i, rightRegular_rootPlus_uMinus i⟩

theorem rightRegular_annihilation_endpoint_packet (i : Fin 3) :
    rightRegular (rootMinus i) uPlus = 0 ∧
      rightRegular (rootMinus i) uMinus = rootMinus i :=
  ⟨rightRegular_rootMinus_uPlus i, rightRegular_rootMinus_uMinus i⟩

end InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
