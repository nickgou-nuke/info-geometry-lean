import InfoGeometry.Lie.SplitOctonionEllPolarization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCrossTensor

/-!
# Cross-channel products for the distinguished split-octonion axis

This owner computes the actual canonical Zorn products of the paired
square-zero channels.  The commutator, anticommutator, and complementary
idempotents are consequences of those products.  No exponential, thermal,
Kantor, or exceptional-group interpretation is asserted.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Lie.SplitOctonionEllCrossChannel

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CZ := CanonicalZorn

/-- Positive idempotent determined by the distinguished split axis. -/
noncomputable def uPlus : CZ :=
  (1 / 2 : ℝ) • (1 + lUnit)

/-- Negative idempotent determined by the distinguished split axis. -/
noncomputable def uMinus : CZ :=
  (1 / 2 : ℝ) • (1 - lUnit)

/-- The positive axial element is idempotent for the actual Zorn product. -/
theorem uPlus_sq : uPlus * uPlus = uPlus := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    ((1 / 2 : ℝ) • (1 + lUnit)) ((1 / 2 : ℝ) • (1 + lUnit)) =
      (1 / 2 : ℝ) • (1 + lUnit)
  exact ell_idempotent_plus

/-- The negative axial element is idempotent for the actual Zorn product. -/
theorem uMinus_sq : uMinus * uMinus = uMinus := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    ((1 / 2 : ℝ) • (1 - lUnit)) ((1 / 2 : ℝ) • (1 - lUnit)) =
      (1 / 2 : ℝ) • (1 - lUnit)
  exact ell_idempotent_minus

/-- The two axial idempotents are orthogonal in positive-negative order. -/
theorem uPlus_mul_uMinus : uPlus * uMinus = 0 := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    ((1 / 2 : ℝ) • (1 + lUnit)) ((1 / 2 : ℝ) • (1 - lUnit)) = 0
  exact ell_idempotent_plus_mul_minus

/-- The two axial idempotents are orthogonal in negative-positive order. -/
theorem uMinus_mul_uPlus : uMinus * uPlus = 0 := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    ((1 / 2 : ℝ) • (1 - lUnit)) ((1 / 2 : ℝ) • (1 + lUnit)) = 0
  exact ell_idempotent_minus_mul_plus

/-- The complementary axial idempotents resolve the unit. -/
theorem uPlus_add_uMinus : uPlus + uMinus = 1 := by
  unfold uPlus uMinus
  module

/-- Their signed difference is the distinguished split axis. -/
theorem uPlus_sub_uMinus : uPlus - uMinus = lUnit := by
  unfold uPlus uMinus
  module

/-- In each quaternionic direction, the ordered positive-negative product is
the positive axial idempotent. -/
theorem rootPlus_mul_rootMinus (a : Fin 3) :
    rootPlus a * rootMinus a = uPlus := by
  fin_cases a <;>
    ext i <;>
    simp [uPlus, rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/-- Reversing the channel order gives the negative axial idempotent. -/
theorem rootMinus_mul_rootPlus (a : Fin 3) :
    rootMinus a * rootPlus a = uMinus := by
  fin_cases a <;>
    ext i <;>
    simp [uMinus, rootPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem uPlus_mul_rootPlus (a : Fin 3) :
    uPlus * rootPlus a = rootPlus a := by
  fin_cases a <;>
    ext i <;>
    simp [uPlus, rootPlus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem rootPlus_mul_uMinus (a : Fin 3) :
    rootPlus a * uMinus = rootPlus a := by
  fin_cases a <;>
    ext i <;>
    simp [uMinus, rootPlus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem uMinus_mul_rootMinus (a : Fin 3) :
    uMinus * rootMinus a = rootMinus a := by
  fin_cases a <;>
    ext i <;>
    simp [uMinus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem rootMinus_mul_uPlus (a : Fin 3) :
    rootMinus a * uPlus = rootMinus a := by
  fin_cases a <;>
    ext i <;>
    simp [uPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem uMinus_mul_rootPlus (a : Fin 3) :
    uMinus * rootPlus a = 0 := by
  fin_cases a <;>
    ext i <;>
    simp [uMinus, rootPlus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem rootPlus_mul_uPlus (a : Fin 3) :
    rootPlus a * uPlus = 0 := by
  fin_cases a <;>
    ext i <;>
    simp [uPlus, rootPlus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem uPlus_mul_rootMinus (a : Fin 3) :
    uPlus * rootMinus a = 0 := by
  fin_cases a <;>
    ext i <;>
    simp [uPlus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem rootMinus_mul_uMinus (a : Fin 3) :
    rootMinus a * uMinus = 0 := by
  fin_cases a <;>
    ext i <;>
    simp [uMinus, rootMinus, chiralNull, ellBasis, quaternionBasis,
      iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/-! ## Direct axial action from the Peirce routing packet

These are binary product identities.  They are deliberately proved from the
two complementary idempotents and the routing lemmas above; no reassociation
or associativity of the split-octonion product is used.
-/

theorem lUnit_mul_rootPlus (a : Fin 3) :
    lUnit * rootPlus a = rootPlus a := by
  rw [← uPlus_sub_uMinus]
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    (uPlus - uMinus) (rootPlus a) = rootPlus a
  rw [zMul_sub_left]
  rw [show InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul uPlus (rootPlus a) =
      rootPlus a from uPlus_mul_rootPlus a,
    show InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul uMinus (rootPlus a) =
      0 from uMinus_mul_rootPlus a, sub_zero]

theorem rootPlus_mul_lUnit (a : Fin 3) :
    rootPlus a * lUnit = -rootPlus a := by
  rw [← uPlus_sub_uMinus]
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    (rootPlus a) (uPlus - uMinus) = -rootPlus a
  rw [zMul_sub_right]
  rw [show InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (rootPlus a) uPlus =
      0 from rootPlus_mul_uPlus a,
    show InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (rootPlus a) uMinus =
      rootPlus a from rootPlus_mul_uMinus a, zero_sub]

theorem lUnit_mul_rootMinus (a : Fin 3) :
    lUnit * rootMinus a = -rootMinus a := by
  rw [← uPlus_sub_uMinus]
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    (uPlus - uMinus) (rootMinus a) = -rootMinus a
  rw [zMul_sub_left]
  rw [show InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul uPlus (rootMinus a) =
      0 from uPlus_mul_rootMinus a,
    show InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul uMinus (rootMinus a) =
      rootMinus a from uMinus_mul_rootMinus a, zero_sub]

theorem rootMinus_mul_lUnit (a : Fin 3) :
    rootMinus a * lUnit = rootMinus a := by
  rw [← uPlus_sub_uMinus]
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    (rootMinus a) (uPlus - uMinus) = rootMinus a
  rw [zMul_sub_right]
  rw [show InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (rootMinus a) uPlus =
      rootMinus a from rootMinus_mul_uPlus a,
    show InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (rootMinus a) uMinus =
      0 from rootMinus_mul_uMinus a, sub_zero]

/-! The two root channels form the signed eigenspaces for multiplication by
the distinguished split axis. -/

theorem lUnit_mul_rootChannel (b : Bool) (a : Fin 3) :
    lUnit * (if b then rootPlus a else rootMinus a) =
      if b then rootPlus a else -rootMinus a := by
  cases b
  · exact lUnit_mul_rootMinus a
  · exact lUnit_mul_rootPlus a

theorem rootChannel_mul_lUnit (b : Bool) (a : Fin 3) :
    (if b then rootPlus a else rootMinus a) * lUnit =
      if b then -rootPlus a else rootMinus a := by
  cases b
  · exact rootMinus_mul_lUnit a
  · exact rootPlus_mul_lUnit a

theorem lUnit_rootChannel_commutator (b : Bool) (a : Fin 3) :
    lUnit * (if b then rootPlus a else rootMinus a) -
        (if b then rootPlus a else rootMinus a) * lUnit =
      if b then 2 • rootPlus a else -(2 • rootMinus a) := by
  cases b
  · change lUnit * rootMinus a - rootMinus a * lUnit = -(2 • rootMinus a)
    rw [lUnit_mul_rootMinus, rootMinus_mul_lUnit]
    module
  · change lUnit * rootPlus a - rootPlus a * lUnit = 2 • rootPlus a
    rw [lUnit_mul_rootPlus, rootPlus_mul_lUnit]
    module

theorem lUnit_rootChannel_anticommutator (b : Bool) (a : Fin 3) :
    lUnit * (if b then rootPlus a else rootMinus a) +
        (if b then rootPlus a else rootMinus a) * lUnit = 0 := by
  cases b
  · change lUnit * rootMinus a + rootMinus a * lUnit = 0
    rw [lUnit_mul_rootMinus, rootMinus_mul_lUnit]
    module
  · change lUnit * rootPlus a + rootPlus a * lUnit = 0
    rw [lUnit_mul_rootPlus, rootPlus_mul_lUnit]
    module

/-- The commutator of the paired root channels recovers the axial generator. -/
theorem root_commutator (a : Fin 3) :
    rootPlus a * rootMinus a - rootMinus a * rootPlus a = lUnit := by
  rw [rootPlus_mul_rootMinus, rootMinus_mul_rootPlus, uPlus_sub_uMinus]

/-- The anticommutator of the paired root channels recovers the unit. -/
theorem root_anticommutator (a : Fin 3) :
    rootPlus a * rootMinus a + rootMinus a * rootPlus a = 1 := by
  rw [rootPlus_mul_rootMinus, rootMinus_mul_rootPlus, uPlus_add_uMinus]

end InfoGeometry.Lie.SplitOctonionEllCrossChannel
