import InfoGeometry.Lie.SplitOctonionEllPolarization

/-!
# Cross-channel products for the distinguished split-octonion axis

This owner computes the actual canonical Zorn products of the paired
square-zero channels.  The commutator, anticommutator, and complementary
idempotents are consequences of those products.  No exponential, thermal,
Kantor, or exceptional-group interpretation is asserted.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllCrossChannel

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
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

/-- The commutator of the paired root channels recovers the axial generator. -/
theorem root_commutator (a : Fin 3) :
    rootPlus a * rootMinus a - rootMinus a * rootPlus a = lUnit := by
  rw [rootPlus_mul_rootMinus, rootMinus_mul_rootPlus, uPlus_sub_uMinus]

/-- The anticommutator of the paired root channels recovers the unit. -/
theorem root_anticommutator (a : Fin 3) :
    rootPlus a * rootMinus a + rootMinus a * rootPlus a = 1 := by
  rw [rootPlus_mul_rootMinus, rootMinus_mul_rootPlus, uPlus_add_uMinus]

end InfoGeometry.Lie.SplitOctonionEllCrossChannel
