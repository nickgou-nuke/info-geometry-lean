/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornPolarizationMetricBridge

/-! Multiplication adjoints for the existing split polar form on the full Zorn
carrier. Octonion conjugation reverses the multiplication side; the polar
adjoint identities preserve it. Neither is the positive coefficient adjoint. -/
namespace InfoGeometry.Canonical.ZornPolarAdjoint
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge

/-- Split-polar adjoint identity for left multiplication. -/
theorem polar_left_adjoint (X Y W : ZornCoord) :
    polarPair (zornMul X Y) W = polarPair Y (zornMul (zornConj X) W) := by
  simp [polarPair, zornMul, zornConj, zornMk, zornA, zornB, zornX, zornY,
    dot3, cross3]
  ring

/-- Split-polar adjoint identity for right multiplication. -/
theorem polar_right_adjoint (X Y W : ZornCoord) :
    polarPair (zornMul Y X) W = polarPair Y (zornMul W (zornConj X)) := by
  simp [polarPair, zornMul, zornConj, zornMk, zornA, zornB, zornX, zornY,
    dot3, cross3]
  ring

/-- Conjugation exchanges left and right multiplication, unlike the polar adjoint. -/
theorem conjugate_mul (X Y : ZornCoord) :
    zornConj (zornMul X Y) = zornMul (zornConj Y) (zornConj X) := by
  ext i <;> try fin_cases i
  all_goals simp [zornConj, zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3]
  all_goals ring

/-- Conversion to the existing positive Hilbertized pairing inserts the
fundamental symmetry; it does not leave the polar adjoint unchanged. -/
theorem hilbertized_left_adjoint (X Y W : ZornCoord) :
    polarPair (zornMul X Y) (fundamental W) =
      polarPair Y (fundamental (zornMul (fundamental (zornConj X)) W)) := by
  rw [polar_left_adjoint, fundamental_mul, fundamental_sq]

/-- The same change of pairing for right multiplication. -/
theorem hilbertized_right_adjoint (X Y W : ZornCoord) :
    polarPair (zornMul Y X) (fundamental W) =
      polarPair Y (fundamental (zornMul W (fundamental (zornConj X)))) := by
  rw [polar_right_adjoint, fundamental_mul, fundamental_sq]

end InfoGeometry.Canonical.ZornPolarAdjoint
