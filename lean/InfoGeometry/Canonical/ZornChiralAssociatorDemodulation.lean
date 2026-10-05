import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.ZornAssociatorDerivationCurvatureBridge
import InfoGeometry.Canonical.ZbwDarwinDemodulation

/-!
# Stratum 28: Zorn Chiral Associator Demodulation

This module provides an algebraic identity relating the mathematical non-associativity
of the Zorn matrix multiplication to the native 3D scalar triple product.
-/

namespace InfoGeometry.Canonical.ZornChiralAssociatorDemodulation

open InfoGeometry.Canonical.ZornAssociatorDerivationCurvature
open InfoGeometry.Canonical.GaugedZornDiracKahler
open InfoGeometry.Canonical.ZornGaugeBosonGellMannTwistor

variable {R : Type*} [CommRing R]

/-- The cyclic invariance of the native dot3/cross3 scalar triple product. -/
theorem scalar_triple_product_cyclic (u v w : Vec3 R) :
    dot3 (cross3 u v) w = dot3 u (cross3 v w) := by
  dsimp [dot3, cross3]
  ring

/-- Swapping the first two vectors reverses the scalar triple product. -/
theorem scalar_triple_product_swap (u v w : Vec3 R) :
    dot3 v (cross3 u w) = - dot3 u (cross3 v w) := by
  dsimp [dot3, cross3]
  ring

/-- Reversing the orientation of the cross-product inputs reverses the scalar. -/
theorem scalar_triple_product_orientation_reversal (u v w : Vec3 R) :
    dot3 u (cross3 w v) = - dot3 u (cross3 v w) := by
  dsimp [dot3, cross3]
  ring

/-- A scalar triple product with a repeated vector in the first two slots vanishes. -/
theorem scalar_triple_product_repeated (u w : Vec3 R) :
    dot3 u (cross3 u w) = 0 := by
  dsimp [dot3, cross3]
  ring

/-- A scalar triple product vanishes when the two cross-product inputs agree. -/
theorem scalar_triple_product_repeated_last (u v : Vec3 R) :
    dot3 u (cross3 v v) = 0 := by
  dsimp [dot3, cross3]
  ring

/--
**Algebraic Identity**:
Evaluating the associator on three quark states (S, p, ε)
yields a diagonal matrix with exactly (-T, T), where T = S · (p × ε).
This serves as a coordinate readback of the associator defect.
-/
theorem zorn_associator_three_quarks_demodulation (S p eps : Vec3 R) :
    let T := dot3 S (cross3 p eps)
    zornAssociator (ZornMatrix.quark S) (ZornMatrix.quark p) (ZornMatrix.quark eps) =
    ZornMatrix.sub (ZornMatrix.smul T ZornMatrix.PMinus) (ZornMatrix.smul T ZornMatrix.PPlus) := by
  intro T
  dsimp only [T]
  dsimp [zornAssociator, ZornMatrix.sub, ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.smul, ZornMatrix.PMinus, ZornMatrix.PPlus]
  congr 1
  · dsimp [dot3, cross3]; ring
  · dsimp [dot3, cross3]; ring
  · ext i; fin_cases i <;> { dsimp [cross3, dot3]; ring }
  · ext i; fin_cases i <;> { dsimp [cross3, dot3]; ring }

end InfoGeometry.Canonical.ZornChiralAssociatorDemodulation
