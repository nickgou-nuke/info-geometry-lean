import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.ZornAssociatorDerivationCurvatureBridge
import InfoGeometry.Canonical.ZbwDarwinDemodulation

/-!
# Stratum 28: Zorn Chiral Associator Demodulation

This module formally bridges the mathematical non-associativity of the Zorn vacuum
to the macroscopic T-odd scalar triple product observed in polarization correlations.

As stated in the epistemological diagnosis:
"The non-associativity of the vacuum (the [U₁, U₂, U₃] ≠ 0 associator) requires the
correlation function to contain a parity-violating, T-odd scalar triple product:
W(θ, ϕ) ⊃ A_chiral (S_core · (p_e × ε_γ))"

Here we prove that evaluating the Zorn associator on three pure-quark states
exactly demodulates into a diagonal matrix whose components are precisely
the chiral scalar triple product.
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

/-- Interchanging two arguments reverses the scalar triple product. -/
theorem scalar_triple_product_swap (u v w : Vec3 R) :
    dot3 v (cross3 u w) = - dot3 u (cross3 v w) := by
  dsimp [dot3, cross3]
  ring

/-- A scalar triple product with a repeated vector vanishes. -/
theorem scalar_triple_product_repeated (u w : Vec3 R) :
    dot3 u (cross3 u w) = 0 := by
  dsimp [dot3, cross3]
  ring

/-- The scalar triple product also vanishes when its last two vectors agree. -/
theorem scalar_triple_product_repeated_last (u v : Vec3 R) :
    dot3 u (cross3 v v) = 0 := by
  rw [InfoGeometry.Canonical.ZornDiracKahlerSU3Bridge.cross3_self]
  simp [dot3]

/--
**The Chiral Demodulator Theorem**:
The fundamental non-associativity of the Zorn vacuum directly produces the
T-odd, parity-violating chiral scalar triple product on the diagonal.
Specifically, evaluating the associator on three quark states (S, p, ε)
yields a diagonal matrix with exactly (-T, T), where T = S · (p × ε).

This proves that the abstract algebraic associator defect acts as a chiral
demodulator, emitting macroscopic polarization correlations.
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
