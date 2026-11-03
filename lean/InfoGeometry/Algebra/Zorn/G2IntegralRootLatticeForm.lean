/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2IntegralWeylLatticeAction

/-!
# The integral symmetrized Cartan form of the `G₂` root lattice

In simple-root coordinates, the short and long simple roots have squared
lengths `2` and `6`, with mutual pairing `-3`. The associated integral
symmetric bilinear form is preserved by both simple Weyl reflections.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntegralRootLatticeForm

open InfoGeometry.Algebra.Zorn.G2IntegralWeylLatticeAction
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2Roots

/-- The integral symmetrized Cartan pairing in the ordered simple-root basis
`(α₁, α₂)`, with Gram matrix `[[2, -3], [-3, 6]]`. -/
def cartanPairing (v w : ℤ × ℤ) : ℤ :=
  2 * v.1 * w.1 - 3 * v.1 * w.2 - 3 * v.2 * w.1 + 6 * v.2 * w.2

/-- The associated integral squared-length form. -/
def rootNorm (v : ℤ × ℤ) : ℤ := cartanPairing v v

theorem cartanPairing_symmetric (v w : ℤ × ℤ) :
    cartanPairing v w = cartanPairing w v := by
  rcases v with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  simp [cartanPairing]
  ring

theorem cartanPairing_simpleReflectionOne (v w : ℤ × ℤ) :
    cartanPairing (simpleReflectionOne v) (simpleReflectionOne w) =
      cartanPairing v w := by
  rcases v with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  simp [cartanPairing, simpleReflectionOne, s1]
  ring

theorem cartanPairing_simpleReflectionTwo (v w : ℤ × ℤ) :
    cartanPairing (simpleReflectionTwo v) (simpleReflectionTwo w) =
      cartanPairing v w := by
  rcases v with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  simp [cartanPairing, simpleReflectionTwo, s2]
  ring

theorem rootNorm_simpleReflectionOne (v : ℤ × ℤ) :
    rootNorm (simpleReflectionOne v) = rootNorm v := by
  exact congrArg (fun z : ℤ => z) (cartanPairing_simpleReflectionOne v v)

theorem rootNorm_simpleReflectionTwo (v : ℤ × ℤ) :
    rootNorm (simpleReflectionTwo v) = rootNorm v := by
  exact congrArg (fun z : ℤ => z) (cartanPairing_simpleReflectionTwo v v)

theorem simpleRoot_norms :
    rootNorm (1, 0) = 2 ∧ rootNorm (0, 1) = 6 ∧
      cartanPairing (1, 0) (0, 1) = -3 := by
  norm_num [rootNorm, cartanPairing]

theorem positiveRoot_norms :
    rootNorm (rootCoordinates .alpha) = 2 ∧
    rootNorm (rootCoordinates .alpha_add_beta) = 2 ∧
    rootNorm (rootCoordinates .two_alpha_beta) = 2 ∧
    rootNorm (rootCoordinates .beta) = 6 ∧
    rootNorm (rootCoordinates .three_alpha_beta) = 6 ∧
    rootNorm (rootCoordinates .three_alpha_two_beta) = 6 := by
  norm_num [rootNorm, cartanPairing, rootCoordinates]

theorem signedRoot_norm_preserved
    (r : Bool × InfoGeometry.Algebra.Zorn.G2Combinatorics.G2PositiveRoot) :
    rootNorm (signedRootCoordinate r).1 =
      rootNorm (rootCoordinates r.2) := by
  rcases r with ⟨sign, α⟩
  cases sign <;> simp [signedRootCoordinate, positiveRootInFullCarrier,
    rootNorm, cartanPairing, rootCoordinates]

end InfoGeometry.Algebra.Zorn.G2IntegralRootLatticeForm
