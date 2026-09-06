/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Algebra.Zorn.G2PositiveRootsInvariance

namespace InfoGeometry.Exceptional.G2PhaseInvariantComplement

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2Roots

theorem s1Root_positive_of_complement (r : G2CoordinateRoot)
    (hr : r.1 ∈ phiPlusWithoutAlpha1) :
    isPositive (s1Root r) := by
  have himage : s1 r.1 ∈ phiPlusWithoutAlpha1 := by
    rw [← s1_image_complement]
    exact Finset.mem_image_of_mem s1 hr
  dsimp [phiPlusWithoutAlpha1] at himage
  simp only [Finset.mem_insert, Finset.mem_singleton] at himage
  dsimp [isPositive, phiPlus]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hs1 : (s1Root r).1 = s1 r.1 := rfl
  rw [hs1]
  rcases himage with h | h | h | h | h
  · rw [h]; right; left; rfl
  · rw [h]; right; right; left; rfl
  · rw [h]; right; right; right; left; rfl
  · rw [h]; right; right; right; right; left; rfl
  · rw [h]; right; right; right; right; right; rfl

theorem s2Root_positive_of_complement (r : G2CoordinateRoot)
    (hr : r.1 ∈ phiPlusWithoutAlpha2) :
    isPositive (s2Root r) := by
  have himage : s2 r.1 ∈ phiPlusWithoutAlpha2 := by
    rw [← s2_image_complement]
    exact Finset.mem_image_of_mem s2 hr
  dsimp [phiPlusWithoutAlpha2] at himage
  simp only [Finset.mem_insert, Finset.mem_singleton] at himage
  dsimp [isPositive, phiPlus]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hs2 : (s2Root r).1 = s2 r.1 := rfl
  rw [hs2]
  rcases himage with h | h | h | h | h
  · rw [h]; left; rfl
  · rw [h]; right; right; left; rfl
  · rw [h]; right; right; right; left; rfl
  · rw [h]; right; right; right; right; left; rfl
  · rw [h]; right; right; right; right; right; rfl

end InfoGeometry.Exceptional.G2PhaseInvariantComplement
