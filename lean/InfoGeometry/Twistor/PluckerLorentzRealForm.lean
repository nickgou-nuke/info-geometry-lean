/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PluckerInfinityChart
import InfoGeometry.Bridge.ZornConformalSixConeBridge

/-!
# The Lorentzian real form in the Plücker graph convention

The existing real `ConformalSix` carrier has quadratic polynomial of signature
`(2,4)`. This file maps that carrier injectively into the complex Klein
coordinates in the graph convention and proves `kleinQ = -quadratic24`.
The normalized affine slice is exactly the existing Hermitian Pauli matrix,
whose determinant gives the real Minkowski interval of signature `(1,3)`.

This is a specified real slice of a complex quadric. Six independently real
Plücker coordinates instead give the split real form; choosing an infinity
twistor does not change that signature. No compactification homeomorphism or
identification of real conformal groups is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.PluckerLorentzRealForm

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Twistor.PluckerInfinityChart
open InfoGeometry.Bridge.ZornConformalSixCone
open InfoGeometry.Canonical.PauliHestenesSpinMomentum

/-- Lorentzian conjugation in this six-coordinate graph convention. -/
def lorentzConjugation (P : Plucker6 ℂ) : Plucker6 ℂ :=
  ⟨star P.p01, -star P.p13, star P.p03,
    star P.p12, -star P.p02, star P.p23⟩

@[simp] theorem lorentzConjugation_involutive (P : Plucker6 ℂ) :
    lorentzConjugation (lorentzConjugation P) = P := by
  apply Plucker6.ext <;> simp [lorentzConjugation]

/-- Real `(2,4)` coordinates in the complex Klein carrier. -/
def lorentzPlucker (X : ConformalSix) : Plucker6 ℂ where
  p01 := ((X.b0 - X.bz : ℝ) : ℂ)
  p02 := ⟨-X.ax, X.ay⟩
  p03 := ((X.a0 + X.az : ℝ) : ℂ)
  p12 := ((-X.a0 + X.az : ℝ) : ℂ)
  p13 := ⟨X.ax, X.ay⟩
  p23 := ((X.b0 + X.bz : ℝ) : ℂ)

/-- Recover all six real coordinates; no real degree of freedom is discarded. -/
def lorentzReadback (P : Plucker6 ℂ) : ConformalSix where
  a0 := (P.p03.re - P.p12.re) / 2
  ax := P.p13.re
  ay := P.p13.im
  az := (P.p03.re + P.p12.re) / 2
  b0 := (P.p01.re + P.p23.re) / 2
  bz := (P.p23.re - P.p01.re) / 2

@[simp] theorem lorentzReadback_lorentzPlucker (X : ConformalSix) :
    lorentzReadback (lorentzPlucker X) = X := by
  cases X
  simp only [lorentzReadback, lorentzPlucker, Complex.ofReal_re]
  congr 1 <;> ring

theorem lorentzPlucker_injective : Function.Injective lorentzPlucker :=
  Function.LeftInverse.injective lorentzReadback_lorentzPlucker

@[simp] theorem lorentzConjugation_lorentzPlucker (X : ConformalSix) :
    lorentzConjugation (lorentzPlucker X) = lorentzPlucker X := by
  apply Plucker6.ext <;> apply Complex.ext <;>
    simp [lorentzConjugation, lorentzPlucker]

/-- The quadratic identity fixes both the real form and its overall sign. -/
theorem kleinQ_lorentzPlucker (X : ConformalSix) :
    kleinQ (lorentzPlucker X) = -(quadratic24 X : ℂ) := by
  apply Complex.ext <;>
    simp [kleinQ, lorentzPlucker, quadratic24, pow_two] <;> ring

/-- The existing Dirac-cone affine embedding is the actual Pauli graph frame,
with precisely its homogeneous scale `κ`. -/
theorem lorentzPlucker_diracConeEmbedding (κ : ℝ) (P : PauliParavector) :
    lorentzPlucker (diracConeEmbedding κ P) =
      Plucker6.scale (κ : ℂ) (graphPlucker P.pauliMatrix) := by
  apply Plucker6.ext
  all_goals
    simp only [lorentzPlucker, diracConeEmbedding, Plucker6.scale,
      graphPlucker_coordinates]
  · rw [P.det_pauliMatrix_eq_minkowskiNormSq]
    push_cast
    ring
  all_goals
    apply Complex.ext <;>
      simp [PauliParavector.pauliMatrix] <;> ring

@[simp] theorem lorentzPlucker_diracConeEmbedding_one (P : PauliParavector) :
    lorentzPlucker (diracConeEmbedding 1 P) = graphPlucker P.pauliMatrix := by
  rw [lorentzPlucker_diracConeEmbedding]
  apply Plucker6.ext <;> simp [Plucker6.scale]

theorem pauliMatrix_difference (P Q : PauliParavector) :
    P.pauliMatrix - Q.pauliMatrix =
      (PauliParavector.mk (P.energy - Q.energy) (P.px - Q.px)
        (P.py - Q.py) (P.pz - Q.pz)).pauliMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PauliParavector.pauliMatrix] <;> ring

/-- The normalized projective pairing is exactly the mostly-minus interval. -/
theorem normalizedInterval_pauli (P Q : PauliParavector) :
    normalizedInterval (graphPlucker P.pauliMatrix) (graphPlucker Q.pauliMatrix) =
      (((P.energy - Q.energy) ^ 2 - (P.px - Q.px) ^ 2 -
        (P.py - Q.py) ^ 2 - (P.pz - Q.pz) ^ 2 : ℝ) : ℂ) := by
  rw [normalizedInterval_graphPlucker, pauliMatrix_difference,
    PauliParavector.det_pauliMatrix_eq_minkowskiNormSq]
  rfl

/-- Independent nonzero homogeneous scales cancel from the Lorentzian interval. -/
theorem normalizedInterval_diracConeEmbedding (κ μ : ℝ)
    (hκ : κ ≠ 0) (hμ : μ ≠ 0) (P Q : PauliParavector) :
    normalizedInterval (lorentzPlucker (diracConeEmbedding κ P))
        (lorentzPlucker (diracConeEmbedding μ Q)) =
      (((P.energy - Q.energy) ^ 2 - (P.px - Q.px) ^ 2 -
        (P.py - Q.py) ^ 2 - (P.pz - Q.pz) ^ 2 : ℝ) : ℂ) := by
  rw [lorentzPlucker_diracConeEmbedding, lorentzPlucker_diracConeEmbedding,
    normalizedInterval_scale _ _ (Complex.ofReal_ne_zero.mpr hκ)
      (Complex.ofReal_ne_zero.mpr hμ) _ _ (by simp) (by simp),
    normalizedInterval_pauli]

end InfoGeometry.Twistor.PluckerLorentzRealForm
