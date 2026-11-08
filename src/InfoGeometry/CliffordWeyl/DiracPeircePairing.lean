/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceMatrixTracePairing
import InfoGeometry.Physics.KreinDiracKasparovSpinorBilinear

/-! Dirac adjunction exchanges opposite Peirce components. Matrix trace
separation consequently detects zero within each component after adjunction.
The trace expression is generally sesquilinear; positivity and properness
of the star operation are not assumed.
-/
namespace InfoGeometry.Physics.KasparovKreinData
open InfoGeometry.Core.PeirceDecomposition

section Ring
variable {A : Type*} [Ring A] [StarRing A] (K : KasparovKreinData A)

theorem diracAdjoint_complement (P : A) :
    K.diracAdjoint (complementIdempotent P) = 1 - K.diracAdjoint P := by
  have hη : K.eta * K.eta = 1 := K.2.1
  simp only [complementIdempotent, diracAdjoint, star_sub, star_one,
    mul_sub, mul_one, sub_mul, hη]

theorem diracAdjoint_component10 (P X : A) :
    K.diracAdjoint (component10 P X) =
      component01 (K.diracAdjoint P) (K.diracAdjoint X) := by
  unfold component10 component01
  rw [diracAdjoint_mul, diracAdjoint_mul, diracAdjoint_complement]
  simp only [complementIdempotent, mul_assoc]

theorem diracAdjoint_component01 (P X : A) :
    K.diracAdjoint (component01 P X) =
      component10 (K.diracAdjoint P) (K.diracAdjoint X) := by
  unfold component10 component01
  rw [diracAdjoint_mul, diracAdjoint_mul, diracAdjoint_complement]
  simp only [complementIdempotent, mul_assoc]

end Ring

section Matrix
variable {R n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]
variable (K : KasparovKreinData (Matrix n n R))

theorem component10_eq_zero_of_dirac_trace_pairing (P X : Matrix n n R)
    (hP : K.diracAdjoint P = P) (hX : component10 P X = X)
    (h : ∀ Y, Matrix.trace (X * K.diracAdjoint (component10 P Y)) = 0) : X = 0 := by
  apply component10_eq_zero_of_trace_pairing P X hX
  intro Y
  have hy := h (K.diracAdjoint Y)
  rw [diracAdjoint_component10, hP, diracAdjoint_involution] at hy
  exact hy

theorem component01_eq_zero_of_dirac_trace_pairing (P X : Matrix n n R)
    (hP : K.diracAdjoint P = P) (hX : component01 P X = X)
    (h : ∀ Y, Matrix.trace (X * K.diracAdjoint (component01 P Y)) = 0) : X = 0 := by
  apply component01_eq_zero_of_trace_pairing P X hX
  intro Y
  have hy := h (K.diracAdjoint Y)
  rw [diracAdjoint_component01, hP, diracAdjoint_involution] at hy
  exact hy

end Matrix
end InfoGeometry.Physics.KasparovKreinData
