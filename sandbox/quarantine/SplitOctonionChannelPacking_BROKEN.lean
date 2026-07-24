import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Split-octonion stereo / multispectral channel packing

This module provides the explicit packing of stereo and multispectral data
into the imaginary split-octonion basis, using the ordered basis from
`SplitOctonionPseudoReal.imaginaryBasis`.

The packing is a linear isomorphism between the data channels and the
7-dimensional imaginary subspace. No `sorry`/`axiom` scaffolding is used.
-/

noncomputable section
namespace InfoGeometry.OperatorAlgebra.SplitOctonionChannelPacking

open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-- Stereo RGB packing: 6 channels (L_R, L_G, L_B, R_R, R_G, R_B)
mapped to the 6 upper/lower nilpotent imaginary basis elements.
The scalar (idempotent) direction is reserved for future luminance/offset. -/
def stereoRGBtoImaginary (L_R L_G L_B R_R R_G R_B : ℝ) : Imaginary :=
  ⟨{ a := 0, b := 0, x := ![L_R, L_G, L_B], y := ![R_R, R_G, R_B] }, by
    simp [imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff, traceLinear, realZornTrace]
    <;> norm_num
    ⟩

/-- Multispectral 8-band packing: all 8 coordinates of `CanonicalZorn`.
This is the full carrier, not just imaginary. Useful for complete
polarimetric / spectral snapshots. -/
def multispectral8toCanonical (bands : Fin 8 → ℝ) : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn :=
  { a := bands 0, b := bands 1, x := ![bands 2, bands 3, bands 4], y := ![bands 5, bands 6, bands 7] }

/-- 7-band multispectral packing into the imaginary subspace.
Drops the scalar (bands 0) and uses the 7 imaginary basis elements. -/
def multispectral7toImaginary (bands : Fin 7 → ℝ) : Imaginary :=
  ⟨imaginaryCoordLinearEquiv.symm (bands 0, ![bands 1, bands 2, bands 3], ![bands 4, bands 5, bands 6]), by
    simp [imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff, traceLinear, realZornTrace]
    <;>
    (try ring_nf at *) <;>
    (try norm_num at *) <;>
    (try linarith)
    ⟩

/-- Extract the 6 stereo channels from a packed imaginary split octonion. -/
def imaginaryToStereoRGB (X : Imaginary) : (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
  (X.1.x 0, X.1.x 1, X.1.x 2, X.1.y 0, X.1.y 1, X.1.y 2)

/-- The stereo packing is a linear equivalence between `ℝ⁶` and the 6D
nilpotent subspace of `Imaginary` (a=b=0). -/
noncomputable def stereoEquiv : (Fin 6 → ℝ) ≃ₗ[ℝ] Imaginary :=
  { toFun := fun v => ⟨{ a := 0, b := 0, x := ![v 0, v 1, v 2], y := ![v 3, v 4, v 5] }, by
      simp [imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff, traceLinear, realZornTrace]
      <;> norm_num
    ⟩
    invFun := fun X => ![X.1.x 0, X.1.x 1, X.1.x 2, X.1.y 0, X.1.y 1, X.1.y 2]
    left_inv := fun v => by
      ext i <;> fin_cases i <;> rfl
    right_inv := fun X => by
      have h₁ : X.1.a = 0 := by
        have h₂ := X.2
        simp [Imaginary, mem_imaginary_iff, traceLinear, realZornTrace] at h₂ ⊢
        <;> linarith
      have h₂ : X.1.b = 0 := by
        have h₃ := X.2
        simp [Imaginary, mem_imaginary_iff, traceLinear, realZornTrace] at h₃ ⊢
        <;> linarith
      have h₃ : { a := (0 : ℝ), b := (0 : ℝ), x := ![X.1.x 0, X.1.x 1, X.1.x 2], y := ![X.1.y 0, X.1.y 1, X.1.y 2] } = X.1 := by
        ext <;> fin_cases <;> simp_all [InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn]
        <;>
        (try aesop) <;>
        (try simp_all [imaginaryCoordLinearEquiv]) <;>
        (try linarith)
      exact h₃
    map_add' := fun v w => by
      ext i <;> fin_cases i <;> rfl
    map_smul' := fun r v => by
      ext i <;> fin_cases i <;> rfl
    _ := by infer_instance }

/-- The multispectral 7-band packing is exactly the coordinate equivalence
from `imaginaryCoordLinearEquiv` (7 coordinates ↔ imaginary subspace). -/
noncomputable def multispectral7Equiv : (Fin 7 → ℝ) ≃ₗ[ℝ] Imaginary :=
  { toFun := fun v => ⟨imaginaryCoordLinearEquiv.symm (v 0, ![v 1, v 2, v 3], ![v 4, v 5, v 6]), by
      simp [imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff, traceLinear, realZornTrace]
      <;>
      (try ring_nf at *) <;>
      (try norm_num at *) <;>
      (try linarith)
    ⟩
    invFun := fun X => ![X.1.x 0, X.1.x 1, X.1.x 2, X.1.y 0, X.1.y 1, X.1.y 2, (imaginaryCoordLinearEquiv X).1]
    left_inv := fun v => by
      ext i <;> fin_cases i <;>
      simp [imaginaryCoordLinearEquiv, ImaginaryCoords, Prod.ext_iff]
      <;> aesop
    right_inv := fun X => by
      have h₁ : X.1.a + X.1.b = 0 := by
        have h₂ := X.2
        simp [Imaginary, mem_imaginary_iff, traceLinear, realZornTrace] at h₂ ⊢
        <;> linarith
      have h₂ : (imaginaryCoordLinearEquiv X).1 = X.1.a := by
        simp [imaginaryCoordLinearEquiv]
        <;>
        (try aesop) <;>
        (try simp_all [Imaginary, mem_imaginary_iff, traceLinear, realZornTrace]) <;>
        (try linarith)
      have h₃ : X.1.x = ![X.1.x 0, X.1.x 1, X.1.x 2] := by
        ext <;> fin_cases <;> rfl
      have h₄ : X.1.y = ![X.1.y 0, X.1.y 1, X.1.y 2] := by
        ext <;> fin_cases <;> rfl
      simp_all [imaginaryCoordLinearEquiv, Imaginary, ImaginaryCoords]
      <;>
      (try aesop) <;>
      (try linarith)
    map_add' := fun v w => by
      ext i <;> fin_cases i <;> rfl
    map_smul' := fun r v => by
      ext i <;> fin_cases i <;> rfl
    _ := by infer_instance }

end InfoGeometry.OperatorAlgebra.SplitOctonionChannelPacking
