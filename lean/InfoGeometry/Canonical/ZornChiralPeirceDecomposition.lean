import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.ZornCliffordRepresentation
import Mathlib.Tactic

/-!
# Chiral Peirce decomposition of canonical Zorn matrices

This owner connects the already-proved Peirce projections in `ZornSpinor` to
the three explicit upper and lower vector coordinate generators.  It is a
coordinate theorem over an arbitrary commutative ring; it does not add
associativity to the Zorn carrier.
-/

namespace InfoGeometry.Canonical

open ZornMatrix
open ZornClifford

variable {R : Type*} [CommRing R]

def chiralUpperBasis (i : Fin 3) : ZornMatrix R :=
  { a := 0, b := 0, x := Pi.single i 1, y := 0 }

def chiralLowerBasis (i : Fin 3) : ZornMatrix R :=
  { a := 0, b := 0, x := 0, y := Pi.single i 1 }

theorem colorProject_eq_chiralUpper_sum (Z : ZornMatrix R) :
    colorProject Z = ∑ i : Fin 3, Z.x i • chiralUpperBasis i := by
  rw [colorProject_apply]
  cases Z with
  | mk a b x y =>
      apply ZornMatrix.ext
      · simp [chiralUpperBasis, Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b]
      · simp [chiralUpperBasis, Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b]
      · funext c
        fin_cases c <;>
          simp [chiralUpperBasis, Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y]
      · funext c
        fin_cases c <;>
          simp [chiralUpperBasis, Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y]

theorem anticolorProject_eq_chiralLower_sum (Z : ZornMatrix R) :
    anticolorProject Z = ∑ i : Fin 3, Z.y i • chiralLowerBasis i := by
  rw [anticolorProject_apply]
  cases Z with
  | mk a b x y =>
      apply ZornMatrix.ext
      · simp [chiralLowerBasis, Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b]
      · simp [chiralLowerBasis, Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b]
      · funext c
        fin_cases c <;>
          simp [chiralLowerBasis, Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y]
      · funext c
        fin_cases c <;>
          simp [chiralLowerBasis, Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y]

theorem peircePlusPlus_eq_scalar_chiralPlus (Z : ZornMatrix R) :
    peirceComponent zornPlus zornPlus Z = Z.a • zornPlus := by
  rw [peirce_plus_plus_apply]
  cases Z with
  | mk a b x y =>
      apply ZornMatrix.ext
      · simp [zornPlus, InfoGeometry.Canonical.ZornMatrix.smul_a]
      · simp [zornPlus, InfoGeometry.Canonical.ZornMatrix.smul_b]
      · funext c; fin_cases c <;> simp [zornPlus, InfoGeometry.Canonical.ZornMatrix.smul_x]
      · funext c; fin_cases c <;> simp [zornPlus, InfoGeometry.Canonical.ZornMatrix.smul_y]

theorem peirceMinusMinus_eq_scalar_chiralMinus (Z : ZornMatrix R) :
    peirceComponent zornMinus zornMinus Z = Z.b • zornMinus := by
  rw [peirce_minus_minus_apply]
  cases Z with
  | mk a b x y =>
      apply ZornMatrix.ext
      · simp [zornMinus, InfoGeometry.Canonical.ZornMatrix.smul_a]
      · simp [zornMinus, InfoGeometry.Canonical.ZornMatrix.smul_b]
      · funext c; fin_cases c <;> simp [zornMinus, InfoGeometry.Canonical.ZornMatrix.smul_x]
      · funext c; fin_cases c <;> simp [zornMinus, InfoGeometry.Canonical.ZornMatrix.smul_y]

theorem zorn_chiral_peirce_decomposition (Z : ZornMatrix R) :
    Z = Z.a • zornPlus + Z.b • zornMinus +
      (∑ i : Fin 3, Z.x i • chiralUpperBasis i) +
      (∑ i : Fin 3, Z.y i • chiralLowerBasis i) := by
  cases Z with
  | mk a b x y =>
      apply ZornMatrix.ext
      · simp [chiralUpperBasis, chiralLowerBasis, zornPlus, zornMinus,
          Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b, InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y]
      · simp [chiralUpperBasis, chiralLowerBasis, zornPlus, zornMinus,
          Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b, InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y]
      · funext c
        fin_cases c <;>
          simp [chiralUpperBasis, chiralLowerBasis, zornPlus, zornMinus,
            Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b, InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y]
      · funext c
        fin_cases c <;>
          simp [chiralUpperBasis, chiralLowerBasis, zornPlus, zornMinus,
            Fin.sum_univ_three, InfoGeometry.Canonical.ZornMatrix.smul_a, InfoGeometry.Canonical.ZornMatrix.smul_b, InfoGeometry.Canonical.ZornMatrix.smul_x, InfoGeometry.Canonical.ZornMatrix.smul_y]

/--
Left-ideal / upper-chiral reconstruction, exposed under the user-facing name
used in the split-octonion basis-change discussion.
-/
theorem leftIdeal_eq_sigmaPlus_span (Z : ZornMatrix R) :
    colorProject Z = ∑ i : Fin 3, Z.x i • chiralUpperBasis i := by
  simpa using colorProject_eq_chiralUpper_sum (R := R) Z

/--
Right-ideal / lower-chiral reconstruction, exposed under the user-facing name
used in the split-octonion basis-change discussion.
-/
theorem rightIdeal_eq_sigmaMinus_span (Z : ZornMatrix R) :
    anticolorProject Z = ∑ i : Fin 3, Z.y i • chiralLowerBasis i := by
  simpa using anticolorProject_eq_chiralLower_sum (R := R) Z

/-- Full Peirce-style chiral decomposition in the standard Zorn coordinates. -/
theorem peirce_decomposition_chiral_basis (Z : ZornMatrix R) :
    Z = Z.a • zornPlus + Z.b • zornMinus +
      (∑ i : Fin 3, Z.x i • chiralUpperBasis i) +
      (∑ i : Fin 3, Z.y i • chiralLowerBasis i) := by
  simpa using zorn_chiral_peirce_decomposition (R := R) Z

/-! ## Representation readout in the same chiral basis -/

/--
The native Clifford/soldering representation respects the chiral Peirce
coordinates.  This is a basis-specialization of its linearity, not a second
operator carrier or a new algebra structure on the Zorn matrices.
-/
theorem diracGammaLinear_chiral_decomposition (Z : ZornMatrix R) :
    diracGammaLinear Z =
      Z.a • diracGammaLinear zornPlus +
      Z.b • diracGammaLinear zornMinus +
        (∑ i : Fin 3, Z.x i • diracGammaLinear (chiralUpperBasis i)) +
        (∑ i : Fin 3, Z.y i • diracGammaLinear (chiralLowerBasis i)) := by
  have hZ := zorn_chiral_peirce_decomposition (R := R) Z
  calc
    diracGammaLinear Z =
        diracGammaLinear
          (Z.a • zornPlus + Z.b • zornMinus +
            (∑ i : Fin 3, Z.x i • chiralUpperBasis i) +
            (∑ i : Fin 3, Z.y i • chiralLowerBasis i)) :=
      congrArg diracGammaLinear hZ
    _ = _ := by simp only [map_add, map_smul, map_sum]

end InfoGeometry.Canonical
