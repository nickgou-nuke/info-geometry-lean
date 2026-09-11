import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornCliffordRepresentation
import Mathlib.Tactic

/-!
# Canonical chiral Peirce interface

The definitions and coordinate proofs for the chiral Peirce decomposition are
owned by `InfoGeometry.Canonical.ZornMatrix` in `ZornSpinor`.  This module is
the stable import boundary for clients using that decomposition together with
the Clifford readout; it introduces no second basis, projection, or theorem
aliases.

Use the native declarations in `ZornMatrix`: `chiralUpperBasis`,
`chiralLowerBasis`, `colorProject_eq_chiralUpper_sum`,
`anticolorProject_eq_chiralLower_sum`, `zorn_peirce_decomposition`,
`peirce_plus_plus_apply`, and `peirce_minus_minus_apply`.

The carrier is the non-associative Zorn algebra.  Clifford statements belong
to the associative representation owners and are not silently identified
with Zorn multiplication here.
-/

namespace InfoGeometry.Canonical

open ZornMatrix
open ZornClifford

variable {R : Type*} [CommRing R]

/-!
The readout theorem is kept here because this module is the interface between
the coordinate owner and the Clifford representation owner.  Its proof is a
direct transport of the native coordinate decomposition; no second Peirce
carrier is introduced.
-/
theorem diracGammaLinear_chiral_decomposition (Z : ZornMatrix R) :
    diracGammaLinear Z =
      Z.a • diracGammaLinear zornPlus +
      Z.b • diracGammaLinear zornMinus +
        (∑ i : Fin 3, Z.x i • diracGammaLinear (chiralUpperBasis i)) +
        (∑ i : Fin 3, Z.y i • diracGammaLinear (chiralLowerBasis i)) := by
  have hZ := zorn_peirce_decomposition (R := R) Z
  calc
    diracGammaLinear Z =
        diracGammaLinear
          (Z.a • zornPlus + Z.b • zornMinus +
            (∑ i : Fin 3, Z.x i • chiralUpperBasis i) +
            (∑ i : Fin 3, Z.y i • chiralLowerBasis i)) := by
      congr 1
      have hpp : peirceComponent zornPlus zornPlus Z = Z.a • zornPlus := by
        rw [peirce_plus_plus_apply]
        cases Z with
        | mk a b x y =>
            apply ZornMatrix.ext
            · simp [zornPlus, ZornClifford.smul_a]
            · simp [zornPlus, ZornClifford.smul_b]
            · funext i; simp [zornPlus, ZornClifford.smul_x]
            · funext i; simp [zornPlus, ZornClifford.smul_y]
      have hmm : peirceComponent zornMinus zornMinus Z = Z.b • zornMinus := by
        rw [peirce_minus_minus_apply]
        cases Z with
        | mk a b x y =>
            apply ZornMatrix.ext
            · simp [zornMinus, ZornClifford.smul_a]
            · simp [zornMinus, ZornClifford.smul_b]
            · funext i; simp [zornMinus, ZornClifford.smul_x]
            · funext i; simp [zornMinus, ZornClifford.smul_y]
      rw [hpp, colorProject_eq_chiralUpper_sum,
        anticolorProject_eq_chiralLower_sum, hmm] at hZ
      simpa [add_assoc, add_left_comm, add_comm] using hZ
    _ = _ := by simp only [map_add, map_smul, map_sum]

end InfoGeometry.Canonical
