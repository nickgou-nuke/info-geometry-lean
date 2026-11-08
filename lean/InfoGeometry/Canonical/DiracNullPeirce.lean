/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevSpinorSolder

/-! Normalized null spinors supply the same reflexive operator laws used by
the Zorn null-pair and Weyl owners, with the sesquilinear Dirac bra retained. -/
noncomputable section
namespace InfoGeometry.Canonical.DiracNullPeirce
open Matrix ReflexiveNilpotentFlows
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open SpinorialCore.Krein
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem solder_product (J : Matrix n n ℂ) (x y z w : n → ℂ) :
    solder J x y * solder J z w =
      (SpinorialCore.Krein.pairing J y z) • solder J x w := by
  simpa only [SpinorialCore.Krein.pairing, dotProduct_mulVec, diracRow]
    using solder_fierz_product J x y z w

theorem null_solder_square (J : Matrix n n ℂ) (x : n → ℂ)
    (hx : SpinorialCore.Krein.pairing J x x = 0) :
    solder J x x * solder J x x = 0 := by
  rw [solder_product, hx, zero_smul]

theorem solder_reflexive (J : Matrix n n ℂ) (x y : n → ℂ)
    (hxy : SpinorialCore.Krein.pairing J x y = 1)
    (hyx : SpinorialCore.Krein.pairing J y x = 1) :
    solder J x x * solder J y y * solder J x x = solder J x x := by
  rw [solder_product, hxy, one_smul, solder_product, hyx, one_smul]

/-- Harmonic completion gives an actual ambient unit even for proper support. -/
def nullSolderWeylUnit (J : Matrix n n ℂ) (x y : n → ℂ)
    (hx : SpinorialCore.Krein.pairing J x x = 0)
    (hy : SpinorialCore.Krein.pairing J y y = 0)
    (hxy : SpinorialCore.Krein.pairing J x y = 1)
    (hyx : SpinorialCore.Krein.pairing J y x = 1) : (Matrix n n ℂ)ˣ :=
  weylUnit (null_solder_square J x hx) (null_solder_square J y hy)
    (solder_reflexive J x y hxy hyx)

theorem null_solder_weyl_exchange (J : Matrix n n ℂ) (x y : n → ℂ)
    (hx : SpinorialCore.Krein.pairing J x x = 0)
    (hy : SpinorialCore.Krein.pairing J y y = 0)
    (hxy : SpinorialCore.Krein.pairing J x y = 1)
    (hyx : SpinorialCore.Krein.pairing J y x = 1) :
    weyl (solder J x x) (solder J y y) ^ 4 = 1 ∧
    weyl (solder J x x) (solder J y y) * solder J x x *
      weylInv (solder J x x) (solder J y y) = -solder J y y := by
  exact ⟨weyl_fourth (null_solder_square J x hx) (null_solder_square J y hy)
    (solder_reflexive J x y hxy hyx) (solder_reflexive J y x hyx hxy),
    weyl_swap_d (null_solder_square J x hx) (solder_reflexive J x y hxy hyx)
      (solder_reflexive J y x hyx hxy)⟩

theorem normalized_support_trace (J : Matrix n n ℂ) (x y : n → ℂ)
    (hxy : SpinorialCore.Krein.pairing J x y = 1)
    (hyx : SpinorialCore.Krein.pairing J y x = 1) :
    Matrix.trace (support (solder J x x) (solder J y y)) = 2 := by
  unfold support
  rw [solder_product, solder_product, hxy, hyx, one_smul, one_smul, Matrix.trace_add]
  have ht (a b : n → ℂ) : Matrix.trace (solder J a b) =
      SpinorialCore.Krein.pairing J b a := by
    simp only [solder, Matrix.trace_vecMulVec, diracRow,
      SpinorialCore.Krein.pairing, dotProduct_mulVec]
    exact dotProduct_comm _ _
  rw [ht, ht, hyx, hxy]
  norm_num

end InfoGeometry.Canonical.DiracNullPeirce
