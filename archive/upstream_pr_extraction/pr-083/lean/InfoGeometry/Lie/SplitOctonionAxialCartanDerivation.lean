import InfoGeometry.Lie.SplitOctonionAxialDrazinDefect
import InfoGeometry.Lie.CanonicalZornDerivation

/-!
# Traceless axial Cartan derivations of the canonical split octonions

The uniform signed tripotent grading and a multiplication-preserving Cartan
flow are different operators.  This file proves both sides of that boundary:

* the uniform grading is not a derivation, by a concrete cross-color product;
* coordinate weights `k : Fin 3 → ℝ` define a genuine derivation when
  `∑ i, k i = 0`.

The traceless condition is derived into the Leibniz proof from the native Zorn
cross-product formula; it is not stored as an assumed derivation witness.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialCartanDerivation

open scoped BigOperators
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
open InfoGeometry.Lie.SplitOctonionAxialDrazinDefect
open InfoGeometry.Singular.Drazin

abbrev CZ := ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

attribute [local simp] Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero
  Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_succ
  Pi.smul_apply Pi.add_apply Pi.sub_apply Pi.neg_apply

/-- Coordinate-weighted axial endomorphism: upper and lower vector slots have
opposite weights, while the two diagonal coordinates are fixed. -/
def axialCartanEnd (k : Fin 3 → ℝ) : EndCZ where
  toFun Z :=
    { a := 0
      b := 0
      x := fun i => k i * Z.x i
      y := fun i => -(k i) * Z.y i }
  map_add' X Y := by
    ext i <;> simp [ZornMatrix.add_def] <;> ring
  map_smul' r X := by
    ext i <;> simp [Equiv.smul_def, coordEquiv] <;> ring

@[simp] theorem axialCartanEnd_apply (k : Fin 3 → ℝ) (Z : CZ) :
    axialCartanEnd k Z =
      { a := 0
        b := 0
        x := fun i => k i * Z.x i
        y := fun i => -(k i) * Z.y i } :=
  rfl

/-- The uniform tripotent grading is not a derivation of the split-octonion
multiplication. -/
theorem axialGrading_not_derivation : ¬ IsDerivation axialGrading := by
  intro h
  have h01 := h (chiralUpperBasis (R := ℝ) 0) (chiralUpperBasis (R := ℝ) 1)
  have hy := congrArg (fun Z : CZ => Z.y 2) h01
  norm_num [axialGrading, chiralUpperBasis, ZornMatrix.mul_def,
    ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
    Equiv.smul_def, coordEquiv] at hy

/-- Traceless coordinate weights satisfy the native Zorn Leibniz law. -/
theorem axialCartanEnd_isDerivation
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) :
    IsDerivation (axialCartanEnd k) := by
  have hsum : k 0 + k 1 + k 2 = 0 := by
    simpa [Fin.sum_univ_three] using hk
  have hk0 : k 0 = -(k 1 + k 2) := by linarith
  have hk1 : k 1 = -(k 0 + k 2) := by linarith
  have hk2 : k 2 = -(k 0 + k 1) := by linarith
  intro X Y
  cases X
  cases Y
  ext i
  · simp [axialCartanEnd, ZornMatrix.mul, ZornMatrix.dot,
      ZornMatrix.cross]
    ring
  · simp [axialCartanEnd, ZornMatrix.mul, ZornMatrix.dot,
      ZornMatrix.cross]
    ring
  · fin_cases i
    · simp [axialCartanEnd, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross, hk0]
      ring
    · simp [axialCartanEnd, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross, hk1]
      ring
    · simp [axialCartanEnd, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross, hk2]
      ring
  · fin_cases i
    · simp [axialCartanEnd, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross, hk0]
      ring
    · simp [axialCartanEnd, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross, hk1]
      ring
    · simp [axialCartanEnd, ZornMatrix.mul, ZornMatrix.dot,
        ZornMatrix.cross, hk2]
      ring

/-! ## Native weight readout on the circular root generators -/

@[simp] theorem axialCartanEnd_chiralUpperBasis
    (k : Fin 3 → ℝ) (i : Fin 3) :
    axialCartanEnd k (chiralUpperBasis i) =
      k i • chiralUpperBasis i := by
  ext j <;>
    simp [axialCartanEnd, chiralUpperBasis, Equiv.smul_def, coordEquiv,
      Pi.single_apply]
  all_goals fin_cases i <;> fin_cases j <;> norm_num

@[simp] theorem axialCartanEnd_chiralLowerBasis
    (k : Fin 3 → ℝ) (i : Fin 3) :
    axialCartanEnd k (chiralLowerBasis i) =
      -(k i) • chiralLowerBasis i := by
  ext j <;>
    simp [axialCartanEnd, chiralLowerBasis, Equiv.smul_def, coordEquiv,
      Pi.single_apply]
  all_goals fin_cases i <;> fin_cases j <;> norm_num

/-- The traceless coordinate Cartan action is an actual element of the
native derivation Lie subalgebra, rather than merely a separately packaged
Leibniz witness. -/
theorem axialCartanEnd_mem_canonicalZornDerivations
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) :
    axialCartanEnd k ∈ canonicalZornDerivations := by
  rw [mem_canonicalZornDerivations]
  exact axialCartanEnd_isDerivation k hk

/-- The genuine Cartan derivation preserves the signed axial grading, hence
its infinitesimal flow does not mix the three tripotent sectors. -/
theorem axialCartanEnd_commutes_axialGrading
    (k : Fin 3 → ℝ) :
    axialCartanEnd k * axialGrading = axialGrading * axialCartanEnd k := by
  apply LinearMap.ext
  intro Z
  change axialCartanEnd k (axialGrading Z) =
    axialGrading (axialCartanEnd k Z)
  rw [axialGrading_apply, axialCartanEnd_apply, axialGrading_apply]
  ext i <;> simp [axialCartanEnd]

/-- The same infinitesimal Cartan action preserves the positive Peirce/root
projector. -/
theorem axialCartanEnd_commutes_axialPPlus
    (k : Fin 3 → ℝ) :
    axialCartanEnd k * axialPPlus = axialPPlus * axialCartanEnd k := by
  apply LinearMap.ext
  intro Z
  change axialCartanEnd k (axialPPlus Z) =
    axialPPlus (axialCartanEnd k Z)
  rw [axialPPlus_apply, axialCartanEnd_apply, axialPPlus_apply]
  rw [colorProject_apply, colorProject_apply]
  ext i <;> simp [axialCartanEnd]

/-- The negative Peirce/root sector is preserved as well. -/
theorem axialCartanEnd_commutes_axialPMinus
    (k : Fin 3 → ℝ) :
    axialCartanEnd k * axialPMinus = axialPMinus * axialCartanEnd k := by
  apply LinearMap.ext
  intro Z
  change axialCartanEnd k (axialPMinus Z) =
    axialPMinus (axialCartanEnd k Z)
  rw [axialPMinus_apply, axialCartanEnd_apply, axialPMinus_apply]
  rw [anticolorProject_apply, anticolorProject_apply]
  ext i <;> simp [axialCartanEnd]

/-- The stationary/defect Peirce sector is preserved infinitesimally. -/
theorem axialCartanEnd_commutes_axialPZero
    (k : Fin 3 → ℝ) :
    axialCartanEnd k * axialPZero = axialPZero * axialCartanEnd k := by
  apply LinearMap.ext
  intro Z
  change axialCartanEnd k (axialPZero Z) =
    axialPZero (axialCartanEnd k Z)
  rw [axialPZero_apply, axialCartanEnd_apply, axialPZero_apply]
  ext i <;> simp [axialCartanEnd]

/-- The infinitesimal Cartan action commutes with the native Drazin support
projector, independently of the finite closed-flow construction. -/
theorem axialCartanEnd_commutes_axialDrazinProjector
    (k : Fin 3 → ℝ) :
    axialCartanEnd k *
        Drazin_Projector axialGrading axialGrading 1
          axialGrading_isDrazinInverse =
      Drazin_Projector axialGrading axialGrading 1
          axialGrading_isDrazinInverse * axialCartanEnd k := by
  rw [axial_drazinProjector_eq_active]
  calc
    axialCartanEnd k * (axialPPlus + axialPMinus) =
        axialCartanEnd k * axialPPlus +
          axialCartanEnd k * axialPMinus := by rw [mul_add]
    _ = axialPPlus * axialCartanEnd k +
          axialPMinus * axialCartanEnd k := by
      rw [axialCartanEnd_commutes_axialPPlus,
        axialCartanEnd_commutes_axialPMinus]
    _ = (axialPPlus + axialPMinus) * axialCartanEnd k := by
      rw [add_mul]

/-- The complementary Drazin defect projector is preserved by the same
infinitesimal Cartan action. -/
theorem axialCartanEnd_commutes_axialDrazinDefect
    (k : Fin 3 → ℝ) :
    axialCartanEnd k *
        (1 - Drazin_Projector axialGrading axialGrading 1
          axialGrading_isDrazinInverse) =
      (1 - Drazin_Projector axialGrading axialGrading 1
          axialGrading_isDrazinInverse) * axialCartanEnd k := by
  rw [axial_drazinComplement_eq_PZero]
  exact axialCartanEnd_commutes_axialPZero k

end InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
