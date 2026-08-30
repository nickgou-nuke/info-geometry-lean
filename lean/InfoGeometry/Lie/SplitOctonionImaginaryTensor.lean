import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Lie.SplitOctonionErlangenInvariant
import InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
import InfoGeometry.Algebra.ZornDerivationBridge
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Native imaginary split-octonion commutator tensor

The imaginary split-octonion carrier supplies a seven-dimensional analogue of
the three-dimensional cross-product readout.  This owner uses the actual Zorn
product and the already-proved determinant-polar bilinear form.  It deliberately
stops before asserting stability of a split `G₂` three-form or classifying its
automorphism group.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryTensor

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionImaginaryAction

abbrev CZ := CanonicalZorn
abbrev Imaginary := InfoGeometry.Lie.SplitOctonionImaginaryAction.Imaginary

theorem realZornTrace_mul_cyclic (X Y Z : CZ) :
    realZornTrace ((X * Y) * Z) = realZornTrace ((Y * Z) * X) := by
  change InfoGeometry.Algebra.ZornVectorMatrix.trace
      (canonicalVectorEquiv ((X * Y) * Z)) =
    InfoGeometry.Algebra.ZornVectorMatrix.trace
      (canonicalVectorEquiv ((Y * Z) * X))
  rw [canonicalVectorEquiv_mul, canonicalVectorEquiv_mul,
    canonicalVectorEquiv_mul, canonicalVectorEquiv_mul]
  exact InfoGeometry.Algebra.ZornVectorMatrix.trace_mul_cyclic _ _ _

/-! ## The native commutator cross product -/

/-- The imaginary commutator, with the usual one-half normalization. -/
def imaginaryCross (X Y : Imaginary) : Imaginary :=
  ⟨(1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1), by
    change realZornTrace ((1 / 2 : ℝ) •
      (X.1 * Y.1 - Y.1 * X.1)) = 0
    change traceLinear ((1 / 2 : ℝ) •
      (X.1 * Y.1 - Y.1 * X.1)) = 0
    rw [map_smul, map_sub]
    change (1 / 2 : ℝ) •
      (realZornTrace (X.1 * Y.1) - realZornTrace (Y.1 * X.1)) = 0
    rw [realZornTrace_mul_comm Y.1 X.1]
    simp⟩

/-- The imaginary product splits into its determinant-polar scalar channel and
    its antisymmetric commutator channel.  This is the native split analogue
    of the usual scalar-plus-cross decomposition; it does not identify the
    split form with the definite Euclidean Fano model. -/
theorem imaginary_mul_decomposition (X Y : Imaginary) :
    X.1 * Y.1 =
      (-(1 / 2 : ℝ) * imaginaryPolar X Y) • (1 : CanonicalZorn) +
      (imaginaryCross X Y).1 := by
  have hmul (A B : CanonicalZorn) :
      A * B = InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul A B := by
    ext <;> rfl
  have hanti := imaginary_anticommutator_eq X Y
  have hanti' : X.1 * Y.1 + Y.1 * X.1 =
      -(imaginaryPolar X Y) • (1 : CanonicalZorn) := by
    rw [hmul, hmul]
    exact hanti
  unfold imaginaryCross
  change X.1 * Y.1 =
    (-(1 / 2 : ℝ) * imaginaryPolar X Y) • (1 : CanonicalZorn) +
      (1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1)
  calc
    X.1 * Y.1 =
        (1 / 2 : ℝ) •
          ((X.1 * Y.1 + Y.1 * X.1) + (X.1 * Y.1 - Y.1 * X.1)) := by
      module
    _ = (1 / 2 : ℝ) •
          (-(imaginaryPolar X Y) • (1 : CanonicalZorn) +
            (X.1 * Y.1 - Y.1 * X.1)) := by rw [hanti']
    _ = (-(1 / 2 : ℝ) * imaginaryPolar X Y) • (1 : CanonicalZorn) +
          (1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1) := by
      module

theorem imaginary_mul_sub_swap_eq_two_cross (X Y : Imaginary) :
    X.1 * Y.1 - Y.1 * X.1 = 2 • (imaginaryCross X Y).1 := by
  unfold imaginaryCross
  module

@[simp] theorem imaginaryCross_swap (X Y : Imaginary) :
    imaginaryCross Y X = -imaginaryCross X Y := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (Y.1 * X.1 - X.1 * Y.1) =
    -((1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1))
  module

theorem imaginaryCross_coord_swap (X Y : Imaginary) :
    imaginaryCoordLinearEquiv (imaginaryCross Y X) =
      -imaginaryCoordLinearEquiv (imaginaryCross X Y) := by
  rw [imaginaryCross_swap]
  exact map_neg imaginaryCoordLinearEquiv (imaginaryCross X Y)

@[simp] theorem imaginaryCross_self (X : Imaginary) :
    imaginaryCross X X = 0 := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (X.1 * X.1 - X.1 * X.1) = 0
  simp

theorem imaginaryCross_coord_self (X : Imaginary) :
    imaginaryCoordLinearEquiv (imaginaryCross X X) = 0 := by
  rw [imaginaryCross_self]
  exact map_zero imaginaryCoordLinearEquiv

theorem imaginaryCross_add_left (X Y Z : Imaginary) :
    imaginaryCross (X + Y) Z = imaginaryCross X Z + imaginaryCross Y Z := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • ((X.1 + Y.1) * Z.1 - Z.1 * (X.1 + Y.1)) =
    (1 / 2 : ℝ) • (X.1 * Z.1 - Z.1 * X.1) +
      (1 / 2 : ℝ) • (Y.1 * Z.1 - Z.1 * Y.1)
  rw [add_mul, mul_add, sub_eq_add_neg, sub_eq_add_neg]
  module

theorem imaginaryCross_add_right (X Y Z : Imaginary) :
    imaginaryCross X (Y + Z) = imaginaryCross X Y + imaginaryCross X Z := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (X.1 * (Y.1 + Z.1) - (Y.1 + Z.1) * X.1) =
    (1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1) +
      (1 / 2 : ℝ) • (X.1 * Z.1 - Z.1 * X.1)
  rw [mul_add, add_mul, sub_eq_add_neg, sub_eq_add_neg]
  module

theorem imaginaryCross_smul_left (r : ℝ) (X Y : Imaginary) :
    imaginaryCross (r • X) Y = r • imaginaryCross X Y := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • ((r • X.1) * Y.1 - Y.1 * (r • X.1)) =
    r • ((1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1))
  rw [smul_mul, mul_smul]
  module

theorem imaginaryCross_smul_right (r : ℝ) (X Y : Imaginary) :
    imaginaryCross X (r • Y) = r • imaginaryCross X Y := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (X.1 * (r • Y.1) - (r • Y.1) * X.1) =
    r • ((1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1))
  rw [mul_smul, smul_mul]
  module

theorem imaginaryCross_coord_add_left (X Y Z : Imaginary) :
    imaginaryCoordLinearEquiv (imaginaryCross (X + Y) Z) =
      imaginaryCoordLinearEquiv (imaginaryCross X Z) +
        imaginaryCoordLinearEquiv (imaginaryCross Y Z) := by
  rw [imaginaryCross_add_left]
  exact map_add imaginaryCoordLinearEquiv _ _

theorem imaginaryCross_coord_add_right (X Y Z : Imaginary) :
    imaginaryCoordLinearEquiv (imaginaryCross X (Y + Z)) =
      imaginaryCoordLinearEquiv (imaginaryCross X Y) +
        imaginaryCoordLinearEquiv (imaginaryCross X Z) := by
  rw [imaginaryCross_add_right]
  exact map_add imaginaryCoordLinearEquiv _ _

theorem imaginaryCross_coord_smul_left (r : ℝ) (X Y : Imaginary) :
    imaginaryCoordLinearEquiv (imaginaryCross (r • X) Y) =
      r • imaginaryCoordLinearEquiv (imaginaryCross X Y) := by
  rw [imaginaryCross_smul_left]
  exact map_smul imaginaryCoordLinearEquiv r _

theorem imaginaryCross_coord_smul_right (r : ℝ) (X Y : Imaginary) :
    imaginaryCoordLinearEquiv (imaginaryCross X (r • Y)) =
      r • imaginaryCoordLinearEquiv (imaginaryCross X Y) := by
  rw [imaginaryCross_smul_right]
  exact map_smul imaginaryCoordLinearEquiv r _

/-- The native seven-coordinate realization of the imaginary commutator cross.
It is transported from the canonical Zorn imaginary carrier; it is not
identified with the compact Fano cross without an additional signature map. -/
def imaginaryCrossSeven (u v : ImaginarySeven) : ImaginarySeven :=
  imaginaryCoords_seven
    (imaginaryCoordLinearEquiv
      (imaginaryCross
        (imaginaryCoordLinearEquiv.symm (imaginaryCoords_seven.symm u))
        (imaginaryCoordLinearEquiv.symm (imaginaryCoords_seven.symm v))))

@[simp] theorem imaginaryCrossSeven_swap (u v : ImaginarySeven) :
    imaginaryCrossSeven v u = -imaginaryCrossSeven u v := by
  unfold imaginaryCrossSeven
  rw [imaginaryCross_swap]
  let z : Imaginary := imaginaryCross
    (imaginaryCoordLinearEquiv.symm (imaginaryCoords_seven.symm u))
    (imaginaryCoordLinearEquiv.symm (imaginaryCoords_seven.symm v))
  have hz : imaginaryCoordLinearEquiv (-z) =
      -imaginaryCoordLinearEquiv z := imaginaryCoordLinearEquiv.map_neg z
  rw [hz]
  calc
    imaginaryCoords_seven (-imaginaryCoordLinearEquiv z) =
        -imaginaryCoords_seven (imaginaryCoordLinearEquiv z) :=
      imaginaryCoords_seven.map_neg _
    _ = -imaginaryCoords_seven
        (imaginaryCoordLinearEquiv
          (imaginaryCross
            (imaginaryCoordLinearEquiv.symm (imaginaryCoords_seven.symm u))
            (imaginaryCoordLinearEquiv.symm (imaginaryCoords_seven.symm v)))) := by
      rfl

@[simp] theorem imaginaryCrossSeven_self (u : ImaginarySeven) :
    imaginaryCrossSeven u u = 0 := by
  simp only [imaginaryCrossSeven, imaginaryCross_self,
    imaginaryCoordLinearEquiv.map_zero, imaginaryCoords_seven.map_zero]

theorem imaginaryCrossSeven_add_left (u v w : ImaginarySeven) :
    imaginaryCrossSeven (u + v) w =
      imaginaryCrossSeven u w + imaginaryCrossSeven v w := by
  simp only [imaginaryCrossSeven, map_add, imaginaryCross_add_left]

theorem imaginaryCrossSeven_add_right (u v w : ImaginarySeven) :
    imaginaryCrossSeven u (v + w) =
      imaginaryCrossSeven u v + imaginaryCrossSeven u w := by
  simp only [imaginaryCrossSeven, map_add, imaginaryCross_add_right]

theorem imaginaryCrossSeven_smul_left (r : ℝ) (u v : ImaginarySeven) :
    imaginaryCrossSeven (r • u) v = r • imaginaryCrossSeven u v := by
  simp only [imaginaryCrossSeven, map_smul, imaginaryCross_smul_left]

theorem imaginaryCrossSeven_smul_right (r : ℝ) (u v : ImaginarySeven) :
    imaginaryCrossSeven u (r • v) = r • imaginaryCrossSeven u v := by
  simp only [imaginaryCrossSeven, map_smul, imaginaryCross_smul_right]

/- The split-signature seven-dimensional product is a genuine bilinear
   tensor on the coordinate carrier.  It is kept separate from the compact
   Fano convention, whose quadratic form has a different signature. -/
noncomputable def imaginaryCrossSevenLinear :
    ImaginarySeven →ₗ[ℝ] ImaginarySeven →ₗ[ℝ] ImaginarySeven :=
  LinearMap.mk₂ ℝ imaginaryCrossSeven
    imaginaryCrossSeven_add_left
    imaginaryCrossSeven_smul_left
    imaginaryCrossSeven_add_right
    imaginaryCrossSeven_smul_right

@[simp] theorem imaginaryCrossSevenLinear_apply
    (u v : ImaginarySeven) :
    imaginaryCrossSevenLinear u v = imaginaryCrossSeven u v := rfl

/- The coordinate projection is an actual intertwiner for the intrinsic
   split commutator tensor. -/
theorem imaginaryCoords_seven_cross
    (X Y : Imaginary) :
    imaginaryCoords_seven (imaginaryCoordLinearEquiv (imaginaryCross X Y)) =
      imaginaryCrossSeven
        (imaginaryCoords_seven (imaginaryCoordLinearEquiv X))
        (imaginaryCoords_seven (imaginaryCoordLinearEquiv Y)) := by
  simp only [imaginaryCrossSeven, LinearEquiv.symm_apply_apply]

/-! ## The product-induced scalar three-slot readout -/

/-- The determinant-polar pairing read against the native commutator cross. -/
def imaginaryCommutatorForm (X Y Z : Imaginary) : ℝ :=
  imaginaryPolarBilin (imaginaryCross X Y) Z

theorem imaginaryCommutatorForm_add_left (X Y Z W : Imaginary) :
    imaginaryCommutatorForm (X + Y) Z W =
      imaginaryCommutatorForm X Z W + imaginaryCommutatorForm Y Z W := by
  rw [imaginaryCommutatorForm, imaginaryCross_add_left]
  change imaginaryPolarBilin (imaginaryCross X Z + imaginaryCross Y Z) W =
    imaginaryPolarBilin (imaginaryCross X Z) W +
      imaginaryPolarBilin (imaginaryCross Y Z) W
  rw [map_add]
  rfl

theorem imaginaryCommutatorForm_add_middle (X Y Z W : Imaginary) :
    imaginaryCommutatorForm X (Y + Z) W =
      imaginaryCommutatorForm X Y W + imaginaryCommutatorForm X Z W := by
  rw [imaginaryCommutatorForm, imaginaryCross_add_right]
  change imaginaryPolarBilin (imaginaryCross X Y + imaginaryCross X Z) W =
    imaginaryPolarBilin (imaginaryCross X Y) W +
      imaginaryPolarBilin (imaginaryCross X Z) W
  rw [map_add]
  rfl

theorem imaginaryCommutatorForm_add_last (X Y Z W : Imaginary) :
    imaginaryCommutatorForm X Y (Z + W) =
      imaginaryCommutatorForm X Y Z + imaginaryCommutatorForm X Y W := by
  rw [imaginaryCommutatorForm]
  change imaginaryPolarBilin (imaginaryCross X Y) (Z + W) =
    imaginaryPolarBilin (imaginaryCross X Y) Z +
      imaginaryPolarBilin (imaginaryCross X Y) W
  rw [map_add]

theorem imaginaryCommutatorForm_smul_left (r : ℝ) (X Y Z : Imaginary) :
    imaginaryCommutatorForm (r • X) Y Z =
      r • imaginaryCommutatorForm X Y Z := by
  rw [imaginaryCommutatorForm, imaginaryCross_smul_left]
  change imaginaryPolarBilin (r • imaginaryCross X Y) Z =
    r • imaginaryPolarBilin (imaginaryCross X Y) Z
  rw [map_smul]
  rfl

theorem imaginaryCommutatorForm_smul_middle (r : ℝ) (X Y Z : Imaginary) :
    imaginaryCommutatorForm X (r • Y) Z =
      r • imaginaryCommutatorForm X Y Z := by
  rw [imaginaryCommutatorForm, imaginaryCross_smul_right]
  change imaginaryPolarBilin (r • imaginaryCross X Y) Z =
    r • imaginaryPolarBilin (imaginaryCross X Y) Z
  rw [map_smul]
  rfl

theorem imaginaryCommutatorForm_smul_last (r : ℝ) (X Y Z : Imaginary) :
    imaginaryCommutatorForm X Y (r • Z) =
      r • imaginaryCommutatorForm X Y Z := by
  rw [imaginaryCommutatorForm]
  change imaginaryPolarBilin (imaginaryCross X Y) (r • Z) =
    r • imaginaryPolarBilin (imaginaryCross X Y) Z
  rw [map_smul]

theorem imaginaryCommutatorForm_swap_first_two (X Y Z : Imaginary) :
    imaginaryCommutatorForm Y X Z =
      -imaginaryCommutatorForm X Y Z := by
  rw [imaginaryCommutatorForm, imaginaryCross_swap]
  change imaginaryPolarBilin (-imaginaryCross X Y) Z =
    -imaginaryPolarBilin (imaginaryCross X Y) Z
  rw [map_neg]
  rfl

theorem imaginaryCommutatorForm_self_first (X Z : Imaginary) :
    imaginaryCommutatorForm X X Z = 0 := by
  rw [imaginaryCommutatorForm, imaginaryCross_self]
  simp

theorem imaginaryCommutatorForm_cyclic (X Y Z : Imaginary) :
    imaginaryCommutatorForm X Y Z =
      imaginaryCommutatorForm Y Z X := by
  unfold imaginaryCommutatorForm imaginaryCross
  simp only [imaginaryPolarBilin, LinearMap.mk₂_apply]
  change -realZornTrace
      (((1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1)) * Z.1) =
    -realZornTrace
      (((1 / 2 : ℝ) • (Y.1 * Z.1 - Z.1 * Y.1)) * X.1)
  rw [smul_mul, smul_mul]
  change -traceLinear ((1 / 2 : ℝ) • ((X.1 * Y.1 - Y.1 * X.1) * Z.1)) =
    -traceLinear ((1 / 2 : ℝ) • ((Y.1 * Z.1 - Z.1 * Y.1) * X.1))
  rw [map_smul, map_smul, sub_mul, sub_mul, map_sub, map_sub]
  change -((1 / 2 : ℝ) •
      (realZornTrace (X.1 * Y.1 * Z.1) -
        realZornTrace (Y.1 * X.1 * Z.1))) =
    -((1 / 2 : ℝ) •
      (realZornTrace (Y.1 * Z.1 * X.1) -
        realZornTrace (Z.1 * Y.1 * X.1)))
  have h₁ := realZornTrace_mul_cyclic X.1 Y.1 Z.1
  have h₂ := realZornTrace_mul_cyclic Z.1 Y.1 X.1
  rw [h₁, h₂]

theorem imaginaryCommutatorForm_self_last (X Y : Imaginary) :
    imaginaryCommutatorForm X Y Y = 0 := by
  calc
    imaginaryCommutatorForm X Y Y = imaginaryCommutatorForm Y Y X :=
      imaginaryCommutatorForm_cyclic X Y Y
    _ = 0 := imaginaryCommutatorForm_self_first Y X

theorem imaginaryCommutatorForm_zero_of_eq_first_second
    (X Y Z : Imaginary) (h : X = Y) :
    imaginaryCommutatorForm X Y Z = 0 := by
  subst Y
  exact imaginaryCommutatorForm_self_first X Z

theorem imaginaryCommutatorForm_zero_of_eq_first_third
    (X Y Z : Imaginary) (h : X = Z) :
    imaginaryCommutatorForm X Y Z = 0 := by
  calc
    imaginaryCommutatorForm X Y Z = imaginaryCommutatorForm Y Z X :=
      imaginaryCommutatorForm_cyclic X Y Z
    _ = 0 := by rw [h]; exact imaginaryCommutatorForm_self_last Y Z

theorem imaginaryCommutatorForm_zero_of_eq_second_third
    (X Y Z : Imaginary) (h : Y = Z) :
    imaginaryCommutatorForm X Y Z = 0 := by
  calc
    imaginaryCommutatorForm X Y Z = imaginaryCommutatorForm Y Z X :=
      imaginaryCommutatorForm_cyclic X Y Z
    _ = 0 := by rw [h]; exact imaginaryCommutatorForm_self_first Z X

theorem imaginaryCommutatorForm_swap_last_two (X Y Z : Imaginary) :
    imaginaryCommutatorForm X Z Y =
      -imaginaryCommutatorForm X Y Z := by
  calc
    imaginaryCommutatorForm X Z Y = imaginaryCommutatorForm Z Y X :=
      imaginaryCommutatorForm_cyclic X Z Y
    _ = -imaginaryCommutatorForm Y Z X :=
      imaginaryCommutatorForm_swap_first_two Y Z X
    _ = -imaginaryCommutatorForm X Y Z := by
      rw [imaginaryCommutatorForm_cyclic X Y Z]

/-! ## The genuine alternating three-form -/

noncomputable def imaginaryCommutatorMultilinear :
    MultilinearMap ℝ (fun _ : Fin 3 => Imaginary) ℝ :=
  MultilinearMap.mk'
    (fun v => imaginaryCommutatorForm (v 0) (v 1) (v 2)) (by
      intro m i x y
      fin_cases i
      · change imaginaryCommutatorForm (x + y) (m 1) (m 2) = _
        rw [imaginaryCommutatorForm_add_left]
        simp [Function.update]
      · change imaginaryCommutatorForm (m 0) (x + y) (m 2) = _
        rw [imaginaryCommutatorForm_add_middle]
        simp [Function.update]
      · change imaginaryCommutatorForm (m 0) (m 1) (x + y) = _
        rw [imaginaryCommutatorForm_add_last]
        simp [Function.update]) (by
      intro m i r x
      fin_cases i
      · change imaginaryCommutatorForm (r • x) (m 1) (m 2) = _
        rw [imaginaryCommutatorForm_smul_left]
        simp [Function.update]
      · change imaginaryCommutatorForm (m 0) (r • x) (m 2) = _
        rw [imaginaryCommutatorForm_smul_middle]
        simp [Function.update]
      · change imaginaryCommutatorForm (m 0) (m 1) (r • x) = _
        rw [imaginaryCommutatorForm_smul_last]
        simp [Function.update])

noncomputable def imaginaryCommutatorAlternating :
    Imaginary [⋀^Fin 3]→ₗ[ℝ] ℝ :=
  AlternatingMap.mk imaginaryCommutatorMultilinear (by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change imaginaryCommutatorForm (v 0) (v 1) (v 2) = 0
      have h : v 0 = v 1 := by simpa using hij
      exact imaginaryCommutatorForm_zero_of_eq_first_second _ _ _ h
    · change imaginaryCommutatorForm (v 0) (v 1) (v 2) = 0
      have h : v 0 = v 2 := by simpa using hij
      exact imaginaryCommutatorForm_zero_of_eq_first_third _ _ _ h
    · change imaginaryCommutatorForm (v 0) (v 1) (v 2) = 0
      have h : v 1 = v 0 := by simpa using hij
      exact imaginaryCommutatorForm_zero_of_eq_first_second _ _ _ h.symm
    · exact (hne rfl).elim
    · change imaginaryCommutatorForm (v 0) (v 1) (v 2) = 0
      have h : v 1 = v 2 := by simpa using hij
      exact imaginaryCommutatorForm_zero_of_eq_second_third _ _ _ h
    · change imaginaryCommutatorForm (v 0) (v 1) (v 2) = 0
      have h : v 2 = v 0 := by simpa using hij
      exact imaginaryCommutatorForm_zero_of_eq_first_third _ _ _ h.symm
    · change imaginaryCommutatorForm (v 0) (v 1) (v 2) = 0
      have h : v 2 = v 1 := by simpa using hij
      exact imaginaryCommutatorForm_zero_of_eq_second_third _ _ _ h.symm
    · exact (hne rfl).elim
    )

@[simp] theorem imaginaryCommutatorAlternating_apply
    (X Y Z : Imaginary) :
    imaginaryCommutatorAlternating ![X, Y, Z] =
      imaginaryCommutatorForm X Y Z := rfl

noncomputable def imaginaryCommutatorExteriorMap :
    (⋀[ℝ]^3 Imaginary) →ₗ[ℝ] ℝ :=
  exteriorPower.alternatingMapLinearEquiv imaginaryCommutatorAlternating

theorem imaginaryCommutatorExteriorMap_ιMulti
    (X Y Z : Imaginary) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3 ![X, Y, Z]) =
      imaginaryCommutatorForm X Y Z := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    imaginaryCommutatorAlternating ![X, Y, Z]

/-! ## Functoriality under native composition automorphisms -/

theorem imaginaryAut_preserves_cross
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (X Y : Imaginary) :
    imaginaryAut φ (imaginaryCross X Y) =
      imaginaryCross (imaginaryAut φ X) (imaginaryAut φ Y) := by
  apply Subtype.ext
  change (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut)
      ((1 / 2 : ℝ) •
        (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X.1 Y.1 -
          InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul Y.1 X.1)) =
    (1 / 2 : ℝ) •
      (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
          ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X.1)
          ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) Y.1) -
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
          ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) Y.1)
          ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X.1))
  rw [map_smul, map_sub,
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_mul,
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_mul]

theorem imaginaryAut_preserves_commutatorForm
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (X Y Z : Imaginary) :
    imaginaryCommutatorForm (imaginaryAut φ X) (imaginaryAut φ Y)
        (imaginaryAut φ Z) =
      imaginaryCommutatorForm X Y Z := by
  unfold imaginaryCommutatorForm
  rw [← imaginaryAut_preserves_cross]
  rw [imaginaryPolarBilin_apply]
  rw [imaginaryPolarBilin_apply]
  exact InfoGeometry.Lie.SplitOctonionErlangenInvariant.imaginaryAut_preserves_polar φ _ _

theorem imaginaryAut_preserves_exteriorEvaluation
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (X Y Z : Imaginary) :
    imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3
          ![imaginaryAut φ X, imaginaryAut φ Y, imaginaryAut φ Z]) =
      imaginaryCommutatorExteriorMap
        (exteriorPower.ιMulti ℝ 3 ![X, Y, Z]) := by
  rw [imaginaryCommutatorExteriorMap_ιMulti,
    imaginaryCommutatorExteriorMap_ιMulti,
    imaginaryAut_preserves_commutatorForm]

/-! ## Infinitesimal invariance criterion -/

theorem commutatorForm_lieDerivative_eq_zero_of_cross_derivation
    (D : Module.End ℝ Imaginary)
    (hcross : ∀ X Y : Imaginary,
      D (imaginaryCross X Y) =
        imaginaryCross (D X) Y + imaginaryCross X (D Y))
    (hpolar : ∀ X Y : Imaginary,
      imaginaryPolarBilin (D X) Y + imaginaryPolarBilin X (D Y) = 0)
    (X Y Z : Imaginary) :
    imaginaryCommutatorForm (D X) Y Z +
        imaginaryCommutatorForm X (D Y) Z +
        imaginaryCommutatorForm X Y (D Z) = 0 := by
  have hcrossXY := hcross X Y
  have hpolarXY := hpolar (imaginaryCross X Y) Z
  rw [imaginaryCommutatorForm, imaginaryCommutatorForm,
    imaginaryCommutatorForm]
  calc
    imaginaryPolarBilin (imaginaryCross (D X) Y) Z +
        imaginaryPolarBilin (imaginaryCross X (D Y)) Z +
        imaginaryPolarBilin (imaginaryCross X Y) (D Z) =
        imaginaryPolarBilin (imaginaryCross (D X) Y + imaginaryCross X (D Y)) Z +
        imaginaryPolarBilin (imaginaryCross X Y) (D Z) := by
      rw [map_add]
      rfl
    _ = imaginaryPolarBilin (D (imaginaryCross X Y)) Z +
        imaginaryPolarBilin (imaginaryCross X Y) (D Z) := by
          rw [hcrossXY]
    _ = 0 := hpolarXY

/-! ## The traceless Cartan specialization -/

open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation

noncomputable def axialCartanImaginaryEnd (k : Fin 3 → ℝ) :
    Module.End ℝ Imaginary where
  toFun X :=
    ⟨axialCartanEnd k X.1, by
      change (axialCartanEnd k X.1).a + (axialCartanEnd k X.1).b = 0
      rw [axialCartanEnd_apply]
      norm_num⟩
  map_add' X Y := by
    apply Subtype.ext
    exact (axialCartanEnd k).map_add X.1 Y.1
  map_smul' r X := by
    apply Subtype.ext
    exact (axialCartanEnd k).map_smul r X.1

@[simp] theorem axialCartanImaginaryEnd_apply
    (k : Fin 3 → ℝ) (X : Imaginary) :
    axialCartanImaginaryEnd k X =
      ⟨axialCartanEnd k X.1, by
        change (axialCartanEnd k X.1).a + (axialCartanEnd k X.1).b = 0
        rw [axialCartanEnd_apply]
        norm_num⟩ := rfl

theorem axialCartanImaginaryEnd_cross_derivation
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (X Y : Imaginary) :
    axialCartanImaginaryEnd k (imaginaryCross X Y) =
      imaginaryCross (axialCartanImaginaryEnd k X) Y +
        imaginaryCross X (axialCartanImaginaryEnd k Y) := by
  apply Subtype.ext
  change axialCartanEnd k
      ((1 / 2 : ℝ) • (X.1 * Y.1 - Y.1 * X.1)) =
    (1 / 2 : ℝ) •
      ((axialCartanEnd k X.1) * Y.1 - Y.1 * (axialCartanEnd k X.1)) +
      (1 / 2 : ℝ) •
        (X.1 * (axialCartanEnd k Y.1) - (axialCartanEnd k Y.1) * X.1)
  rw [map_smul, map_sub,
    axialCartanEnd_isDerivation k hk,
    axialCartanEnd_isDerivation k hk]
  module

private theorem axialCartanEnd_trace_zero
    (k : Fin 3 → ℝ) (X : CZ) :
    realZornTrace (axialCartanEnd k X) = 0 := by
  change (axialCartanEnd k X).a + (axialCartanEnd k X).b = 0
  rw [axialCartanEnd_apply]
  norm_num

theorem axialCartanImaginaryEnd_polar_skew
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (X Y : Imaginary) :
    imaginaryPolarBilin (axialCartanImaginaryEnd k X) Y +
        imaginaryPolarBilin X (axialCartanImaginaryEnd k Y) = 0 := by
  change -traceLinear ((axialCartanEnd k X.1) * Y.1) +
      -traceLinear (X.1 * (axialCartanEnd k Y.1)) = 0
  have hderiv := axialCartanEnd_isDerivation k hk X.1 Y.1
  have htrace := axialCartanEnd_trace_zero k (X.1 * Y.1)
  rw [hderiv] at htrace
  change traceLinear
      ((axialCartanEnd k X.1) * Y.1 + X.1 * (axialCartanEnd k Y.1)) = 0 at htrace
  rw [map_add] at htrace
  linarith

theorem axialCartanImaginaryEnd_commutatorForm_lieInvariant
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (X Y Z : Imaginary) :
    imaginaryCommutatorForm (axialCartanImaginaryEnd k X) Y Z +
        imaginaryCommutatorForm X (axialCartanImaginaryEnd k Y) Z +
        imaginaryCommutatorForm X Y (axialCartanImaginaryEnd k Z) = 0 := by
  exact commutatorForm_lieDerivative_eq_zero_of_cross_derivation
    (axialCartanImaginaryEnd k)
    (axialCartanImaginaryEnd_cross_derivation k hk)
    (axialCartanImaginaryEnd_polar_skew k hk) X Y Z

end InfoGeometry.Lie.SplitOctonionImaginaryTensor
