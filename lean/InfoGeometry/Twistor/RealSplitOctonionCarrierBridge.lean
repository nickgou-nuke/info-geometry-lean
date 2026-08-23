import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Real twistor carrier, split-quaternion blocks, and the Zorn carrier

This module closes the carrier-level part of the twistor/split-octonion bridge.
A complex twistor has four complex coordinates and therefore eight real
coordinates.  Those same eight real coordinates admit two useful readouts:

* two real `2 × 2` matrix blocks, the associative split-quaternion carrier;
* the established `1 + 3 + 3 + 1` exterior/Peirce coordinates, hence the
  canonical Zorn split-octonion carrier.

No bi-twistor reality condition is assumed here.  In particular, a free pair
`Z ⊕ W` has sixteen real dimensions.  A later bi-twistor theorem must define
and prove the relevant eight-real-dimensional fixed locus before transporting
any product.  The equivalences below are linear carrier equivalences only; they
do not assert that complex scalar multiplication or matrix multiplication is
the split-octonion product.
-/

open scoped Matrix

noncomputable section

namespace InfoGeometry.Twistor.RealSplitOctonionCarrierBridge

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

abbrev Real8 := Fin 8 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat2Pair := Mat2 × Mat2

/-- Real and imaginary coordinates of a complex twistor, in the order
`ω₀.re, ω₀.im, ω₁.re, ω₁.im, π₀.re, π₀.im, π₁.re, π₁.im`. -/
def twistorRealCoordinates : Twistor4 →ₗ[ℝ] Real8 where
  toFun Z := ![
    (Z.1 0).re, (Z.1 0).im,
    (Z.1 1).re, (Z.1 1).im,
    (Z.2 0).re, (Z.2 0).im,
    (Z.2 1).re, (Z.2 1).im]
  map_add' Z W := by
    ext i
    fin_cases i <;> simp
  map_smul' r Z := by
    ext i
    fin_cases i <;> simp

/-- Reconstruct a complex twistor from its eight real coordinates. -/
def realCoordinatesTwistor : Real8 →ₗ[ℝ] Twistor4 where
  toFun c :=
    (![⟨c 0, c 1⟩, ⟨c 2, c 3⟩],
     ![⟨c 4, c 5⟩, ⟨c 6, c 7⟩])
  map_add' c d := by
    ext i <;> fin_cases i <;> apply Complex.ext <;> simp
  map_smul' r c := by
    ext i <;> fin_cases i <;> apply Complex.ext <;> simp

@[simp] theorem realCoordinatesTwistor_twistorRealCoordinates
    (Z : Twistor4) :
    realCoordinatesTwistor (twistorRealCoordinates Z) = Z := by
  rcases Z with ⟨ω, π⟩
  ext i <;> fin_cases i <;> apply Complex.ext <;> simp [twistorRealCoordinates,
    realCoordinatesTwistor]

@[simp] theorem twistorRealCoordinates_realCoordinatesTwistor
    (c : Real8) :
    twistorRealCoordinates (realCoordinatesTwistor c) = c := by
  ext i
  fin_cases i <;> rfl

/-- A complex twistor, regarded as a real vector space, is exactly `ℝ⁸`. -/
noncomputable def twistorRealEquivReal8 : Twistor4 ≃ₗ[ℝ] Real8 where
  toLinearMap := twistorRealCoordinates
  invFun := realCoordinatesTwistor
  left_inv := realCoordinatesTwistor_twistorRealCoordinates
  right_inv := twistorRealCoordinates_realCoordinatesTwistor

/-- Package eight real coordinates into two real `2 × 2` matrix blocks. -/
def real8ToMat2Pair : Real8 →ₗ[ℝ] Mat2Pair where
  toFun c :=
    (!![c 0, c 1; c 2, c 3],
     !![c 4, c 5; c 6, c 7])
  map_add' c d := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp
  map_smul' r c := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp

/-- Read two real `2 × 2` matrix blocks back as eight real coordinates. -/
def mat2PairToReal8 : Mat2Pair →ₗ[ℝ] Real8 where
  toFun M := ![
    M.1 0 0, M.1 0 1, M.1 1 0, M.1 1 1,
    M.2 0 0, M.2 0 1, M.2 1 0, M.2 1 1]
  map_add' M N := by
    ext i
    fin_cases i <;> simp
  map_smul' r M := by
    ext i
    fin_cases i <;> simp

@[simp] theorem mat2PairToReal8_real8ToMat2Pair (c : Real8) :
    mat2PairToReal8 (real8ToMat2Pair c) = c := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem real8ToMat2Pair_mat2PairToReal8 (M : Mat2Pair) :
    real8ToMat2Pair (mat2PairToReal8 M) = M := by
  rcases M with ⟨A, B⟩
  ext i j <;> fin_cases i <;> fin_cases j <;> rfl

/-- The eight-real-dimensional twistor carrier decomposes linearly into two
real `2 × 2` matrix blocks.  This is the split-quaternionic block readout; no
multiplicative intertwining is asserted. -/
noncomputable def real8EquivMat2Pair : Real8 ≃ₗ[ℝ] Mat2Pair where
  toLinearMap := real8ToMat2Pair
  invFun := mat2PairToReal8
  left_inv := mat2PairToReal8_real8ToMat2Pair
  right_inv := real8ToMat2Pair_mat2PairToReal8

noncomputable def twistorRealEquivMat2Pair : Twistor4 ≃ₗ[ℝ] Mat2Pair :=
  twistorRealEquivReal8.trans real8EquivMat2Pair

/-- Real twistor coordinates transported to the literal three-dimensional
exterior algebra using the established circular Peirce coordinate basis. -/
noncomputable def twistorRealEquivExterior3 : Twistor4 ≃ₗ[ℝ] Exterior3 :=
  twistorRealEquivReal8.trans exterior3SplitOctonionCoordinateEquiv.symm

/-- Carrier-level bridge from a complex twistor, regarded as an eight-real-
dimensional vector space, to the canonical Zorn split-octonion carrier. -/
noncomputable def twistorRealEquivZorn : Twistor4 ≃ₗ[ℝ] CanonicalSplitOctonion :=
  twistorRealEquivExterior3.trans exterior3CircularPeirceEquiv

/-- The twistor-to-Zorn carrier bridge factors through the established exterior
`1 + 3 + 3 + 1` carrier. -/
theorem twistorRealEquivZorn_factorization (Z : Twistor4) :
    twistorRealEquivZorn Z =
      exterior3CircularPeirceEquiv (twistorRealEquivExterior3 Z) := by
  rfl

/-- The two canonical eight-real-dimensional readouts coexist: associative
`2 × 2 ⊕ 2 × 2` blocks and the nonassociative Zorn carrier. -/
theorem twistor_real_carrier_has_block_and_zorn_readouts :
    Nonempty (Twistor4 ≃ₗ[ℝ] Mat2Pair) ∧
      Nonempty (Twistor4 ≃ₗ[ℝ] CanonicalSplitOctonion) := by
  exact ⟨⟨twistorRealEquivMat2Pair⟩, ⟨twistorRealEquivZorn⟩⟩

end InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
