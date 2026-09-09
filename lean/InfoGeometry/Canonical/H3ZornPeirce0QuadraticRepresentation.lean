import Mathlib
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment
import InfoGeometry.Exceptional.RealSplitAlbertFreudenthal

/-!
# Peirce-0 quadratic representation on the split Albert carrier

This file closes the finite theorem-safe statement that the quadratic Jordan
representation preserves the Peirce zero space of the first primitive diagonal
idempotent.

The native `H3Zorn` layout is

```
[ α₁   a    c* ]
[ a*   α₂   b  ]
[ c    b*   α₃ ]
```

so the lower-right `H₂(𝕆_s)` block is characterized by
`α₁ = 0`, `a = 0`, `c = 0`, leaving the ten real coordinates
`(α₂, α₃, b)`.

The repository already owns both the verified Jordan product and the cubic
quadratic operator `H3Zorn.U`.  We do not introduce parallel split-octonion or
Albert carriers.
-/

noncomputable section

set_option maxHeartbeats 1200000

namespace InfoGeometry.Canonical.H3ZornPeirce0QuadraticRepresentation

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment

/-- Coordinate characterization of the Peirce zero space `V₀(e₁)` in the
repository's native `H3Zorn` convention. -/
def InPeirce0E1 (X : H3Zorn ℝ) : Prop :=
  X.α₁ = 0 ∧ X.a = 0 ∧ X.c = 0

/-- The corresponding coordinate condition on the explicit real Albert
carrier.  Under `toH3`, `z₁ ↦ b`, `z₂ ↦ c`, `z₃ ↦ a`. -/
def InRealPeirce0E1 (X : RealAlbertMatrix) : Prop :=
  X.α₁ = 0 ∧ X.z₂ = 0 ∧ X.z₃ = 0

/-- The explicit real Albert product preserves the lower-right `H₂(𝕆_s)`
coordinate block. -/
theorem realAlbertMul_preserves_peirce0E1
    {X Y : RealAlbertMatrix}
    (hX : InRealPeirce0E1 X) (hY : InRealPeirce0E1 Y) :
    InRealPeirce0E1 (RealAlbertMatrix.mul X Y) := by
  rcases hX with ⟨hX1, hX2, hX3⟩
  rcases hY with ⟨hY1, hY2, hY3⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [RealAlbertMatrix.mul, hX1, hY1, hX2, hY2, hX3, hY3,
      RealSplitOct.zero, RealSplitOct.mul, RealSplitOct.conj]
  · apply RealSplitOct.ext <;>
      simp [RealAlbertMatrix.mul, hX1, hY1, hX2, hY2, hX3, hY3,
        RealSplitOct.zero, RealSplitOct.mul, RealSplitOct.conj,
        RealSplitOct.smul]
  · apply RealSplitOct.ext <;>
      simp [RealAlbertMatrix.mul, hX1, hY1, hX2, hY2, hX3, hY3,
        RealSplitOct.zero, RealSplitOct.mul, RealSplitOct.conj,
        RealSplitOct.smul]

/-- The native verified Jordan product preserves `V₀(e₁)`.  The proof is
transported through the already-proved explicit-coordinate product theorem. -/
theorem jordanMul_preserves_peirce0E1
    {X Y : H3Zorn ℝ}
    (hX : InPeirce0E1 X) (hY : InPeirce0E1 Y) :
    InPeirce0E1 (X * Y) := by
  let XR : RealAlbertMatrix := equiv.symm X
  let YR : RealAlbertMatrix := equiv.symm Y
  have hfromZorn_zero : RealSplitOctZornAlignment.fromZorn
      (ZornVectorMatrix.zero : ZornVectorMatrix ℝ) = 0 := by
    apply RealSplitOct.ext <;> rfl
  have htoZorn_zero : RealSplitOctZornAlignment.toZorn
      (0 : RealSplitOct) = (0 : ZornVectorMatrix ℝ) := by
    apply ZornVectorMatrix.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  have hXR : InRealPeirce0E1 XR := by
    rcases hX with ⟨h1, ha, hc⟩
    simp [XR, InRealPeirce0E1, equiv_symm_apply, fromH3, h1, ha, hc,
      hfromZorn_zero]
  have hYR : InRealPeirce0E1 YR := by
    rcases hY with ⟨h1, ha, hc⟩
    simp [YR, InRealPeirce0E1, equiv_symm_apply, fromH3, h1, ha, hc,
      hfromZorn_zero]
  have hmul := realAlbertMul_preserves_peirce0E1 hXR hYR
  have htransport := InfoGeometry.Algebra.RealAlbertMatrix.toH3_mul XR YR
  have hXR' : toH3 XR = X := by
    exact equiv.apply_symm_apply X
  have hYR' : toH3 YR = Y := by
    exact equiv.apply_symm_apply Y
  rw [hXR', hYR', candidateJordanMul_eq_mul] at htransport
  rcases hmul with ⟨h1, hz2, hz3⟩
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg H3Zorn.α₁ htransport
    calc
      (X * Y).α₁ = (toH3 (RealAlbertMatrix.mul XR YR)).α₁ := h.symm
      _ = (RealAlbertMatrix.mul XR YR).α₁ := rfl
      _ = 0 := h1
  · have h := congrArg H3Zorn.a htransport
    calc
      (X * Y).a = (toH3 (RealAlbertMatrix.mul XR YR)).a := h.symm
      _ = RealSplitOctZornAlignment.toZorn (RealAlbertMatrix.mul XR YR).z₃ := rfl
      _ = 0 := by rw [hz3]; exact htoZorn_zero
  · have h := congrArg H3Zorn.c htransport
    calc
      (X * Y).c = (toH3 (RealAlbertMatrix.mul XR YR)).c := h.symm
      _ = RealSplitOctZornAlignment.toZorn (RealAlbertMatrix.mul XR YR).z₂ := rfl
      _ = 0 := by rw [hz2]; exact htoZorn_zero

/-- `V₀(e₁)` is stable under scalar multiplication. -/
theorem smul_preserves_peirce0E1
    (r : ℝ) {X : H3Zorn ℝ} (hX : InPeirce0E1 X) :
    InPeirce0E1 (r • X) := by
  rcases hX with ⟨h1, ha, hc⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [H3Zorn.smul_readback, h1]
  · simpa [H3Zorn.smul_readback, ZornVectorMatrix.smul_zero, ha]
  · simpa [H3Zorn.smul_readback, ZornVectorMatrix.smul_zero, hc]

/-- `V₀(e₁)` is stable under subtraction. -/
theorem sub_preserves_peirce0E1
    {X Y : H3Zorn ℝ}
    (hX : InPeirce0E1 X) (hY : InPeirce0E1 Y) :
    InPeirce0E1 (X - Y) := by
  rcases hX with ⟨hX1, hXa, hXc⟩
  rcases hY with ⟨hY1, hYa, hYc⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [H3Zorn.sub_readback, hX1, hY1]
  · apply ZornVectorMatrix.ext <;>
      simp [H3Zorn.sub_readback, hXa, hYa, ZornVectorMatrix.sub_eq_add_neg,
        ZornVectorMatrix.neg, ZornVectorMatrix.add, ZornVectorMatrix.zero]
  · apply ZornVectorMatrix.ext <;>
      simp [H3Zorn.sub_readback, hXc, hYc, ZornVectorMatrix.sub_eq_add_neg,
        ZornVectorMatrix.neg, ZornVectorMatrix.add, ZornVectorMatrix.zero]

/-- Jordan-polynomial form of the quadratic representation:
`P(y)x = 2 y ∘ (y ∘ x) - y² ∘ x`. -/
def quadraticP (y x : H3Zorn ℝ) : H3Zorn ℝ :=
  (2 : ℝ) • (y * (y * x)) - (y * y) * x

/-- The Jordan-polynomial definition is exactly the repository's existing
cubic quadratic operator `H3Zorn.U`. -/
theorem quadraticP_eq_U (y x : H3Zorn ℝ) :
    quadraticP y x = H3Zorn.U y x := by
  rw [quadraticP]
  change
    (2 : ℝ) • candidateJordanMul y (candidateJordanMul y x) -
        candidateJordanMul (candidateJordanMul y y) x = H3Zorn.U y x
  rw [H3ZornJordanQuadraticReconstruction]
  simp only [candidateJordanMul, H3Zorn.T_smul_left,
    H3Zorn.T_smul_right, smul_smul]
  module

/-- Main preservation theorem: if both the quadratic parameter and argument
belong to `V₀(e₁)`, then the quadratic Jordan representation stays in that
10-dimensional Peirce space. -/
theorem quadraticP_preserves_peirce0E1
    {y x : H3Zorn ℝ}
    (hy : InPeirce0E1 y) (hx : InPeirce0E1 x) :
    InPeirce0E1 (quadraticP y x) := by
  apply sub_preserves_peirce0E1
  · apply smul_preserves_peirce0E1
    apply jordanMul_preserves_peirce0E1 hy
    exact jordanMul_preserves_peirce0E1 hy hx
  · apply jordanMul_preserves_peirce0E1
    · exact jordanMul_preserves_peirce0E1 hy hy
    · exact hx

/-- Equivalent statement for the repository-native cubic `U`-operator. -/
theorem U_preserves_peirce0E1
    {y x : H3Zorn ℝ}
    (hy : InPeirce0E1 y) (hx : InPeirce0E1 x) :
    InPeirce0E1 (H3Zorn.U y x) := by
  rw [← quadraticP_eq_U]
  exact quadraticP_preserves_peirce0E1 hy hx

/-! ## Explicit ten-dimensional carrier -/

/-- Ten real coordinates for the lower-right Hermitian `H₂(𝕆_s)` block. -/
abbrev Minkowski10 := Fin 10 → ℝ

/-- Reconstruct the native split-octonion `b` block from eight coordinates. -/
def zornOfMinkowski10 (v : Minkowski10) : ZornVectorMatrix ℝ :=
  { a := v 2
    v := fun i => match i with
      | 0 => v 3
      | 1 => v 4
      | 2 => v 5
    w := fun i => match i with
      | 0 => v 6
      | 1 => v 7
      | 2 => v 8
    b := v 9 }

/-- Embedding of ten-dimensional coordinates into `V₀(e₁)`. -/
def toH3 (v : Minkowski10) : H3Zorn ℝ :=
  { α₁ := 0
    α₂ := v 0
    α₃ := v 1
    a := ZornVectorMatrix.zero
    b := zornOfMinkowski10 v
    c := ZornVectorMatrix.zero }

/-- Coordinate readback from `H3Zorn` to the ten-dimensional lower-right block. -/
def fromH3 (X : H3Zorn ℝ) : Minkowski10 :=
  ![X.α₂, X.α₃,
    X.b.a, X.b.v 0, X.b.v 1, X.b.v 2,
    X.b.w 0, X.b.w 1, X.b.w 2, X.b.b]

@[simp] theorem toH3_in_peirce0E1 (v : Minkowski10) :
    InPeirce0E1 (toH3 v) := by
  exact ⟨rfl, rfl, rfl⟩

@[simp] theorem fromH3_toH3 (v : Minkowski10) :
    fromH3 (toH3 v) = v := by
  ext i
  fin_cases i <;> rfl

/-- Elements in `V₀(e₁)` are reconstructed exactly from the ten-coordinate
readback. -/
theorem toH3_fromH3_of_mem
    {X : H3Zorn ℝ} (hX : InPeirce0E1 X) :
    toH3 (fromH3 X) = X := by
  rcases hX with ⟨h1, ha, hc⟩
  apply H3Zorn.ext_h3
  · exact h1.symm
  · rfl
  · rfl
  · simpa [toH3, ha]
  · apply ZornVectorMatrix.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  · simpa [toH3, hc]

/-- The coordinate carrier really has real dimension ten. -/
theorem finrank_minkowski10 : Module.finrank ℝ Minkowski10 = 10 := by
  simp [Minkowski10]

/-- The induced ten-dimensional quadratic representation. -/
def P10 (u v : Minkowski10) : Minkowski10 :=
  fromH3 (quadraticP (toH3 u) (toH3 v))

/-- The ten-dimensional embedding strictly intertwines the induced operation
with the native split-Albert quadratic representation. -/
theorem toH3_intertwines_P10 (u v : Minkowski10) :
    toH3 (P10 u v) = quadraticP (toH3 u) (toH3 v) := by
  apply toH3_fromH3_of_mem
  exact quadraticP_preserves_peirce0E1
    (toH3_in_peirce0E1 u) (toH3_in_peirce0E1 v)

/-- Native `U`-operator form of the ten-dimensional intertwining theorem. -/
theorem toH3_intertwines_U (u v : Minkowski10) :
    toH3 (P10 u v) = H3Zorn.U (toH3 u) (toH3 v) := by
  rw [toH3_intertwines_P10, quadraticP_eq_U]

/-- Compact closure packet. -/
theorem peirce0_quadratic_representation_packet :
    Module.finrank ℝ Minkowski10 = 10 ∧
    (∀ y x : H3Zorn ℝ,
      InPeirce0E1 y → InPeirce0E1 x →
        InPeirce0E1 (H3Zorn.U y x)) := by
  exact ⟨finrank_minkowski10,
    fun y x hy hx => U_preserves_peirce0E1 hy hx⟩

end InfoGeometry.Canonical.H3ZornPeirce0QuadraticRepresentation
