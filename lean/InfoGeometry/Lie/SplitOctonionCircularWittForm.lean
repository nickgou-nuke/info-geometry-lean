import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Algebra.Zorn.SplitQuaternionCore
import InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes

/-!
# The Witt form in genuine circular Peirce coordinates

The circular Peirce basis identifies the split-octonion carrier with
`Coord := Fin 8 → ℝ`.  This file records the resulting `(4,4)` Witt
decomposition on the coordinate carrier.  The two summands are defined by
their coordinate support; no associativity of the octonion multiplication is
used.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularWittForm

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Canonical.ZornMatrix

abbrev Coord := Fin 8 → ℝ

/-- The polar form associated to the transported circular quadratic form. -/
def circularPeircePolar (x y : Coord) : ℝ :=
  x 0 * y 4 + x 4 * y 0 -
    (x 1 * y 5 + x 5 * y 1 +
      x 2 * y 6 + x 6 * y 2 +
      x 3 * y 7 + x 7 * y 3)

/-- The explicit circular Witt quadratic polynomial. -/
def circularWittQuadratic (x : Coord) : ℝ :=
  x 0 * x 4 - (x 1 * x 5 + x 2 * x 6 + x 3 * x 7)

/-- The diagonal `V → V ⊕ V` embedding of the circular Witt carrier. -/
noncomputable def minkowskiDiagonalEmbedding :
    (Fin 4 → ℝ) →ₗ[ℝ] Coord where
  toFun u i := if h : i.val < 4 then u ⟨i.val, by omega⟩ else u ⟨i.val - 4, by omega⟩
  map_add' u v := by
    ext i
    by_cases hi : i.val < 4 <;> simp [hi]
  map_smul' r u := by
    ext i
    by_cases hi : i.val < 4 <;> simp [hi]

theorem minkowskiDiagonalEmbedding_apply_left (u : Fin 4 → ℝ) (i : Fin 4) :
    minkowskiDiagonalEmbedding u (Fin.castAdd 4 i) = u i := by
  simp [minkowskiDiagonalEmbedding]

theorem minkowskiDiagonalEmbedding_apply_right (u : Fin 4 → ℝ) (i : Fin 4) :
    minkowskiDiagonalEmbedding u (Fin.addNat i 4) = u i := by
  simp [minkowskiDiagonalEmbedding]

theorem circularWittQuadratic_minkowskiDiagonal (u : Fin 4 → ℝ) :
    circularWittQuadratic (minkowskiDiagonalEmbedding u) =
      u 0 * u 0 - (u 1 * u 1 + u 2 * u 2 + u 3 * u 3) := by
  simp [circularWittQuadratic, minkowskiDiagonalEmbedding]

theorem circularPeircePolar_minkowskiDiagonal (u v : Fin 4 → ℝ) :
    circularPeircePolar (minkowskiDiagonalEmbedding u)
        (minkowskiDiagonalEmbedding v) =
      u 0 * v 0 + u 0 * v 0 -
        (u 1 * v 1 + u 1 * v 1 +
          u 2 * v 2 + u 2 * v 2 +
          u 3 * v 3 + u 3 * v 3) := by
  simp [circularPeircePolar, minkowskiDiagonalEmbedding]

theorem circularPeircePolar_add_left (x₁ x₂ y : Coord) :
    circularPeircePolar (x₁ + x₂) y =
      circularPeircePolar x₁ y + circularPeircePolar x₂ y := by
  simp [circularPeircePolar, add_mul]
  ring

theorem circularPeircePolar_smul_left (r : ℝ) (x y : Coord) :
    circularPeircePolar (r • x) y = r * circularPeircePolar x y := by
  simp [circularPeircePolar, smul_eq_mul]
  ring

theorem circularPeircePolar_add_right (x y₁ y₂ : Coord) :
    circularPeircePolar x (y₁ + y₂) =
      circularPeircePolar x y₁ + circularPeircePolar x y₂ := by
  simp [circularPeircePolar, mul_add]
  ring

theorem circularPeircePolar_symm (x y : Coord) :
    circularPeircePolar x y = circularPeircePolar y x := by
  simp [circularPeircePolar]
  ring

/-- The positive circular sector, supported on coordinates `0,1,2,3`. -/
def positiveCircularSubmodule : Submodule ℝ Coord where
  carrier := {x | ∀ i : Fin 8, 4 ≤ i.val → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro r x hx i hi
    simp [hx i hi]

/-- The negative circular sector, supported on coordinates `4,5,6,7`. -/
def negativeCircularSubmodule : Submodule ℝ Coord where
  carrier := {x | ∀ i : Fin 8, i.val < 4 → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro r x hx i hi
    simp [hx i hi]

/-- The coordinate inclusion of the positive four-plane. -/
noncomputable def positiveCircularEmbedding :
    (Fin 4 → ℝ) →ₗ[ℝ] Coord where
  toFun a i := if h : i.val < 4 then a ⟨i.val, h⟩ else 0
  map_add' a b := by
    ext i
    by_cases h : i.val < 4 <;> simp [h]
  map_smul' r a := by
    ext i
    by_cases h : i.val < 4 <;> simp [h]

/-- The coordinate inclusion of the negative four-plane. -/
noncomputable def negativeCircularEmbedding :
    (Fin 4 → ℝ) →ₗ[ℝ] Coord where
  toFun b i := if h : 4 ≤ i.val then b ⟨i.val - 4, by omega⟩ else 0
  map_add' a b := by
    ext i
    by_cases h : 4 ≤ i.val <;> simp [h]
  map_smul' r b := by
    ext i
    by_cases h : 4 ≤ i.val <;> simp [h]

theorem positiveCircularEmbedding_injective :
    Function.Injective positiveCircularEmbedding := by
  intro a b h
  funext i
  have hi : (Fin.castAdd 4 i : Fin 8).val < 4 := by
    simp
  have := congrFun h (Fin.castAdd 4 i)
  simpa [positiveCircularEmbedding, hi] using this

theorem negativeCircularEmbedding_injective :
    Function.Injective negativeCircularEmbedding := by
  intro a b h
  funext i
  have hi : 4 ≤ (Fin.addNat i 4 : Fin 8).val := by
    simp
  have := congrFun h (Fin.addNat i 4)
  simpa [negativeCircularEmbedding, hi] using this

theorem positiveCircularSubmodule_eq_range :
    positiveCircularSubmodule = LinearMap.range positiveCircularEmbedding := by
  apply le_antisymm
  · rintro x hx
    refine ⟨fun i => x (Fin.castLE (by decide : 4 ≤ 8) i), ?_⟩
    ext i
    by_cases hi : i.val < 4
    · simp [positiveCircularEmbedding, hi]
    · simp [positiveCircularEmbedding, hi, hx i (Nat.le_of_not_gt hi)]
  · rintro x ⟨a, rfl⟩ i hi
    simp [positiveCircularEmbedding, Nat.not_lt.mpr hi]

theorem negativeCircularSubmodule_eq_range :
    negativeCircularSubmodule = LinearMap.range negativeCircularEmbedding := by
  apply le_antisymm
  · rintro x hx
    refine ⟨(fun i => x (Fin.addNat i 4)), ?_⟩
    ext i
    by_cases hi : 4 ≤ i.val
    · simp [negativeCircularEmbedding, hi]
    · simp [negativeCircularEmbedding, hi, hx i (Nat.lt_of_not_ge hi)]
  · rintro x ⟨b, rfl⟩ i hi
    simp [negativeCircularEmbedding, Nat.not_le.mpr hi]

theorem positive_isTotallyIsotropic
    {x y : Coord} (hx : x ∈ positiveCircularSubmodule)
    (hy : y ∈ positiveCircularSubmodule) :
    circularPeircePolar x y = 0 := by
  have hx4 := hx 4 (by decide)
  have hx5 := hx 5 (by decide)
  have hx6 := hx 6 (by decide)
  have hx7 := hx 7 (by decide)
  have hy4 := hy 4 (by decide)
  have hy5 := hy 5 (by decide)
  have hy6 := hy 6 (by decide)
  have hy7 := hy 7 (by decide)
  simp [circularPeircePolar, hx4, hx5, hx6, hx7, hy4, hy5, hy6, hy7]

theorem negative_isTotallyIsotropic
    {x y : Coord} (hx : x ∈ negativeCircularSubmodule)
    (hy : y ∈ negativeCircularSubmodule) :
    circularPeircePolar x y = 0 := by
  have hx0 := hx 0 (by decide)
  have hx1 := hx 1 (by decide)
  have hx2 := hx 2 (by decide)
  have hx3 := hx 3 (by decide)
  have hy0 := hy 0 (by decide)
  have hy1 := hy 1 (by decide)
  have hy2 := hy 2 (by decide)
  have hy3 := hy 3 (by decide)
  simp [circularPeircePolar, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]

theorem circularPeircePolar_positive_negative (a b : Fin 4 → ℝ) :
    circularPeircePolar (positiveCircularEmbedding a)
      (negativeCircularEmbedding b) =
      a 0 * b 0 - (a 1 * b 1 + a 2 * b 2 + a 3 * b 3) := by
  simp [circularPeircePolar, positiveCircularEmbedding,
    negativeCircularEmbedding]

def positivePart (x : Coord) : Coord := fun i =>
  if i.val < 4 then x i else 0

def negativePart (x : Coord) : Coord := fun i =>
  if 4 ≤ i.val then x i else 0

theorem positivePart_mem (x : Coord) :
    positivePart x ∈ positiveCircularSubmodule := by
  intro i hi
  simp [positivePart, Nat.not_lt.mpr hi]

theorem negativePart_mem (x : Coord) :
    negativePart x ∈ negativeCircularSubmodule := by
  intro i hi
  simp [negativePart, Nat.not_le.mpr hi]

theorem positivePart_add_negativePart (x : Coord) :
    positivePart x + negativePart x = x := by
  funext i
  by_cases hi : i.val < 4
  · have hnot : ¬ 4 ≤ i.val := Nat.not_le.mpr hi
    simp [positivePart, negativePart, hi, hnot]
  · have hle : 4 ≤ i.val := Nat.le_of_not_gt hi
    simp [positivePart, negativePart, hi, hle]

theorem circularWittDecomposition :
    positiveCircularSubmodule ⊔ negativeCircularSubmodule = ⊤ ∧
      positiveCircularSubmodule ⊓ negativeCircularSubmodule = ⊥ := by
  constructor
  · apply le_antisymm le_top
    intro x hx
    rw [← positivePart_add_negativePart x]
    exact Submodule.add_mem _
      (show positivePart x ∈ positiveCircularSubmodule ⊔ negativeCircularSubmodule from
        (show positiveCircularSubmodule ≤ positiveCircularSubmodule ⊔ negativeCircularSubmodule from le_sup_left)
          (positivePart_mem x))
      (show negativePart x ∈ positiveCircularSubmodule ⊔ negativeCircularSubmodule from
        (show negativeCircularSubmodule ≤ positiveCircularSubmodule ⊔ negativeCircularSubmodule from le_sup_right)
          (negativePart_mem x))
  · apply le_antisymm
    · intro x hx
      change x = 0
      funext i
      fin_cases i
      · exact hx.2 0 (by decide)
      · exact hx.2 1 (by decide)
      · exact hx.2 2 (by decide)
      · exact hx.2 3 (by decide)
      · exact hx.1 4 (by decide)
      · exact hx.1 5 (by decide)
      · exact hx.1 6 (by decide)
      · exact hx.1 7 (by decide)
    · exact bot_le

theorem circularPairing_nondegenerate_left
    {x : Coord} (hx : ∀ y : Coord, circularPeircePolar x y = 0) :
    x = 0 := by
  funext i
  fin_cases i
  · have h := hx (Pi.single 4 1)
    simpa [circularPeircePolar, Pi.single_apply] using h
  · have h := hx (Pi.single 5 1)
    simpa [circularPeircePolar, Pi.single_apply] using h
  · have h := hx (Pi.single 6 1)
    simpa [circularPeircePolar, Pi.single_apply] using h
  · have h := hx (Pi.single 7 1)
    simpa [circularPeircePolar, Pi.single_apply] using h
  · have h := hx (Pi.single 0 1)
    simpa [circularPeircePolar, Pi.single_apply] using h
  · have h := hx (Pi.single 1 1)
    simpa [circularPeircePolar, Pi.single_apply] using h
  · have h := hx (Pi.single 2 1)
    simpa [circularPeircePolar, Pi.single_apply] using h
  · have h := hx (Pi.single 3 1)
    simpa [circularPeircePolar, Pi.single_apply] using h

theorem circularPairing_nondegenerate_right
    {y : Coord} (hy : ∀ x : Coord, circularPeircePolar x y = 0) :
    y = 0 := by
  apply circularPairing_nondegenerate_left
  intro x
  rw [circularPeircePolar_symm]
  exact hy x

theorem circularPairing_nondegenerate :
    (∀ x : Coord, (∀ y : Coord, circularPeircePolar x y = 0) → x = 0) ∧
      (∀ y : Coord, (∀ x : Coord, circularPeircePolar x y = 0) → y = 0) := by
  exact ⟨fun x hx => circularPairing_nondegenerate_left hx,
    fun y hy => circularPairing_nondegenerate_right hy⟩

theorem circularPairing_nondegenerate_on_sectors :
    (∀ x ∈ positiveCircularSubmodule,
      (∀ y ∈ negativeCircularSubmodule, circularPeircePolar x y = 0) → x = 0) ∧
      (∀ y ∈ negativeCircularSubmodule,
        (∀ x ∈ positiveCircularSubmodule, circularPeircePolar x y = 0) → y = 0) := by
  constructor
  · intro x hx hxy
    apply circularPairing_nondegenerate_left
    intro y
    rw [← positivePart_add_negativePart y, circularPeircePolar_add_right]
    rw [positive_isTotallyIsotropic hx (positivePart_mem y)]
    rw [hxy (negativePart y) (negativePart_mem y)]
    simp
  · intro y hy hxy
    apply circularPairing_nondegenerate_right
    intro x
    rw [← positivePart_add_negativePart x, circularPeircePolar_add_left]
    rw [hxy (positivePart x) (positivePart_mem x)]
    rw [negative_isTotallyIsotropic (negativePart_mem x) hy]
    simp

theorem circularPeircePolar_from_wittQuadratic (x y : Coord) :
    circularPeircePolar x y =
      circularWittQuadratic (x + y) - circularWittQuadratic x -
        circularWittQuadratic y := by
  simp [circularPeircePolar, circularWittQuadratic]
  ring

end InfoGeometry.Lie.SplitOctonionCircularWittForm
