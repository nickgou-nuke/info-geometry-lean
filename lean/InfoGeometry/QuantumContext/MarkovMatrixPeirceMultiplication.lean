/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0

/-!
# Multiplication routing for the four Markov Peirce corners

The four ranges from `MarkovMatrixFourCornerK0` split the full matrix module
additively. This file proves their multiplicative routing law: compatible
middle supports compose into the corner with the two outer supports, while
incompatible supports multiply to zero.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovMatrixPeirceMultiplication

open InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0

variable {ι : Type} [Fintype ι]

abbrev MatrixCarrier := Matrix ι ι ℝ
abbrev MatrixEnd := Module.End ℝ (MatrixCarrier (ι := ι))

/-- The two support labels underlying the four existing corner labels. -/
inductive SupportSide where
  | range
  | kernel
  deriving DecidableEq

def cornerLeftSide : Corner → SupportSide
  | .rangeRange => .range
  | .rangeKernel => .range
  | .kernelRange => .kernel
  | .kernelKernel => .kernel

def cornerRightSide : Corner → SupportSide
  | .rangeRange => .range
  | .rangeKernel => .kernel
  | .kernelRange => .range
  | .kernelKernel => .kernel

/-- The idempotent selected by a range/kernel support label. -/
def supportIdempotent (E F : MatrixCarrier (ι := ι)) : SupportSide → MatrixCarrier (ι := ι)
  | .range => E
  | .kernel => F

/-- Existing corner label selected by its left and right support labels. -/
def cornerOfSides : SupportSide → SupportSide → Corner
  | .range, .range => .rangeRange
  | .range, .kernel => .rangeKernel
  | .kernel, .range => .kernelRange
  | .kernel, .kernel => .kernelKernel

@[simp]
theorem cornerLeftSide_cornerOfSides (s t : SupportSide) :
    cornerLeftSide (cornerOfSides s t) = s := by
  cases s <;> cases t <;> rfl

@[simp]
theorem cornerRightSide_cornerOfSides (s t : SupportSide) :
    cornerRightSide (cornerOfSides s t) = t := by
  cases s <;> cases t <;> rfl

private theorem cornerEnd_eq_sandwich (E F : MatrixCarrier (ι := ι)) (c : Corner) :
    cornerEnd E F c = cornerMap
      (supportIdempotent E F (cornerLeftSide c))
      (supportIdempotent E F (cornerRightSide c)) := by
  cases c <;> rfl

private theorem cornerEnd_apply_sandwich
    (E F X : MatrixCarrier (ι := ι)) (c : Corner) :
    cornerEnd E F c X = supportIdempotent E F (cornerLeftSide c) *
      (X * supportIdempotent E F (cornerRightSide c)) := by
  rw [cornerEnd_eq_sandwich]
  exact cornerMap_apply _ _ _

private theorem cornerEnd_idempotent_of_supports
    (E F : MatrixCarrier (ι := ι)) (c : Corner)
    (hE : E * E = E) (hF : F * F = F) :
    cornerEnd E F c * cornerEnd E F c = cornerEnd E F c := by
  apply LinearMap.ext
  intro X
  change cornerEnd E F c (cornerEnd E F c X) = cornerEnd E F c X
  rw [cornerEnd_apply_sandwich, cornerEnd_apply_sandwich]
  cases c <;> simp only [cornerLeftSide, cornerRightSide, supportIdempotent]
  · simp only [mul_assoc]
    rw [hE, ← mul_assoc E E (X * E), hE]
  · simp only [mul_assoc]
    rw [← mul_assoc E E (X * (F * F)), hE, hF]
  · simp only [mul_assoc]
    rw [← mul_assoc F F (X * (E * E)), hF, hE]
  · simp only [mul_assoc]
    rw [hF, ← mul_assoc F F (X * F), hF]

private theorem supportIdempotent_mul_eq
    (E F : MatrixCarrier (ι := ι)) (hE : E * E = E) (hF : F * F = F)
    (s : SupportSide) : supportIdempotent E F s * supportIdempotent E F s =
      supportIdempotent E F s := by
  cases s <;> simp [supportIdempotent, hE, hF]

private theorem supportIdempotent_mul_zero_of_ne
    (E F : MatrixCarrier (ι := ι)) (hEF : E * F = 0) (hFE : F * E = 0)
    {s t : SupportSide} (hst : s ≠ t) :
    supportIdempotent E F s * supportIdempotent E F t = 0 := by
  cases s <;> cases t
  · exact (hst rfl).elim
  · simpa [supportIdempotent] using hEF
  · simpa [supportIdempotent] using hFE
  · exact (hst rfl).elim

private theorem sandwich_product_corner
    (A B D x y : MatrixCarrier (ι := ι))
    (hB : B * B = B) :
    A * ((x * B * y) * D) =
      (A * (x * B)) * (B * (y * D)) := by
  calc
    A * ((x * B * y) * D) = A * (x * (B * (y * D))) := by simp only [mul_assoc]
    _ = A * (x * ((B * B) * (y * D))) := by rw [hB]
    _ = (A * (x * B)) * (B * (y * D)) := by simp only [mul_assoc]

private theorem sandwich_product_zero
    (A B C D x y : MatrixCarrier (ι := ι)) (hBC : B * C = 0) :
    (A * (x * B)) * (C * (y * D)) = 0 := by
  calc
    (A * (x * B)) * (C * (y * D)) = A * (x * (B * (C * (y * D)))) := by
      simp only [mul_assoc]
    _ = A * (x * ((B * C) * (y * D))) := by rw [← mul_assoc B C (y * D)]
    _ = 0 := by rw [hBC]; simp

/-- Compatible corner products land in the corner with the outer supports. -/
theorem corner_product_mem_of_compatible_supports
    (E F : MatrixCarrier (ι := ι))
    (hE : E * E = E) (hF : F * F = F)
    (c d : Corner) (X Y : MatrixCarrier (ι := ι))
    (hX : X ∈ LinearMap.range (cornerEnd E F c))
    (hY : Y ∈ LinearMap.range (cornerEnd E F d))
    (hCompat : cornerRightSide c = cornerLeftSide d) :
    X * Y ∈ LinearMap.range
      (cornerEnd E F (cornerOfSides (cornerLeftSide c) (cornerRightSide d))) := by
  rcases hX with ⟨x, rfl⟩
  rcases hY with ⟨y, rfl⟩
  refine ⟨x * supportIdempotent E F (cornerRightSide c) * y, ?_⟩
  rw [cornerEnd_apply_sandwich]
  let A := supportIdempotent E F (cornerLeftSide c)
  let B := supportIdempotent E F (cornerRightSide c)
  let D := supportIdempotent E F (cornerRightSide d)
  have hB : B * B = B := by dsimp [B]; exact supportIdempotent_mul_eq E F hE hF _
  have hCompat' : supportIdempotent E F (cornerRightSide c) =
      supportIdempotent E F (cornerLeftSide d) := by rw [hCompat]
  simp only [cornerEnd_apply_sandwich, cornerLeftSide_cornerOfSides,
    cornerRightSide_cornerOfSides]
  rw [← hCompat']
  simpa [A, B, D, mul_assoc] using sandwich_product_corner A B D x y hB

/-- Products of corner elements vanish when the middle support labels differ. -/
theorem corner_product_eq_zero_of_incompatible_supports
    (E F : MatrixCarrier (ι := ι))
    (hEF : E * F = 0) (hFE : F * E = 0)
    (c d : Corner) (X Y : MatrixCarrier (ι := ι))
    (hX : X ∈ LinearMap.range (cornerEnd E F c))
    (hY : Y ∈ LinearMap.range (cornerEnd E F d))
    (hIncompat : cornerRightSide c ≠ cornerLeftSide d) :
    X * Y = 0 := by
  rcases hX with ⟨x, rfl⟩
  rcases hY with ⟨y, rfl⟩
  rw [cornerEnd_apply_sandwich, cornerEnd_apply_sandwich]
  simpa only [mul_assoc] using sandwich_product_zero
    (supportIdempotent E F (cornerLeftSide c))
    (supportIdempotent E F (cornerRightSide c))
    (supportIdempotent E F (cornerLeftSide d))
    (supportIdempotent E F (cornerRightSide d)) x y
    (supportIdempotent_mul_zero_of_ne E F hEF hFE hIncompat)

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-- The compatible-corner product law specialized to the range and
complement idempotents of a Markov group inverse. -/
theorem markov_corner_product_mem_of_compatible_supports
    [DecidableEq ι]
    (P G : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse (1 - P) G)
    (c d : Corner) (X Y : MatrixCarrier (ι := ι))
    (hX : X ∈ LinearMap.range
      (cornerEnd (markovRangeIdempotent P G)
        (1 - markovRangeIdempotent P G) c))
    (hY : Y ∈ LinearMap.range
      (cornerEnd (markovRangeIdempotent P G)
        (1 - markovRangeIdempotent P G) d))
    (hCompat : cornerRightSide c = cornerLeftSide d) :
    X * Y ∈ LinearMap.range
      (cornerEnd (markovRangeIdempotent P G)
        (1 - markovRangeIdempotent P G)
        (cornerOfSides (cornerLeftSide c) (cornerRightSide d))) := by
  exact corner_product_mem_of_compatible_supports
    (markovRangeIdempotent P G) (1 - markovRangeIdempotent P G)
    (markovRangeIdempotent_idempotent P G hG)
    (markovRangeComplement_idempotent P G hG) c d X Y hX hY hCompat

/-- The incompatible-corner product vanishes for the complementary
idempotents canonically supplied by a Markov group inverse. -/
theorem markov_corner_product_eq_zero_of_incompatible_supports
    [DecidableEq ι]
    (P G : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse (1 - P) G)
    (c d : Corner) (X Y : MatrixCarrier (ι := ι))
    (hX : X ∈ LinearMap.range
      (cornerEnd (markovRangeIdempotent P G)
        (1 - markovRangeIdempotent P G) c))
    (hY : Y ∈ LinearMap.range
      (cornerEnd (markovRangeIdempotent P G)
        (1 - markovRangeIdempotent P G) d))
    (hIncompat : cornerRightSide c ≠ cornerLeftSide d) :
    X * Y = 0 := by
  exact corner_product_eq_zero_of_incompatible_supports
    (markovRangeIdempotent P G) (1 - markovRangeIdempotent P G)
    (markovRange_mul_kernelComplement_eq_zero P G hG)
    (markovKernelComplement_mul_range_eq_zero P G hG)
    c d X Y hX hY hIncompat

end InfoGeometry.QuantumContext.MarkovMatrixPeirceMultiplication
