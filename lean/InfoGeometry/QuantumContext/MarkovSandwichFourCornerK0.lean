/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovTwoSidedGroupInverse
import InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0

/-!
# Two-sided Markov group inverse and the existing four-corner split

For `L = 1 - P` and a matrix group inverse `G`, the group inverse of
`X ↦ L * (X * L)` is `X ↦ G * (X * G)`. Its regular idempotent is the
range-range Peirce endomorphism for `E = L * G`; its complementary idempotent
is the sum of the other three existing Peirce endomorphisms. Thus the active
range of the two-sided group inverse is exactly the range-range corner already
used by the projective-module `K₀(ℝ)` decomposition. No `K₀(Matrix ι ι ℝ)`
claim is made.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovSandwichFourCornerK0

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0
open InfoGeometry.QuantumContext.MarkovTwoSidedGroupInverse

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def rangeIdempotent (P G : MatrixCarrier (ι := ι)) : MatrixCarrier (ι := ι) :=
  markovRangeIdempotent P G

private def kernelComplement (P G : MatrixCarrier (ι := ι)) : MatrixCarrier (ι := ι) :=
  1 - markovRangeIdempotent P G

/-- The regular idempotent of the two-sided Markov group-inverse pair is the
range-range Peirce endomorphism from the existing four-corner decomposition. -/
theorem markovSandwich_regularIdempotent_eq_rangeRange
    (P G : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G) :
    regularIdempotent
        (cornerMap (1 - P) (1 - P)) (cornerMap G G) =
      cornerEnd (rangeIdempotent P G) (kernelComplement P G) .rangeRange := by
  change cornerMap (1 - P) (1 - P) * cornerMap G G =
    cornerEnd (rangeIdempotent P G) (kernelComplement P G) .rangeRange
  rw [cornerMap_mul]
  change cornerMap ((1 - P) * G) (G * (1 - P)) =
    cornerEnd (markovRangeIdempotent P G)
      (1 - markovRangeIdempotent P G) .rangeRange
  change cornerMap ((1 - P) * G) (G * (1 - P)) =
    cornerMap ((1 - P) * G) ((1 - P) * G)
  rw [← hG.2.2]

/-- The complementary idempotent of the two-sided Markov group inverse is
the sum of the range-kernel, kernel-range, and kernel-kernel Peirce maps. -/
theorem markovSandwich_principalIdempotent_eq_otherThreeCorners
    (P G : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G) :
    principalIdempotent
        (cornerMap (1 - P) (1 - P)) (cornerMap G G) =
      cornerEnd (rangeIdempotent P G) (kernelComplement P G) .rangeKernel +
        cornerEnd (rangeIdempotent P G) (kernelComplement P G) .kernelRange +
        cornerEnd (rangeIdempotent P G) (kernelComplement P G) .kernelKernel := by
  let E := rangeIdempotent P G
  let F := kernelComplement P G
  have hsum : E + F = 1 := by
    dsimp [E, F, rangeIdempotent, kernelComplement]
    noncomm_ring
  have hcorners : cornerEnd E F .rangeRange + cornerEnd E F .rangeKernel +
      cornerEnd E F .kernelRange + cornerEnd E F .kernelKernel = 1 := by
    apply LinearMap.ext
    intro X
    simp only [cornerEnd, cornerMap, Module.End.one_apply]
    change E * (X * E) + E * (X * F) + F * (X * E) + F * (X * F) = X
    calc
      _ = (E + F) * (X * (E + F)) := by noncomm_ring
      _ = X := by rw [hsum]; simp
  change 1 - regularIdempotent
      (cornerMap (1 - P) (1 - P)) (cornerMap G G) = _
  rw [markovSandwich_regularIdempotent_eq_rangeRange P G hG]
  change 1 - cornerEnd E F .rangeRange = _
  rw [← hcorners]
  noncomm_ring

/-- The image of the two-sided regular idempotent is exactly the existing
range-range Peirce submodule, which is the first projective-module summand in
`markovMatrixFourCornerK0_split`. -/
theorem markovSandwich_regularRange_eq_rangeRangeCorner
    (P G : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G) :
    LinearMap.range
        (regularIdempotent
          (cornerMap (1 - P) (1 - P)) (cornerMap G G)) =
      LinearMap.range
        (cornerEnd (rangeIdempotent P G) (kernelComplement P G) .rangeRange) := by
  rw [markovSandwich_regularIdempotent_eq_rangeRange P G hG]

end InfoGeometry.QuantumContext.MarkovSandwichFourCornerK0
