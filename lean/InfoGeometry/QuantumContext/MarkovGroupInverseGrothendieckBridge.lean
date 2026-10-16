/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceProjectorGrothendieckClass
import InfoGeometry.QuantumContext.MarkovGroupInversePetzSupport

/-!
# Additive Grothendieck readout of the Markov group-inverse split

The range idempotent `L * G` and its complement `1 - L * G` form the
orthogonal idempotent frame already used by the Peirce projector owner. This
file transports that concrete noncommutative matrix frame through the existing
additive Grothendieck class map. It makes no claim about analytic K-theory or
the Grothendieck group of projective modules.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Canonical.PeirceProjectorGrothendieckClass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The range idempotent as an element of the Peirce owner's idempotent API. -/
def markovRangeIdempotentStructure (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    Idempotent (Matrix ι ι ℝ) where
  val := markovRangeIdempotent P G
  is_idem := markovRangeIdempotent_idempotent P G hG

/-- The complementary stationary idempotent in the same API. -/
def markovKernelIdempotentStructure (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    Idempotent (Matrix ι ι ℝ) where
  val := 1 - markovRangeIdempotent P G
  is_idem := markovRangeComplement_idempotent P G hG

/-- The Markov range and complementary idempotents are orthogonal in both
orders in the full, generally noncommutative matrix ring. -/
theorem markovRange_kernelIdempotents_orthogonal
    (P G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    Orthogonal (markovRangeIdempotentStructure P G hG)
      (markovKernelIdempotentStructure P G hG) := by
  constructor
  · exact markovRange_mul_kernelComplement_eq_zero P G hG
  · exact markovKernelComplement_mul_range_eq_zero P G hG

/-- The two Markov group-inverse idempotents add to the matrix identity. -/
theorem markovRange_kernelIdempotents_sum
    (P G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    (markovRangeIdempotentStructure P G hG).val +
      (markovKernelIdempotentStructure P G hG).val = 1 := by
  exact markovRange_kernelComplement_sum P G

/-- The additive Grothendieck class of the Markov range idempotent and its
stationary complement is the class of the identity in the repository's
existing Peirce class map. -/
theorem markovGroupInverse_grothendieck_split
    (P G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    k0Class (markovRangeIdempotentStructure P G hG) +
      k0Class (markovKernelIdempotentStructure P G hG) =
        grothendieckMap (Matrix ι ι ℝ) (1 : Matrix ι ι ℝ) := by
  exact peirce_k0_motive_sum
    (markovRangeIdempotentStructure P G hG)
    (markovKernelIdempotentStructure P G hG)
    (markovRange_kernelIdempotents_orthogonal P G hG)
    (markovRange_kernelIdempotents_sum P G hG)

end InfoGeometry.QuantumContext.MarkovDrazin
