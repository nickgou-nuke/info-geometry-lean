/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Streaming.WeakValueLineAlgebra
import InfoGeometry.Streaming.WeakPropertySeparation

open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
open InfoGeometry.Streaming.TwoBoundaryDyadCompression

#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.weakValue_mul_of_pre_eigenvector
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.weakValue_dyad_middle
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.weakValue_mul_defect
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.weakValue_rankOne_pre_mul
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.weakValue_rankOne_pre
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.weakValue_mul_all_left_iff
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.preLineAlgebra
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.mem_preLineAlgebra_iff
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.mem_preLineAlgebra_iff_multiplicative
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.weakValueCharacter
#print axioms InfoGeometry.Streaming.TwoBoundaryDyadCompression.weakValueCharacter_apply

example {ι : Type*} [Fintype ι] (p : RegularBoundaryPair ι) :
    boundaryDyad p ∈ preLineAlgebra p := by
  rw [mem_preLineAlgebra_iff, boundaryDyad_pre, weakValue_boundaryDyad, one_smul]

example {ι : Type*} [Fintype ι] (p : RegularBoundaryPair ι) :
    weakValueCharacter p 1 = 1 := map_one _

open InfoGeometry.Streaming.WeakPropertySeparation

example : weakValue boundaryPair
    (corridorSpinZ * (1 - boundaryDyad boundaryPair) * corridorSpinZ) = -4 := by
  rw [← weakValue_mul_defect, corridorSpinZ_square_weakValue, corridorSpinZ_weakValue]
  norm_num
