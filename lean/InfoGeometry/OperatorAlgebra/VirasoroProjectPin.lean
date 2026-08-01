import InfoGeometry.External.Virasoro.VirasoroAlgebra

/-!
The vendored Virasoro implementation is the owner of the algebraic facts.
This module exposes only direct readback lemmas; repository pin metadata,
route-status enums, and populated-string certificates are not mathematical
proofs and are intentionally not represented in the Lean theorem surface.
-/

namespace InfoGeometry.OperatorAlgebra

/-- Minimal local readback for the Virasoro bracket on basis generators. -/
theorem virasoroProject_lgen_readback (K : Type*) [Field K] [CharZero K] (n m : ℤ) :
    ⁅VirasoroProject.VirasoroAlgebra.lgen K n, VirasoroProject.VirasoroAlgebra.lgen K m⁆ =
      (n - m : K) • VirasoroProject.VirasoroAlgebra.lgen K (n + m) +
        if n + m = 0 then ((n ^ 3 - n : K) / 12) • VirasoroProject.VirasoroAlgebra.cgen K else 0 := by
  exact VirasoroProject.VirasoroAlgebra.lgen_bracket (𝕜 := K) n m

/-- Minimal local readback for the Virasoro central generator. -/
theorem virasoroProject_cgen_readback (K : Type*) [Field K] [CharZero K] (Z : VirasoroProject.VirasoroAlgebra K) :
    ⁅VirasoroProject.VirasoroAlgebra.cgen K, Z⁆ = 0 := by
  exact VirasoroProject.VirasoroAlgebra.cgen_bracket (𝕜 := K) Z

end InfoGeometry.OperatorAlgebra
