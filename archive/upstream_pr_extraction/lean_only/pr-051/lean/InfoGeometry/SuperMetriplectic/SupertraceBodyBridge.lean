import InfoGeometry.Algebraic.SplitSuperGeometry
import InfoGeometry.OperatorAlgebra.ModularWeightTrace

/-!
# Operator supertrace bridge

This module is intentionally operatorial.  The former scalar `evenQuadratic`,
`oddQuadratic`, and `nilpotentCancellation` packet was only bookkeeping: it
did not construct a graded operator, a trace/weight, or a noncommutative
Berezinian.  The maintained owners for those objects are
`ParityInvolution.supertrace`, `ParityPreservingOperatorAction`, and the
split-Clifford supervolume API.
-/

namespace InfoGeometry.SuperMetriplectic

namespace SplitParitySupertraceTranslation

open InfoGeometry.Algebraic.SplitSignature

/-- The split-Clifford endomorphism carrier. -/
abbrev SplitParitySupertraceShadow (n : ℕ) := SplitCliffordEnd n

namespace SplitParitySupertraceShadow

/-- The canonical grade involution as an endomorphism of the carrier. -/
noncomputable def parity {n : ℕ}
    (_ : SplitParitySupertraceShadow n) : SplitCliffordEnd n :=
  parityOp n

/-- The parity-weighted trace supplied by the split-Clifford owner. -/
noncomputable def supertraceReadout {n : ℕ}
    (_ : SplitParitySupertraceShadow n) : SplitCliffordEnd n → ℝ :=
  cliffordSupertrace n

/-- The positive exponential Berezinian readout. -/
noncomputable def superBerezinianReadout {n : ℕ}
    (_ : SplitParitySupertraceShadow n) : SplitCliffordEnd n → ℝ :=
  superBerezinian n

/-- The negative logarithmic supervolume potential. -/
noncomputable def supervolumePotential {n : ℕ}
    (_ : SplitParitySupertraceShadow n) : SplitCliffordEnd n → ℝ :=
  superEffectiveAction n

end SplitParitySupertraceShadow

@[simp]
theorem parity_comp_self (n : ℕ) (x : Cl_nn n) :
    parityOp n ((parityOp n) x) = x :=
  InfoGeometry.Algebraic.SplitSuperGeometry.parityOp_comp_self n x

@[simp]
theorem supervolumePotential_eq_neg_log_superBerezinian
    (n : ℕ) (x : SplitCliffordEnd n) :
    (superEffectiveAction n) x = - Real.log ((superBerezinian n) x) :=
  InfoGeometry.Algebraic.SplitSuperGeometry.superEffectiveAction_eq_neg_log_superBerezinian n x

theorem superBerezinianReadout_pos
    (n : ℕ) (x : SplitCliffordEnd n) :
    0 < SplitParitySupertraceShadow.superBerezinianReadout x x := by
  change 0 < superBerezinian n x
  exact InfoGeometry.Algebraic.SplitSuperGeometry.superBerezinian_pos n x

end SplitParitySupertraceTranslation

end InfoGeometry.SuperMetriplectic
