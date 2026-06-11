import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

set_option linter.unusedSectionVars false

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.StandardFormNaturalConeBridge

@[rep_depth operator]
structure DoubledTomitaCartanCarrier (Left Right : Type*) where
  theta : Left × Right → Left × Right

@[rep_depth operator]
def IsTomitaCartanInvolution {Left Right : Type*}
    (C : DoubledTomitaCartanCarrier Left Right) : Prop :=
  ∀ x : Left × Right, C.theta (C.theta x) = x

@[rep_depth operator]
def IsTomitaCartanSelfDual {Left Right : Type*}
    (C : DoubledTomitaCartanCarrier Left Right)
    (x : Left × Right) : Prop :=
  C.theta x = x

@[rep_depth operator]
def IsTomitaCartanAntiSelfDual {Left Right : Type*}
    [Neg Left] [Neg Right]
    (C : DoubledTomitaCartanCarrier Left Right)
    (x : Left × Right) : Prop :=
  C.theta x = -x

@[rep_depth operator]
def tomitaCartanSelfDualSector {Left Right : Type*}
    (C : DoubledTomitaCartanCarrier Left Right) : Set (Left × Right) :=
  {x | IsTomitaCartanSelfDual C x}

@[rep_depth operator]
def tomitaCartanAntiSelfDualSector {Left Right : Type*}
    [Neg Left] [Neg Right]
    (C : DoubledTomitaCartanCarrier Left Right) : Set (Left × Right) :=
  {x | IsTomitaCartanAntiSelfDual C x}

namespace DoubledTomitaCartanCarrier

variable {Left Right : Type*}
variable (C : DoubledTomitaCartanCarrier Left Right)

@[rep_depth operator]
theorem theta_sq_of_isTomitaCartanInvolution
    (hC : IsTomitaCartanInvolution C)
    (x : Left × Right) :
    C.theta (C.theta x) = x :=
  hC x

@[rep_depth operator]
theorem mem_selfDualSector_iff
    (x : Left × Right) :
    x ∈ tomitaCartanSelfDualSector C ↔ C.theta x = x :=
  Iff.rfl

@[rep_depth operator]
theorem mem_antiSelfDualSector_iff
    [Neg Left] [Neg Right]
    (x : Left × Right) :
    x ∈ tomitaCartanAntiSelfDualSector C ↔ C.theta x = -x :=
  Iff.rfl

end DoubledTomitaCartanCarrier

/-! ## Natural-cone standard-form carrier -/

variable (Alg Hilb NormalPositive : Type*)
variable (act : Alg → Hilb → Hilb)
variable (J : Hilb → Hilb)
variable (cone : Set Hilb)
variable (isNormalPositive : NormalPositive → Prop)
variable (coneVector : NormalPositive → Hilb)
variable (eval : NormalPositive → Alg → ℝ)
variable (innerReadout : Hilb → Hilb → ℝ)

@[rep_depth operator]
theorem coneVector_mem_thm (ω : NormalPositive) (hω : isNormalPositive ω) :
    coneVector ω ∈ cone := by
  sorry

@[rep_depth operator]
theorem eval_eq_vector_readout_thm (ω : NormalPositive) (A : Alg) (hω : isNormalPositive ω) :
    eval ω A = innerReadout (act A (coneVector ω)) (coneVector ω) := by
  sorry

@[rep_depth operator]
theorem J_fixes_cone_thm (ξ : Hilb) (hξ : ξ ∈ cone) :
    J ξ = ξ := by
  sorry

end InfoGeometry.Canonical.StandardFormNaturalConeBridge
