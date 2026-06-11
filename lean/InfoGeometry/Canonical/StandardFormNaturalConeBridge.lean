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

@[rep_depth operator]
structure NaturalConeStandardFormInterface
    (Alg Hilb NormalPositive : Type*) where
  act : Alg → Hilb → Hilb
  J : Hilb → Hilb
  cone : Set Hilb
  isNormalPositive : NormalPositive → Prop
  coneVector : NormalPositive → Hilb
  eval : NormalPositive → Alg → ℝ
  innerReadout : Hilb → Hilb → ℝ
  coneVector_mem :
    ∀ (ω : NormalPositive), isNormalPositive ω → cone (coneVector ω)
  eval_eq_vector_readout :
    ∀ (ω : NormalPositive) (A : Alg), isNormalPositive ω →
      eval ω A = innerReadout (act A (coneVector ω)) (coneVector ω)
  J_fixes_cone :
    ∀ (ξ : Hilb), cone ξ → J ξ = ξ

namespace NaturalConeStandardFormInterface

variable {Alg Hilb NormalPositive : Type*}
variable (S : NaturalConeStandardFormInterface Alg Hilb NormalPositive)

@[rep_depth operator]
theorem coneVector_mem_of_normal
    (ω : NormalPositive) (hω : S.isNormalPositive ω) :
    S.cone (S.coneVector ω) :=
  S.coneVector_mem ω hω

@[rep_depth operator]
theorem eval_eq_vector_readout_of_normal
    (ω : NormalPositive) (A : Alg) (hω : S.isNormalPositive ω) :
    S.eval ω A =
      S.innerReadout (S.act A (S.coneVector ω)) (S.coneVector ω) :=
  S.eval_eq_vector_readout ω A hω

@[rep_depth operator]
theorem J_fixes_coneVector
    (ω : NormalPositive) (hω : S.isNormalPositive ω) :
    S.J (S.coneVector ω) = S.coneVector ω :=
  S.J_fixes_cone (S.coneVector ω) (S.coneVector_mem ω hω)

end NaturalConeStandardFormInterface

end InfoGeometry.Canonical.StandardFormNaturalConeBridge
