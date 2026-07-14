import InfoGeometry.Canonical.StandardFormNaturalConeBridge
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ArakiConnesHaagerupBridge

Carrier layer for the Araki--Connes--Haagerup triad.

This file does not prove Tomita--Takesaki theory, construct a crossed product,
or define an unbounded relative modular logarithm.  It only records the
data interfaces:

* Haagerup/standard-form natural cone;
* Connes cocycle / Weyl transport channel;
* Araki relative entropy readout;
* optional continuous-core weight channel.
-/

noncomputable section

namespace ArakiConnesHaagerupBridge

open InfoGeometry.Canonical.StandardFormNaturalConeBridge
open InfoGeometry.Canonical.TypeIIIModularCantorSystem

/--
Araki--Connes--Haagerup compatibility carrier.

This structure records carriers and readouts only.  It does not expose
entropy/cocycle or cone/core compatibility as theorem-like fields.
-/
@[rep_depth operator]
structure ArakiConnesHaagerupTriad
    (Alg Hilb NormalPositive Core : Type*) where
  /-- Haagerup/Araki standard-form natural-cone interface. -/
  standard :
    NaturalConeStandardFormInterface Alg Hilb NormalPositive

  /-- Connes cocycle / projective Weyl transport socket. -/
  connesCocycle :
    ℝ → Alg

  /-- Araki relative entropy readout socket. -/
  arakiRelativeEntropy :
    NormalPositive → NormalPositive → ℝ

  /-- Continuous-core carrier map. -/
  toCore :
    Alg → Core

  /-- Core weight/trace-like readout. -/
  coreWeight :
    Core → ℝ

namespace ArakiConnesHaagerupTriad

variable {Alg Hilb NormalPositive Core : Type*}
variable (T : ArakiConnesHaagerupTriad Alg Hilb NormalPositive Core)

/-- Readback: normal positive functionals are represented by natural-cone vectors. -/
@[rep_depth operator]
theorem coneVector_mem_of_normal
    (ω : NormalPositive)
    (hω : T.standard.isNormalPositive ω) :
    T.standard.coneVector ω ∈ T.standard.cone :=
  T.standard.coneVector_mem_of_normal ω hω

/-- Readback: standard-form evaluation is vector-state evaluation. -/
@[rep_depth operator]
theorem eval_eq_vector_readout_of_normal
    (ω : NormalPositive)
    (A : Alg)
    (hω : T.standard.isNormalPositive ω) :
    T.standard.eval ω A =
      T.standard.innerReadout (T.standard.act A (T.standard.coneVector ω))
        (T.standard.coneVector ω) :=
  T.standard.eval_eq_vector_readout_of_normal ω A hω

end ArakiConnesHaagerupTriad

/-! ## Cantor extension socket -/

/--
Standard-form Cantor cone system with explicit dyadic weights.

The logarithmic potential is routed through `TypeIIIModularCantorSystem`'s
finite-word definitions; positivity is carried as data for logarithmic laws.
-/
@[rep_depth thermo]
structure StandardFormCantorConeSystem
    (Alg Hilb NormalPositive : Type*) where
  /-- Standard-form natural-cone interface. -/
  standard :
    NaturalConeStandardFormInterface Alg Hilb NormalPositive

  /-- Dyadic cylinder projection carrier. -/
  cylinderProjection :
    BinaryWord → Alg

  /-- Reflected/right cylinder carrier. -/
  reflectedCylinder :
    BinaryWord → Alg

  /-- Positive reference cylinder weight. -/
  referenceWeight :
    BinaryWord → ℝ

  /-- Positivity of cylinder weights. -/
  referenceWeight_pos :
    ∀ w : BinaryWord, 0 < referenceWeight w

namespace StandardFormCantorConeSystem

variable {Alg Hilb NormalPositive : Type*}
variable (C : StandardFormCantorConeSystem Alg Hilb NormalPositive)

/-- Cylinder logarithmic potential `-log μ(w)`. -/
@[rep_depth thermo]
def cylinderPotential (w : BinaryWord) : ℝ :=
  TypeIIIModularCantorSystem.cylinderPotential C.referenceWeight w

/-- Branch logarithmic increment `-log(μ(wb)/μ(w))`. -/
@[rep_depth thermo]
def branchIncrement (w : BinaryWord) (b : Bool) : ℝ :=
  TypeIIIModularCantorSystem.branchIncrement C.referenceWeight w b

/-- One-step logarithmic chain rule along the dyadic tree. -/
@[rep_depth thermo]
theorem cylinderPotential_child
    (w : BinaryWord)
    (b : Bool) :
    C.cylinderPotential (BinaryWord.child w b) =
      C.cylinderPotential w + C.branchIncrement w b :=
  TypeIIIModularCantorSystem.cylinderPotential_child C.referenceWeight C.referenceWeight_pos w b

end StandardFormCantorConeSystem

end ArakiConnesHaagerupBridge
