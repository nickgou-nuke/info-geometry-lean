import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.RegularSupportSecondLaw

Second Law on modularly invariant Drazin regular support.

The theorem-safe principle is:

* entropy production is certified only on the regular Drazin corner `pMp`;
* the complementary Drazin defect sector `qMq` is indexed as memory/noise,
  not inserted into regular heat flow;
* modular fixedness of `p` gives no leakage from the regular support into `q`.

This module is witness-gated. It does not assert that every Drazin support
automatically carries a positive Onsager/metriplectic dissipator.
-/

noncomputable section

namespace InfoGeometry.Canonical.RegularSupportSecondLaw

/-- Abstract modular flow by multiplicative equivalences. -/
@[rep_depth krein]
structure ModularFlow (Op : Type*) [Monoid Op] where
  sigma : ℝ → Op ≃* Op
  sigma_zero : sigma 0 = MulEquiv.refl Op
  sigma_add : ∀ s t : ℝ, sigma (s + t) = (sigma s).trans (sigma t)

/-- Expectation state, not assumed tracial. -/
@[rep_depth krein]
structure RealExpectationState
    (Op : Type*) [One Op] [Mul Op] [Star Op] [AddCommMonoid Op] [SMul ℝ Op] where
  expect : Op → ℝ
  unital : expect 1 = 1
  zero : expect 0 = 0
  positive : ∀ x : Op, 0 ≤ expect (star x * x)

/--
Drazin regular support.

`p = A * AD` is required to be a self-adjoint projection.  `q` is the defect
complement.
-/
@[rep_depth krein]
structure DrazinRegularSupport (Op : Type*) [Ring Op] [Star Op] where
  A : Op
  AD : Op
  p : Op
  q : Op
  p_def : p = A * AD
  commute : A * AD = AD * A
  p_idempotent : p * p = p
  p_self_adjoint : star p = p
  q_def : q = 1 - p

/-- The regular corner condition: `x ∈ pMp`. -/
@[rep_depth krein]
def InRegularCorner
    {Op : Type*} [Ring Op] [Star Op]
    (D : DrazinRegularSupport Op) (x : Op) : Prop :=
  D.p * x * D.p = x

/-- The defect corner condition: `x ∈ qMq`. -/
@[rep_depth krein]
def InDefectCorner
    {Op : Type*} [Ring Op] [Star Op]
    (D : DrazinRegularSupport Op) (x : Op) : Prop :=
  D.q * x * D.q = x

/-- The Drazin support is fixed by the modular flow. -/
@[rep_depth krein]
def ModularFixedSupport
    {Op : Type*} [Ring Op] [Star Op]
    (flow : ModularFlow Op) (D : DrazinRegularSupport Op) : Prop :=
  ∀ t : ℝ, flow.sigma t D.p = D.p

/--
Compressed regular state packet.

The intended formula is `φA(x) = φ(p*x*p) / φ(p)`, but this file keeps the
compressed state as supplied data.  The compression formula can be added later
as a stronger owner theorem once division/positivity hypotheses are fixed.
-/
@[rep_depth krein]
structure CompressedRegularState
    (Op : Type*) [Ring Op] [Star Op] [SMul ℝ Op]
    (D : DrazinRegularSupport Op) where
  baseState : RealExpectationState Op
  compressedState : RealExpectationState Op
  supported_on_regular :
    ∀ x : Op,
      compressedState.expect x =
        compressedState.expect (D.p * x * D.p)

/--
Regular Onsager dissipator.

The positivity axiom is restricted to the regular Drazin corner.
-/
@[rep_depth krein]
structure RegularOnsagerDissipator
    (Op : Type*) [Ring Op] [Star Op] [SMul ℝ Op] where
  Λ : Op → Op
  regular_preserving :
    ∀ (D : DrazinRegularSupport Op) (x : Op),
      InRegularCorner D x →
        InRegularCorner D (Λ x)
  positive_on_regular :
    ∀ (φ : RealExpectationState Op) (D : DrazinRegularSupport Op) (x : Op),
      InRegularCorner D x →
        0 ≤ φ.expect (star x * Λ x)

/-- Entropy production in the regular Drazin sector: `EP(x) = φA(x* Λ x)`. -/
@[rep_depth krein]
def entropyProduction
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (φA : RealExpectationState Op)
    (ΛA : RegularOnsagerDissipator Op)
    (x : Op) : ℝ :=
  φA.expect (star x * ΛA.Λ x)

/--
Second Law on the regular Drazin support.

If `x` lives in the regular corner `pMp`, then its entropy production is
nonnegative.
-/
@[rep_depth krein]
theorem second_law_on_regular_support
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (φA : RealExpectationState Op)
    (D : DrazinRegularSupport Op)
    (ΛA : RegularOnsagerDissipator Op)
    (x : Op)
    (hx : InRegularCorner D x) :
    0 ≤ entropyProduction φA ΛA x :=
  ΛA.positive_on_regular φA D x hx

/-- The dissipative force remains in the regular corner. -/
@[rep_depth krein]
theorem dissipator_preserves_regular_corner
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (D : DrazinRegularSupport Op)
    (ΛA : RegularOnsagerDissipator Op)
    (x : Op)
    (hx : InRegularCorner D x) :
    InRegularCorner D (ΛA.Λ x) :=
  ΛA.regular_preserving D x hx

/-- Leakage from the regular Drazin support into the defect complement. -/
@[rep_depth krein]
def leakageOperator
    {Op : Type*} [Ring Op] [Star Op]
    (flow : ModularFlow Op)
    (D : DrazinRegularSupport Op)
    (t : ℝ) : Op :=
  D.q * flow.sigma t D.p * D.p

/-- Right leakage from the regular support into the defect complement. -/
@[rep_depth krein]
def rightLeakageOperator
    {Op : Type*} [Ring Op] [Star Op]
    (flow : ModularFlow Op)
    (D : DrazinRegularSupport Op)
    (t : ℝ) : Op :=
  D.p * flow.sigma t D.p * D.q

/--
If the support is modularly fixed and `q * p = 0`, then there is no left
leakage.
-/
@[rep_depth krein]
theorem no_left_leakage_of_modular_fixed_support
    {Op : Type*} [Ring Op] [Star Op]
    (flow : ModularFlow Op)
    (D : DrazinRegularSupport Op)
    (hFix : ModularFixedSupport flow D)
    (hOrth : D.q * D.p = 0) :
    ∀ t : ℝ, leakageOperator flow D t = 0 := by
  intro t
  unfold leakageOperator
  unfold ModularFixedSupport at hFix
  rw [hFix t]
  calc
    D.q * D.p * D.p = (D.q * D.p) * D.p := rfl
    _ = 0 * D.p := by rw [hOrth]
    _ = 0 := by simp

/--
If the support is modularly fixed and `p * q = 0`, then there is no right
leakage.
-/
@[rep_depth krein]
theorem no_right_leakage_of_modular_fixed_support
    {Op : Type*} [Ring Op] [Star Op]
    (flow : ModularFlow Op)
    (D : DrazinRegularSupport Op)
    (hFix : ModularFixedSupport flow D)
    (hOrth : D.p * D.q = 0) :
    ∀ t : ℝ, rightLeakageOperator flow D t = 0 := by
  intro t
  unfold rightLeakageOperator
  unfold ModularFixedSupport at hFix
  rw [hFix t]
  calc
    D.p * D.p * D.q = (D.p * D.p) * D.q := rfl
    _ = D.p * D.q := by rw [D.p_idempotent]
    _ = 0 := hOrth

/--
No-leakage package: modular fixedness plus orthogonality forbids leakage in
both directions.
-/
@[rep_depth krein]
theorem no_leakage_of_modular_fixed_support
    {Op : Type*} [Ring Op] [Star Op]
    (flow : ModularFlow Op)
    (D : DrazinRegularSupport Op)
    (hFix : ModularFixedSupport flow D)
    (hLeftOrth : D.q * D.p = 0)
    (hRightOrth : D.p * D.q = 0) :
    (∀ t : ℝ, leakageOperator flow D t = 0)
      ∧
    (∀ t : ℝ, rightLeakageOperator flow D t = 0) :=
  ⟨
    no_left_leakage_of_modular_fixed_support flow D hFix hLeftOrth,
    no_right_leakage_of_modular_fixed_support flow D hFix hRightOrth
  ⟩

/-- Leakage energy measured by an expectation state. -/
@[rep_depth krein]
def leakageEnergy
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (φA : RealExpectationState Op)
    (flow : ModularFlow Op)
    (D : DrazinRegularSupport Op)
    (t : ℝ) : ℝ :=
  φA.expect (star (leakageOperator flow D t) * leakageOperator flow D t)

/--
If modular fixedness kills the leakage operator, then the measured leakage
energy is zero.
-/
@[rep_depth krein]
theorem leakage_energy_zero_of_modular_fixed_support
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (φA : RealExpectationState Op)
    (flow : ModularFlow Op)
    (D : DrazinRegularSupport Op)
    (hFix : ModularFixedSupport flow D)
    (hOrth : D.q * D.p = 0) :
    ∀ t : ℝ, leakageEnergy φA flow D t = 0 := by
  intro t
  unfold leakageEnergy
  rw [no_left_leakage_of_modular_fixed_support flow D hFix hOrth t]
  simpa using φA.zero

/--
Defect memory readout.

This records that the defect sector is indexed/read out separately rather than
inserted into the regular entropy production law.
-/
@[rep_depth krein]
structure DefectMemoryReadout
    (Op : Type*) [Ring Op] [Star Op]
    (D : DrazinRegularSupport Op) where
  readout : Op → ℝ
  supported_on_defect :
    ∀ x : Op, readout x = readout (D.q * x * D.q)

/--
Expectation-based defect memory index.

The intended readout is `φ(p_even) - φ(p_odd)` for defect-supported parity
projections.
-/
@[rep_depth krein]
structure DefectMemoryIndexData
    (Op : Type*) [Ring Op] [Star Op] [SMul ℝ Op]
    (D : DrazinRegularSupport Op) where
  state : RealExpectationState Op
  evenProjection : Op
  oddProjection : Op
  even_supported : InDefectCorner D evenProjection
  odd_supported : InDefectCorner D oddProjection

/-- Defect memory index `φ(p_even) - φ(p_odd)`. -/
@[rep_depth krein]
def defectMemoryIndex
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    {D : DrazinRegularSupport Op}
    (I : DefectMemoryIndexData Op D) : ℝ :=
  I.state.expect I.evenProjection - I.state.expect I.oddProjection

/--
A regular heat law plus a separate defect memory readout.

This is the theorem-safe thermodynamic split.
-/
@[rep_depth krein]
structure RegularHeatDefectMemorySplit
    (Op : Type*) [Ring Op] [Star Op] [SMul ℝ Op] where
  support : DrazinRegularSupport Op
  compressedState : RealExpectationState Op
  dissipator : RegularOnsagerDissipator Op
  defectReadout : DefectMemoryReadout Op support

/-- The heat law applies only in the regular corner of the split. -/
@[rep_depth krein]
theorem split_second_law_on_regular_corner
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (S : RegularHeatDefectMemorySplit Op)
    (x : Op)
    (hx : InRegularCorner S.support x) :
    0 ≤ entropyProduction S.compressedState S.dissipator x :=
  second_law_on_regular_support
    S.compressedState S.support S.dissipator x hx

/--
Certificate packet for the regular-support Second Law lane.

It packages the state, flow, Drazin support, dissipator, modular fixedness, and
two-sided orthogonality used by the no-leakage theorems.
-/
@[rep_depth krein]
structure RegularSupportSecondLawCertificate
    (Op : Type*) [Ring Op] [Star Op] [SMul ℝ Op] where
  state : RealExpectationState Op
  flow : ModularFlow Op
  support : DrazinRegularSupport Op
  dissipator : RegularOnsagerDissipator Op
  support_fixed : ModularFixedSupport flow support
  left_orthogonal : support.q * support.p = 0
  right_orthogonal : support.p * support.q = 0

/-- Certificate readback: modular fixed support gives two-sided no leakage. -/
@[rep_depth krein]
theorem certificate_no_leakage
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (C : RegularSupportSecondLawCertificate Op) :
    (∀ t : ℝ, leakageOperator C.flow C.support t = 0)
      ∧
    (∀ t : ℝ, rightLeakageOperator C.flow C.support t = 0) :=
  no_leakage_of_modular_fixed_support
    C.flow C.support C.support_fixed C.left_orthogonal C.right_orthogonal

/-- Certificate readback: the Second Law holds on the regular corner. -/
@[rep_depth krein]
theorem certificate_second_law
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (C : RegularSupportSecondLawCertificate Op)
    (x : Op)
    (hx : InRegularCorner C.support x) :
    0 ≤ entropyProduction C.state C.dissipator x :=
  second_law_on_regular_support C.state C.support C.dissipator x hx

/-- Certificate readback: left leakage energy vanishes. -/
@[rep_depth krein]
theorem certificate_leakage_energy_zero
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (C : RegularSupportSecondLawCertificate Op) :
    ∀ t : ℝ, leakageEnergy C.state C.flow C.support t = 0 :=
  leakage_energy_zero_of_modular_fixed_support
    C.state C.flow C.support C.support_fixed C.left_orthogonal

/-- Owner target for the regular-support Second Law socket. -/
@[rep_depth krein]
def RegularSupportSecondLawTarget : Prop :=
  ∃ Op : Type,
    ∃ (_hRing : Ring Op)
      (_hStar : Star Op)
      (_hSmul : SMul ℝ Op) ,
      Nonempty (RegularHeatDefectMemorySplit Op)

/-- Constructor for the regular-support Second Law target. -/
@[rep_depth krein]
theorem constructRegularSupportSecondLawTarget
    {Op : Type} [Ring Op] [Star Op] [SMul ℝ Op]
    (S : RegularHeatDefectMemorySplit Op) :
    RegularSupportSecondLawTarget := by
  exact
    ⟨Op, inferInstance, inferInstance, inferInstance , ⟨S⟩⟩

end InfoGeometry.Canonical.RegularSupportSecondLaw
