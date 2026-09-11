import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-!
# InfoGeometry.Canonical.ZetaChiralConeAlgebra

Theorem-safe bridge from the centered zeta symmetry projectors to a chiral
natural-cone vocabulary.

This file proves only finite algebra on abstract zeta-like readouts
`ZetaCenteredChart → ℂ`:

* the antiunitary `J` action induced by the critical mirror;
* the `J`-even and `J`-odd projectors;
* a `J`-even completed readout has `P⁺ ξ = ξ` and `P⁻ ξ = 0`;
* a nonzero odd part of an uncompleted readout is exactly a nonzero supplied
  modular-density channel.

It does not construct the completed Riemann xi function, prove Schwarz
reflection, prove the Riemann functional equation, build a von Neumann algebra,
construct a Tomita--Takesaki natural cone, or prove RH.  Those analytic/operator
claims are exposed as explicit predicates below.

#### BUCKET 1: CLOSED FINITE THEOREMS
`J` is an involution on readouts; `P⁺` and `P⁻` split a readout; `J`-even
readouts have zero odd projection; nonzero odd projection is exactly nonzero
modular density by definition.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`completedXi_projector_packet` depends on the explicit premise
`CompletedXiJEven xi`.

#### BUCKET 3: OPEN CLOSURE DEBT
Analytic xi/zeta construction, AQFT double-cone algebras, standard-form natural
cones, Radon--Nikodym derivatives, KMS uniqueness, and RH are not claimed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZetaChiralConeAlgebra

open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open ZetaAffineChart
open ZetaCenteredChart

/-- A zeta-like scalar readout on centered coordinates. -/
abbrev ZetaReadout : Type :=
  ZetaCenteredChart → ℂ

/-! ## Antiunitary critical-mirror action and projectors -/

/--
Antiunitary critical-mirror action on a zeta-like readout.

In centered coordinates this is
`(J ⋅ F)(u,v) = star (F (-u,v))`.
-/
def JAction (F : ZetaReadout) : ZetaReadout :=
  fun x => star (F (criticalMirror x))

/-- A readout is `J`-even when it is fixed by the antiunitary critical mirror. -/
def IsJEven (F : ZetaReadout) : Prop :=
  JAction F = F

/-- A readout is `J`-odd when the antiunitary critical mirror negates it. -/
def IsJOdd (F : ZetaReadout) : Prop :=
  JAction F = -F

/-- The `+1` Cartan projector for the antiunitary critical mirror. -/
def JPlusProjector (F : ZetaReadout) : ZetaReadout :=
  fun x => (1 / 2 : ℂ) * (F x + JAction F x)

/-- The `-1` Cartan projector for the antiunitary critical mirror. -/
def JMinusProjector (F : ZetaReadout) : ZetaReadout :=
  fun x => (1 / 2 : ℂ) * (F x - JAction F x)

@[simp] theorem JAction_involutive (F : ZetaReadout) :
    JAction (JAction F) = F := by
  funext x
  simp [JAction, criticalMirror]

/-- The `J`-even and `J`-odd projectors resolve a readout. -/
theorem JPlus_add_JMinus (F : ZetaReadout) :
    (fun x => JPlusProjector F x + JMinusProjector F x) = F := by
  funext x
  simp [JPlusProjector, JMinusProjector]
  ring

/-- A `J`-even readout is entirely in the positive projector sector. -/
theorem JPlus_eq_self_of_JEven
    {F : ZetaReadout} (hF : IsJEven F) :
    JPlusProjector F = F := by
  funext x
  have hx : JAction F x = F x := by
    exact congrFun hF x
  simp [JPlusProjector, hx]
  ring

/-- A `J`-even readout has zero negative projector. -/
theorem JMinus_eq_zero_of_JEven
    {F : ZetaReadout} (hF : IsJEven F) :
    JMinusProjector F = 0 := by
  funext x
  have hx : JAction F x = F x := by
    exact congrFun hF x
  simp [JMinusProjector, hx]

/-- The positive projector is `J`-even. -/
theorem JPlus_isJEven (F : ZetaReadout) :
    IsJEven (JPlusProjector F) := by
  funext x
  simp [JAction, JPlusProjector, criticalMirror]
  ring

/-- The negative projector is `J`-odd. -/
theorem JMinus_isJOdd (F : ZetaReadout) :
    IsJOdd (JMinusProjector F) := by
  funext x
  simp [JAction, JMinusProjector, criticalMirror]
  ring

/-! ## Completed xi and uncompleted zeta readout predicates -/

/--
Explicit premise saying an abstract completed xi readout satisfies the
antiunitary critical-mirror symmetry.

Analytically, this would be supplied from Schwarz reflection plus the completed
functional equation.  This file does not prove those analytic facts.
-/
def CompletedXiJEven (xi : ZetaReadout) : Prop :=
  IsJEven xi

/-- The positive xi projection equals xi under the explicit `J`-even premise. -/
theorem completedXi_JPlus_eq_self
    {xi : ZetaReadout} (hxi : CompletedXiJEven xi) :
    JPlusProjector xi = xi :=
  JPlus_eq_self_of_JEven hxi

/-- The negative xi projection vanishes under the explicit `J`-even premise. -/
theorem completedXi_JMinus_eq_zero
    {xi : ZetaReadout} (hxi : CompletedXiJEven xi) :
    JMinusProjector xi = 0 :=
  JMinus_eq_zero_of_JEven hxi

/--
Combined completed-xi projector packet.

This is the exact finite projector consequence: `P⁺_J ξ = ξ` and `P⁻_J ξ = 0`.
-/
theorem completedXi_projector_packet
    {xi : ZetaReadout} (hxi : CompletedXiJEven xi) :
    JPlusProjector xi = xi ∧ JMinusProjector xi = 0 :=
  ⟨completedXi_JPlus_eq_self hxi, completedXi_JMinus_eq_zero hxi⟩

/-- The odd projection of an uncompleted zeta readout. -/
def uncompletedZetaOddDensity (zeta : ZetaReadout) : ZetaReadout :=
  JMinusProjector zeta

/--
Predicate saying the uncompleted readout has a nonzero scale-normal/odd
component.
-/
def HasNonzeroOddDensity (zeta : ZetaReadout) : Prop :=
  ∃ x, uncompletedZetaOddDensity zeta x ≠ 0

/-- Nonzero odd density is exactly nonzero negative projector. -/
theorem hasNonzeroOddDensity_iff
    (zeta : ZetaReadout) :
    HasNonzeroOddDensity zeta ↔ ∃ x, JMinusProjector zeta x ≠ 0 :=
  Iff.rfl

/-! ## Chiral natural-cone vocabulary as explicit predicates -/

/--
Abstract natural-cone/chiral-cone anchor predicate.

`xi` is a cone anchor when the supplied embedding places it in the cone and it
is `J`-even.  This is a predicate, not a construction of a standard-form von
Neumann algebra.
-/
def IsChiralConeAnchor
    {ConeVector : Type*}
    (embed : ZetaReadout → ConeVector)
    (naturalCone : Set ConeVector)
    (xi : ZetaReadout) : Prop :=
  embed xi ∈ naturalCone ∧ CompletedXiJEven xi

/--
Abstract relative modular density predicate.

The supplied density readout is the odd projector of the uncompleted zeta
readout and is nonzero somewhere.
-/
def IsRelativeModularDensity
    (zeta density : ZetaReadout) : Prop :=
  density = uncompletedZetaOddDensity zeta ∧ HasNonzeroOddDensity zeta

/-- A chiral-cone anchor has vanishing negative xi projection. -/
theorem anchor_has_zero_negative_projection
    {ConeVector : Type*}
    {embed : ZetaReadout → ConeVector}
    {naturalCone : Set ConeVector}
    {xi : ZetaReadout}
    (hanchor : IsChiralConeAnchor embed naturalCone xi) :
    JMinusProjector xi = 0 :=
  completedXi_JMinus_eq_zero hanchor.2

/-- A supplied relative modular density is the odd projector by definition. -/
theorem relativeModularDensity_eq_oddProjection
    {zeta density : ZetaReadout}
    (hdensity : IsRelativeModularDensity zeta density) :
    density = JMinusProjector zeta :=
  hdensity.1

end InfoGeometry.Canonical.ZetaChiralConeAlgebra
