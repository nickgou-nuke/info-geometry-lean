import Mathlib.Tactic
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-!
# InfoGeometry.Arithmetic.ZetaChiralConeProjection

Projection of centered completed-zeta symmetry packets onto the Tomita/Cartan
`J`-even and `J`-odd sectors.

This module proves the theorem-safe algebraic statement behind the intended
picture:

* on centered zeta coordinates, `J` acts on scalar fields by
  `F ↦ fun x => star (F (criticalMirror x))`;
* if a completed `xi` readout satisfies Schwarz reflection and the centered
  functional equation, then it is `J`-fixed;
* therefore its `J`-even projector is itself and its `J`-odd projector is zero;
* the uncompleted zeta odd part is recorded as a symbolic relative modular
  density, with nonvanishing left as an explicit predicate.

No analytic Riemann xi function, AQFT standard form, natural cone, KMS
classification, Radon--Nikodym theorem, or Riemann Hypothesis statement is
proved here.  Those analytic identifications must be supplied by separate owner
modules.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaChiralConeProjection

open Complex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

abbrev CenteredField :=
  ZetaCenteredChart → ℂ

/-! ## Coordinate identities -/

/-- In centered coordinates, conjugation after the critical mirror is functional duality. -/
theorem conjugation_criticalMirror_eq_functionalDual (x : ZetaCenteredChart) :
    conjugation (criticalMirror x) = functionalDual x := by
  rfl

/-! ## Tomita action and Cartan projectors on centered scalar fields -/

/--
Tomita/Fourier `J` action on centered scalar fields:
`(JF)(x) = star (F (criticalMirror x))`.
-/
def zetaJAction (F : CenteredField) : CenteredField :=
  fun x => star (F (criticalMirror x))

/-- A centered scalar field is `J`-invariant when the Tomita action fixes it pointwise. -/
def JInvariant (F : CenteredField) : Prop :=
  ∀ x, zetaJAction F x = F x

/-- A centered scalar field is `J`-anti-invariant when the Tomita action negates it pointwise. -/
def JAntiInvariant (F : CenteredField) : Prop :=
  ∀ x, zetaJAction F x = -F x

/-- The symbolic natural-cone anchor lane: the `J`-fixed centered scalar fields. -/
def JFixedCone : Set CenteredField :=
  {F | JInvariant F}

/-- The `J`-even projector on centered scalar fields. -/
def JEvenProjector (F : CenteredField) : CenteredField :=
  fun x => ((F x) + zetaJAction F x) / 2

/-- The `J`-odd projector on centered scalar fields. -/
def JOddProjector (F : CenteredField) : CenteredField :=
  fun x => ((F x) - zetaJAction F x) / 2

/-- `J` is an involution on centered scalar fields. -/
theorem zetaJAction_involutive :
    Function.Involutive zetaJAction := by
  intro F
  funext x
  simp [zetaJAction, criticalMirror]

/-- A `J`-fixed field is unchanged by the `J`-even projector. -/
theorem JEvenProjector_eq_self_of_JInvariant
    {F : CenteredField} (hF : JInvariant F) :
    JEvenProjector F = F := by
  funext x
  simp [JEvenProjector, hF x]

/-- A `J`-fixed field has zero `J`-odd projection. -/
theorem JOddProjector_eq_zero_of_JInvariant
    {F : CenteredField} (hF : JInvariant F) :
    JOddProjector F = 0 := by
  funext x
  simp [JOddProjector, hF x]

/-! ## Completed xi symmetry packet -/

/--
Centered completed-xi symmetry packet.

`schwarz_reflection` is the centered version of
`star (xi(u,v)) = xi(u,-v)`.

`functional_equation` is the centered version of
`xi(-u,-v) = xi(u,v)`.
-/
structure CenteredXiSymmetryPacket where
  xi : CenteredField
  schwarz_reflection :
    ∀ x, star (xi x) = xi (conjugation x)
  functional_equation :
    ∀ x, xi (functionalDual x) = xi x

namespace CenteredXiSymmetryPacket

/-- Schwarz reflection plus the centered functional equation make `xi` `J`-fixed. -/
theorem xi_JInvariant (X : CenteredXiSymmetryPacket) :
    JInvariant X.xi := by
  intro x
  calc
    zetaJAction X.xi x
        = star (X.xi (criticalMirror x)) := by
            rfl
    _ = X.xi (conjugation (criticalMirror x)) := by
            rw [X.schwarz_reflection (criticalMirror x)]
    _ = X.xi (functionalDual x) := by
            rw [conjugation_criticalMirror_eq_functionalDual]
    _ = X.xi x := X.functional_equation x

/-- The completed `xi` packet lies in the symbolic `J`-fixed cone. -/
theorem xi_mem_JFixedCone (X : CenteredXiSymmetryPacket) :
    X.xi ∈ JFixedCone :=
  X.xi_JInvariant

/-- The `J`-even projection of completed `xi` is completed `xi`. -/
theorem xi_JEvenProjector_eq (X : CenteredXiSymmetryPacket) :
    JEvenProjector X.xi = X.xi :=
  JEvenProjector_eq_self_of_JInvariant X.xi_JInvariant

/-- The `J`-odd / scale-normal projection of completed `xi` is zero. -/
theorem xi_JOddProjector_eq_zero (X : CenteredXiSymmetryPacket) :
    JOddProjector X.xi = 0 :=
  JOddProjector_eq_zero_of_JInvariant X.xi_JInvariant

end CenteredXiSymmetryPacket

/-! ## Symbolic uncompleted-zeta odd density -/

/--
The symbolic relative modular density attached to an uncompleted zeta readout:
its `J`-odd Cartan component.
-/
def relativeModularDensity (zeta : CenteredField) : CenteredField :=
  JOddProjector zeta

/--
Predicate asserting that the uncompleted zeta readout has a nonzero scale-normal
component.  This is not proved analytically here.
-/
def HasScaleNormalComponent (zeta : CenteredField) : Prop :=
  ∃ x, relativeModularDensity zeta x ≠ 0

/-- A nonzero odd density obstructs `J`-invariance. -/
theorem not_JInvariant_of_hasScaleNormalComponent
    {zeta : CenteredField}
    (h : HasScaleNormalComponent zeta) :
    ¬ JInvariant zeta := by
  intro hzeta
  rcases h with ⟨x, hx⟩
  have hzero_fun : JOddProjector zeta = 0 :=
    JOddProjector_eq_zero_of_JInvariant hzeta
  exact hx (by simpa [relativeModularDensity] using congrFun hzero_fun x)

/-! ## Chiral-cone anchor readout -/

/--
The theorem-safe chiral-cone anchor readout for a completed-xi symmetry packet.

The `cone` here is the symbolic `J`-fixed cone of centered scalar fields.  This
does not construct the full Tomita--Takesaki natural cone; it records the exact
projection facts that a future standard-form owner can consume.
-/
def ChiralConeAnchorReadout :=
  {anchor : CenteredField //
    anchor ∈ JFixedCone ∧
      JEvenProjector anchor = anchor ∧
        JOddProjector anchor = 0}

namespace ChiralConeAnchorReadout

abbrev anchor (A : ChiralConeAnchorReadout) : CenteredField := A.1

theorem anchor_mem_cone (A : ChiralConeAnchorReadout) :
    A.anchor ∈ JFixedCone :=
  A.2.1

theorem even_projection_eq_anchor (A : ChiralConeAnchorReadout) :
    JEvenProjector A.anchor = A.anchor :=
  A.2.2.1

theorem odd_projection_eq_zero (A : ChiralConeAnchorReadout) :
    JOddProjector A.anchor = 0 :=
  A.2.2.2

def mk
    (anchor : CenteredField)
    (anchor_mem_cone : anchor ∈ JFixedCone)
    (even_projection_eq_anchor : JEvenProjector anchor = anchor)
    (odd_projection_eq_zero : JOddProjector anchor = 0) :
    ChiralConeAnchorReadout :=
  ⟨anchor, ⟨anchor_mem_cone,
    ⟨even_projection_eq_anchor, odd_projection_eq_zero⟩⟩⟩

end ChiralConeAnchorReadout

/-- Completed `xi` supplies a theorem-safe symbolic chiral-cone anchor. -/
def CenteredXiSymmetryPacket.toChiralConeAnchorReadout
    (X : CenteredXiSymmetryPacket) :
    ChiralConeAnchorReadout :=
  ChiralConeAnchorReadout.mk X.xi
    X.xi_mem_JFixedCone
    X.xi_JEvenProjector_eq
    X.xi_JOddProjector_eq_zero

end InfoGeometry.Arithmetic.ZetaChiralConeProjection
