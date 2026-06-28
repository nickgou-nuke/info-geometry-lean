/-
InfoGeometry/Geometry/BilingualUpperHalfPlane.lean

Bilingual Complex and Krein-Hestenes Upper Half-Plane.

Following the Pauli Auditor Protocol and the Erlanger Program of Klein symmetry:
we define the complex upper half-plane in parallel operatorial/Krein-Hestenes
language.

A point in the upper half-plane is an operator `τ` on the doubled real carrier
`H₂` such that:

1. `τ` commutes with the Hestenes phase axis `K`;
2. its `K`-rotated quadratic form is strictly negative:

     `⟪v, K (τ v)⟫_ℝ < 0`

   for all nonzero `v`.
-/

import Mathlib
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Quantum.HestenesKahler

noncomputable section

namespace InfoGeometry.Geometry

open scoped InnerProductSpace

open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Quantum

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The doubled real carrier. -/
local notation "H₂" => DoubledSpace E

/-- Real bounded endomorphisms of the doubled carrier. -/
abbrev DoubledEnd
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  DoubledSpace E →L[ℝ] DoubledSpace E

local notation "EndH" => DoubledEnd E

/--
An endomorphism is phase-linear if it commutes with the Hestenes phase axis `K`.
-/
def PhaseLinear
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (T : EndH) : Prop :=
  T.comp D.K = D.K.comp T

namespace PhaseLinear

variable {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}

/--
Pointwise form of phase-linearity.
-/
theorem map_K
    {T : EndH}
    (hT : PhaseLinear D T)
    (v : H₂) :
    T (D.K v) = D.K (T v) := by
  have h :=
    congrArg (fun L : EndH => L v) hT
  simpa [PhaseLinear, ContinuousLinearMap.comp_apply] using h

/--
The composite of two phase-linear endomorphisms is phase-linear.
-/
theorem comp
    {S T : EndH}
    (hS : PhaseLinear D S)
    (hT : PhaseLinear D T) :
    PhaseLinear D (S.comp T) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  calc
    S (T (D.K v))
        = S (D.K (T v)) := by
          rw [PhaseLinear.map_K hT v]
    _ = D.K (S (T v)) := by
          rw [PhaseLinear.map_K hS (T v)]

/--
The sum of two phase-linear endomorphisms is phase-linear.
-/
theorem add
    {S T : EndH}
    (hS : PhaseLinear D S)
    (hT : PhaseLinear D T) :
    PhaseLinear D (S + T) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  calc
    S (D.K v) + T (D.K v)
        = D.K (S v) + D.K (T v) := by
          rw [PhaseLinear.map_K hS v, PhaseLinear.map_K hT v]
    _ = D.K (S v + T v) := by
          exact (map_add D.K (S v) (T v)).symm

end PhaseLinear

/--
The bilingual upper half-plane.

Instead of scalar coordinates `x + iy` with `y > 0`, a point is an operator
`τ` on the doubled space that is phase-linear and satisfies the Krein-Hestenes
upper-half-plane positivity condition.
-/
structure BilingualUpperHalfPlane
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) where

  /-- The operator representing the upper-half-plane point. -/
  tau : EndH

  /-- `τ` commutes with the Hestenes phase axis `K`. -/
  phase_linear :
    PhaseLinear D tau

  /--
  Coordinateless upper-half-plane positivity.

  If formally `τ = x + yK`, then `Kτ = xK - y`, so `y > 0` corresponds to
  strict negativity of this real quadratic form.
  -/
  K_positivity :
    ∀ v : H₂, v ≠ 0 →
      ⟪v, D.K (tau v)⟫_ℝ < (0 : ℝ)

namespace BilingualUpperHalfPlane

variable {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}
variable (Z : BilingualUpperHalfPlane D)

/--
Pointwise phase-linearity for a bilingual upper-half-plane point.
-/
theorem phase_linear_apply
    (v : H₂) :
    Z.tau (D.K v) = D.K (Z.tau v) :=
  PhaseLinear.map_K Z.phase_linear v

/--
The upper-half-plane positivity condition, re-exported as a theorem.
-/
theorem K_positivity_apply
    (v : H₂)
    (hv : v ≠ 0) :
    ⟪v, D.K (Z.tau v)⟫_ℝ < (0 : ℝ) :=
  Z.K_positivity v hv

/--
The denominator of a Möbius action is phase-linear whenever its blocks are
phase-linear.

This proves only the commutation with `K` for `Cτ + D`; invertibility and
phase-linearity of the inverse are separate data.
-/
theorem denominator_phase_linear
    {C D_op : EndH}
    (hC : PhaseLinear D C)
    (hD : PhaseLinear D D_op) :
    PhaseLinear D (C.comp Z.tau + D_op) :=
  PhaseLinear.add
    (PhaseLinear.comp hC Z.phase_linear)
    hD

/-- The denominator phase-linearity is stable under right-composition by `τ`. -/
theorem denominator_phase_linear_comp
    {C D_op : EndH}
    (hC : PhaseLinear D C)
    (hD : PhaseLinear D D_op) :
    PhaseLinear D (C.comp Z.tau + D_op) := by
  simpa using denominator_phase_linear (D := D) (Z := Z) hC hD

/--
Raw fractional-linear Möbius action.

For operator blocks

`g = [[A, B], [C, D]]`

and denominator unit

`Cτ + D ∈ End(H₂)ˣ`,

the raw action is

`g • τ = (Aτ + B) (Cτ + D)⁻¹`.

This returns only an endomorphism. To obtain a new
`BilingualUpperHalfPlane`, one must also supply the positivity-preservation
proof.
-/
def moebius_action
    (A B C D_op : EndH)
    (_hA : PhaseLinear D A)
    (_hB : PhaseLinear D B)
    (_hC : PhaseLinear D C)
    (_hD : PhaseLinear D D_op)
    (denomUnit : Units EndH)
    (_h_denom : C.comp Z.tau + D_op = denomUnit.val)
    (_h_denom_inv : PhaseLinear D denomUnit.inv) :
    EndH :=
  (A.comp Z.tau + B).comp denomUnit.inv

/--
The raw Möbius action is phase-linear, provided the numerator blocks and the
inverse denominator are phase-linear.
-/
theorem moebius_action_phase_linear
    (A B C D_op : EndH)
    (hA : PhaseLinear D A)
    (hB : PhaseLinear D B)
    (hC : PhaseLinear D C)
    (hD : PhaseLinear D D_op)
    (denomUnit : Units EndH)
    (h_denom : C.comp Z.tau + D_op = denomUnit.val)
    (h_denom_inv : PhaseLinear D denomUnit.inv) :
    PhaseLinear D
      (Z.moebius_action
        A B C D_op hA hB hC hD denomUnit h_denom h_denom_inv) := by
  dsimp [moebius_action]
  exact
    PhaseLinear.comp
      (PhaseLinear.add
        (PhaseLinear.comp hA Z.phase_linear)
        hB)
      h_denom_inv

/--
Proof-carrying datum for a Möbius self-map of the bilingual upper half-plane.

The final field is essential: phase-linearity follows algebraically, but
upper-half-plane positivity requires the appropriate Krein/symplectic positivity
hypotheses. Until that group action is formalized, positivity is carried as
explicit evidence.
-/
structure MoebiusActionDatum
    (Z : BilingualUpperHalfPlane D) where

  /-- Numerator left block. -/
  A : EndH

  /-- Numerator translation block. -/
  B : EndH

  /-- Denominator left block. -/
  C : EndH

  /-- Denominator translation block. -/
  D_op : EndH

  /-- `A` commutes with the Hestenes phase axis. -/
  A_phase :
    PhaseLinear D A

  /-- `B` commutes with the Hestenes phase axis. -/
  B_phase :
    PhaseLinear D B

  /-- `C` commutes with the Hestenes phase axis. -/
  C_phase :
    PhaseLinear D C

  /-- `D_op` commutes with the Hestenes phase axis. -/
  D_phase :
    PhaseLinear D D_op

  /-- The denominator as a unit of the real endomorphism algebra. -/
  denomUnit : Units EndH

  /-- The unit really is the denominator `Cτ + D`. -/
  denom_eq :
    C.comp Z.tau + D_op = denomUnit.val

  /-- The inverse denominator commutes with the Hestenes phase axis. -/
  denom_inv_phase :
    PhaseLinear D denomUnit.inv

  /--
  The raw Möbius action preserves the upper-half-plane positivity condition.
  This is where the future Krein-symplectic positivity theorem should plug in.
  -/
  K_positivity :
    ∀ v : H₂, v ≠ 0 →
      ⟪v,
        D.K
          ((Z.moebius_action
              A B C D_op
              A_phase B_phase C_phase D_phase
              denomUnit denom_eq denom_inv_phase) v)⟫_ℝ
        < (0 : ℝ)

/--
The Möbius action as a genuine self-map of the bilingual upper half-plane.

The algebraic phase-linearity proof is internal; positivity is supplied by the
`MoebiusActionDatum`.
-/
def moebiusMap
    (M : MoebiusActionDatum Z) :
    BilingualUpperHalfPlane D where

  tau :=
    Z.moebius_action
      M.A M.B M.C M.D_op
      M.A_phase M.B_phase M.C_phase M.D_phase
      M.denomUnit M.denom_eq M.denom_inv_phase

  phase_linear := by
    exact
      Z.moebius_action_phase_linear
        M.A M.B M.C M.D_op
        M.A_phase M.B_phase M.C_phase M.D_phase
        M.denomUnit M.denom_eq M.denom_inv_phase

  K_positivity :=
    M.K_positivity

/--
The Möbius image has the expected underlying raw action.
-/
@[simp]
theorem moebiusMap_tau
    (M : MoebiusActionDatum Z) :
    (Z.moebiusMap M).tau =
      Z.moebius_action
        M.A M.B M.C M.D_op
        M.A_phase M.B_phase M.C_phase M.D_phase
        M.denomUnit M.denom_eq M.denom_inv_phase :=
  rfl

/--
The Möbius image is phase-linear.
-/
theorem moebiusMap_phase_linear
    (M : MoebiusActionDatum Z) :
    PhaseLinear D (Z.moebiusMap M).tau :=
  (Z.moebiusMap M).phase_linear

/--
The Möbius image satisfies the upper-half-plane positivity condition.
-/
theorem moebiusMap_K_positivity
    (M : MoebiusActionDatum Z)
    (v : H₂)
    (hv : v ≠ 0) :
    ⟪v, D.K ((Z.moebiusMap M).tau v)⟫_ℝ < (0 : ℝ) :=
  (Z.moebiusMap M).K_positivity v hv

end BilingualUpperHalfPlane

end InfoGeometry.Geometry
