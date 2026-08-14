import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

open scoped ComplexConjugate

/-!
# A finite involution packet on `ℂ`

This module defines four explicit maps (identity, inversion, conjugation, and
their composite) and the predicate that a set is closed under them.  No
analytic zero-free or global covering theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry

/-- Labels for the four explicit involutive maps. -/
@[rep_depth thermo]
inductive V4
| id
| inv
| conj
| cpt
deriving DecidableEq, Repr

/-- The corresponding pointwise action on `ℂ`. -/
@[rep_depth thermo]
def v4Action (g : V4) (z : ℂ) : ℂ :=
  match g with
  | V4.id => z
  | V4.inv => z⁻¹
  | V4.conj => conj z
  | V4.cpt => (conj z)⁻¹

/-- A set is closed under all four explicit maps. -/
@[rep_depth thermo]
def IsV4Symmetric (S : Set ℂ) : Prop :=
  ∀ (g : V4) (z : ℂ), z ∈ S → v4Action g z ∈ S

end InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry
