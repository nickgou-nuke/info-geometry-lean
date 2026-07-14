import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

open scoped ComplexConjugate

/-!
# InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry

V4 CPT/Mobius compactification of the Asano symmetry group.

This module formalizes the Klein-four action on the fugacity plane. By
exploiting inversion and conjugation symmetries of the Lee-Yang/Asano
forbidden sets, it reduces the global analytic covering argument to a finite
orbit check over endpoint representatives.

Honest status: this module provides the topological reduction skeleton. The
actual global nondegenerate Asano theorem remains deferred as socket debt.
-/

noncomputable section

namespace AsanoKleinFourSymmetry

/-- The `V4` (Klein-four) symmetry group generators for the Asano chart. -/
@[rep_depth thermo]
inductive V4
| id
| inv
| conj
| cpt
deriving DecidableEq, Repr

/-- The native action of `V4` on the complex fugacity plane. -/
@[rep_depth thermo]
def v4Action (g : V4) (z : ℂ) : ℂ :=
  match g with
  | V4.id => z
  | V4.inv => z⁻¹
  | V4.conj => conj z
  | V4.cpt => (conj z)⁻¹

/-- A set of complex roots is `V4`-symmetric if it is closed under the action. -/
@[rep_depth thermo]
def IsV4Symmetric (S : Set ℂ) : Prop :=
  ∀ (g : V4) (z : ℂ), z ∈ S → v4Action g z ∈ S

end AsanoKleinFourSymmetry
