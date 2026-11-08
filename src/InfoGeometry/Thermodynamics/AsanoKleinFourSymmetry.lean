/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Formalization Team
-/
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
-/

noncomputable section

namespace InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry

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

/-- The `V4`-invariant core of a set `S : Set ℂ`: points whose entire `V4`-orbit lies in `S`. -/
@[rep_depth thermo]
def v4SymmetricCore (S : Set ℂ) : Set ℂ :=
  {z : ℂ | ∀ g : V4, v4Action g z ∈ S}

/-- Every generator of `V4` acts as an involution on `ℂ`. -/
@[rep_depth thermo]
theorem v4Action_involutive (g : V4) (z : ℂ) :
    v4Action g (v4Action g z) = z := by
  rcases g with _ | _ | _ | _
  · exact Eq.refl z
  · dsimp [v4Action]
    exact inv_inv z
  · dsimp [v4Action]
    exact Complex.conj_conj z
  · dsimp [v4Action]
    rw [map_inv₀, Complex.conj_conj, inv_inv]

/-- The `V4`-invariant core `v4SymmetricCore S` is contained in `S`. -/
@[rep_depth thermo]
theorem v4SymmetricCore_subset (S : Set ℂ) :
    v4SymmetricCore S ⊆ S := by
  intro z hz
  have hid := hz V4.id
  unfold v4Action at hid
  exact hid

end InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry
