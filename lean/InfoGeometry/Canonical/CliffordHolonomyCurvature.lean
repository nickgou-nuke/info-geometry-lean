/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.UnitriangularBCH
import InfoGeometry.Clifford.Cl22QuaternionCayley
import InfoGeometry.Quantum.OperatorWeylHolonomy

/-!
# Explicit specializations connecting operator holonomy to BCH and quaternion axes

These are actual maps between the independently constructed lanes. The BCH
exponential provides unit labels for the permutation lattice, whose holonomy
is exactly one plus the nilpotent matrix bracket. Quaternion Cayley units give
a second nonflat holonomy, with the characteristic-two boundary explicit.
The imported quaternion owner separately realizes constant-axis differential
curvature. No limiting map from discrete holonomy to derivatives is asserted.
-/

namespace InfoGeometry.Canonical.CliffordHolonomyCurvature

open InfoGeometry.Algebra.UnitriangularBCH
open InfoGeometry.Quantum.OperatorWeylHolonomy
open InfoGeometry.Clifford.Cl22QuaternionCayley

variable {ι A : Type*} [Ring A]

/-- Constant exponential edge labels turn the lattice plaquette into the exact
noncommutative BCH commutator. No finiteness of the vertex type is needed. -/
theorem unipotent_holonomy [Invertible (2 : A)] (σ : Equiv.Perm ι)
    (x y : BCH3 A) (i : ι) :
    ((holonomy σ (fun _ => expUnitHom y) (fun _ => expUnitHom x) i :
        (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A) =
      1 + (nilpotentMatrix x * nilpotentMatrix y -
        nilpotentMatrix y * nilpotentMatrix x) :=
  expUnitHom_commutator x y

/-- The same BCH curvature is the diagonal of the group commutator of the
actual weighted permutation and vertex matrices. -/
theorem unipotent_matrix_commutator [Fintype ι] [DecidableEq ι]
    [Invertible (2 : A)] (σ : Equiv.Perm ι) (x y : BCH3 A) :
    (((vertexUnit (fun _ : ι => expUnitHom x) *
        shiftUnit σ (fun _ => expUnitHom y) *
        (vertexUnit (fun _ : ι => expUnitHom x))⁻¹ *
        (shiftUnit σ (fun _ => expUnitHom y))⁻¹) :
        (Matrix ι ι (Matrix (Fin 3) (Fin 3) A))ˣ) :
        Matrix ι ι (Matrix (Fin 3) (Fin 3) A)) =
      Matrix.diagonal (fun _ =>
        1 + (nilpotentMatrix x * nilpotentMatrix y -
          nilpotentMatrix y * nilpotentMatrix x)) := by
  rw [← holonomyUnit_eq_group_commutator]
  change Matrix.diagonal (fun i =>
    ((holonomy σ (fun _ => expUnitHom y) (fun _ => expUnitHom x) i :
      (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A)) = _
  congr 1
  funext i
  exact unipotent_holonomy σ x y i

/-- The quaternion Cayley factors supply genuinely nonflat operator holonomy
whenever the displayed twice-identity is nonzero. -/
theorem quaternion_holonomy_ne_one [Invertible (2 : Nested A)]
    (h2 : (2 : Nested A) ≠ 0) (σ : Equiv.Perm ι) (i : ι) :
    holonomy σ
      (fun _ => cayleyUnit (axisJ : Nested A) axisJ_square)
      (fun _ => cayleyUnit (axisI : Nested A) axisI_square) i ≠ 1 := by
  intro h
  have hc := (holonomy_eq_one_iff_edge_commutes σ _ _ i).mp h
  have hm := congrArg (fun u : (Nested A)ˣ => (u : Nested A)) hc
  exact cayley_factors_do_not_commute h2 hm

/-- The nonflat quaternion plaquette obstructs commutation in its full
weighted matrix representation whenever a vertex is supplied. -/
theorem quaternion_matrix_do_not_commute [Fintype ι] [DecidableEq ι]
    [Invertible (2 : Nested A)] (h2 : (2 : Nested A) ≠ 0)
    (σ : Equiv.Perm ι) (i : ι) :
    ¬ Commute
      (vertexUnit (fun _ : ι => cayleyUnit (axisI : Nested A) axisI_square))
      (shiftUnit σ (fun _ => cayleyUnit (axisJ : Nested A) axisJ_square)) := by
  intro h
  have hflat := (holonomy_eq_one_iff_matrix_commute σ _ _).mpr h
  exact quaternion_holonomy_ne_one h2 σ i (congrFun hflat i)

end InfoGeometry.Canonical.CliffordHolonomyCurvature
