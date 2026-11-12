/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.CSSKoszulExtension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.NormNum

/-!
# Homology detects the off-diagonal Koszul coupling

After reducing the three Koszul generators to zero, the zero coupling has
native homology `R³ × R³`, whereas coupling by the first coordinate vector
has native homology `R² × R²`. These are calculations on the same coupled
short complexes defined in `CSSKoszulExtension`.

The coefficient reduction from the lattice translation ring is supplied by
the separate periodic-code module. The calculation here makes no assertion
about physical circuit equivalence or arbitrary finite system sizes.
-/

namespace InfoGeometry.Quantum.CSSKoszulExtension

open CategoryTheory Matrix

universe u

variable {R : Type u} [CommRing R]

/-- The nonzero coupling used for the explicit homology comparison. -/
def unitCoupling (R : Type u) [CommRing R] : Vec3 R := ![1, 0, 0]

@[simp] theorem boundary1_zero : boundary1 (0 : Vec3 R) = 0 := by
  apply LinearMap.ext
  intro x
  simp

@[simp] theorem boundary2_zero : boundary2 (0 : Vec3 R) = 0 := by
  apply LinearMap.ext
  intro x
  ext i
  fin_cases i <;> simp [boundary2, koszulMatrix, dotProduct, Fin.sum_univ_three]

@[simp] theorem boundary1_unitCoupling (x : Vec3 R) :
    boundary1 (unitCoupling R) x = x 0 := by
  simp [unitCoupling, boundary1, dotProduct, Fin.sum_univ_three]

@[simp] theorem incoming_zero_zero : incoming (0 : Vec3 R) 0 = 0 := by
  apply LinearMap.ext
  intro x
  simp

@[simp] theorem outgoing_zero_zero : outgoing (0 : Vec3 R) 0 = 0 := by
  apply LinearMap.ext
  intro x
  simp

@[simp] theorem incoming_zero_unit (x : Vec3 R × R) :
    incoming (0 : Vec3 R) (unitCoupling R) x = (x.2 • unitCoupling R, 0) := by
  simp

@[simp] theorem outgoing_zero_unit (x : Vec3 R × Vec3 R) :
    outgoing (0 : Vec3 R) (unitCoupling R) x = (-x.2 0, 0) := by
  simp [unitCoupling, dotProduct, Fin.sum_univ_three]

theorem zero_boundary_range :
    (complex (0 : Vec3 R) 0).moduleCatToCycles.range = ⊥ := by
  have h : (complex (0 : Vec3 R) 0).moduleCatToCycles = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change incoming (0 : Vec3 R) 0 x = 0
    rw [incoming_zero_zero]
    rfl
  rw [h, LinearMap.range_zero]

/-- With both differentials zero, all six coordinates survive in homology. -/
noncomputable def zeroHomologyEquiv (R : Type u) [CommRing R] :
    (complex (0 : Vec3 R) 0).homology ≃ₗ[R] (Vec3 R × Vec3 R) :=
  (complex (0 : Vec3 R) 0).moduleCatHomologyIso.toLinearEquiv |>.trans
    ((Submodule.quotEquivOfEqBot _ zero_boundary_range).trans
      (LinearEquiv.ofTop _ (by
        change (outgoing (0 : Vec3 R) 0).ker = ⊤
        rw [outgoing_zero_zero, LinearMap.ker_zero])))

/-- Restriction to the last two coordinates. -/
def tailCoordinates : Vec3 R →ₗ[R] (Fin 2 → R) where
  toFun x i := x i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Four surviving coordinates of a cycle in the unit-coupled complex. -/
def unitCycleCoordinates :
    (complex (0 : Vec3 R) (unitCoupling R)).g.hom.ker →ₗ[R]
      ((Fin 2 → R) × (Fin 2 → R)) :=
  (tailCoordinates.prodMap tailCoordinates).comp
    (complex (0 : Vec3 R) (unitCoupling R)).g.hom.ker.subtype

@[simp] theorem unitCycleCoordinates_apply
    (x : (complex (0 : Vec3 R) (unitCoupling R)).g.hom.ker) :
    unitCycleCoordinates x =
      (fun i => x.1.1 i.succ, fun i => x.1.2 i.succ) := rfl

theorem unit_cycle_second_zero
    (x : (complex (0 : Vec3 R) (unitCoupling R)).g.hom.ker) : x.1.2 0 = 0 := by
  change (outgoing (0 : Vec3 R) (unitCoupling R)).ker at x
  have h := LinearMap.mem_ker.mp x.2
  change outgoing (0 : Vec3 R) (unitCoupling R) x.1 = 0 at h
  rw [outgoing_zero_unit] at h
  have hfirst := congrArg Prod.fst h
  simpa using hfirst

theorem unitCycleCoordinates_surjective :
    Function.Surjective (unitCycleCoordinates (R := R)) := by
  rintro ⟨x, y⟩
  refine ⟨⟨(![0, x 0, x 1], ![0, y 0, y 1]), ?_⟩, ?_⟩
  · change outgoing (0 : Vec3 R) (unitCoupling R)
      (![0, x 0, x 1], ![0, y 0, y 1]) = 0
    rw [outgoing_zero_unit]
    simp
  · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- The coordinates removed by the projection are exactly the coupled
boundaries, rather than an additional imposed quotient relation. -/
theorem unit_boundary_range_eq_ker :
    (complex (0 : Vec3 R) (unitCoupling R)).moduleCatToCycles.range =
      (unitCycleCoordinates (R := R)).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change Vec3 R × R at y
    rw [LinearMap.mem_ker]
    change (tailCoordinates (incoming (0 : Vec3 R) (unitCoupling R) y).1,
      tailCoordinates (incoming (0 : Vec3 R) (unitCoupling R) y).2) = 0
    rw [incoming_zero_unit]
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [tailCoordinates, unitCoupling]
  · intro hx
    have hcoords := LinearMap.mem_ker.mp hx
    have hx1 : x.1.1 1 = 0 := congrArg (fun z => z.1 0) hcoords
    have hx2 : x.1.1 2 = 0 := congrArg (fun z => z.1 1) hcoords
    have hy1 : x.1.2 1 = 0 := congrArg (fun z => z.2 0) hcoords
    have hy2 : x.1.2 2 = 0 := congrArg (fun z => z.2 1) hcoords
    refine ⟨(0, x.1.1 0), ?_⟩
    apply Subtype.ext
    change incoming (0 : Vec3 R) (unitCoupling R) (0, x.1.1 0) = x.1
    rw [incoming_zero_unit]
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [unitCoupling, hx1, hx2]
    · funext i
      fin_cases i <;> simp [unit_cycle_second_zero x, hy1, hy2]

/-- The unit coupling removes exactly two of the six homology coordinates. -/
noncomputable def unitHomologyEquiv (R : Type u) [CommRing R] :
    (complex (0 : Vec3 R) (unitCoupling R)).homology ≃ₗ[R]
      ((Fin 2 → R) × (Fin 2 → R)) :=
  (complex (0 : Vec3 R) (unitCoupling R)).moduleCatHomologyIso.toLinearEquiv |>.trans
    ((Submodule.quotEquivOfEq _ _ unit_boundary_range_eq_ker).trans
      ((unitCycleCoordinates (R := R)).quotKerEquivOfSurjective
        unitCycleCoordinates_surjective))

section Field

variable (K : Type u) [Field K]

theorem finrank_homology_zero :
    Module.finrank K (complex (0 : Vec3 K) 0).homology = 6 := by
  rw [(zeroHomologyEquiv K).finrank_eq]
  simp [Vec3, Module.finrank_prod]

theorem finrank_homology_unit :
    Module.finrank K (complex (0 : Vec3 K) (unitCoupling K)).homology = 4 := by
  rw [(unitHomologyEquiv K).finrank_eq]
  simp [Module.finrank_prod]

/-- The reduced complexes cannot be isomorphic: their native homology
dimensions differ. This is an algebraic obstruction to a chain isomorphism. -/
theorem not_nonempty_zero_unit_complex_iso :
    ¬ Nonempty (complex (0 : Vec3 K) 0 ≅ complex (0 : Vec3 K) (unitCoupling K)) := by
  rintro ⟨e⟩
  have h := (ShortComplex.homologyMapIso e).toLinearEquiv.finrank_eq
  rw [finrank_homology_zero, finrank_homology_unit] at h
  norm_num at h

end Field

end InfoGeometry.Quantum.CSSKoszulExtension
