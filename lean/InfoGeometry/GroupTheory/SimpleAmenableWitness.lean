/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import OAI.GroupTheory.SimpleAmenable.Main

/-!
# Concrete simple amenable permutation-group witness

Expose the external existence theorem on its actual polygon alternating-group
carrier. This is a permutation subgroup arising from the track action, not a
new abstract group or a commutative proxy.
-/

public section

noncomputable section

namespace InfoGeometry.GroupTheory.SimpleAmenableWitness

open OAI.SimpleAmenable

/-- The external construction supplies a concrete infinite, finitely
presented, simple, Følner-amenable polygon alternating group at stage `206`.
The statement retains its subgroup-of-permutations carrier. -/
theorem exists_polygon_alternating_simple_amenable_group :
    ∃ a : ℕ, 0 < a ∧
      Infinite (polygonAlternatingGroup a 206) ∧
      Group.IsFinitelyPresented (polygonAlternatingGroup a 206) ∧
      IsSimpleGroup (polygonAlternatingGroup a 206) ∧
      FolnerAmenable (polygonAlternatingGroup a 206) := by
  obtain ⟨a, ha, hprogress⟩ :=
    OAI.SimpleAmenable.fixed_track_polygon_progress
  obtain ⟨hinfinite, hsimple, hfolner, H, hH, q, hpresented, hsurjective, hcentral⟩ :=
    hprogress 206 (by omega)
  have hperfect : Group.IsPerfect (polygonAlternatingGroup a 206) :=
    polygonAlternatingGroup_perfect a 206 (by omega)
  have hh2 : Module.Finite ℤ
      (groupHomology.H2
        (IntegralTransgression.coefficients (polygonAlternatingGroup a 206))) :=
    polygon_alternating_H2_finite a 206 ha (by omega)
  letI : Group H := hH
  letI : Group.IsFinitelyPresented H := hpresented
  letI : Group.IsPerfect (polygonAlternatingGroup a 206) := hperfect
  letI : Module.Finite ℤ
      (groupHomology.H2
        (IntegralTransgression.coefficients (polygonAlternatingGroup a 206))) := hh2
  have hfp : Group.IsFinitelyPresented (polygonAlternatingGroup a 206) :=
    finitelyPresented_of_central_cover_h2 q hsurjective hcentral
  exact ⟨a, ha, hinfinite, hfp, hsimple, hfolner⟩

/-! ## Faithful noncommutative operator realization -/

/-- The concrete stage-206 polygon alternating group. Its elements are
permutations of the external construction's actual track-point carrier. -/
abbrev PolygonGroup (a : ℕ) := polygonAlternatingGroup a 206

/-- The permutation of track points underlying an element of the polygon
alternating subgroup. -/
def polygonPerm {a : ℕ} (g : PolygonGroup a) : Equiv.Perm (TrackPoint a 206) :=
  (g : polygonFullGroup a 206).val

/-- The inverse-reindexing operator induced by a polygon permutation. -/
def polygonOperator {a : ℕ} (g : PolygonGroup a) :
    Module.End ℝ (TrackPoint a 206 → ℝ) where
  toFun f x := f ((polygonPerm g)⁻¹ x)
  map_add' f h := by funext x; rfl
  map_smul' c f := by funext x; rfl

/-- Composition of these operators follows the multiplication in the
permutation subgroup. -/
def polygonOperatorRep (a : ℕ) :
    PolygonGroup a →* Module.End ℝ (TrackPoint a 206 → ℝ) where
  toFun := polygonOperator
  map_one' := by ext f x; rfl
  map_mul' g h := by ext f x; rfl

/-- Package each polygon permutation operator as a unit in the full
endomorphism algebra of the track-point function space. -/
def polygonOperatorUnit {a : ℕ} (g : PolygonGroup a) :
    (Module.End ℝ (TrackPoint a 206 → ℝ))ˣ where
  val := polygonOperator g
  inv := polygonOperator g⁻¹
  val_inv := by ext f x; simp [polygonOperator, polygonPerm]
  inv_val := by ext f x; simp [polygonOperator, polygonPerm]

/-- The unit-valued representation of the polygon alternating group. -/
def polygonOperatorUnitRep (a : ℕ) :
    PolygonGroup a →* (Module.End ℝ (TrackPoint a 206 → ℝ))ˣ where
  toFun := polygonOperatorUnit
  map_one' := by apply Units.ext; ext f x; rfl
  map_mul' g h := by apply Units.ext; ext f x; rfl

/-- Function probes separate distinct track-point permutations, so the
operator-unit representation is faithful. -/
theorem polygonOperatorUnitRep_injective (a : ℕ) :
    Function.Injective (polygonOperatorUnitRep a) := by
  classical
  intro g h hgh
  have hop : polygonOperator g = polygonOperator h := congrArg Units.val hgh
  have hinv : (polygonPerm g)⁻¹ = (polygonPerm h)⁻¹ := by
    apply Equiv.ext
    intro x
    let gx := (polygonPerm g)⁻¹ x
    let hx := (polygonPerm h)⁻¹ x
    let δ : TrackPoint a 206 → ℝ := fun y => if y = gx then 1 else 0
    have heval := congrArg (fun T : Module.End ℝ (TrackPoint a 206 → ℝ) => T δ x) hop
    change δ gx = δ hx at heval
    have hargs : hx = gx := by
      by_cases h' : hx = gx
      · exact h'
      · simp [δ, gx, hx] at heval
        exact False.elim (h' heval)
    change gx = hx
    exact hargs.symm
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hsymm := congrArg (fun p : Equiv.Perm (TrackPoint a 206) => p x)
    (congrArg Inv.inv hinv)
  simpa [polygonPerm] using hsymm

/-- The faithful operator image, as a subgroup of units in the endomorphism
algebra of real-valued functions on the polygon track-point carrier. -/
def polygonOperatorGroup (a : ℕ) :
    Subgroup (Module.End ℝ (TrackPoint a 206 → ℝ))ˣ :=
  (⊤ : Subgroup (PolygonGroup a)).map (polygonOperatorUnitRep a)

/-- The polygon simple group and its faithful operator-unit image are
isomorphic. -/
def polygonOperatorRangeRep (a : ℕ) :
    PolygonGroup a →* ↥(polygonOperatorGroup a) where
  toFun g := ⟨polygonOperatorUnitRep a g,
    Subgroup.mem_map.mpr ⟨g, trivial, rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one (polygonOperatorUnitRep a)
  map_mul' g h := by apply Subtype.ext; exact map_mul (polygonOperatorUnitRep a) g h

def polygonOperatorGroup_equiv (a : ℕ) :
    PolygonGroup a ≃* ↥(polygonOperatorGroup a) :=
  MulEquiv.ofBijective (polygonOperatorRangeRep a)
    ⟨fun g h hh => polygonOperatorUnitRep_injective a (congrArg Subtype.val hh),
      fun u => by
        obtain ⟨g, _, hg⟩ := Subgroup.mem_map.mp u.2
        exact ⟨g, Subtype.ext hg⟩⟩

/-- Simplicity of the polygon group is retained by its noncommutative
endomorphism-unit realization. -/
theorem polygonOperatorGroup_simple (a : ℕ) (ha : 0 < a) :
    IsSimpleGroup ↥(polygonOperatorGroup a) := by
  letI : IsSimpleGroup (PolygonGroup a) := polygonAlternatingGroup_simple a 206 (by omega)
  exact (polygonOperatorGroup_equiv a).symm.isSimpleGroup

/-- The simple amenable polygon group has noncommuting elements. If it were
commutative, Mathlib's commutative-simple-group theorem would make it finite,
contrary to the external construction's infinitude theorem. -/
theorem polygonGroup_exists_noncommuting_pair (a : ℕ) (ha : 0 < a) :
    ∃ g h : PolygonGroup a, g * h ≠ h * g := by
  have hinfinite : Infinite (PolygonGroup a) :=
    (polygon_infinite_simple_folner ha (by norm_num : 15 ≤ 206)).1
  by_contra hpair
  push_neg at hpair
  letI : CommGroup (PolygonGroup a) :=
    { (inferInstance : Group (PolygonGroup a)) with mul_comm := hpair }
  letI : IsSimpleGroup (PolygonGroup a) :=
    polygonAlternatingGroup_simple a 206 (by omega)
  letI : Finite (PolygonGroup a) := IsSimpleGroup.finite
  exact hinfinite.not_finite this

/-- The noncommuting polygon elements remain noncommuting in the faithful
endomorphism-unit group. -/
theorem polygonOperatorGroup_exists_noncommuting_pair (a : ℕ) (ha : 0 < a) :
    ∃ U V : ↥(polygonOperatorGroup a), U * V ≠ V * U := by
  obtain ⟨g, h, hne⟩ := polygonGroup_exists_noncommuting_pair a ha
  let e := polygonOperatorGroup_equiv a
  refine ⟨e g, e h, ?_⟩
  intro hcomm
  apply hne
  apply e.injective
  calc
    e (g * h) = e g * e h := map_mul e g h
    _ = e h * e g := hcomm
    _ = e (h * g) := (map_mul e h g).symm

end InfoGeometry.GroupTheory.SimpleAmenableWitness
