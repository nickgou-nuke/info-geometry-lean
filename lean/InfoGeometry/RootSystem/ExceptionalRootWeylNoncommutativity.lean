/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.RootSystem.ExceptionalRootOperatorWeyl

/-!
# Noncommuting exceptional root-Weyl operators

Adjacent simple reflections fail to commute on the integral root lattice.
Faithfulness then carries explicit witnesses into the operator-unit group on
real-valued root-lattice functions.
-/

namespace InfoGeometry.RootSystem.Exceptional

open InfoGeometry.Exceptional.CFSGPort.Chevalley

private theorem reflect_coord_of_ne (τ : Tag) (i j : Fin τ.rank)
    (v : RootLattice τ) (hij : i ≠ j) :
    reflect τ i v j = v j := by
  simp [reflect, hij]

private theorem reflect_single_coord_of_ne (τ : Tag) (i j : Fin τ.rank)
    (hij : i ≠ j) :
    reflect τ j (Pi.single i (1 : ℤ) : RootLattice τ) j = -τ.cartan j i := by
  unfold reflect
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hij,
    mul_zero, sub_zero]
  have hsum :
      (∑ k, τ.cartan j k * ((Pi.single i (1 : ℤ) : RootLattice τ) k)) = τ.cartan j i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k hk hki
      simp [hki]
    · simp
  rw [hsum]
  simp [hij]

private theorem simpleReflection_noncommute_of_cartan_ne_zero
    (τ : Tag) (i j : Fin τ.rank) (hij : i ≠ j)
    (hcartan : τ.cartan j i ≠ 0) :
    simpleReflection τ i * simpleReflection τ j ≠
      simpleReflection τ j * simpleReflection τ i := by
  intro h
  have hfun := congrArg (fun w : Equiv.Perm (RootLattice τ) =>
    w (Pi.single i (1 : ℤ) : RootLattice τ)) h
  simp only [Equiv.Perm.mul_apply] at hfun
  change reflect τ i (reflect τ j (Pi.single i (1 : ℤ) : RootLattice τ)) =
    reflect τ j (reflect τ i (Pi.single i (1 : ℤ) : RootLattice τ)) at hfun
  have hcoord := congrArg (fun v : RootLattice τ => v j) hfun
  have hleft :
      reflect τ i (reflect τ j (Pi.single i (1 : ℤ) : RootLattice τ)) j = -τ.cartan j i := by
    rw [reflect_coord_of_ne τ i j _ hij]
    exact reflect_single_coord_of_ne τ i j hij
  have hright :
      reflect τ j (reflect τ i (Pi.single i (1 : ℤ) : RootLattice τ)) j = τ.cartan j i := by
    rw [reflect_single_self τ i]
    have hlin : reflect τ j (-(Pi.single i (1 : ℤ) : RootLattice τ)) =
        -reflect τ j (Pi.single i (1 : ℤ) : RootLattice τ) := by
      simpa [reflectHom_apply] using
        (map_neg (reflectHom τ j) (Pi.single i (1 : ℤ) : RootLattice τ))
    rw [hlin]
    simp [reflect_single_coord_of_ne τ i j hij]
  rw [hleft, hright] at hcoord
  exact hcartan (by omega)

private def reflectionWeylElement (τ : Tag) (i : Fin τ.rank) :
    rootLatticeWeylGroup τ :=
  ⟨simpleReflection τ i, Subgroup.subset_closure ⟨i, rfl⟩⟩

private theorem reflectionWeylElement_noncommute
    (τ : Tag) (i j : Fin τ.rank) (hij : i ≠ j)
    (hcartan : τ.cartan j i ≠ 0) :
    reflectionWeylElement τ i * reflectionWeylElement τ j ≠
      reflectionWeylElement τ j * reflectionWeylElement τ i := by
  intro h
  apply simpleReflection_noncommute_of_cartan_ne_zero τ i j hij hcartan
  exact congrArg (fun w : rootLatticeWeylGroup τ =>
    (w : Equiv.Perm (RootLattice τ))) h

/-- In every exceptional root system, an explicitly selected pair of simple
reflections is noncommuting in the concrete lattice Weyl subgroup. -/
theorem exceptionalRootWeyl_has_noncommuting_pair (τ : Tag) :
    ∃ g h : rootLatticeWeylGroup τ, g * h ≠ h * g := by
  cases τ with
  | G2 =>
      let i : Fin 2 := ⟨0, by omega⟩
      let j : Fin 2 := ⟨1, by omega⟩
      exact ⟨reflectionWeylElement .G2 i, reflectionWeylElement .G2 j,
        reflectionWeylElement_noncommute .G2 i j
          (by intro h; have hh := congrArg Fin.val h; norm_num at hh)
          (by change (Tag.cartan .G2 j i) ≠ 0; norm_num [Tag.cartan, i, j])⟩
  | F4 =>
      let i : Fin 4 := ⟨0, by omega⟩
      let j : Fin 4 := ⟨1, by omega⟩
      exact ⟨reflectionWeylElement .F4 i, reflectionWeylElement .F4 j,
        reflectionWeylElement_noncommute .F4 i j
          (by intro h; have hh := congrArg Fin.val h; norm_num at hh)
          (by change (Tag.cartan .F4 j i) ≠ 0; norm_num [Tag.cartan, i, j])⟩
  | D4 =>
      let i : Fin 4 := ⟨0, by omega⟩
      let j : Fin 4 := ⟨2, by omega⟩
      exact ⟨reflectionWeylElement .D4 i, reflectionWeylElement .D4 j,
        reflectionWeylElement_noncommute .D4 i j
          (by intro h; have hh := congrArg Fin.val h; norm_num at hh)
          (by change (Tag.cartan .D4 j i) ≠ 0; norm_num [Tag.cartan, i, j])⟩
  | E6 =>
      let i : Fin 6 := ⟨0, by omega⟩
      let j : Fin 6 := ⟨2, by omega⟩
      exact ⟨reflectionWeylElement .E6 i, reflectionWeylElement .E6 j,
        reflectionWeylElement_noncommute .E6 i j
          (by intro h; have hh := congrArg Fin.val h; norm_num at hh)
          (by change (Tag.cartan .E6 j i) ≠ 0; norm_num [Tag.cartan, Tag.cartanE, i, j])⟩
  | E7 =>
      let i : Fin 7 := ⟨0, by omega⟩
      let j : Fin 7 := ⟨2, by omega⟩
      exact ⟨reflectionWeylElement .E7 i, reflectionWeylElement .E7 j,
        reflectionWeylElement_noncommute .E7 i j
          (by intro h; have hh := congrArg Fin.val h; norm_num at hh)
          (by change (Tag.cartan .E7 j i) ≠ 0; norm_num [Tag.cartan, Tag.cartanE, i, j])⟩
  | E8 =>
      let i : Fin 8 := ⟨0, by omega⟩
      let j : Fin 8 := ⟨2, by omega⟩
      exact ⟨reflectionWeylElement .E8 i, reflectionWeylElement .E8 j,
        reflectionWeylElement_noncommute .E8 i j
          (by intro h; have hh := congrArg Fin.val h; norm_num at hh)
          (by change (Tag.cartan .E8 j i) ≠ 0; norm_num [Tag.cartan, Tag.cartanE, i, j])⟩

/-- The concrete operator-unit Weyl group has an explicit noncommuting pair
for every exceptional tag. -/
theorem exceptionalRootOperatorWeyl_has_noncommuting_pair (τ : Tag) :
    ∃ U V : (Module.End ℝ (RootLattice τ → ℝ))ˣ,
      U ∈ rootOperatorWeylGroup τ ∧ V ∈ rootOperatorWeylGroup τ ∧
        U * V ≠ V * U := by
  obtain ⟨g, h, hgh⟩ := exceptionalRootWeyl_has_noncommuting_pair τ
  refine ⟨rootWeylOperatorUnitRep τ g, rootWeylOperatorUnitRep τ h, ?_, ?_, ?_⟩
  · rw [rootOperatorWeylGroup, Subgroup.mem_map]
    exact ⟨g, trivial, rfl⟩
  · rw [rootOperatorWeylGroup, Subgroup.mem_map]
    exact ⟨h, trivial, rfl⟩
  · exact rootWeylOperatorUnitRep_ne_mul_swap τ g h hgh

end InfoGeometry.RootSystem.Exceptional
