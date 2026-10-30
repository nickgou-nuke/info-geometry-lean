/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.RootSystem.ExceptionalRootLatticeWeyl
import InfoGeometry.RootSystem.ExceptionalRootOperatorWeyl
import InfoGeometry.CoxeterPort.MatrixGroup

/-!
# D₄ relations on the exceptional root-coordinate lattice

These calculations establish the braid and commuting relations directly on
the root-coordinate carrier. They are the local inputs for a Coxeter-to-Weyl
homomorphism.
-/

noncomputable section

namespace InfoGeometry.RootSystem.Exceptional

open InfoGeometry.Exceptional.CFSGPort.Chevalley

/-- The integer Cartan pairing of a root coordinate vector with a simple root. -/
def cartanPairing (τ : Tag) (i : Fin τ.rank)
    (v : Fin τ.rank → ℤ) : ℤ := ∑ k, τ.cartan i k * v k

private theorem cartanE_symmetric (r : ℕ) (i j : Fin r) :
    Tag.cartanE r i j = Tag.cartanE r j i := by
  unfold Tag.cartanE
  omega

private theorem cartanE_off_diagonal (r : ℕ) (i j : Fin r) (hij : i ≠ j) :
    Tag.cartanE r i j = 0 ∨ Tag.cartanE r i j = -1 := by
  unfold Tag.cartanE
  rw [ite_eq_right hij]
  split_ifs <;> simp

private theorem reflect_pairing (τ : Tag) (i : Fin τ.rank)
    (v : Fin τ.rank → ℤ) :
    reflect τ i v = v - cartanPairing τ i v • Pi.single i 1 := rfl

private theorem cartanPairing_single (τ : Tag) (i j : Fin τ.rank) :
    cartanPairing τ i (Pi.single j (1 : ℤ)) = τ.cartan i j := by
  unfold cartanPairing
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Pi.single_eq_of_ne hkj]
  · simp

theorem cartanPairing_reflect (τ : Tag) (i j : Fin τ.rank)
    (v : Fin τ.rank → ℤ) :
    cartanPairing τ i (reflect τ j v) =
      cartanPairing τ i v - cartanPairing τ j v * τ.cartan i j := by
  unfold cartanPairing
  simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hterm (k : Fin τ.rank) :
      τ.cartan i k * (v k - (∑ l, τ.cartan j l * v l) *
        ((Pi.single j (1 : ℤ) : Fin τ.rank → ℤ) k)) =
        τ.cartan i k * v k - (∑ l, τ.cartan j l * v l) *
          (τ.cartan i k * ((Pi.single j (1 : ℤ) : Fin τ.rank → ℤ) k)) := by ring
  have hsum : ∑ k, τ.cartan i k * ((Pi.single j (1 : ℤ) : Fin τ.rank → ℤ) k) =
      τ.cartan i j := by
    simpa [cartanPairing] using cartanPairing_single τ i j
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_sub_distrib,
    ← Finset.mul_sum, hsum]

theorem reflect_commute_of_cartan_zero (τ : Tag) (i j : Fin τ.rank)
    (hij : τ.cartan i j = 0) (hji : τ.cartan j i = 0) (v : Fin τ.rank → ℤ) :
    reflect τ i (reflect τ j v) = reflect τ j (reflect τ i v) := by
  have hpi : cartanPairing τ i (reflect τ j v) = cartanPairing τ i v := by
    rw [cartanPairing_reflect, hij, mul_zero, sub_zero]
  have hpj : cartanPairing τ j (reflect τ i v) = cartanPairing τ j v := by
    rw [cartanPairing_reflect, hji, mul_zero, sub_zero]
  have hpi' : cartanPairing τ i (v - cartanPairing τ j v • Pi.single j 1) =
      cartanPairing τ i v := by simpa only [reflect_pairing] using hpi
  have hpj' : cartanPairing τ j (v - cartanPairing τ i v • Pi.single i 1) =
      cartanPairing τ j v := by simpa only [reflect_pairing] using hpj
  simp only [reflect_pairing]
  rw [hpi', hpj']
  module

theorem reflect_braid_of_cartan_neg_one (τ : Tag) (i j : Fin τ.rank)
    (hii : τ.cartan i i = 2) (hjj : τ.cartan j j = 2)
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1)
    (v : Fin τ.rank → ℤ) :
    reflect τ i (reflect τ j (reflect τ i v)) =
      reflect τ j (reflect τ i (reflect τ j v)) := by
  let a := cartanPairing τ i v
  let b := cartanPairing τ j v
  have hia : cartanPairing τ i (reflect τ i v) = -a := by
    rw [cartanPairing_reflect]
    dsimp [a]
    rw [hii]
    ring
  have hja : cartanPairing τ j (reflect τ i v) = b + a := by
    rw [cartanPairing_reflect]
    dsimp [a, b]
    rw [hji]
    ring
  have hbj : cartanPairing τ j (reflect τ j v) = -b := by
    rw [cartanPairing_reflect]
    dsimp [b]
    rw [hjj]
    ring
  have hib : cartanPairing τ i (reflect τ j v) = a + b := by
    rw [cartanPairing_reflect]
    dsimp [a, b]
    rw [hij]
    ring
  have hleft : cartanPairing τ i (reflect τ j (reflect τ i v)) = b := by
    rw [cartanPairing_reflect, hia, hja, hij]
    ring
  have hright : cartanPairing τ j (reflect τ i (reflect τ j v)) = a := by
    rw [cartanPairing_reflect, hbj, hib, hji]
    ring
  simp only [reflect_pairing] at hia hja hbj hib hleft hright
  simp only [reflect_pairing]
  rw [hleft, hja, hright, hib]
  module

/-- Adjacent D₄ root-coordinate reflections at nodes 0 and 2 satisfy the braid law. -/
theorem d4RootCoordinate_reflection_braid_02 :
    simpleReflection .D4 (⟨0, by decide⟩ : Fin 4) *
      simpleReflection .D4 (⟨2, by decide⟩ : Fin 4) *
      simpleReflection .D4 (⟨0, by decide⟩ : Fin 4) =
    simpleReflection .D4 (⟨2, by decide⟩ : Fin 4) *
      simpleReflection .D4 (⟨0, by decide⟩ : Fin 4) *
      simpleReflection .D4 (⟨2, by decide⟩ : Fin 4) := by
  apply Equiv.ext
  intro v
  exact reflect_braid_of_cartan_neg_one .D4 ⟨0, by decide⟩ ⟨2, by decide⟩
    (by decide) (by decide) (by decide) (by decide) v

/-- The first and second D₄ root-coordinate reflections commute. -/
theorem d4RootCoordinate_reflection_commute_01 :
    Commute (simpleReflection .D4 (⟨0, by decide⟩ : Fin 4))
      (simpleReflection .D4 (⟨1, by decide⟩ : Fin 4)) := by
  change simpleReflection .D4 (⟨0, by decide⟩ : Fin 4) *
    simpleReflection .D4 (⟨1, by decide⟩ : Fin 4) =
      simpleReflection .D4 (⟨1, by decide⟩ : Fin 4) *
        simpleReflection .D4 (⟨0, by decide⟩ : Fin 4)
  apply Equiv.ext
  intro v
  exact reflect_commute_of_cartan_zero .D4 ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) (by decide) v

/-- The Coxeter matrix attached to a simply-laced exceptional Cartan matrix.
An off-diagonal pair has label three exactly when the two Cartan entries are
both `-1`; otherwise its label is two. The relation theorem below is only
applied after supplying the simply-laced Cartan hypotheses. -/
def simplyLacedCoxeterMatrix (τ : Tag) : CoxeterMatrix (Fin τ.rank) where
  M i j := if i = j then 1 else if τ.cartan i j * τ.cartan j i = 1 then 3 else 2
  isSymm := by
    ext i j
    change (if j = i then 1 else if τ.cartan j i * τ.cartan i j = 1 then 3 else 2) =
      (if i = j then 1 else if τ.cartan i j * τ.cartan j i = 1 then 3 else 2)
    simp [eq_comm, mul_comm]
  diagonal := by
    intro i
    simp
  off_diagonal := by
    intro i j hij
    by_cases hcart : τ.cartan i j * τ.cartan j i = 1 <;>
      simp [hij, hcart]

private theorem simpleReflection_cube_eq_one_of_involutions_and_braid
    {G : Type*} [Group G] (s t : G)
    (hs : s * s = 1) (ht : t * t = 1)
    (hbraid : s * t * s = t * s * t) : (s * t) ^ 3 = 1 := by
  calc
    (s * t) ^ 3 = s * t * s * t * s * t := by
      rw [pow_succ, pow_succ, pow_one]
      simp only [mul_assoc]
    _ = t * s * t * t * s * t := by rw [hbraid]
    _ = (t * s) * (t * t) * (s * t) := by group
    _ = (t * s) * 1 * (s * t) := by rw [ht]
    _ = t * (s * s) * t := by group
    _ = t * 1 * t := by rw [hs]
    _ = 1 := by simp [ht]

/-- The simple reflections of a simply-laced Cartan system satisfy the
relations of its Coxeter matrix on the actual integral root-coordinate
lattice. -/
theorem simpleReflection_isLiftable_of_simplyLaced (τ : Tag)
    (hdiag : ∀ i : Fin τ.rank, τ.cartan i i = 2)
    (hsymm : ∀ i j : Fin τ.rank, τ.cartan i j = τ.cartan j i)
    (hoff : ∀ i j : Fin τ.rank, i ≠ j →
      τ.cartan i j = 0 ∨ τ.cartan i j = -1) :
    (simplyLacedCoxeterMatrix τ).IsLiftable (simpleReflection τ) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [show (simplyLacedCoxeterMatrix τ) i i = 1 by simp [simplyLacedCoxeterMatrix]]
    simpa using simpleReflection_sq τ i
  · rcases hoff i j hij with hzero | hadj
    · have hji : τ.cartan j i = 0 := by rw [hsymm]; exact hzero
      have hlabel : (simplyLacedCoxeterMatrix τ) i j = 2 := by
        simp [simplyLacedCoxeterMatrix, hij, hzero, hji]
      rw [hlabel]
      have hcomm : Commute (simpleReflection τ i) (simpleReflection τ j) := by
        apply Equiv.ext
        intro v
        exact reflect_commute_of_cartan_zero τ i j hzero hji v
      calc
        (simpleReflection τ i * simpleReflection τ j) ^ 2 =
            simpleReflection τ i * simpleReflection τ j *
              (simpleReflection τ i * simpleReflection τ j) := by rw [pow_two]
        _ = simpleReflection τ i * (simpleReflection τ j * simpleReflection τ i) *
              simpleReflection τ j := by group
        _ = simpleReflection τ i * (simpleReflection τ i * simpleReflection τ j) *
              simpleReflection τ j := by rw [hcomm.eq]
        _ = 1 := by
          rw [← mul_assoc]
          simp [simpleReflection_sq]
    · have hji : τ.cartan j i = -1 := by rw [hsymm]; exact hadj
      have hlabel : (simplyLacedCoxeterMatrix τ) i j = 3 := by
        simp [simplyLacedCoxeterMatrix, hij, hadj, hji]
      rw [hlabel]
      apply simpleReflection_cube_eq_one_of_involutions_and_braid
        (simpleReflection τ i) (simpleReflection τ j)
        (simpleReflection_sq τ i) (simpleReflection_sq τ j)
      apply Equiv.ext
      intro v
      exact reflect_braid_of_cartan_neg_one τ i j (hdiag i) (hdiag j) hadj hji v

/-- The abstract simply-laced Coxeter group maps onto the concrete subgroup
generated by the simple reflections on the root lattice. The theorem states
surjectivity; it makes no injectivity claim about the presentation map. -/
noncomputable def simplyLacedCoxeterToWeyl (τ : Tag)
    (hdiag : ∀ i : Fin τ.rank, τ.cartan i i = 2)
    (hsymm : ∀ i j : Fin τ.rank, τ.cartan i j = τ.cartan j i)
    (hoff : ∀ i j : Fin τ.rank, i ≠ j →
      τ.cartan i j = 0 ∨ τ.cartan i j = -1) :
    (simplyLacedCoxeterMatrix τ).Group →* rootLatticeWeylGroup τ := by
  let f : Fin τ.rank → rootLatticeWeylGroup τ := fun i =>
    ⟨simpleReflection τ i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hf : (simplyLacedCoxeterMatrix τ).IsLiftable f := by
    intro i j
    apply Subtype.ext
    exact simpleReflection_isLiftable_of_simplyLaced τ hdiag hsymm hoff i j
  exact (simplyLacedCoxeterMatrix τ).toCoxeterSystem.lift ⟨f, hf⟩

@[simp] theorem simplyLacedCoxeterToWeyl_simple (τ : Tag)
    (hdiag : ∀ i : Fin τ.rank, τ.cartan i i = 2)
    (hsymm : ∀ i j : Fin τ.rank, τ.cartan i j = τ.cartan j i)
    (hoff : ∀ i j : Fin τ.rank, i ≠ j →
      τ.cartan i j = 0 ∨ τ.cartan i j = -1)
    (i : Fin τ.rank) :
    simplyLacedCoxeterToWeyl τ hdiag hsymm hoff
      ((simplyLacedCoxeterMatrix τ).simple i) =
        ⟨simpleReflection τ i, Subgroup.subset_closure ⟨i, rfl⟩⟩ := by
  let f : Fin τ.rank → rootLatticeWeylGroup τ := fun j =>
    ⟨simpleReflection τ j, Subgroup.subset_closure ⟨j, rfl⟩⟩
  have hf : (simplyLacedCoxeterMatrix τ).IsLiftable f := by
    intro j k
    apply Subtype.ext
    exact simpleReflection_isLiftable_of_simplyLaced τ hdiag hsymm hoff j k
  change ((simplyLacedCoxeterMatrix τ).toCoxeterSystem.lift ⟨f, hf⟩)
      ((simplyLacedCoxeterMatrix τ).simple i) = f i
  exact CoxeterSystem.lift_apply_simple
    (simplyLacedCoxeterMatrix τ).toCoxeterSystem hf i

theorem simplyLacedCoxeterToWeyl_surjective (τ : Tag)
    (hdiag : ∀ i : Fin τ.rank, τ.cartan i i = 2)
    (hsymm : ∀ i j : Fin τ.rank, τ.cartan i j = τ.cartan j i)
    (hoff : ∀ i j : Fin τ.rank, i ≠ j →
      τ.cartan i j = 0 ∨ τ.cartan i j = -1) :
    Function.Surjective (simplyLacedCoxeterToWeyl τ hdiag hsymm hoff) := by
  intro w
  let f := simplyLacedCoxeterToWeyl τ hdiag hsymm hoff
  let φ := (rootLatticeWeylGroup τ).subtype.comp f
  have hgen : rootLatticeWeylGroup τ ≤ φ.range := by
    change Subgroup.closure (Set.range (simpleReflection τ)) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    change simpleReflection τ i ∈ φ.range
    rw [MonoidHom.mem_range]
    refine ⟨(simplyLacedCoxeterMatrix τ).simple i, ?_⟩
    change (rootLatticeWeylGroup τ).subtype
      (f ((simplyLacedCoxeterMatrix τ).simple i)) = simpleReflection τ i
    rw [simplyLacedCoxeterToWeyl_simple τ hdiag hsymm hoff i]
    rfl
  obtain ⟨x, hx⟩ := (MonoidHom.mem_range).1 (hgen w.property)
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- For each simply-laced exceptional E-type Cartan matrix, the concrete
root-lattice Weyl group is the image of the corresponding abstract Coxeter
group. -/
theorem exceptionalTypeE_CoxeterToWeyl_surjective (τ : Tag)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    Function.Surjective
      (simplyLacedCoxeterToWeyl τ
        (fun i => Tag.cartan_self τ i)
        (fun i j => by
          rcases hτ with rfl | rfl | rfl
          · exact cartanE_symmetric 6 i j
          · exact cartanE_symmetric 7 i j
          · exact cartanE_symmetric 8 i j)
        (fun i j hij => by
          rcases hτ with rfl | rfl | rfl
          · exact cartanE_off_diagonal 6 i j hij
          · exact cartanE_off_diagonal 7 i j hij
          · exact cartanE_off_diagonal 8 i j hij)) := by
  exact simplyLacedCoxeterToWeyl_surjective τ _ _ _

/-- The exceptional simply-laced Coxeter group represented directly in the
noncommutative operator-unit subgroup on real-valued root-lattice functions. -/
noncomputable def simplyLacedCoxeterToOperatorWeyl (τ : Tag)
    (hdiag : ∀ i : Fin τ.rank, τ.cartan i i = 2)
    (hsymm : ∀ i j : Fin τ.rank, τ.cartan i j = τ.cartan j i)
    (hoff : ∀ i j : Fin τ.rank, i ≠ j →
      τ.cartan i j = 0 ∨ τ.cartan i j = -1) :
    (simplyLacedCoxeterMatrix τ).Group →* ↥(rootOperatorWeylGroup τ) where
  toFun g := ⟨rootWeylOperatorUnitRep τ
    (simplyLacedCoxeterToWeyl τ hdiag hsymm hoff g), by
      rw [rootOperatorWeylGroup, Subgroup.mem_map]
      exact ⟨simplyLacedCoxeterToWeyl τ hdiag hsymm hoff g, trivial, rfl⟩⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; simp

@[simp] theorem simplyLacedCoxeterToOperatorWeyl_simple
    (τ : Tag) (hdiag : ∀ i : Fin τ.rank, τ.cartan i i = 2)
    (hsymm : ∀ i j : Fin τ.rank, τ.cartan i j = τ.cartan j i)
    (hoff : ∀ i j : Fin τ.rank, i ≠ j →
      τ.cartan i j = 0 ∨ τ.cartan i j = -1) (i : Fin τ.rank) :
    (simplyLacedCoxeterToOperatorWeyl τ hdiag hsymm hoff
      ((simplyLacedCoxeterMatrix τ).simple i) :
        ↥(rootOperatorWeylGroup τ)).1 =
      rootWeylOperatorUnitRep τ
        ⟨simpleReflection τ i, Subgroup.subset_closure ⟨i, rfl⟩⟩ := by
  simp [simplyLacedCoxeterToOperatorWeyl, simplyLacedCoxeterToWeyl_simple]

/-- For E₆, E₇, and E₈, the abstract Coxeter group surjects onto its actual
operator-unit Weyl image. This is the representation on endomorphisms, not
only the underlying action on root coordinates. -/
theorem exceptionalTypeE_CoxeterToOperatorWeyl_surjective (τ : Tag)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    Function.Surjective
      (simplyLacedCoxeterToOperatorWeyl τ
        (fun i => Tag.cartan_self τ i)
        (fun i j => by
          rcases hτ with rfl | rfl | rfl
          · exact cartanE_symmetric 6 i j
          · exact cartanE_symmetric 7 i j
          · exact cartanE_symmetric 8 i j)
        (fun i j hij => by
          rcases hτ with rfl | rfl | rfl
          · exact cartanE_off_diagonal 6 i j hij
          · exact cartanE_off_diagonal 7 i j hij
          · exact cartanE_off_diagonal 8 i j hij)) := by
  intro U
  have hU := U.property
  change U.1 ∈ (⊤ : Subgroup (rootLatticeWeylGroup τ)).map
    (rootWeylOperatorUnitRep τ) at hU
  rw [Subgroup.mem_map] at hU
  obtain ⟨w, -, hw⟩ := hU
  obtain ⟨g, hg⟩ := exceptionalTypeE_CoxeterToWeyl_surjective τ hτ w
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change rootWeylOperatorUnitRep τ
      (simplyLacedCoxeterToWeyl τ _ _ _ g) = U.1
  rw [hg]
  exact hw


end InfoGeometry.RootSystem.Exceptional
