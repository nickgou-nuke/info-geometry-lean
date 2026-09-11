import InfoGeometry.Lie.ExceptionalAutomorphicZetaBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment

/-!
# The finite root-star action supplied by the native G₂ root owner

This file deliberately stops at the root-star level.  The existing
`G2IntegralRootLattice` is a rank witness, not yet a concrete additive lattice
carrier, so no Weyl action on that structure is asserted here.
The Mathlib root reflections do, however, act on the twelve native roots and
preserve the exhaustive root star.  This is the honest finite prerequisite for
an eventual lattice construction.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2RootStarAction

open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment

attribute [local instance] Classical.decEq

abbrev RootIndex :=
  InfoGeometry.Lie.CanonicalZornRootSystemComparison.RootIndex

abbrev P :=
  InfoGeometry.Lie.CanonicalZornRootSystemComparison.P

abbrev FiniteRoot := G2Root

noncomputable def finiteRootToRootIndex : FiniteRoot ≃ RootIndex :=
  rootIndexEquiv.trans nativeRootIndexEquiv

def shortRoot : RootIndex :=
  nativeRootIndex nativeShortSimpleIndex

def longRoot : RootIndex :=
  nativeRootIndex nativeLongSimpleIndex

noncomputable def shortWeylReflection : P.weylGroup :=
  ⟨RootPairing.Equiv.reflection P shortRoot,
    RootPairing.reflection_mem_weylGroup P shortRoot⟩

noncomputable def longWeylReflection : P.weylGroup :=
  ⟨RootPairing.Equiv.reflection P longRoot,
    RootPairing.reflection_mem_weylGroup P longRoot⟩

theorem shortWeylReflection_sq : shortWeylReflection ^ 2 = 1 := by
  apply Subtype.ext
  change (RootPairing.Equiv.reflection P shortRoot) ^ 2 = 1
  rw [sq, mul_eq_one_iff_inv_eq, RootPairing.Equiv.reflection_inv]

theorem longWeylReflection_sq : longWeylReflection ^ 2 = 1 := by
  apply Subtype.ext
  change (RootPairing.Equiv.reflection P longRoot) ^ 2 = 1
  rw [sq, mul_eq_one_iff_inv_eq, RootPairing.Equiv.reflection_inv]

noncomputable def rootStarReflection
    (α : RootIndex) (S : Finset RootIndex) : Finset RootIndex :=
  by
    classical
    exact S.image (P.reflectionPerm α)

theorem rootStarReflection_univ (α : RootIndex) :
    rootStarReflection α (Finset.univ : Finset RootIndex) = Finset.univ := by
  classical
  ext β
  constructor
  · intro h
    exact Finset.mem_univ β
  · intro h
    obtain ⟨γ, hβ⟩ :=
      (P.reflectionPerm α).surjective β
    change β ∈ (Finset.univ : Finset RootIndex).image (P.reflectionPerm α)
    exact Finset.mem_image.mpr ⟨γ, Finset.mem_univ γ, hβ⟩

@[simp] theorem rootStarReflection_singleton (α β : RootIndex) :
    rootStarReflection α {β} = {(P.reflectionPerm α) β} := by
  classical
  simp [rootStarReflection]

theorem rootStarReflection_involutive (α : RootIndex) (S : Finset RootIndex) :
    rootStarReflection α (rootStarReflection α S) = S := by
  classical
  unfold rootStarReflection
  rw [Finset.image_image]
  have hfun : (P.reflectionPerm α) ∘ (P.reflectionPerm α) = id := by
    funext β
    exact P.reflectionPerm_self α β
  rw [hfun]
  simp

theorem rootStarReflection_card (α : RootIndex) (S : Finset RootIndex) :
    (rootStarReflection α S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S (P.reflectionPerm α).injective

theorem nativeRootPairing_reflection_invariant
    (α β γ : RootIndex) :
    P.pairing (P.reflectionPerm α β) (P.reflectionPerm α γ) =
      P.pairing β γ := by
  simpa only [P.reflectionPerm_self] using
    (P.pairing_reflectionPerm α (P.reflectionPerm α β) γ)

theorem rootPairing_reflectionPerm_coroot_formula
    (α β : RootIndex) :
    P.coroot (P.reflectionPerm α β) =
      P.coroot β - (P.pairing α β) • P.coroot α := by
  exact (P.reflectionPerm_coroot α β).symm

theorem rootStarReflection_singleton_weylGroup (α β : RootIndex) :
    rootStarReflection α {β} =
      {P.weylGroupToPerm
          ⟨RootPairing.Equiv.reflection P α,
            RootPairing.reflection_mem_weylGroup P α⟩ β} := by
  exact rootStarReflection_singleton α β

noncomputable def weylGroupRootStarAction
    (g : P.weylGroup) (S : Finset RootIndex) : Finset RootIndex :=
  by
    classical
    exact S.image (P.weylGroupToPerm g)

/-! The permutation action is exported as the native monoid hom supplied by
`RootPairing`.  This keeps the root-index action on the canonical Mathlib
carrier and avoids introducing a second Weyl-group representation. -/
abbrev rootActionTransport : P.weylGroup →* Equiv.Perm RootIndex :=
  P.weylGroupToPerm

/-! Conjugate the native permutation action along the existing finite-root
equivalence.  This is the canonical action on the finite root carrier; it is
not asserted to equal the separately defined finite Weyl action. -/
noncomputable def rootActionOnFiniteRoot (g : P.weylGroup) :
    Equiv.Perm FiniteRoot :=
  finiteRootToRootIndex.trans
    ((rootActionTransport g).trans finiteRootToRootIndex.symm)

/-! The finite-root reflection below is the canonical transport of
`RootPairing.reflectionPerm`.  It is intentionally separate from the native
`sAction`/`lAction` definitions; their equality is a later readback theorem. -/
noncomputable def rootPairingReflectionOnFiniteRoot
    (α : FiniteRoot) : FiniteRoot ≃ FiniteRoot :=
  finiteRootToRootIndex.trans
    ((P.reflectionPerm (finiteRootToRootIndex α)).trans
      finiteRootToRootIndex.symm)

/-- Native-facing coroot and pairing notation, transported from the
    authoritative Mathlib `RootPairing` along the finite-root equivalence. -/
noncomputable def nativeRootCoroot (α : FiniteRoot) :=
  P.coroot (finiteRootToRootIndex α)

theorem nativeRootCoroot_spec (α : FiniteRoot) :
    nativeRootCoroot α = P.coroot (finiteRootToRootIndex α) := rfl

noncomputable def nativeRootPairing (β α : FiniteRoot) : ℝ :=
  P.pairing (finiteRootToRootIndex β) (finiteRootToRootIndex α)

theorem nativeRootPairing_apply (β α : FiniteRoot) :
    nativeRootPairing β α =
      P.root (finiteRootToRootIndex β) (nativeRootCoroot α) := by
  unfold nativeRootPairing nativeRootCoroot
  exact nativeRootIndex_pairing_apply
    (rootIndexEquiv α) (rootIndexEquiv β)

theorem nativeFiniteRootPairing_reflection_invariant
    (α β γ : FiniteRoot) :
    nativeRootPairing
        (rootPairingReflectionOnFiniteRoot α β)
        (rootPairingReflectionOnFiniteRoot α γ) =
      nativeRootPairing β γ := by
  unfold nativeRootPairing rootPairingReflectionOnFiniteRoot
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  exact nativeRootPairing_reflection_invariant
    (finiteRootToRootIndex α) (finiteRootToRootIndex β)
    (finiteRootToRootIndex γ)

theorem rootPairingReflectionOnFiniteRoot_sq (α : FiniteRoot) :
    rootPairingReflectionOnFiniteRoot α ^ 2 = 1 := by
  rw [pow_two]
  apply Equiv.ext
  intro β
  simp [rootPairingReflectionOnFiniteRoot, P.reflectionPerm_self]

theorem rootPairingReflectionOnFiniteRoot_root_formula
    (α β : FiniteRoot) :
    P.root (finiteRootToRootIndex
      (rootPairingReflectionOnFiniteRoot α β)) =
      P.root (finiteRootToRootIndex β) -
        (P.pairing (finiteRootToRootIndex β)
          (finiteRootToRootIndex α)) •
          P.root (finiteRootToRootIndex α) := by
  simp only [rootPairingReflectionOnFiniteRoot, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [P.root_reflectionPerm]
  exact P.reflection_apply_root _ _

theorem native_root_reflection_formula (α β : FiniteRoot) :
    P.root (finiteRootToRootIndex
      (rootPairingReflectionOnFiniteRoot α β)) =
      P.root (finiteRootToRootIndex β) -
        nativeRootPairing β α • P.root (finiteRootToRootIndex α) := by
  exact rootPairingReflectionOnFiniteRoot_root_formula α β

theorem native_coroot_reflection_formula (α β : FiniteRoot) :
    nativeRootCoroot (rootPairingReflectionOnFiniteRoot α β) =
      P.coroot (finiteRootToRootIndex β) -
        (P.pairing (finiteRootToRootIndex α)
          (finiteRootToRootIndex β)) •
          nativeRootCoroot α := by
  unfold nativeRootCoroot rootPairingReflectionOnFiniteRoot
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  exact (P.reflectionPerm_coroot _ _).symm

theorem rootActionOnFiniteRoot_apply (g : P.weylGroup) (r : FiniteRoot) :
    finiteRootToRootIndex (rootActionOnFiniteRoot g r) =
      rootActionTransport g (finiteRootToRootIndex r) := by
  simp [rootActionOnFiniteRoot]

theorem rootActionOnFiniteRoot_equivariant (g : P.weylGroup) (r : FiniteRoot) :
    rootActionOnFiniteRoot g r =
      finiteRootToRootIndex.symm
        (rootActionTransport g (finiteRootToRootIndex r)) := by
  rfl

theorem rootActionOnFiniteRoot_mul (g h : P.weylGroup) :
    rootActionOnFiniteRoot (g * h) =
      rootActionOnFiniteRoot g * rootActionOnFiniteRoot h := by
  apply Equiv.ext
  intro r
  apply finiteRootToRootIndex.injective
  simp only [Equiv.Perm.mul_apply, rootActionOnFiniteRoot_apply]
  exact congrArg (fun q : Equiv.Perm RootIndex => q (finiteRootToRootIndex r))
    (map_mul rootActionTransport g h)

/-! The transported action is a genuine group action on the finite root
carrier.  This packages the pointwise transport above without identifying it
with the separately defined native `sAction`/`cAction` yet. -/
noncomputable def finiteRootAction : P.weylGroup →* Equiv.Perm FiniteRoot :=
{ toFun := rootActionOnFiniteRoot
  map_one' := by
    apply Equiv.ext
    intro r
    apply finiteRootToRootIndex.injective
    simp [rootActionOnFiniteRoot]
  map_mul' := by
    intro g h
    exact rootActionOnFiniteRoot_mul g h }

@[simp] theorem finiteRootAction_apply (g : P.weylGroup) (r : FiniteRoot) :
    finiteRootAction g r = rootActionOnFiniteRoot g r := rfl

theorem rootActionOnFiniteRoot_reflection (α : FiniteRoot) :
    rootActionOnFiniteRoot
        ⟨RootPairing.Equiv.reflection P (finiteRootToRootIndex α),
          RootPairing.reflection_mem_weylGroup P (finiteRootToRootIndex α)⟩ =
      rootPairingReflectionOnFiniteRoot α := by
  rfl

theorem rootActionOnFiniteRoot_long_on_short :
    finiteRootToRootIndex
        (rootActionOnFiniteRoot longWeylReflection
          (finiteRootToRootIndex.symm (nativeRootIndex nativeShortSimpleIndex))) =
      nativeRootIndex ⟨9, by decide, by decide⟩ := by
  rw [rootActionOnFiniteRoot_apply]
  simpa [longWeylReflection, rootActionTransport] using
    native_long_reflection_short

theorem rootActionOnFiniteRoot_short_on_long :
    finiteRootToRootIndex
        (rootActionOnFiniteRoot shortWeylReflection
          (finiteRootToRootIndex.symm (nativeRootIndex nativeLongSimpleIndex))) =
      nativeRootIndex ⟨11, by decide, by decide⟩ := by
  rw [rootActionOnFiniteRoot_apply]
  simpa [shortWeylReflection, rootActionTransport] using
    native_short_reflection_long

theorem native_sAction_preserves_rootLength (r : FiniteRoot) :
    (sAction r).1 = r.1 := by
  cases r with
  | mk l k => cases l <;> rfl

theorem native_cAction_preserves_rootLength (r : FiniteRoot) :
    (cAction r).1 = r.1 := by
  rfl

theorem rootActionOnFiniteRoot_card_image (g : P.weylGroup)
    (S : Finset FiniteRoot) :
    (S.image (rootActionOnFiniteRoot g)).card = S.card := by
  exact Finset.card_image_of_injective S (rootActionOnFiniteRoot g).injective

noncomputable def shortRootOrbit : Finset FiniteRoot :=
  (Finset.univ : Finset (ZMod 6)).image
    (fun k => (RootLength.Short, k))

noncomputable def longRootOrbit : Finset FiniteRoot :=
  (Finset.univ : Finset (ZMod 6)).image
    (fun k => (RootLength.Long, k))

theorem shortRootOrbit_card : shortRootOrbit.card = 6 := by
  classical
  rw [shortRootOrbit, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Prod.mk.inj h |>.2

theorem longRootOrbit_card : longRootOrbit.card = 6 := by
  classical
  rw [longRootOrbit, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Prod.mk.inj h |>.2

theorem shortRootOrbit_disjoint_longRootOrbit :
    Disjoint shortRootOrbit longRootOrbit := by
  classical
  rw [shortRootOrbit, longRootOrbit]
  simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_univ,
    true_and]
  rintro _ ⟨_, rfl⟩ ⟨_, h⟩
  cases h

theorem shortRootOrbit_union_longRootOrbit :
    shortRootOrbit ∪ longRootOrbit = Finset.univ := by
  classical
  ext r
  cases r with
  | mk l k =>
    cases l <;> simp [shortRootOrbit, longRootOrbit]

theorem shortRootOrbit_union_longRootOrbit_card :
    (shortRootOrbit ∪ longRootOrbit).card = 12 := by
  rw [Finset.card_union_of_disjoint shortRootOrbit_disjoint_longRootOrbit,
    shortRootOrbit_card, longRootOrbit_card]

noncomputable def shortRootIndices : Finset RootIndex :=
  shortRootOrbit.map finiteRootToRootIndex.toEmbedding

noncomputable def longRootIndices : Finset RootIndex :=
  longRootOrbit.map finiteRootToRootIndex.toEmbedding

theorem shortRootIndices_card : shortRootIndices.card = 6 := by
  rw [shortRootIndices, Finset.card_map, shortRootOrbit_card]

theorem longRootIndices_card : longRootIndices.card = 6 := by
  rw [longRootIndices, Finset.card_map, longRootOrbit_card]

@[simp] theorem rootActionTransport_apply (g : P.weylGroup) (i : RootIndex) :
    rootActionTransport g i = P.weylGroupToPerm g i := rfl

theorem rootActionTransport_mul (g h : P.weylGroup) :
    rootActionTransport (g * h) =
      rootActionTransport g * rootActionTransport h := by
  exact map_mul (rootActionTransport) g h

set_option maxHeartbeats 1000000 in
theorem rootActionTransport_pairing_invariant
    (g : P.weylGroup) (β γ : RootIndex) :
    P.pairing (rootActionTransport g β) (rootActionTransport g γ) =
      P.pairing β γ := by
  let pred : (q : P.Aut) → q ∈ P.weylGroup → Prop := fun q h ↦
    ∀ β γ, P.pairing (rootActionTransport ⟨q, h⟩ β)
      (rootActionTransport ⟨q, h⟩ γ) = P.pairing β γ
  have hpred : pred g.1 g.2 := by
    refine RootPairing.weylGroup.induction P (pred := pred) ?_ ?_ ?_ g.2
    · intro i β γ
      change P.pairing (P.reflectionPerm i β) (P.reflectionPerm i γ) =
        P.pairing β γ
      simpa only [P.reflectionPerm_self] using
        (P.pairing_reflectionPerm i (P.reflectionPerm i β) γ)
    · intro β γ
      simp
    · intro x y hx hy hxpred hypred β γ
      change P.pairing
        (rootActionTransport ⟨x * y, Subgroup.mul_mem P.weylGroup hx hy⟩ β)
        (rootActionTransport ⟨x * y, Subgroup.mul_mem P.weylGroup hx hy⟩ γ) = _
      rw [show (⟨x * y, Subgroup.mul_mem P.weylGroup hx hy⟩ : P.weylGroup) =
        (⟨x, hx⟩ : P.weylGroup) * ⟨y, hy⟩ by rfl, rootActionTransport_mul]
      simp only [Equiv.Perm.mul_apply]
      rw [hxpred]
      exact hypred _ _
  exact hpred β γ

theorem rootActionTransport_rootStarAction (g : P.weylGroup)
    (S : Finset RootIndex) :
    weylGroupRootStarAction g S = S.image (rootActionTransport g) := by
  rfl

theorem weylGroupRootStarAction_mul (g h : P.weylGroup) (S : Finset RootIndex) :
    weylGroupRootStarAction (g * h) S =
      weylGroupRootStarAction g (weylGroupRootStarAction h S) := by
  classical
  unfold weylGroupRootStarAction
  rw [P.weylGroupToPerm.map_mul]
  simp only [Finset.image_image]
  rfl

theorem rootStarReflection_eq_weylGroup_reflection
    (α : RootIndex) (S : Finset RootIndex) :
    rootStarReflection α S =
      weylGroupRootStarAction
        ⟨RootPairing.Equiv.reflection P α,
          RootPairing.reflection_mem_weylGroup P α⟩ S := by
  classical
  unfold rootStarReflection weylGroupRootStarAction
  apply congrArg (fun f : RootIndex → RootIndex => S.image f)
  funext β
  exact Finset.singleton_injective
    (rootStarReflection_singleton_weylGroup α β)

/-- Root-star reflection expressed through the exported Mathlib permutation
    hom.  This is the carrier-safe form used by downstream action bridges. -/
theorem rootStarReflection_eq_rootActionTransport_reflection
    (α : RootIndex) (S : Finset RootIndex) :
    rootStarReflection α S =
      S.image (rootActionTransport
        ⟨RootPairing.Equiv.reflection P α,
          RootPairing.reflection_mem_weylGroup P α⟩) := by
  exact rootStarReflection_eq_weylGroup_reflection α S

/-! These two named instances are the generator-level interface for a later
    carrier bridge from the Cartan Weyl subgroup.  Keeping them here avoids
    identifying the two carriers before the corresponding linear-equivalence
    theorem has been proved. -/
theorem shortWeylReflection_rootStarAction (S : Finset RootIndex) :
    rootStarReflection shortRoot S =
      weylGroupRootStarAction shortWeylReflection S := by
  exact rootStarReflection_eq_weylGroup_reflection shortRoot S

theorem longWeylReflection_rootStarAction (S : Finset RootIndex) :
    rootStarReflection longRoot S =
      weylGroupRootStarAction longWeylReflection S := by
  exact rootStarReflection_eq_weylGroup_reflection longRoot S

/-- The root action of a native reflection is the reflection of the
corresponding root in the ambient `RootPairing`.  This is the basic
carrier-alignment lemma used when transporting Coxeter calculations to the
root-index action. -/
@[simp] theorem rootPairing_reflection_apply_root (α β : RootIndex) :
    P.root (P.reflectionPerm α β) = P.reflection α (P.root β) := by
  exact P.root_reflectionPerm α β

theorem rootPairing_reflection_apply_root_formula (α β : RootIndex) :
    P.root (P.reflectionPerm α β) =
      P.root β - (P.pairing β α) • P.root α := by
  rw [rootPairing_reflection_apply_root]
  exact P.reflection_apply_root α β

theorem rootPairing_simpleProduct_apply_root (i : RootIndex) :
    P.root (P.weylGroupToPerm
        (shortWeylReflection * longWeylReflection) i) =
      P.reflection shortRoot (P.reflection longRoot (P.root i)) := by
  rw [← RootPairing.weylGroup_apply_root]
  rfl

noncomputable def canonicalRootStar :
    G2DoubleRootStar :=
  by
    classical
    exact G2DoubleRootStar.mk (Finset.univ : Finset RootIndex) rfl

@[simp] theorem canonicalRootStar_roots :
    canonicalRootStar.roots = (Finset.univ : Finset RootIndex) := rfl

theorem weylGroupRootStarAction_canonical (g : P.weylGroup) :
    weylGroupRootStarAction g canonicalRootStar.roots =
      canonicalRootStar.roots := by
  classical
  rw [canonicalRootStar_roots]
  ext r
  constructor
  · intro h
    exact Finset.mem_univ r
  · intro h
    obtain ⟨q, hq⟩ := (P.weylGroupToPerm g).surjective r
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq⟩

theorem g2Weyl_rootStar_invariant (g : P.weylGroup) :
    weylGroupRootStarAction g canonicalRootStar.roots =
      canonicalRootStar.roots :=
  weylGroupRootStarAction_canonical g

theorem rootActionTransport_canonicalRootStar (g : P.weylGroup) :
    canonicalRootStar.roots.image (rootActionTransport g) =
      canonicalRootStar.roots := by
  exact weylGroupRootStarAction_canonical g

theorem canonicalRootStar_card :
    canonicalRootStar.roots.card = 12 := by
  classical
  rw [canonicalRootStar_roots]
  exact rootIndex_card

theorem canonicalRootStar_reflection_invariant (α : RootIndex) :
    rootStarReflection α canonicalRootStar.roots = canonicalRootStar.roots := by
  classical
  rw [canonicalRootStar_roots, rootStarReflection_univ]

theorem rootStarReflection_canonical_eq_weylGroup_reflection
    (α : RootIndex) :
    rootStarReflection α canonicalRootStar.roots =
      weylGroupRootStarAction
        ⟨RootPairing.Equiv.reflection P α,
          RootPairing.reflection_mem_weylGroup P α⟩
        canonicalRootStar.roots := by
  rw [canonicalRootStar_reflection_invariant,
    weylGroupRootStarAction_canonical]

theorem rootStarReflection_long_on_short :
    rootStarReflection (nativeRootIndex nativeLongSimpleIndex)
        {nativeRootIndex nativeShortSimpleIndex} =
      {nativeRootIndex ⟨9, by decide, by decide⟩} := by
  classical
  simp [rootStarReflection, native_long_reflection_short]

theorem rootStarReflection_short_on_long :
    rootStarReflection (nativeRootIndex nativeShortSimpleIndex)
        {nativeRootIndex nativeLongSimpleIndex} =
      {nativeRootIndex ⟨11, by decide, by decide⟩} := by
  classical
  simp [rootStarReflection, native_short_reflection_long]

/-- A root reflection transported to the typed exhaustive root-star carrier. -/
noncomputable def reflectRootStar (α : RootIndex) (S : G2DoubleRootStar) :
    G2DoubleRootStar :=
  { roots := rootStarReflection α S.roots
    h_exhaustive := by
      rw [S.h_exhaustive, rootStarReflection_univ] }

@[simp] theorem reflectRootStar_roots (α : RootIndex) (S : G2DoubleRootStar) :
    (reflectRootStar α S).roots = rootStarReflection α S.roots := rfl

theorem reflectRootStar_exhaustive (α : RootIndex) (S : G2DoubleRootStar) :
    (reflectRootStar α S).roots = Finset.univ := by
  rw [reflectRootStar_roots, S.h_exhaustive, rootStarReflection_univ]

end InfoGeometry.Lie.CanonicalZornG2RootStarAction
