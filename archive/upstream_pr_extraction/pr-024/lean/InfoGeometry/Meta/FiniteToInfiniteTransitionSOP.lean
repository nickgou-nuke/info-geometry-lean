import InfoGeometry.Meta.InductiveInvariantPacket

/-!
# InfoGeometry.Meta.FiniteToInfiniteTransitionSOP

Modified finite-to-infinite transition SOP, in theorem form.

This module records only what the finite algebraic induction proves:

* a finite chain of star-preserving bonding maps transports the local
  supergraded closure packet to its image;
* a scalar/readout invariant that is stable under each finite bonding map is
  stable along every finite chain;
* equality of readouts is stable along every finite chain when both readouts are
  individually stable.

It deliberately does not construct a direct limit, a completion, a von Neumann
algebra, a Fuglede--Kadison determinant, a Type II/III factor, or a Virasoro
central-charge theorem.  Those require separate owner interfaces and proofs.
-/

namespace InfoGeometry.Meta.FiniteToInfiniteTransitionSOP

open InfoGeometry.Meta.InductiveInvariantPacket

namespace StarRingHom

variable {A : Type*} [Ring A] [StarRing A]

/--
A scalar/readout invariant stable under each one-step bonding map is stable along
any finite bonding chain.

This is the theorem-level form of the normalized-trace/logdet stabilization SOP:
once the local theorem `readout (bond n x) = readout x` is proved for each
finite bond, all finite iterates are automatic.  No limit object is claimed.
-/
theorem readout_stable_along_finite_chain
    {R : Type*} (readout : A → R) (φ : Nat → StarRingHom A A)
    (hstable : ∀ n x, readout (φ n x) = readout x)
    (n k : Nat) (x : A) :
    readout (StarRingHom.chain φ n k x) = readout x := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [StarRingHom.chain_succ_apply]
      rw [hstable]
      exact ih

/--
Two scalar/readout functions that are each stable under the finite bonds preserve
their equality along every finite chain.

This is the safe finite replacement for informal statements such as “the ratio
survives the inductive limit”.  What is proved here is exactly finite-chain
stability.
-/
theorem readout_eq_stable_along_finite_chain
    {R : Type*} (left right : A → R) (φ : Nat → StarRingHom A A)
    (hleft : ∀ n x, left (φ n x) = left x)
    (hright : ∀ n x, right (φ n x) = right x)
    {x : A} (hxy : left x = right x) (n k : Nat) :
    left (StarRingHom.chain φ n k x) =
      right (StarRingHom.chain φ n k x) := by
  rw [readout_stable_along_finite_chain left φ hleft n k x]
  rw [readout_stable_along_finite_chain right φ hright n k x]
  exact hxy

/--
A predicate invariant under every one-step finite bond is invariant under every
finite bonding chain.

This is the exact finite-stage induction rule for positivity, invertibility,
local-domain membership, cylinder-sector membership, or similar algebraic
predicates, once the one-step theorem is proved in the owner file.
-/
theorem predicate_stable_along_finite_chain
    (P : A → Prop) (φ : Nat → StarRingHom A A)
    (hstable : ∀ n x, P x → P (φ n x))
    (n k : Nat) {x : A} (hx : P x) :
    P (StarRingHom.chain φ n k x) := by
  induction k with
  | zero =>
      exact hx
  | succ k ih =>
      rw [StarRingHom.chain_succ_apply]
      exact hstable (n + k) (StarRingHom.chain φ n k x) ih

/--
A binary relation invariant under every one-step finite bond is invariant under
every finite bonding chain.

Use this for finite-stage compatibility relations, image-local commutation
relations, or paired readout relations.  It does not upgrade image-local facts to
global target facts.
-/
theorem relation_stable_along_finite_chain
    (Rel : A → A → Prop) (φ : Nat → StarRingHom A A)
    (hstable : ∀ n x y, Rel x y → Rel (φ n x) (φ n y))
    (n k : Nat) {x y : A} (hxy : Rel x y) :
    Rel (StarRingHom.chain φ n k x) (StarRingHom.chain φ n k y) := by
  induction k with
  | zero =>
      exact hxy
  | succ k ih =>
      rw [StarRingHom.chain_succ_apply]
      rw [StarRingHom.chain_succ_apply]
      exact hstable (n + k)
        (StarRingHom.chain φ n k x)
        (StarRingHom.chain φ n k y) ih

end StarRingHom

namespace SupergradedClosureAt

variable {A R : Type*} [Ring A] [StarRing A]

/--
Modified SOP application: finite closure transport plus finite readout
stabilization.

If a local closure packet is present at the source stage and a scalar/readout is
stable under each finite bonding map, then after any finite number of bondings
both facts hold at the transported image: closure is image-local, and the readout
has exactly the original value.
-/
theorem finite_chain_closure_and_readout
    (I : InfoGeometry.Meta.InductiveInvariantPacket.SupergradedClosureAt A)
    (readout : A → R) (φ : Nat → StarRingHom A A)
    (hstable : ∀ n x, readout (φ n x) = readout x)
    (n k : Nat) :
    InfoGeometry.Meta.InductiveInvariantPacket.SupergradedClosureAt.ImageClosure
      I (StarRingHom.chain φ n k) ∧
      readout (StarRingHom.chain φ n k I.C) = readout I.C := by
  exact ⟨InfoGeometry.Meta.InductiveInvariantPacket.SupergradedClosureAt.chain_image_closure I φ n k,
    StarRingHom.readout_stable_along_finite_chain readout φ hstable n k I.C⟩

end SupergradedClosureAt

end InfoGeometry.Meta.FiniteToInfiniteTransitionSOP
