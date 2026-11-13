/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SandwichLocalizationActions
import InfoGeometry.Algebra.CentralPowerLocalizationStar

/-!
# Swapped involution and invertible Cayley action

Star interchanges the two denominator indices and the two scalar actions.
The Cayley map is an additive equivalence preserving star. It is not asserted
to be linear over the localized centralizer: scalar conjugation is generally
nontrivial. No multiplication of arbitrary ambient fractions is introduced.
-/

namespace InfoGeometry.Algebra.SandwichLocalization

variable {B : Type*} [Ring B] [StarRing B]
variable (s : B) [hself : Fact (star s = s)]

/-- The native centralizer inherits the ambient involution. -/
instance centralizerStarRing : StarRing (Centralizer s) where
  star u := ⟨star (u : B), by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    have h := congrArg star (centralizer_commute s u).eq
    simpa only [star_mul, hself.out] using h.symm⟩
  star_involutive u := Subtype.ext (star_star (u : B))
  star_mul u v := Subtype.ext (star_mul (u : B) (v : B))
  star_add u v := Subtype.ext (star_add (u : B) (v : B))

@[simp] theorem coe_star_centralizer (u : Centralizer s) :
    ((star u : Centralizer s) : B) = star (u : B) := rfl

instance denominatorSelfAdjoint : Fact (star (denominator s) = denominator s) where
  out := Subtype.ext hself.out

/-- Star descends by swapping the two directed indices. -/
def starMap : Space s → Space s :=
  Quotient.lift (fun p : (Σ _ : ℕ × ℕ, B) => repr s p.1.2 (star p.2) p.1.1) (by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨m, hi, hj, he⟩
    apply Quotient.sound
    refine ⟨(m.2, m.1), ⟨hi.2, hi.1⟩, ⟨hj.2, hj.1⟩, ?_⟩
    change s ^ (m.2 - i.2) * star x * s ^ (m.1 - i.1) =
      s ^ (m.2 - j.2) * star y * s ^ (m.1 - j.1)
    simpa only [transition_apply, star_mul, star_pow, hself.out, mul_assoc] using
      congrArg star he)

instance spaceStar : Star (Space s) where
  star := starMap s

@[simp] theorem star_repr (k l : ℕ) (x : B) :
    star (repr s k x l) = repr s l (star x) k := rfl

instance spaceStarAddMonoid : StarAddMonoid (Space s) where
  star_involutive z := by
    obtain ⟨k, x, l, rfl⟩ := exists_repr s z
    simp only [star_repr, star_star]
  star_add z w := by
    obtain ⟨k, x, l, rfl⟩ := exists_repr s z
    obtain ⟨k', y, l', rfl⟩ := exists_repr s w
    simp only [repr_add, star_repr, star_add, star_mul, star_pow, hself.out, mul_assoc]

/-- The ambient embedding preserves its additive involution. -/
@[simp] theorem star_of (x : B) : star (of s x) = of s (star x) := rfl

/-- Star exchanges left multiplication with right multiplication by the adjoint. -/
theorem star_left_smul (q : Scalars s) (z : Space s) :
    star (q • z) = MulOpposite.op (star q) • star z := by
  obtain ⟨a, u, rfl⟩ := CentralPowerLocalization.exists_repr (denominator s) q
  obtain ⟨k, x, l, rfl⟩ := exists_repr s z
  simp only [left_smul_repr, right_smul_repr, CentralPowerLocalization.star_repr,
    star_repr, coe_star_centralizer, star_mul]

/-- The opposite exchange law follows on every ambient numerator. -/
theorem star_right_smul (q : Scalars s) (z : Space s) :
    star (MulOpposite.op q • z) = star q • star z := by
  obtain ⟨a, u, rfl⟩ := CentralPowerLocalization.exists_repr (denominator s) q
  obtain ⟨k, x, l, rfl⟩ := exists_repr s z
  simp only [left_smul_repr, right_smul_repr, CentralPowerLocalization.star_repr,
    star_repr, coe_star_centralizer, star_mul]

theorem commute_star_right (a : B) (ha : Commute s a) : Commute s (star a) := by
  have h := congrArg star ha.eq
  simpa only [star_mul, hself.out] using h.symm

private theorem sandwich_norm_cancel (a d x : B) (had : a * d = s ^ 2)
    (k l : ℕ) :
    repr s (k + 1 + 1) (a * (d * x * a) * d) (l + 1 + 1) = repr s k x l := by
  have hnum : a * (d * x * a) * d = s ^ 2 * x * s ^ 2 := by
    calc
      _ = (a * d) * x * (a * d) := by noncomm_ring
      _ = _ := by rw [had]
  rw [hnum]
  simpa only [Nat.add_assoc] using repr_bond s k l 2 2 x

/-- The Cayley numerator determines an actual additive equivalence. Both inverse
laws are proved from the ordered polynomial norm identities. -/
noncomputable def cayleyEquiv (a : B) (ha : Commute s a)
    (hleft : star a * a = s ^ 2) (hright : a * star a = s ^ 2) :
    Space s ≃+ Space s where
  toFun := sandwich s 1 1 a (star a) ha (commute_star_right s a ha)
  invFun := sandwich s 1 1 (star a) a (commute_star_right s a ha) ha
  left_inv z := by
    obtain ⟨k, x, l, rfl⟩ := exists_repr s z
    simp only [sandwich_repr]
    exact sandwich_norm_cancel s (star a) a x hleft k l
  right_inv z := by
    obtain ⟨k, x, l, rfl⟩ := exists_repr s z
    simp only [sandwich_repr]
    exact sandwich_norm_cancel s a (star a) x hright k l
  map_add' := (sandwich s 1 1 a (star a) ha (commute_star_right s a ha)).map_add

@[simp] theorem cayleyEquiv_repr (a : B) (ha : Commute s a)
    (hleft : star a * a = s ^ 2) (hright : a * star a = s ^ 2)
    (k l : ℕ) (x : B) :
    cayleyEquiv s a ha hleft hright (repr s k x l) =
      repr s (k + 1) (a * x * star a) (l + 1) := rfl

/-- Cayley dressing preserves star on the whole ambient additive localization. -/
theorem cayleyEquiv_star (a : B) (ha : Commute s a)
    (hleft : star a * a = s ^ 2) (hright : a * star a = s ^ 2) (z : Space s) :
    star (cayleyEquiv s a ha hleft hright z) =
      cayleyEquiv s a ha hleft hright (star z) := by
  obtain ⟨k, x, l, rfl⟩ := exists_repr s z
  simp only [cayleyEquiv_repr, star_repr, star_mul, star_star, mul_assoc]

/-- In particular the actual self-adjoint subspace is preserved. -/
theorem cayleyEquiv_selfAdjoint (a : B) (ha : Commute s a)
    (hleft : star a * a = s ^ 2) (hright : a * star a = s ^ 2)
    (z : Space s) (hz : star z = z) :
    star (cayleyEquiv s a ha hleft hright z) = cayleyEquiv s a ha hleft hright z := by
  rw [cayleyEquiv_star, hz]

/-- The scalar numerator lies in the actual denominator centralizer. -/
def scalarNumerator (a : B) (ha : Commute s a) : Centralizer s :=
  ⟨a, by intro x hx; rcases Set.mem_singleton_iff.mp hx with rfl; exact ha.eq⟩

/-- The existing native Ore construction supplies the unitary scalar. -/
theorem cayley_scalar_unitary (a : B) (ha : Commute s a)
    (hleft : star a * a = s ^ 2) (hright : a * star a = s ^ 2) :
    let u := CentralPowerLocalization.cayley (denominator s) (scalarNumerator s a ha)
    star u * u = 1 ∧ u * star u = 1 := by
  apply CentralPowerLocalization.cayley_unitary
  · exact Subtype.ext hleft
  · exact Subtype.ext hright

/-- The additive equivalence is exactly the two-sided action of the internal
unitary scalar, not a multiplication of arbitrary ambient fractions. -/
theorem cayleyEquiv_eq_scalar_action (a : B) (ha : Commute s a)
    (hleft : star a * a = s ^ 2) (hright : a * star a = s ^ 2) (z : Space s) :
    let u := CentralPowerLocalization.cayley (denominator s) (scalarNumerator s a ha)
    cayleyEquiv s a ha hleft hright z = u • (MulOpposite.op (star u) • z) := by
  obtain ⟨k, x, l, rfl⟩ := exists_repr s z
  dsimp only [CentralPowerLocalization.cayley]
  simp only [cayleyEquiv_repr, CentralPowerLocalization.star_repr,
    left_smul_repr, right_smul_repr, coe_star_centralizer]
  rfl

end InfoGeometry.Algebra.SandwichLocalization
