/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CentralPowerLocalization

/-!
# Additive and integer-module universal property of central localization

The genuine Ore carrier is the direct limit of multiplication by `s` on the
underlying additive groups. The bonding maps are not claimed to be ring
homomorphisms. The ring product is separately supplied by the convolution law
`repr_mul`, which adds stage indices and multiplies ordered numerators.
-/

namespace InfoGeometry.Algebra.CentralPowerLocalization

variable {B : Type*} [Ring B]
variable (s : B) [Fact (∀ x : B, Commute s x)]

/-- The additive bonding map for a stage displacement. -/
def transition (n : ℕ) : B →+ B where
  toFun x := s ^ n * x
  map_zero' := mul_zero _
  map_add' x y := mul_add _ x y

omit [Fact (∀ x : B, Commute s x)] in
/-- Zero displacement is the identity. -/
theorem transition_zero : transition s 0 = AddMonoidHom.id B := by
  ext x
  change s ^ 0 * x = x
  rw [pow_zero, one_mul]

omit [Fact (∀ x : B, Commute s x)] in
/-- Stage displacements compose by addition. -/
theorem transition_comp (n m : ℕ) :
    (transition s m).comp (transition s n) = transition s (n + m) := by
  ext x
  change s ^ m * (s ^ n * x) = s ^ (n + m) * x
  rw [← mul_assoc, ← pow_add, Nat.add_comm]

/-- The canonical additive cocone map from stage `k`. -/
def stage (k : ℕ) : B →+ Away s where
  toFun := repr s k
  map_zero' := repr_zero_numerator s k
  map_add' := repr_add_same s k

/-- The stage maps commute with all bonding maps. -/
theorem stage_transition (k n : ℕ) :
    (stage s (k + n)).comp (transition s n) = stage s k := by
  ext x
  exact (repr_bond s k n x).symm

/-- The same cocone is a cocone of native integer modules. -/
def stageLinearMap (k : ℕ) : B →ₗ[ℤ] Away s :=
  (stage s k).toIntLinearMap

omit [Fact (∀ x : B, Commute s x)] in
/-- Multiplication by the denominator preserves the ring unit exactly in
the trivial case `s=1`; thus these additive bonds are not ring bonds in general. -/
theorem bonding_preserves_one_iff : transition s 1 1 = 1 ↔ s = 1 := by
  change s ^ 1 * 1 = 1 ↔ s = 1
  simp only [pow_one, mul_one]

variable {F : Type*} [AddCommGroup F]

/-- A compatible additive cocone assigns equal values to equal Ore
representatives. This is the descent step, proved from eventual equality. -/
theorem cocone_value_eq (f : ℕ → B →+ F)
    (hf : ∀ k n x, f (k + n) (s ^ n * x) = f k x)
    {k l : ℕ} {x y : B} (h : repr s k x = repr s l y) :
    f k x = f l y := by
  obtain ⟨m, hk, hl, hxy⟩ := (repr_eq_iff_common_stage s k l x y).mp h
  calc
    f k x = f m (s ^ (m - k) * x) := by
      simpa only [Nat.add_sub_of_le hk] using (hf k (m - k) x).symm
    _ = f m (s ^ (m - l) * y) := congrArg (f m) hxy
    _ = f l y := by
      simpa only [Nat.add_sub_of_le hl] using hf l (m - l) y

/-- Evaluate any chosen representative. Compatibility, proved separately,
makes the value independent of the choice. -/
noncomputable def descFun (f : ℕ → B →+ F) (q : Away s) : F :=
  f (exists_repr s q).choose (exists_repr s q).choose_spec.choose

/-- The descended function has exactly the prescribed value at each stage. -/
theorem descFun_repr (f : ℕ → B →+ F)
    (hf : ∀ k n x, f (k + n) (s ^ n * x) = f k x)
    (k : ℕ) (x : B) : descFun s f (repr s k x) = f k x := by
  unfold descFun
  exact cocone_value_eq s f hf (exists_repr s (repr s k x)).choose_spec.choose_spec

/-- The universal map of the additive direct limit is constructed, rather
than stored as a field of an assumed cocone completion. -/
noncomputable def additiveDesc (f : ℕ → B →+ F)
    (hf : ∀ k n x, f (k + n) (s ^ n * x) = f k x) : Away s →+ F where
  toFun := descFun s f
  map_zero' := by
    rw [← repr_zero_numerator s 0, descFun_repr s f hf]
    exact map_zero (f 0)
  map_add' q r := by
    obtain ⟨k, x, rfl⟩ := exists_repr s q
    obtain ⟨l, y, rfl⟩ := exists_repr s r
    rw [repr_add, descFun_repr s f hf, descFun_repr s f hf,
      descFun_repr s f hf, map_add, hf k l x]
    congr 1
    simpa only [Nat.add_comm l k] using hf l k y

/-- Computation rule for the constructed additive universal map. -/
@[simp] theorem additiveDesc_repr (f : ℕ → B →+ F)
    (hf : ∀ k n x, f (k + n) (s ^ n * x) = f k x)
    (k : ℕ) (x : B) : additiveDesc s f hf (repr s k x) = f k x :=
  descFun_repr s f hf k x

/-- The additive universal map is unique. -/
theorem additiveDesc_unique (f : ℕ → B →+ F)
    (hf : ∀ k n x, f (k + n) (s ^ n * x) = f k x)
    (g : Away s →+ F) (hg : ∀ k x, g (repr s k x) = f k x) :
    g = additiveDesc s f hf := by
  ext q
  obtain ⟨k, x, rfl⟩ := exists_repr s q
  rw [hg, additiveDesc_repr]

/-- The universal property of the additive filtered colimit, on the
constructed native Ore quotient. -/
theorem existsUnique_additiveDesc (f : ℕ → B →+ F)
    (hf : ∀ k n x, f (k + n) (s ^ n * x) = f k x) :
    ∃! g : Away s →+ F, ∀ k x, g (repr s k x) = f k x := by
  refine ⟨additiveDesc s f hf, additiveDesc_repr s f hf, ?_⟩
  intro g hg
  exact additiveDesc_unique s f hf g hg

/-- The universal map on native integer modules. -/
noncomputable def moduleDesc (f : ℕ → B →ₗ[ℤ] F)
    (hf : ∀ k n x, f (k + n) (s ^ n * x) = f k x) : Away s →ₗ[ℤ] F :=
  (additiveDesc s (fun k => (f k).toAddMonoidHom) hf).toIntLinearMap

/-- Native integer-module computation rule. -/
@[simp] theorem moduleDesc_repr (f : ℕ → B →ₗ[ℤ] F)
    (hf : ∀ k n x, f (k + n) (s ^ n * x) = f k x)
    (k : ℕ) (x : B) : moduleDesc s f hf (repr s k x) = f k x :=
  additiveDesc_repr s (fun k => (f k).toAddMonoidHom) hf k x

/-- The integer-module colimit universal property follows on the same
carrier, with its ordered convolution ring multiplication retained. -/
theorem existsUnique_moduleDesc (f : ℕ → B →ₗ[ℤ] F)
    (hf : ∀ k n x, f (k + n) (s ^ n * x) = f k x) :
    ∃! g : Away s →ₗ[ℤ] F, ∀ k x, g (repr s k x) = f k x := by
  refine ⟨moduleDesc s f hf, moduleDesc_repr s f hf, ?_⟩
  intro g hg
  ext q
  obtain ⟨k, x, rfl⟩ := exists_repr s q
  rw [hg, moduleDesc_repr]

end InfoGeometry.Algebra.CentralPowerLocalization
