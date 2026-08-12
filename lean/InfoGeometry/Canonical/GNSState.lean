import Mathlib.Tactic
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Canonical.GNSState

open scoped BigOperators

open InfoGeometry.Canonical.CantorCuntzBasis

/-!
# Finite-Cylinder GNS State

This file replaces the abstract generated `CuntzAlgebra` socket with the
finite-cylinder substrate needed before a real GNS completion can be built.

The carrier is the finitely supported real vector space on finite binary
cylinder words.  The pre-inner product is the uniform KMS/Born cylinder
quadratic form

`⟪x,y⟫ = Σ_w x_w y_w 2^(-|w|)`.

This is not the completed GNS Hilbert space and it is not claimed to be
isomorphic to `ℓ²(List Bool, ℝ²)`.  Those analytic completion and
identification theorems remain explicit closure debt.

#### BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully
checked by the kernel.]

* `gnsPreInner_zero_left`
* `gnsPreInner_zero_right`
* `gnsCylinderWeight_nonneg`
* `gnsCylinderWeight_cons`
* `gnsPreInner_symm`
* `gnsPreInner_self_nonneg`
* `gnsPreInner_basis_self`
* `gnsPreInner_basis_ne`
* `gnsPreInner_basis_cons_self`
* `gnsPreInner_basis_false_true`
* `gnsPreInner_basis_true_false`
* `gnsPreInner_self_eq_zero_iff`
* `gnsPreInner_smul_left`
* `gnsPreInner_smul_right`
* `gnsNullQuotientEquiv`
* `gnsNullQuotientPreInner_self_eq_zero_iff`
* `gnsNullQuotientPreInner_smul_left`
* `gnsNullQuotientPreInner_smul_right`
* `gnsPrefix_injective`
* `gnsPreInner_prefix_self`
* `gnsPreInner_prefix`
* `gnsPreInner_prefix_false_true`
* `gnsPreInner_prefix_true_false`
* `gnsNullQuotientPreInner_scaled_prefix_self`
* `gnsNullQuotientPreInner_prefix`
* `gnsNullQuotientPreInner_scaled_prefix`
* `gnsNullQuotientPreInner_scaled_prefix_false_true`
* `gnsNullQuotientPreInner_scaled_prefix_true_false`
* `gnsNullQuotientPreInner_prefix_branch_sum_self`
* `gnsPreInner_basis_eq`
* `gnsNullQuotientPreInner_mk_basis_eq`
* `gnsPreInner_prefix_empty`
* `gnsNullQuotientPreInner_prefix_empty`
* `gnsScaledPrefixCompletion_not_surjective`
* `gnsScaledPrefixCompletion_rangeProjection_sum_ne_id`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* None.

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields,
witnesses, certificates, or renamed placeholders.]

* Prove the explicit unitary identification with the concrete Hilbert/Cantor
  boundary carrier.
* Replace the vacuum-containing Toeplitz prefix carrier by a genuine Cuntz
  boundary carrier before claiming a range-partition representation.
* Transport the prefix operators and phase-axis commutation through that
  completed representation.
-/

/-- Basis vector for a finite binary cylinder word. -/
@[rep_depth operator]
def cylinderBasis (w : List Bool) : (List Bool →₀ ℝ) :=
  Finsupp.single w 1

/-- Uniform binary GNS/KMS cylinder weight: `2^-|w|`. -/
@[rep_depth operator]
def gnsCylinderWeight (w : List Bool) : ℝ :=
  ((1 / 2 : ℝ) ^ w.length)

@[rep_depth operator]
theorem gnsCylinderWeight_nonneg (w : List Bool) :
    0 ≤ gnsCylinderWeight w := by
  unfold gnsCylinderWeight
  exact pow_nonneg (by norm_num) w.length

/-- Prefixing either binary branch halves the finite-cylinder weight. -/
@[rep_depth operator]
theorem gnsCylinderWeight_cons (b : Bool) (w : List Bool) :
    gnsCylinderWeight (b :: w) = (1 / 2 : ℝ) * gnsCylinderWeight w := by
  simp [gnsCylinderWeight, pow_succ, mul_comm]

/--
Uniform KMS/Born pre-inner product on finite cylinder vectors.

The support union is used only to make the finite sum manifest for both inputs.
-/
@[rep_depth operator]
def gnsPreInner (x y : (List Bool →₀ ℝ)) : ℝ :=
  Finset.sum (x.support ∪ y.support) (fun w => x w * y w * gnsCylinderWeight w)

@[simp, rep_depth operator]
theorem gnsPreInner_zero_left (x : (List Bool →₀ ℝ)) :
    gnsPreInner 0 x = 0 := by
  simp [gnsPreInner]

@[simp, rep_depth operator]
theorem gnsPreInner_zero_right (x : (List Bool →₀ ℝ)) :
    gnsPreInner x 0 = 0 := by
  simp [gnsPreInner]

/-- The finite-cylinder GNS pre-inner product is symmetric over `ℝ`. -/
@[rep_depth operator]
theorem gnsPreInner_symm (x y : (List Bool →₀ ℝ)) :
    gnsPreInner x y = gnsPreInner y x := by
  unfold gnsPreInner
  rw [Finset.union_comm]
  refine Finset.sum_congr rfl ?_
  intro w _
  ring

theorem gnsPreInner_smul_left
    (r : ℝ) (x y : (List Bool →₀ ℝ)) :
    gnsPreInner (r • x) y = r * gnsPreInner x y := by
  classical
  by_cases hr : r = 0
  · subst r
    simp [gnsPreInner]
  · unfold gnsPreInner
    rw [Finsupp.support_smul_eq hr]
    calc
      (∑ w ∈ x.support ∪ y.support,
          (r • x) w * y w * gnsCylinderWeight w) =
          ∑ w ∈ x.support ∪ y.support,
            r * (x w * y w * gnsCylinderWeight w) := by
              apply Finset.sum_congr rfl
              intro w hw
              simp [Finsupp.smul_apply, smul_eq_mul]
              ring
      _ = r * ∑ w ∈ x.support ∪ y.support,
            x w * y w * gnsCylinderWeight w := by
              rw [Finset.mul_sum]

theorem gnsPreInner_smul_right
    (r : ℝ) (x y : (List Bool →₀ ℝ)) :
    gnsPreInner x (r • y) = r * gnsPreInner x y := by
  classical
  by_cases hr : r = 0
  · subst r
    simp [gnsPreInner]
  · unfold gnsPreInner
    rw [Finsupp.support_smul_eq hr]
    calc
      (∑ w ∈ x.support ∪ y.support,
          x w * (r • y) w * gnsCylinderWeight w) =
          ∑ w ∈ x.support ∪ y.support,
            r * (x w * y w * gnsCylinderWeight w) := by
              apply Finset.sum_congr rfl
              intro w hw
              simp [Finsupp.smul_apply, smul_eq_mul]
              ring
      _ = r * ∑ w ∈ x.support ∪ y.support,
            x w * y w * gnsCylinderWeight w := by
              rw [Finset.mul_sum]

theorem gnsPreInner_add_left
    (x y z : (List Bool →₀ ℝ)) :
    gnsPreInner (x + y) z = gnsPreInner x z + gnsPreInner y z := by
  classical
  let S := x.support ∪ y.support ∪ z.support
  have hleft : (x + y).support ∪ z.support ⊆ S := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_left _ (Finsupp.support_add hw)
    · exact Finset.mem_union_right _ hw
  have hx : x.support ∪ z.support ⊆ S := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hw)
    · exact Finset.mem_union_right _ hw
  have hy : y.support ∪ z.support ⊆ S := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hw)
    · exact Finset.mem_union_right _ hw
  unfold gnsPreInner
  calc
    Finset.sum ((x + y).support ∪ z.support)
        (fun w => (x + y) w * z w * gnsCylinderWeight w) =
      Finset.sum S
        (fun w => (x + y) w * z w * gnsCylinderWeight w) := by
          refine (Finset.sum_subset
            (s₁ := (x + y).support ∪ z.support) (s₂ := S)
            (f := fun w => (x + y) w * z w * gnsCylinderWeight w)
            hleft ?_)
          intro w hw hnot
          have hzero : (x + y) w = 0 := by
            apply Finsupp.notMem_support_iff.mp
            intro hs
            exact hnot (Finset.mem_union_left _ hs)
          simp [hzero]
    _ = Finset.sum S
        (fun w => (x w * z w * gnsCylinderWeight w) +
          (y w * z w * gnsCylinderWeight w)) := by
          apply Finset.sum_congr rfl
          intro w hw
          simp only [Finsupp.add_apply]
          ring
    _ = Finset.sum S (fun w => x w * z w * gnsCylinderWeight w) +
          Finset.sum S (fun w => y w * z w * gnsCylinderWeight w) := by
          rw [Finset.sum_add_distrib]
    _ = gnsPreInner x z + gnsPreInner y z := by
          congr 1
          · refine (Finset.sum_subset
              (s₁ := x.support ∪ z.support) (s₂ := S)
              (f := fun w => x w * z w * gnsCylinderWeight w)
              hx ?_).symm
            intro w hw hnot
            have hzero : x w = 0 := by
              apply Finsupp.notMem_support_iff.mp
              intro hs
              exact hnot (Finset.mem_union_left _ hs)
            simp [hzero]
          · refine (Finset.sum_subset
              (s₁ := y.support ∪ z.support) (s₂ := S)
              (f := fun w => y w * z w * gnsCylinderWeight w)
              hy ?_).symm
            intro w hw hnot
            have hzero : y w = 0 := by
              apply Finsupp.notMem_support_iff.mp
              intro hs
              exact hnot (Finset.mem_union_left _ hs)
            simp [hzero]

theorem gnsPreInner_add_right
    (x y z : (List Bool →₀ ℝ)) :
    gnsPreInner x (y + z) = gnsPreInner x y + gnsPreInner x z := by
  calc
    gnsPreInner x (y + z) = gnsPreInner (y + z) x :=
      gnsPreInner_symm _ _
    _ = gnsPreInner y x + gnsPreInner z x :=
      gnsPreInner_add_left y z x
    _ = gnsPreInner x y + gnsPreInner x z := by
      rw [gnsPreInner_symm y x, gnsPreInner_symm z x]

/-- The finite-cylinder GNS quadratic form is nonnegative. -/
@[rep_depth operator]
theorem gnsPreInner_self_nonneg (x : (List Bool →₀ ℝ)) :
    0 ≤ gnsPreInner x x := by
  unfold gnsPreInner
  refine Finset.sum_nonneg ?_
  intro w _
  exact mul_nonneg (mul_self_nonneg (x w)) (gnsCylinderWeight_nonneg w)

theorem gnsCylinderWeight_pos (w : List Bool) :
    0 < gnsCylinderWeight w := by
  unfold gnsCylinderWeight
  exact pow_pos (by norm_num) w.length

theorem gnsPreInner_self_eq_zero_iff (x : (List Bool →₀ ℝ)) :
    gnsPreInner x x = 0 ↔ x = 0 := by
  classical
  unfold gnsPreInner
  rw [Finset.union_self]
  constructor
  · intro h
    apply Finsupp.ext
    intro w
    by_cases hw : w ∈ x.support
    · have hterm :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun u hu =>
          mul_nonneg (mul_self_nonneg (x u))
            (gnsCylinderWeight_nonneg u))).mp h w hw
      have hsq : (x w) ^ 2 = 0 := by
        simpa [pow_two] using (mul_eq_zero.mp hterm).resolve_right
          (ne_of_gt (gnsCylinderWeight_pos w))
      exact sq_eq_zero_iff.mp hsq
    · by_contra hne
      exact hw (Finsupp.mem_support_iff.mpr hne)
  · intro hx
    subst x
    simp

abbrev GNSCarrier := List Bool →₀ ℝ

def gnsNullSubmodule : Submodule ℝ GNSCarrier := ⊥

abbrev GNSNullQuotient := GNSCarrier ⧸ gnsNullSubmodule

theorem gnsNullSubmodule_eq_bot : gnsNullSubmodule = (⊥ : Submodule ℝ GNSCarrier) :=
  rfl

noncomputable def gnsNullQuotientEquiv :
    GNSNullQuotient ≃ₗ[ℝ] GNSCarrier :=
  gnsNullSubmodule.quotEquivOfEqBot gnsNullSubmodule_eq_bot

@[simp]
theorem gnsNullQuotientEquiv_apply_mk (x : GNSCarrier) :
    gnsNullQuotientEquiv (Submodule.Quotient.mk x) = x := by
  rfl

@[simp]
theorem gnsNullQuotientEquiv_symm_apply (x : GNSCarrier) :
    (gnsNullQuotientEquiv.symm x) = Submodule.Quotient.mk x := by
  rfl

theorem gnsPreInner_self_eq_zero_iff_mem_null (x : GNSCarrier) :
    gnsPreInner x x = 0 ↔ x ∈ gnsNullSubmodule := by
  rw [gnsNullSubmodule_eq_bot, Submodule.mem_bot]
  exact gnsPreInner_self_eq_zero_iff x

noncomputable def gnsNullQuotientPreInner
    (x y : GNSNullQuotient) : ℝ :=
  gnsPreInner (gnsNullQuotientEquiv x) (gnsNullQuotientEquiv y)

theorem gnsNullQuotientPreInner_symm
    (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner x y = gnsNullQuotientPreInner y x := by
  unfold gnsNullQuotientPreInner
  exact gnsPreInner_symm _ _

theorem gnsNullQuotientPreInner_add_left
    (x y z : GNSNullQuotient) :
    gnsNullQuotientPreInner (x + y) z =
      gnsNullQuotientPreInner x z + gnsNullQuotientPreInner y z := by
  unfold gnsNullQuotientPreInner
  rw [map_add]
  exact gnsPreInner_add_left _ _ _

theorem gnsNullQuotientPreInner_add_right
    (x y z : GNSNullQuotient) :
    gnsNullQuotientPreInner x (y + z) =
      gnsNullQuotientPreInner x y + gnsNullQuotientPreInner x z := by
  unfold gnsNullQuotientPreInner
  rw [map_add]
  exact gnsPreInner_add_right _ _ _

theorem gnsNullQuotientPreInner_self_nonneg (x : GNSNullQuotient) :
    0 ≤ gnsNullQuotientPreInner x x := by
  unfold gnsNullQuotientPreInner
  exact gnsPreInner_self_nonneg _

theorem gnsNullQuotientPreInner_self_eq_zero_iff
    (x : GNSNullQuotient) :
    gnsNullQuotientPreInner x x = 0 ↔ x = 0 := by
  unfold gnsNullQuotientPreInner
  constructor
  · intro h
    apply gnsNullQuotientEquiv.injective
    exact (gnsPreInner_self_eq_zero_iff
      (gnsNullQuotientEquiv x)).mp h
  · intro h
    subst x
    simp

noncomputable def gnsNullQuotientInnerProductCore :
    InnerProductSpace.Core ℝ GNSNullQuotient where
  inner := gnsNullQuotientPreInner
  conj_inner_symm := by
    intro x y
    simpa using gnsNullQuotientPreInner_symm y x
  re_inner_nonneg := by
    intro x
    simpa using gnsNullQuotientPreInner_self_nonneg x
  add_left := by
    intro x y z
    exact gnsNullQuotientPreInner_add_left x y z
  smul_left := by
    intro x y r
    unfold gnsNullQuotientPreInner
    rw [map_smul]
    exact gnsPreInner_smul_left r _ _
  definite := by
    intro x hx
    exact (gnsNullQuotientPreInner_self_eq_zero_iff x).mp hx

noncomputable instance gnsNullQuotientInnerProductCoreInst :
    InnerProductSpace.Core ℝ GNSNullQuotient :=
  gnsNullQuotientInnerProductCore

noncomputable instance gnsNullQuotientNormedAddCommGroup :
    NormedAddCommGroup GNSNullQuotient :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance gnsNullQuotientInnerProductSpace :
    InnerProductSpace ℝ GNSNullQuotient :=
  InnerProductSpace.ofCore gnsNullQuotientInnerProductCore.toCore

theorem gnsNullQuotientPreInner_smul_left
    (r : ℝ) (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner (r • x) y =
      r * gnsNullQuotientPreInner x y := by
  unfold gnsNullQuotientPreInner
  rw [map_smul]
  exact gnsPreInner_smul_left r _ _

theorem gnsNullQuotientPreInner_smul_right
    (r : ℝ) (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner x (r • y) =
      r * gnsNullQuotientPreInner x y := by
  unfold gnsNullQuotientPreInner
  rw [map_smul]
  exact gnsPreInner_smul_right r _ _

noncomputable def gnsPrefix (b : Bool) :
    GNSCarrier →ₗ[ℝ] GNSCarrier :=
  Finsupp.lmapDomain ℝ ℝ (fun w => b :: w)

@[simp]
theorem gnsPrefix_apply (b : Bool) (x : GNSCarrier) :
    gnsPrefix b x = Finsupp.mapDomain (fun w => b :: w) x :=
  rfl

theorem gnsPrefix_injective (b : Bool) :
    Function.Injective (gnsPrefix b) := by
  intro x y h
  change Finsupp.mapDomain (fun w => b :: w) x =
    Finsupp.mapDomain (fun w => b :: w) y at h
  exact Finsupp.mapDomain_injective
    (by
      intro u v huv
      cases huv
      rfl) h

theorem cylinderBasis_empty_not_mem_gnsPrefix_range (b : Bool) :
    cylinderBasis [] ∉ Set.range (gnsPrefix b) := by
  rintro ⟨x, hx⟩
  have hcoord := congrArg (fun z : GNSCarrier => z []) hx
  have hnot : [] ∉ Set.range (fun w : List Bool => b :: w) := by
    rintro ⟨w, hw⟩
    cases hw
  change (Finsupp.mapDomain (fun w : List Bool => b :: w) x) [] =
    cylinderBasis [] [] at hcoord
  rw [Finsupp.mapDomain_notin_range x [] hnot] at hcoord
  simpa [cylinderBasis] using hcoord

theorem gnsPrefix_support (b : Bool) (x : GNSCarrier) :
    (gnsPrefix b x).support = x.support.image (fun w => b :: w) := by
  classical
  change (Finsupp.mapDomain (fun w => b :: w) x).support = _
  exact Finsupp.mapDomain_support_of_injective
    (by
      intro u v huv
      cases huv
      rfl) x

theorem gnsPreInner_prefix_self (b : Bool) (x : GNSCarrier) :
    gnsPreInner (gnsPrefix b x) (gnsPrefix b x) =
      (1 / 2 : ℝ) * gnsPreInner x x := by
  classical
  unfold gnsPreInner
  rw [Finset.union_self, Finset.union_self, gnsPrefix_support]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hinj : Function.Injective (fun w : List Bool => b :: w) := by
      intro v w h
      cases h
      rfl
    rw [gnsPrefix_apply,
      Finsupp.mapDomain_apply hinj x u,
      gnsCylinderWeight_cons]
    ring
  · intro u hu v hv huv
    cases huv
    rfl

theorem gnsPreInner_prefix (b : Bool) (x y : GNSCarrier) :
    gnsPreInner (gnsPrefix b x) (gnsPrefix b y) =
      (1 / 2 : ℝ) * gnsPreInner x y := by
  classical
  unfold gnsPreInner
  rw [gnsPrefix_support, gnsPrefix_support]
  have hinj : Function.Injective (fun w : List Bool => b :: w) := by
    intro u v h
    cases h
    rfl
  have hunion :
      x.support.image (fun w => b :: w) ∪
          y.support.image (fun w => b :: w) =
        (x.support ∪ y.support).image (fun w => b :: w) := by
    rw [Finset.image_union]
  rw [hunion, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [gnsPrefix_apply, gnsPrefix_apply,
      Finsupp.mapDomain_apply hinj x u,
      Finsupp.mapDomain_apply hinj y u,
      gnsCylinderWeight_cons]
    ring
  · intro u hu v hv huv
    cases huv
    rfl

theorem gnsPreInner_prefix_false_true
    (x y : GNSCarrier) :
    gnsPreInner (gnsPrefix false x) (gnsPrefix true y) = 0 := by
  classical
  unfold gnsPreInner
  refine Finset.sum_eq_zero ?_
  intro w hw
  rw [gnsPrefix_apply, gnsPrefix_apply]
  by_cases hfalse : w ∈ Set.range (fun v : List Bool => false :: v)
  · obtain ⟨v, rfl⟩ := hfalse
    have hinj : Function.Injective (fun z : List Bool => false :: z) := by
      intro u v huv
      cases huv
      rfl
    rw [Finsupp.mapDomain_apply hinj x v]
    have hcross : false :: v ∉ Set.range (fun z : List Bool => true :: z) := by
      intro h
      obtain ⟨z, hz⟩ := h
      cases hz
    rw [Finsupp.mapDomain_notin_range y (false :: v) hcross]
    simp
  · rw [Finsupp.mapDomain_notin_range x w hfalse]
    simp

theorem gnsPreInner_prefix_empty (b : Bool) (x : GNSCarrier) :
    gnsPreInner (gnsPrefix b x) (cylinderBasis []) = 0 := by
  classical
  unfold gnsPreInner
  refine Finset.sum_eq_zero ?_
  intro w hw
  rw [gnsPrefix_apply]
  by_cases hprefix : w ∈ Set.range (fun v : List Bool => b :: v)
  · obtain ⟨v, rfl⟩ := hprefix
    have hinj : Function.Injective (fun z : List Bool => b :: z) := by
      intro u v huv
      cases huv
      rfl
    rw [Finsupp.mapDomain_apply hinj x v]
    simp [cylinderBasis]
  · rw [Finsupp.mapDomain_notin_range x w hprefix]
    simp

theorem gnsPreInner_prefix_true_false
    (x y : GNSCarrier) :
    gnsPreInner (gnsPrefix true x) (gnsPrefix false y) = 0 := by
  rw [gnsPreInner_symm]
  exact gnsPreInner_prefix_false_true y x

noncomputable def gnsNullQuotientPrefix (b : Bool) :
    GNSNullQuotient →ₗ[ℝ] GNSNullQuotient :=
  gnsNullQuotientEquiv.symm.toLinearMap.comp
    ((gnsPrefix b).comp gnsNullQuotientEquiv.toLinearMap)

theorem cylinderBasis_empty_class_not_mem_gnsNullQuotientPrefix_range (b : Bool) :
    gnsNullQuotientEquiv.symm (cylinderBasis []) ∉
      Set.range (gnsNullQuotientPrefix b) := by
  rintro ⟨x, hx⟩
  apply cylinderBasis_empty_not_mem_gnsPrefix_range b
  refine ⟨gnsNullQuotientEquiv x, ?_⟩
  have htransport := congrArg gnsNullQuotientEquiv hx
  simpa [gnsNullQuotientPrefix] using htransport

theorem gnsNullQuotientPrefix_injective (b : Bool) :
    Function.Injective (gnsNullQuotientPrefix b) := by
  intro x y h
  apply gnsNullQuotientEquiv.injective
  have h' := congrArg gnsNullQuotientEquiv h
  simpa [gnsNullQuotientPrefix, LinearMap.coe_comp] using
    (gnsPrefix_injective b h')

theorem gnsNullQuotientPreInner_prefix_self
    (b : Bool) (x : GNSNullQuotient) :
    gnsNullQuotientPreInner (gnsNullQuotientPrefix b x)
        (gnsNullQuotientPrefix b x) =
      (1 / 2 : ℝ) * gnsNullQuotientPreInner x x := by
  simp only [gnsNullQuotientPreInner, gnsNullQuotientPrefix,
    LinearMap.coe_comp, Function.comp_apply]
  exact gnsPreInner_prefix_self b (gnsNullQuotientEquiv x)

theorem gnsNullQuotientPreInner_prefix
    (b : Bool) (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner (gnsNullQuotientPrefix b x)
        (gnsNullQuotientPrefix b y) =
      (1 / 2 : ℝ) * gnsNullQuotientPreInner x y := by
  simp only [gnsNullQuotientPreInner, gnsNullQuotientPrefix,
    LinearMap.coe_comp, Function.comp_apply]
  exact gnsPreInner_prefix b
    (gnsNullQuotientEquiv x) (gnsNullQuotientEquiv y)

theorem gnsNullQuotientPreInner_prefix_false_true
    (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner (gnsNullQuotientPrefix false x)
        (gnsNullQuotientPrefix true y) = 0 := by
  simp only [gnsNullQuotientPreInner, gnsNullQuotientPrefix,
    LinearMap.coe_comp, Function.comp_apply]
  exact gnsPreInner_prefix_false_true
    (gnsNullQuotientEquiv x) (gnsNullQuotientEquiv y)

theorem gnsNullQuotientPreInner_prefix_true_false
    (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner (gnsNullQuotientPrefix true x)
        (gnsNullQuotientPrefix false y) = 0 := by
  simp only [gnsNullQuotientPreInner, gnsNullQuotientPrefix,
    LinearMap.coe_comp, Function.comp_apply]
  exact gnsPreInner_prefix_true_false
    (gnsNullQuotientEquiv x) (gnsNullQuotientEquiv y)

theorem gnsNullQuotientPreInner_prefix_empty
    (b : Bool) (x : GNSNullQuotient) :
    gnsNullQuotientPreInner (gnsNullQuotientPrefix b x)
        (gnsNullQuotientEquiv.symm (cylinderBasis [])) = 0 := by
  simp only [gnsNullQuotientPreInner, gnsNullQuotientPrefix,
    LinearMap.coe_comp, Function.comp_apply]
  exact gnsPreInner_prefix_empty b (gnsNullQuotientEquiv x)

theorem gnsNullQuotientPreInner_scaled_prefix_self
    (b : Bool) (x : GNSNullQuotient) :
    gnsNullQuotientPreInner
        ((Real.sqrt 2) • gnsNullQuotientPrefix b x)
        ((Real.sqrt 2) • gnsNullQuotientPrefix b x) =
      gnsNullQuotientPreInner x x := by
  rw [gnsNullQuotientPreInner_smul_left,
    gnsNullQuotientPreInner_smul_right,
    gnsNullQuotientPreInner_prefix_self]
  have hs : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
    rw [← sq]
    exact Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := by
    simp [pow_two, hs]
  ring_nf
  rw [hs2]
  ring

theorem gnsNullQuotientPreInner_scaled_prefix
    (b : Bool) (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner
        ((Real.sqrt 2) • gnsNullQuotientPrefix b x)
        ((Real.sqrt 2) • gnsNullQuotientPrefix b y) =
      gnsNullQuotientPreInner x y := by
  rw [gnsNullQuotientPreInner_smul_left,
    gnsNullQuotientPreInner_smul_right,
    gnsNullQuotientPreInner_prefix]
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := by
    exact Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hs]
  ring

noncomputable def gnsScaledPrefixLinearIsometry (b : Bool) :
    GNSNullQuotient →ₗᵢ[ℝ] GNSNullQuotient :=
  { toLinearMap := (Real.sqrt 2) • gnsNullQuotientPrefix b
    norm_map' := by
      intro x
      rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
      congr 1
      exact gnsNullQuotientPreInner_scaled_prefix_self b x }

noncomputable def gnsScaledPrefixCompletion (b : Bool) :
    UniformSpace.Completion GNSNullQuotient →L[ℝ]
      UniformSpace.Completion GNSNullQuotient :=
  (gnsScaledPrefixLinearIsometry b).toContinuousLinearMap.completion

theorem gnsScaledPrefixCompletion_isometry (b : Bool) :
    Isometry (gnsScaledPrefixCompletion b) := by
  exact (gnsScaledPrefixLinearIsometry b).isometry.completion_map

theorem gnsScaledPrefixCompletion_injective (b : Bool) :
    Function.Injective (gnsScaledPrefixCompletion b) := by
  exact (gnsScaledPrefixCompletion_isometry b).injective

@[simp]
theorem gnsScaledPrefixCompletion_coe (b : Bool) (x : GNSNullQuotient) :
    gnsScaledPrefixCompletion b (x : UniformSpace.Completion GNSNullQuotient) =
      ((Real.sqrt 2) • gnsNullQuotientPrefix b x : GNSNullQuotient) := by
  change UniformSpace.Completion.map
      (gnsScaledPrefixLinearIsometry b).toContinuousLinearMap
      (x : UniformSpace.Completion GNSNullQuotient) = _
  exact UniformSpace.Completion.map_coe
    (gnsScaledPrefixLinearIsometry b).isometry.uniformContinuous x

theorem gnsScaledPrefixCompletion_inner_coe_empty
    (b : Bool) (x : GNSNullQuotient) :
    @inner ℝ (UniformSpace.Completion GNSNullQuotient)
      _ (gnsScaledPrefixCompletion b
          (x : UniformSpace.Completion GNSNullQuotient))
        (gnsNullQuotientEquiv.symm (cylinderBasis []) :
          UniformSpace.Completion GNSNullQuotient) = 0 := by
  rw [gnsScaledPrefixCompletion_coe,
    UniformSpace.Completion.inner_coe]
  change gnsNullQuotientPreInner
      ((Real.sqrt 2) • gnsNullQuotientPrefix b x)
      (gnsNullQuotientEquiv.symm (cylinderBasis [])) = 0
  rw [gnsNullQuotientPreInner_smul_left,
    gnsNullQuotientPreInner_prefix_empty]
  simp

theorem gnsScaledPrefixCompletion_inner_empty
    (b : Bool) (x : UniformSpace.Completion GNSNullQuotient) :
    @inner ℝ (UniformSpace.Completion GNSNullQuotient)
      _ (gnsScaledPrefixCompletion b x)
        (gnsNullQuotientEquiv.symm (cylinderBasis []) :
          UniformSpace.Completion GNSNullQuotient) = 0 := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · have hmap : Continuous
        (fun z : UniformSpace.Completion GNSNullQuotient =>
          (gnsScaledPrefixCompletion b z,
            (gnsNullQuotientEquiv.symm (cylinderBasis []) :
              UniformSpace.Completion GNSNullQuotient))) := by
      exact (gnsScaledPrefixCompletion b).continuous.prodMk continuous_const
    have hcont : Continuous
        (fun z : UniformSpace.Completion GNSNullQuotient =>
          @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
            (gnsScaledPrefixCompletion b z)
            (gnsNullQuotientEquiv.symm (cylinderBasis []) :
              UniformSpace.Completion GNSNullQuotient)) :=
      UniformSpace.Completion.continuous_inner.comp hmap
    exact isClosed_singleton.preimage hcont
  · intro a
    exact gnsScaledPrefixCompletion_inner_coe_empty b a

theorem gnsScaledPrefixCompletion_adjoint_vacuum (b : Bool) :
    ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion b)
        (gnsNullQuotientEquiv.symm (cylinderBasis []) :
          UniformSpace.Completion GNSNullQuotient) = 0 := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  simpa using gnsScaledPrefixCompletion_inner_empty b x

theorem gnsScaledPrefixCompletion_rangeProjection_vacuum (b : Bool) :
    (gnsScaledPrefixCompletion b).comp
        (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion b))
        (gnsNullQuotientEquiv.symm (cylinderBasis []) :
          UniformSpace.Completion GNSNullQuotient) = 0 := by
  rw [ContinuousLinearMap.comp_apply,
    gnsScaledPrefixCompletion_adjoint_vacuum]
  simp

theorem gnsScaledPrefixCompletion_rangeProjection_sum_vacuum :
    ((gnsScaledPrefixCompletion false).comp
        (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion false)) +
      (gnsScaledPrefixCompletion true).comp
        (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion true)))
        (gnsNullQuotientEquiv.symm (cylinderBasis []) :
          UniformSpace.Completion GNSNullQuotient) = 0 := by
  rw [ContinuousLinearMap.add_apply,
    gnsScaledPrefixCompletion_rangeProjection_vacuum,
    gnsScaledPrefixCompletion_rangeProjection_vacuum]
  simp

theorem gnsScaledPrefixCompletion_vacuum_ne_zero :
    (gnsNullQuotientEquiv.symm (cylinderBasis []) :
      UniformSpace.Completion GNSNullQuotient) ≠ 0 := by
  intro hv
  have hone :
      @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
        (gnsNullQuotientEquiv.symm (cylinderBasis []) :
          UniformSpace.Completion GNSNullQuotient)
        (gnsNullQuotientEquiv.symm (cylinderBasis []) :
          UniformSpace.Completion GNSNullQuotient) = 1 := by
    rw [UniformSpace.Completion.inner_coe]
    change gnsNullQuotientPreInner
      (gnsNullQuotientEquiv.symm (cylinderBasis []))
      (gnsNullQuotientEquiv.symm (cylinderBasis [])) = 1
    change gnsPreInner (cylinderBasis []) (cylinderBasis []) = 1
    unfold gnsPreInner cylinderBasis
    rw [Finset.sum_eq_single []]
    · simp [gnsCylinderWeight]
    · intro v _ hvw
      simp [Finsupp.single_eq_of_ne hvw]
    · intro hmem
      simp at hmem
  rw [hv] at hone
  simp at hone

theorem gnsScaledPrefixCompletion_rangeProjection_sum_ne_id :
    (gnsScaledPrefixCompletion false).comp
        (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion false)) +
      (gnsScaledPrefixCompletion true).comp
        (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion true)) ≠
      ContinuousLinearMap.id ℝ (UniformSpace.Completion GNSNullQuotient) := by
  let vacuum : UniformSpace.Completion GNSNullQuotient :=
    (gnsNullQuotientEquiv.symm (cylinderBasis []) :
      UniformSpace.Completion GNSNullQuotient)
  intro h
  have hv := congrArg
    (fun F : UniformSpace.Completion GNSNullQuotient →L[ℝ]
      UniformSpace.Completion GNSNullQuotient => F vacuum) h
  have hvzero : (0 : UniformSpace.Completion GNSNullQuotient) = vacuum := by
    calc
      (0 : UniformSpace.Completion GNSNullQuotient) =
          ((gnsScaledPrefixCompletion false).comp
              (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion false)) +
            (gnsScaledPrefixCompletion true).comp
              (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion true)))
            vacuum :=
        gnsScaledPrefixCompletion_rangeProjection_sum_vacuum.symm
      _ = (ContinuousLinearMap.id ℝ
          (UniformSpace.Completion GNSNullQuotient)) vacuum := hv
      _ = vacuum := by simp
  exact gnsScaledPrefixCompletion_vacuum_ne_zero hvzero.symm

theorem gnsScaledPrefixCompletion_not_surjective (b : Bool) :
    ¬ Function.Surjective (gnsScaledPrefixCompletion b) := by
  let vacuum : UniformSpace.Completion GNSNullQuotient :=
    (gnsNullQuotientEquiv.symm (cylinderBasis []) :
      UniformSpace.Completion GNSNullQuotient)
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj vacuum
  have hzero :
      @inner ℝ (UniformSpace.Completion GNSNullQuotient) _ vacuum vacuum = 0 := by
    calc
      @inner ℝ (UniformSpace.Completion GNSNullQuotient) _ vacuum vacuum =
          @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
            (gnsScaledPrefixCompletion b x) vacuum := by rw [hx]
      _ = 0 := gnsScaledPrefixCompletion_inner_empty b x
  have hone :
      @inner ℝ (UniformSpace.Completion GNSNullQuotient) _ vacuum vacuum = 1 := by
    dsimp [vacuum]
    rw [UniformSpace.Completion.inner_coe]
    change gnsNullQuotientPreInner
      (gnsNullQuotientEquiv.symm (cylinderBasis []))
      (gnsNullQuotientEquiv.symm (cylinderBasis [])) = 1
    change gnsPreInner (cylinderBasis []) (cylinderBasis []) = 1
    unfold gnsPreInner cylinderBasis
    rw [Finset.sum_eq_single []]
    · simp [gnsCylinderWeight]
    · intro v _ hv
      simp [Finsupp.single_eq_of_ne hv]
    · intro hmem
      simp at hmem
  linarith

theorem gnsScaledPrefixCompletion_inner_coe_false_true
    (x y : GNSNullQuotient) :
    @inner ℝ (UniformSpace.Completion GNSNullQuotient)
      _ (gnsScaledPrefixCompletion false
          (x : UniformSpace.Completion GNSNullQuotient))
        (gnsScaledPrefixCompletion true
          (y : UniformSpace.Completion GNSNullQuotient)) = 0 := by
  simp [gnsScaledPrefixCompletion_coe, real_inner_smul_left,
    real_inner_smul_right]
  change gnsNullQuotientPreInner (gnsNullQuotientPrefix false x)
      (gnsNullQuotientPrefix true y) = 0
  exact gnsNullQuotientPreInner_prefix_false_true x y

theorem gnsScaledPrefixCompletion_inner_coe_true_false
    (x y : GNSNullQuotient) :
    @inner ℝ (UniformSpace.Completion GNSNullQuotient)
      _ (gnsScaledPrefixCompletion true
          (x : UniformSpace.Completion GNSNullQuotient))
        (gnsScaledPrefixCompletion false
          (y : UniformSpace.Completion GNSNullQuotient)) = 0 := by
  simp [gnsScaledPrefixCompletion_coe, real_inner_smul_left,
    real_inner_smul_right]
  change gnsNullQuotientPreInner (gnsNullQuotientPrefix true x)
      (gnsNullQuotientPrefix false y) = 0
  exact gnsNullQuotientPreInner_prefix_true_false x y

theorem gnsScaledPrefixCompletion_inner_false_true
    (x y : UniformSpace.Completion GNSNullQuotient) :
    @inner ℝ (UniformSpace.Completion GNSNullQuotient)
      _ (gnsScaledPrefixCompletion false x)
        (gnsScaledPrefixCompletion true y) = 0 := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · have hmap : Continuous (fun p : UniformSpace.Completion GNSNullQuotient ×
        UniformSpace.Completion GNSNullQuotient =>
        (gnsScaledPrefixCompletion false p.1,
          gnsScaledPrefixCompletion true p.2)) :=
      (gnsScaledPrefixCompletion false).continuous.comp continuous_fst |>.prodMk
        ((gnsScaledPrefixCompletion true).continuous.comp continuous_snd)
    have hcont : Continuous (fun p : UniformSpace.Completion GNSNullQuotient ×
        UniformSpace.Completion GNSNullQuotient =>
        @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
          (gnsScaledPrefixCompletion false p.1)
          (gnsScaledPrefixCompletion true p.2)) :=
      UniformSpace.Completion.continuous_inner.comp hmap
    exact isClosed_singleton.preimage hcont
  · intro a b
    exact gnsScaledPrefixCompletion_inner_coe_false_true a b

theorem gnsScaledPrefixCompletion_inner_true_false
    (x y : UniformSpace.Completion GNSNullQuotient) :
    @inner ℝ (UniformSpace.Completion GNSNullQuotient)
      _ (gnsScaledPrefixCompletion true x)
        (gnsScaledPrefixCompletion false y) = 0 := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · have hmap : Continuous (fun p : UniformSpace.Completion GNSNullQuotient ×
        UniformSpace.Completion GNSNullQuotient =>
        (gnsScaledPrefixCompletion true p.1,
          gnsScaledPrefixCompletion false p.2)) :=
      (gnsScaledPrefixCompletion true).continuous.comp continuous_fst |>.prodMk
        ((gnsScaledPrefixCompletion false).continuous.comp continuous_snd)
    have hcont : Continuous (fun p : UniformSpace.Completion GNSNullQuotient ×
        UniformSpace.Completion GNSNullQuotient =>
        @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
          (gnsScaledPrefixCompletion true p.1)
          (gnsScaledPrefixCompletion false p.2)) :=
      UniformSpace.Completion.continuous_inner.comp hmap
    exact isClosed_singleton.preimage hcont
  · intro a b
    exact gnsScaledPrefixCompletion_inner_coe_true_false a b

theorem gnsScaledPrefixCompletion_inner_same_branch
    (b : Bool) (x y : UniformSpace.Completion GNSNullQuotient) :
    @inner ℝ (UniformSpace.Completion GNSNullQuotient)
      _ (gnsScaledPrefixCompletion b x)
        (gnsScaledPrefixCompletion b y) =
      @inner ℝ (UniformSpace.Completion GNSNullQuotient) _ x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · have hmap : Continuous (fun p :
        UniformSpace.Completion GNSNullQuotient ×
          UniformSpace.Completion GNSNullQuotient =>
        (gnsScaledPrefixCompletion b p.1,
          gnsScaledPrefixCompletion b p.2)) :=
      (gnsScaledPrefixCompletion b).continuous.comp continuous_fst |>.prodMk
        ((gnsScaledPrefixCompletion b).continuous.comp continuous_snd)
    have hcont : Continuous (fun p :
        UniformSpace.Completion GNSNullQuotient ×
          UniformSpace.Completion GNSNullQuotient =>
        @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
          (gnsScaledPrefixCompletion b p.1)
          (gnsScaledPrefixCompletion b p.2) -
          @inner ℝ (UniformSpace.Completion GNSNullQuotient) _ p.1 p.2) := by
      exact UniformSpace.Completion.continuous_inner.comp hmap |>.sub
        UniformSpace.Completion.continuous_inner
    have hclosed : IsClosed ((fun p :
        UniformSpace.Completion GNSNullQuotient ×
          UniformSpace.Completion GNSNullQuotient =>
        @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
          (gnsScaledPrefixCompletion b p.1)
          (gnsScaledPrefixCompletion b p.2) -
          @inner ℝ (UniformSpace.Completion GNSNullQuotient) _ p.1 p.2) ⁻¹'
        ({0} : Set ℝ)) := isClosed_singleton.preimage hcont
    convert hclosed using 1
    ext p
    simp [sub_eq_zero]
  · intro a c
    simpa only [gnsScaledPrefixCompletion_coe,
      UniformSpace.Completion.inner_coe, gnsNullQuotientPreInner] using
      (gnsNullQuotientPreInner_scaled_prefix b a c)

theorem gnsScaledPrefixCompletion_adjoint_comp_self
    (b : Bool) :
    (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion b)).comp
        (gnsScaledPrefixCompletion b) =
      ContinuousLinearMap.id ℝ (UniformSpace.Completion GNSNullQuotient) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rw [gnsScaledPrefixCompletion_inner_same_branch]
  simp

theorem gnsScaledPrefixCompletion_adjoint_false_comp_true :
    (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion false)).comp
        (gnsScaledPrefixCompletion true) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  simp [gnsScaledPrefixCompletion_inner_true_false]

theorem gnsScaledPrefixCompletion_adjoint_true_comp_false :
    (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion true)).comp
        (gnsScaledPrefixCompletion false) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  simp [gnsScaledPrefixCompletion_inner_false_true]

/-! The two completed prefix maps satisfy the finite Cuntz--Toeplitz matrix
relation on the cylinder carrier. -/
theorem gnsScaledPrefixCompletion_adjoint_comp
    (b c : Bool) :
    (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion b)).comp
        (gnsScaledPrefixCompletion c) =
      if b = c then
        ContinuousLinearMap.id ℝ (UniformSpace.Completion GNSNullQuotient)
      else 0 := by
  cases b <;> cases c
  · simpa using gnsScaledPrefixCompletion_adjoint_comp_self false
  · simp [gnsScaledPrefixCompletion_adjoint_false_comp_true]
  · simp [gnsScaledPrefixCompletion_adjoint_true_comp_false]
  · simpa using gnsScaledPrefixCompletion_adjoint_comp_self true

theorem gnsScaledPrefixCompletion_adjoint_sum_comp :
    (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion false)).comp
        (gnsScaledPrefixCompletion false) +
      (ContinuousLinearMap.adjoint (gnsScaledPrefixCompletion true)).comp
        (gnsScaledPrefixCompletion true) =
      (2 : ℝ) • ContinuousLinearMap.id ℝ
        (UniformSpace.Completion GNSNullQuotient) := by
  rw [gnsScaledPrefixCompletion_adjoint_comp false false,
    gnsScaledPrefixCompletion_adjoint_comp true true]
  ext x
  change x + x = (2 : ℝ) • x
  exact (two_smul ℝ x).symm

theorem gnsNullQuotientPreInner_scaled_prefix_false_true
    (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner
        ((Real.sqrt 2) • gnsNullQuotientPrefix false x)
        ((Real.sqrt 2) • gnsNullQuotientPrefix true y) = 0 := by
  rw [gnsNullQuotientPreInner_smul_left,
    gnsNullQuotientPreInner_smul_right,
    gnsNullQuotientPreInner_prefix_false_true]
  ring

theorem gnsNullQuotientPreInner_scaled_prefix_true_false
    (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner
        ((Real.sqrt 2) • gnsNullQuotientPrefix true x)
        ((Real.sqrt 2) • gnsNullQuotientPrefix false y) = 0 := by
  rw [gnsNullQuotientPreInner_smul_left,
    gnsNullQuotientPreInner_smul_right,
    gnsNullQuotientPreInner_prefix_true_false]
  ring

theorem gnsNullQuotientPreInner_prefix_branch_sum_self
    (x : GNSNullQuotient) :
    gnsNullQuotientPreInner
        (gnsNullQuotientPrefix false x)
        (gnsNullQuotientPrefix false x) +
      gnsNullQuotientPreInner
        (gnsNullQuotientPrefix true x)
        (gnsNullQuotientPrefix true x) =
      gnsNullQuotientPreInner x x := by
  rw [gnsNullQuotientPreInner_prefix_self,
    gnsNullQuotientPreInner_prefix_self]
  ring

theorem gnsNullQuotientPreInner_prefix_branch_sum
    (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner
        (gnsNullQuotientPrefix false x)
        (gnsNullQuotientPrefix false y) +
      gnsNullQuotientPreInner
        (gnsNullQuotientPrefix true x)
        (gnsNullQuotientPrefix true y) =
      gnsNullQuotientPreInner x y := by
  rw [gnsNullQuotientPreInner_prefix,
    gnsNullQuotientPreInner_prefix]
  ring

theorem gnsNullQuotientPreInner_scaled_prefix_branch_sum
    (x y : GNSNullQuotient) :
    gnsNullQuotientPreInner
        ((Real.sqrt 2) • gnsNullQuotientPrefix false x)
        ((Real.sqrt 2) • gnsNullQuotientPrefix false y) +
      gnsNullQuotientPreInner
        ((Real.sqrt 2) • gnsNullQuotientPrefix true x)
        ((Real.sqrt 2) • gnsNullQuotientPrefix true y) =
      2 * gnsNullQuotientPreInner x y := by
  rw [gnsNullQuotientPreInner_scaled_prefix,
    gnsNullQuotientPreInner_scaled_prefix]
  ring

theorem gnsScaledPrefixCompletion_inner_branch_sum
    (x y : UniformSpace.Completion GNSNullQuotient) :
    @inner ℝ (UniformSpace.Completion GNSNullQuotient)
        _ (gnsScaledPrefixCompletion false x)
          (gnsScaledPrefixCompletion false y) +
      @inner ℝ (UniformSpace.Completion GNSNullQuotient)
        _ (gnsScaledPrefixCompletion true x)
          (gnsScaledPrefixCompletion true y) =
      2 * @inner ℝ (UniformSpace.Completion GNSNullQuotient)
        _ x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · have hleft : Continuous (fun p :
        UniformSpace.Completion GNSNullQuotient ×
          UniformSpace.Completion GNSNullQuotient =>
        @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
          (gnsScaledPrefixCompletion false p.1)
          (gnsScaledPrefixCompletion false p.2)) := by
      have hmap : Continuous (fun p :
          UniformSpace.Completion GNSNullQuotient ×
            UniformSpace.Completion GNSNullQuotient =>
          (gnsScaledPrefixCompletion false p.1,
            gnsScaledPrefixCompletion false p.2)) :=
        (gnsScaledPrefixCompletion false).continuous.comp continuous_fst |>.prodMk
          ((gnsScaledPrefixCompletion false).continuous.comp continuous_snd)
      exact UniformSpace.Completion.continuous_inner.comp hmap
    have hright : Continuous (fun p :
        UniformSpace.Completion GNSNullQuotient ×
          UniformSpace.Completion GNSNullQuotient =>
        @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
          (gnsScaledPrefixCompletion true p.1)
          (gnsScaledPrefixCompletion true p.2)) := by
      have hmap : Continuous (fun p :
          UniformSpace.Completion GNSNullQuotient ×
            UniformSpace.Completion GNSNullQuotient =>
          (gnsScaledPrefixCompletion true p.1,
            gnsScaledPrefixCompletion true p.2)) :=
        (gnsScaledPrefixCompletion true).continuous.comp continuous_fst |>.prodMk
          ((gnsScaledPrefixCompletion true).continuous.comp continuous_snd)
      exact UniformSpace.Completion.continuous_inner.comp hmap
    have hbase : Continuous (fun p :
        UniformSpace.Completion GNSNullQuotient ×
          UniformSpace.Completion GNSNullQuotient =>
        @inner ℝ (UniformSpace.Completion GNSNullQuotient) _ p.1 p.2) :=
      UniformSpace.Completion.continuous_inner
    have hcont : Continuous (fun p :
        UniformSpace.Completion GNSNullQuotient ×
          UniformSpace.Completion GNSNullQuotient =>
        (@inner ℝ (UniformSpace.Completion GNSNullQuotient) _
            (gnsScaledPrefixCompletion false p.1)
            (gnsScaledPrefixCompletion false p.2) +
          @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
            (gnsScaledPrefixCompletion true p.1)
            (gnsScaledPrefixCompletion true p.2)) -
          2 * @inner ℝ (UniformSpace.Completion GNSNullQuotient) _ p.1 p.2) := by
      exact (hleft.add hright).sub (continuous_const.mul hbase)
    have hclosed : IsClosed ((fun p :
        UniformSpace.Completion GNSNullQuotient ×
          UniformSpace.Completion GNSNullQuotient =>
        (@inner ℝ (UniformSpace.Completion GNSNullQuotient) _
            (gnsScaledPrefixCompletion false p.1)
            (gnsScaledPrefixCompletion false p.2) +
          @inner ℝ (UniformSpace.Completion GNSNullQuotient) _
            (gnsScaledPrefixCompletion true p.1)
            (gnsScaledPrefixCompletion true p.2)) -
          2 * @inner ℝ (UniformSpace.Completion GNSNullQuotient) _ p.1 p.2) ⁻¹'
        ({0} : Set ℝ)) := isClosed_singleton.preimage hcont
    convert hclosed using 1
    ext p
    simp [sub_eq_zero]
  · intro a b
    simp [gnsScaledPrefixCompletion_coe, real_inner_smul_left,
      real_inner_smul_right]
    have hs : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
      rw [← sq]
      exact Real.sq_sqrt (by norm_num)
    have hbranch :
        @inner ℝ GNSNullQuotient _
            (gnsNullQuotientPrefix false a)
            (gnsNullQuotientPrefix false b) +
          @inner ℝ GNSNullQuotient _
            (gnsNullQuotientPrefix true a)
            (gnsNullQuotientPrefix true b) =
        @inner ℝ GNSNullQuotient _ a b := by
      exact gnsNullQuotientPreInner_prefix_branch_sum a b
    calc
      Real.sqrt 2 *
            (Real.sqrt 2 *
              @inner ℝ GNSNullQuotient _
                (gnsNullQuotientPrefix false a)
                (gnsNullQuotientPrefix false b)) +
          Real.sqrt 2 *
            (Real.sqrt 2 *
              @inner ℝ GNSNullQuotient _
                (gnsNullQuotientPrefix true a)
                (gnsNullQuotientPrefix true b)) =
          (Real.sqrt 2 * Real.sqrt 2) *
            (@inner ℝ GNSNullQuotient _
                (gnsNullQuotientPrefix false a)
                (gnsNullQuotientPrefix false b) +
              @inner ℝ GNSNullQuotient _
                (gnsNullQuotientPrefix true a)
                (gnsNullQuotientPrefix true b)) := by ring
      _ = 2 * @inner ℝ GNSNullQuotient _ a b := by
        rw [hs, hbranch]

/-- A basis cylinder has squared norm equal to its KMS cylinder weight. -/
@[simp, rep_depth operator]
theorem gnsPreInner_basis_self (w : List Bool) :
    gnsPreInner (cylinderBasis w) (cylinderBasis w) = gnsCylinderWeight w := by
  unfold gnsPreInner cylinderBasis
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hvw
    simp [Finsupp.single_eq_of_ne hvw]
  · intro hw
    simp at hw

/-- Distinct basis cylinders are orthogonal. -/
@[rep_depth operator]
theorem gnsPreInner_basis_ne {u v : List Bool} (h : u ≠ v) :
    gnsPreInner (cylinderBasis u) (cylinderBasis v) = 0 := by
  unfold gnsPreInner cylinderBasis
  refine Finset.sum_eq_zero ?_
  intro w _
  by_cases hwu : w = u
  · subst w
    simp [Finsupp.single_eq_of_ne h]
  · simp [Finsupp.single_eq_of_ne hwu]

@[simp, rep_depth operator]
theorem gnsPreInner_basis_eq (u v : List Bool) :
    gnsPreInner (cylinderBasis u) (cylinderBasis v) =
      if u = v then gnsCylinderWeight u else 0 := by
  by_cases h : u = v
  · subst v
    simp
  · simp [h, gnsPreInner_basis_ne h]

@[simp, rep_depth operator]
theorem gnsNullQuotientPreInner_mk_basis_eq
    (u v : List Bool) :
    gnsNullQuotientPreInner
        (Submodule.Quotient.mk (cylinderBasis u))
        (Submodule.Quotient.mk (cylinderBasis v)) =
      if u = v then gnsCylinderWeight u else 0 := by
  unfold gnsNullQuotientPreInner
  simp [gnsPreInner_basis_eq]

/-- Prefixing the same branch halves the squared basis-cylinder norm. -/
@[rep_depth operator]
theorem gnsPreInner_basis_cons_self (b : Bool) (w : List Bool) :
    gnsPreInner (cylinderBasis (b :: w)) (cylinderBasis (b :: w)) =
      (1 / 2 : ℝ) * gnsPreInner (cylinderBasis w) (cylinderBasis w) := by
  simp [gnsCylinderWeight_cons]

/-- Opposite cylinder branches are orthogonal in the finite GNS pre-inner product. -/
@[rep_depth operator]
theorem gnsPreInner_basis_false_true (u v : List Bool) :
    gnsPreInner (cylinderBasis (false :: u)) (cylinderBasis (true :: v)) = 0 := by
  exact gnsPreInner_basis_ne (by intro h; cases h)

/-- Opposite cylinder branches are orthogonal in the finite GNS pre-inner product. -/
@[rep_depth operator]
theorem gnsPreInner_basis_true_false (u v : List Bool) :
    gnsPreInner (cylinderBasis (true :: u)) (cylinderBasis (false :: v)) = 0 := by
  exact gnsPreInner_basis_ne (by intro h; cases h)

end InfoGeometry.Canonical.GNSState
