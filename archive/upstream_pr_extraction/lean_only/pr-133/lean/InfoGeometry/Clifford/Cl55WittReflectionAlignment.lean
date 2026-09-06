import InfoGeometry.Clifford.Cl55WittReflectionGeneratedSubgroup

namespace InfoGeometry.Clifford.Clifford55

/-!
# Reflection alignment for the split Witt quadratic form

These lemmas are the local constructive step used in a
Cartan--Dieudonne induction.  They do not assert generation of the whole
orthogonal group.
-/

theorem quadraticReflectionIsometry_mem_subgroup
    (v : V55) (hv : Q55 v ≠ 0) :
    orthogonalGroup55FromIsometry (quadraticReflectionIsometry v hv) ∈
      quadraticReflectionSubgroup := by
  exact quadraticReflectionElement_mem_subgroup v hv

theorem quadraticReflection_smul
    (c : ℝ) (hc : c ≠ 0) (v : V55) (hv : Q55 v ≠ 0) :
    quadraticReflection (c • v)
        (by
          rw [QuadraticMap.map_smul]
          simpa [pow_two] using mul_ne_zero (mul_ne_zero hc hc) hv) =
      quadraticReflection v hv := by
  apply LinearEquiv.ext
  intro x
  rw [quadraticReflection_apply, quadraticReflection_apply,
    QuadraticMap.polar_smul_right, QuadraticMap.map_smul]
  simp only [smul_eq_mul, smul_smul]
  congr 1
  field_simp [hc, hv]

theorem exists_normalized_scalar
    (v : V55) (hv : Q55 v ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧
      (Q55 (c • v) = 1 ∨ Q55 (c • v) = -1) := by
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · let a : ℝ := -Q55 v
    have ha : 0 < a := by
      dsimp [a]
      linarith
    have hsq : (Real.sqrt a) ^ 2 = a :=
      Real.sq_sqrt (le_of_lt ha)
    have hsqrt : Real.sqrt a ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 ha)
    refine ⟨(Real.sqrt a)⁻¹, inv_ne_zero hsqrt, Or.inr ?_⟩
    rw [QuadraticMap.map_smul]
    simp only [smul_eq_mul]
    field_simp [hsqrt]
    dsimp [a] at hsq ⊢
    nlinarith
  · let a : ℝ := Q55 v
    have ha : 0 < a := by
      dsimp [a]
      exact hpos
    have hsq : (Real.sqrt a) ^ 2 = a :=
      Real.sq_sqrt (le_of_lt ha)
    have hsqrt : Real.sqrt a ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 ha)
    refine ⟨(Real.sqrt a)⁻¹, inv_ne_zero hsqrt, Or.inl ?_⟩
    rw [QuadraticMap.map_smul]
    simp only [smul_eq_mul]
    field_simp [hsqrt]
    dsimp [a] at hsq ⊢
    nlinarith

theorem quadraticReflection_mem_subgroup
    (v : V55) (hv : Q55 v ≠ 0) :
    orthogonalGroup55FromIsometry (quadraticReflectionIsometry v hv) ∈
      quadraticReflectionSubgroup := by
  rcases exists_normalized_scalar v hv with ⟨c, hc, hnorm⟩
  have hcv : Q55 (c • v) ≠ 0 := by
    rcases hnorm with hnorm | hnorm
    · rw [hnorm]
      norm_num
    · rw [hnorm]
      norm_num
  have heq :
      orthogonalGroup55FromIsometry (quadraticReflectionIsometry (c • v) hcv) =
        orthogonalGroup55FromIsometry (quadraticReflectionIsometry v hv) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change quadraticReflection (c • v) hcv x =
      quadraticReflection v hv x
    simpa using congrArg (fun f => f x)
      (quadraticReflection_smul c hc v hv)
  rw [← heq]
  exact quadraticReflectionIsometry_mem_subgroup (c • v) hcv

noncomputable def quadraticIdentityIsometry : Q55.IsometryEquiv Q55 :=
  QuadraticMap.IsometryEquiv.mk (LinearEquiv.refl ℝ V55) (by
    intro x
    rfl)

theorem quadraticReflection_sub_apply_of_equal_Q
    (x y : V55) (hxy : Q55 x = Q55 y)
    (hu : Q55 (y - x) ≠ 0) :
    quadraticReflection (y - x) hu y = x := by
  rw [quadraticReflection_apply]
  have hpolar :
      QuadraticMap.polar (⇑Q55) y (y - x) = Q55 (y - x) := by
    calc
      QuadraticMap.polar (⇑Q55) y (y - x) =
          QuadraticMap.polar (⇑Q55) y y -
            QuadraticMap.polar (⇑Q55) y x :=
        QuadraticMap.polar_sub_right Q55 y y x
      _ = 2 * Q55 y - QuadraticMap.polar (⇑Q55) y x := by
        rw [QuadraticMap.polar_self]
        norm_num [smul_eq_mul]
      _ = Q55 y + Q55 x - QuadraticMap.polar (⇑Q55) y x := by
        rw [hxy]
        ring
      _ = Q55 y + Q55 (-x) +
          QuadraticMap.polar (⇑Q55) y (-x) := by
        rw [QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
        ring
      _ = Q55 (y + (-x)) :=
        (QuadraticMap.map_add (⇑Q55) y (-x)).symm
      _ = Q55 (y - x) := by rw [sub_eq_add_neg]
  rw [hpolar, div_self hu]
  module

theorem quadraticReflection_add_apply_of_equal_Q
    (x y : V55) (hxy : Q55 x = Q55 y)
    (hu : Q55 (y + x) ≠ 0) :
    quadraticReflection (y + x) hu y = -x := by
  rw [quadraticReflection_apply]
  have hpolar :
      QuadraticMap.polar (⇑Q55) y (y + x) = Q55 (y + x) := by
    calc
      QuadraticMap.polar (⇑Q55) y (y + x) =
          QuadraticMap.polar (⇑Q55) y y +
            QuadraticMap.polar (⇑Q55) y x :=
        QuadraticMap.polar_add_right Q55 y y x
      _ = 2 * Q55 y + QuadraticMap.polar (⇑Q55) y x := by
        rw [QuadraticMap.polar_self]
        norm_num [smul_eq_mul]
      _ = Q55 y + Q55 x + QuadraticMap.polar (⇑Q55) y x := by
        rw [hxy]
        ring
      _ = Q55 (y + x) :=
        (QuadraticMap.map_add (⇑Q55) y x).symm
  rw [hpolar, div_self hu]
  module

theorem quadraticReflection_self_apply_neg
    (x : V55) (hx : Q55 x ≠ 0) :
    quadraticReflection x hx (-x) = x := by
  rw [quadraticReflection_apply, QuadraticMap.polar_neg_left,
    QuadraticMap.polar_self]
  rw [two_smul]
  field_simp [hx]
  module

theorem quadraticReflection_add_norm_of_sub_isotropic
    (x y : V55) (hxy : Q55 x = Q55 y)
    (hy : Q55 y ≠ 0) (hsub : Q55 (y - x) = 0) :
    Q55 (y + x) ≠ 0 := by
  intro hsum
  have hfour : Q55 (y + x) + Q55 (y - x) = 4 * Q55 y := by
    have hplus : Q55 (y + x) =
        Q55 y + Q55 x + QuadraticMap.polar (⇑Q55) y x :=
      QuadraticMap.map_add (⇑Q55) y x
    have hminus : Q55 (y - x) =
        Q55 y + Q55 x - QuadraticMap.polar (⇑Q55) y x := by
      rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q55),
        QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
      abel
    rw [hplus, hminus]
    rw [hxy]
    ring
  rw [hsum, hsub] at hfour
  exact hy (by linarith)

theorem quadraticReflection_alignment
    (x y : V55) (hxy : Q55 x = Q55 y)
    (hy : Q55 y ≠ 0) :
    ∃ r₁ r₂ : Q55.IsometryEquiv Q55, r₁ (r₂ y) = x := by
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨quadraticIdentityIsometry, quadraticIdentityIsometry, rfl⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q55 x ≠ 0 := by
      simpa using hy
    refine ⟨quadraticReflectionIsometry x hx, quadraticIdentityIsometry, ?_⟩
    change quadraticReflection x hx (-x) = x
    simpa using quadraticReflection_self_apply_neg x hx
  by_cases hsub : Q55 (y - x) ≠ 0
  · refine ⟨quadraticIdentityIsometry,
      quadraticReflectionIsometry (y - x) hsub, ?_⟩
    simpa using quadraticReflection_sub_apply_of_equal_Q x y hxy hsub
  · have hsub_zero : Q55 (y - x) = 0 := by
      exact not_ne_iff.mp hsub
    have hadd : Q55 (y + x) ≠ 0 :=
      quadraticReflection_add_norm_of_sub_isotropic x y hxy hy hsub_zero
    have hx : Q55 x ≠ 0 := by
      rw [hxy]
      exact hy
    refine ⟨quadraticReflectionIsometry x hx,
      quadraticReflectionIsometry (y + x) hadd, ?_⟩
    change quadraticReflection x hx
      (quadraticReflection (y + x) hadd y) = x
    rw [quadraticReflection_add_apply_of_equal_Q x y hxy hadd]
    exact quadraticReflection_self_apply_neg x hx

theorem quadraticReflection_alignment_fixing_orthogonal
    (z x y : V55) (hxy : Q55 x = Q55 y)
    (hy : Q55 y ≠ 0)
    (hzx : QuadraticMap.polar (⇑Q55) z x = 0)
    (hzy : QuadraticMap.polar (⇑Q55) z y = 0) :
    ∃ r₁ r₂ : Q55.IsometryEquiv Q55,
      r₁ (r₂ y) = x ∧ r₁ z = z ∧ r₂ z = z := by
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨quadraticIdentityIsometry, quadraticIdentityIsometry, rfl, rfl, rfl⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q55 x ≠ 0 := by
      simpa using hy
    refine ⟨quadraticReflectionIsometry x hx, quadraticIdentityIsometry, ?_, ?_, ?_⟩
    · change quadraticReflection x hx (-x) = x
      simpa using quadraticReflection_self_apply_neg x hx
    · exact quadraticReflection_apply_of_polar_eq_zero x z hx hzx
    · rfl
  by_cases hsub : Q55 (y - x) ≠ 0
  · have hpolar_sub : QuadraticMap.polar (⇑Q55) z (y - x) = 0 := by
      rw [QuadraticMap.polar_sub_right]
      rw [hzy, hzx]
      simp
    refine ⟨quadraticIdentityIsometry,
      quadraticReflectionIsometry (y - x) hsub, ?_, ?_, ?_⟩
    · simpa using quadraticReflection_sub_apply_of_equal_Q x y hxy hsub
    · rfl
    · exact quadraticReflection_apply_of_polar_eq_zero (y - x) z hsub hpolar_sub
  · have hsub_zero : Q55 (y - x) = 0 := by
      exact not_ne_iff.mp hsub
    have hadd : Q55 (y + x) ≠ 0 :=
      quadraticReflection_add_norm_of_sub_isotropic x y hxy hy hsub_zero
    have hpolar_add : QuadraticMap.polar (⇑Q55) z (y + x) = 0 := by
      rw [QuadraticMap.polar_add_right]
      rw [hzy, hzx]
      simp
    have hx : Q55 x ≠ 0 := by
      rw [hxy]
      exact hy
    refine ⟨quadraticReflectionIsometry x hx,
      quadraticReflectionIsometry (y + x) hadd, ?_, ?_, ?_⟩
    · change quadraticReflection x hx
        (quadraticReflection (y + x) hadd y) = x
      rw [quadraticReflection_add_apply_of_equal_Q x y hxy hadd]
      exact quadraticReflection_self_apply_neg x hx
    · exact quadraticReflection_apply_of_polar_eq_zero x z hx hzx
    · exact quadraticReflection_apply_of_polar_eq_zero (y + x) z hadd hpolar_add

theorem quadraticReflectionSubgroup_shell_transitive_fixing_orthogonal
    (z x y : V55) (hxy : Q55 x = Q55 y)
    (hy : Q55 y ≠ 0)
    (hzx : QuadraticMap.polar (⇑Q55) z x = 0)
    (hzy : QuadraticMap.polar (⇑Q55) z y = 0) :
    ∃ r₁ r₂ : orthogonalGroup55,
      r₁ ∈ quadraticReflectionSubgroup ∧
      r₂ ∈ quadraticReflectionSubgroup ∧
      r₁.1 z = z ∧ r₂.1 z = z ∧
      r₁.1 (r₂.1 y) = x := by
  let identity : orthogonalGroup55 :=
    orthogonalGroup55FromIsometry quadraticIdentityIsometry
  have hidentity : identity ∈ quadraticReflectionSubgroup :=
    Subgroup.one_mem _
  have hidentity_apply (w : V55) : identity.1 w = w := by
    rfl
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨identity, identity, hidentity, hidentity,
      hidentity_apply z, hidentity_apply z, by
        rw [hidentity_apply, hidentity_apply]⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q55 x ≠ 0 := by simpa using hy
    let reflection : orthogonalGroup55 :=
      quadraticReflectionElement x hx
    have hreflection : reflection ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup x hx
    refine ⟨reflection, identity, hreflection, hidentity, ?_,
      hidentity_apply z, ?_⟩
    · change quadraticReflection x hx z = z
      exact quadraticReflection_apply_of_polar_eq_zero x z hx hzx
    · change quadraticReflection x hx (identity.1 (-x)) = x
      rw [hidentity_apply]
      exact quadraticReflection_self_apply_neg x hx
  by_cases hsub : Q55 (y - x) ≠ 0
  · have hpolar_sub : QuadraticMap.polar (⇑Q55) z (y - x) = 0 := by
      rw [QuadraticMap.polar_sub_right, hzy, hzx]
      simp
    let reflection : orthogonalGroup55 :=
      quadraticReflectionElement (y - x) hsub
    have hreflection : reflection ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup (y - x) hsub
    refine ⟨identity, reflection, hidentity, hreflection,
      hidentity_apply z, ?_, ?_⟩
    · change quadraticReflection (y - x) hsub z = z
      exact quadraticReflection_apply_of_polar_eq_zero (y - x) z hsub hpolar_sub
    · change identity.1 (quadraticReflection (y - x) hsub y) = x
      rw [hidentity_apply]
      exact quadraticReflection_sub_apply_of_equal_Q x y hxy hsub
  · have hsub_zero : Q55 (y - x) = 0 := not_ne_iff.mp hsub
    have hadd : Q55 (y + x) ≠ 0 :=
      quadraticReflection_add_norm_of_sub_isotropic x y hxy hy hsub_zero
    have hpolar_add : QuadraticMap.polar (⇑Q55) z (y + x) = 0 := by
      rw [QuadraticMap.polar_add_right, hzy, hzx]
      simp
    have hx : Q55 x ≠ 0 := by
      rw [hxy]
      exact hy
    let reflectionX : orthogonalGroup55 :=
      quadraticReflectionElement x hx
    let reflectionAdd : orthogonalGroup55 :=
      quadraticReflectionElement (y + x) hadd
    have hreflectionX : reflectionX ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup x hx
    have hreflectionAdd : reflectionAdd ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup (y + x) hadd
    refine ⟨reflectionX, reflectionAdd, hreflectionX, hreflectionAdd,
      ?_, ?_, ?_⟩
    · change quadraticReflection x hx z = z
      exact quadraticReflection_apply_of_polar_eq_zero x z hx hzx
    · change quadraticReflection (y + x) hadd z = z
      exact quadraticReflection_apply_of_polar_eq_zero (y + x) z hadd hpolar_add
    · change quadraticReflection x hx
        (quadraticReflection (y + x) hadd y) = x
      rw [quadraticReflection_add_apply_of_equal_Q x y hxy hadd]
      exact quadraticReflection_self_apply_neg x hx

theorem quadraticReflectionSubgroup_shell_transitive_fixing_set
    (S : Set V55) (x y : V55) (hxy : Q55 x = Q55 y)
    (hy : Q55 y ≠ 0)
    (hxS : ∀ z ∈ S, QuadraticMap.polar (⇑Q55) z x = 0)
    (hyS : ∀ z ∈ S, QuadraticMap.polar (⇑Q55) z y = 0) :
    ∃ r₁ r₂ : orthogonalGroup55,
      r₁ ∈ quadraticReflectionSubgroup ∧
      r₂ ∈ quadraticReflectionSubgroup ∧
      (∀ z ∈ S, r₁.1 z = z) ∧
      (∀ z ∈ S, r₂.1 z = z) ∧
      r₁.1 (r₂.1 y) = x := by
  let identity : orthogonalGroup55 :=
    orthogonalGroup55FromIsometry quadraticIdentityIsometry
  have hidentity : identity ∈ quadraticReflectionSubgroup :=
    Subgroup.one_mem _
  have hidentity_apply (w : V55) : identity.1 w = w := by
    rfl
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨identity, identity, hidentity, hidentity,
      (fun z _ => hidentity_apply z),
      (fun z _ => hidentity_apply z), by
        rw [hidentity_apply, hidentity_apply]⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q55 x ≠ 0 := by simpa using hy
    let reflection : orthogonalGroup55 :=
      quadraticReflectionElement x hx
    have hreflection : reflection ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup x hx
    refine ⟨reflection, identity, hreflection, hidentity, ?_,
      (fun z _ => hidentity_apply z), ?_⟩
    · intro z hz
      change quadraticReflection x hx z = z
      exact quadraticReflection_apply_of_polar_eq_zero x z hx (hxS z hz)
    · change quadraticReflection x hx (identity.1 (-x)) = x
      rw [hidentity_apply]
      exact quadraticReflection_self_apply_neg x hx
  by_cases hsub : Q55 (y - x) ≠ 0
  · have hpolar_sub : ∀ z ∈ S,
        QuadraticMap.polar (⇑Q55) z (y - x) = 0 := by
      intro z hz
      rw [QuadraticMap.polar_sub_right, hyS z hz, hxS z hz]
      simp
    let reflection : orthogonalGroup55 :=
      quadraticReflectionElement (y - x) hsub
    have hreflection : reflection ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup (y - x) hsub
    refine ⟨identity, reflection, hidentity, hreflection,
      (fun z _ => hidentity_apply z), ?_, ?_⟩
    · intro z hz
      change quadraticReflection (y - x) hsub z = z
      exact quadraticReflection_apply_of_polar_eq_zero
        (y - x) z hsub (hpolar_sub z hz)
    · change identity.1 (quadraticReflection (y - x) hsub y) = x
      rw [hidentity_apply]
      exact quadraticReflection_sub_apply_of_equal_Q x y hxy hsub
  · have hsub_zero : Q55 (y - x) = 0 := not_ne_iff.mp hsub
    have hadd : Q55 (y + x) ≠ 0 :=
      quadraticReflection_add_norm_of_sub_isotropic x y hxy hy hsub_zero
    have hpolar_add : ∀ z ∈ S,
        QuadraticMap.polar (⇑Q55) z (y + x) = 0 := by
      intro z hz
      rw [QuadraticMap.polar_add_right, hyS z hz, hxS z hz]
      simp
    have hx : Q55 x ≠ 0 := by
      rw [hxy]
      exact hy
    let reflectionX : orthogonalGroup55 :=
      quadraticReflectionElement x hx
    let reflectionAdd : orthogonalGroup55 :=
      quadraticReflectionElement (y + x) hadd
    have hreflectionX : reflectionX ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup x hx
    have hreflectionAdd : reflectionAdd ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup (y + x) hadd
    refine ⟨reflectionX, reflectionAdd, hreflectionX, hreflectionAdd,
      ?_, ?_, ?_⟩
    · intro z hz
      change quadraticReflection x hx z = z
      exact quadraticReflection_apply_of_polar_eq_zero x z hx (hxS z hz)
    · intro z hz
      change quadraticReflection (y + x) hadd z = z
      exact quadraticReflection_apply_of_polar_eq_zero
        (y + x) z hadd (hpolar_add z hz)
    · change quadraticReflection x hx
        (quadraticReflection (y + x) hadd y) = x
      rw [quadraticReflection_add_apply_of_equal_Q x y hxy hadd]
      exact quadraticReflection_self_apply_neg x hx

theorem quadraticReflectionSubgroup_shell_transitive
    (x y : V55) (hxy : Q55 x = Q55 y)
    (hy : Q55 y ≠ 0) :
    ∃ r₁ r₂ : orthogonalGroup55,
      r₁ ∈ quadraticReflectionSubgroup ∧
      r₂ ∈ quadraticReflectionSubgroup ∧
      r₁.1 (r₂.1 y) = x := by
  let identity : orthogonalGroup55 :=
    orthogonalGroup55FromIsometry quadraticIdentityIsometry
  have hidentity : identity ∈ quadraticReflectionSubgroup := by
    change identity ∈ quadraticReflectionSubgroup
    exact Subgroup.one_mem _
  have hidentity_apply (z : V55) : identity.1 z = z := by
    rfl
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨identity, identity, hidentity, hidentity, by
      rw [hidentity_apply, hidentity_apply]⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q55 x ≠ 0 := by
      simpa using hy
    let reflection : orthogonalGroup55 :=
      quadraticReflectionElement x hx
    have hreflection : reflection ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup x hx
    refine ⟨reflection, identity, hreflection, hidentity, ?_⟩
    change quadraticReflection x hx (identity.1 (-x)) = x
    rw [hidentity_apply]
    exact quadraticReflection_self_apply_neg x hx
  by_cases hsub : Q55 (y - x) ≠ 0
  · let reflection : orthogonalGroup55 :=
      quadraticReflectionElement (y - x) hsub
    have hreflection : reflection ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup (y - x) hsub
    refine ⟨identity, reflection, hidentity, hreflection, ?_⟩
    change identity.1 (quadraticReflection (y - x) hsub y) = x
    rw [hidentity_apply]
    exact quadraticReflection_sub_apply_of_equal_Q x y hxy hsub
  · have hsub_zero : Q55 (y - x) = 0 := by
      exact not_ne_iff.mp hsub
    have hadd : Q55 (y + x) ≠ 0 :=
      quadraticReflection_add_norm_of_sub_isotropic x y hxy hy hsub_zero
    have hx : Q55 x ≠ 0 := by
      rw [hxy]
      exact hy
    let reflectionX : orthogonalGroup55 :=
      quadraticReflectionElement x hx
    let reflectionAdd : orthogonalGroup55 :=
      quadraticReflectionElement (y + x) hadd
    have hreflectionX : reflectionX ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup x hx
    have hreflectionAdd : reflectionAdd ∈ quadraticReflectionSubgroup :=
      quadraticReflectionElement_mem_subgroup (y + x) hadd
    refine ⟨reflectionX, reflectionAdd, hreflectionX, hreflectionAdd, ?_⟩
    change quadraticReflection x hx
      (quadraticReflection (y + x) hadd y) = x
    rw [quadraticReflection_add_apply_of_equal_Q x y hxy hadd]
    exact quadraticReflection_self_apply_neg x hx

end InfoGeometry.Clifford.Clifford55
