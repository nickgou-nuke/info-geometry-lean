import InfoGeometry.Clifford.RealQuadraticReflectionConjugation

namespace InfoGeometry.Clifford

/-!
# Generic finite spanning-family Cartan--Dieudonné factorization

This theorem uses the explicit orthogonal anisotropic spanning-family
hypotheses needed by the finite induction.  It does not claim the general
nondegenerate Cartan--Dieudonné theorem without separately constructing such
a family.
-/

theorem realQuadraticReflectionSubgroup_shell_transitive_fixing_set
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (S : Set V) (x y : V)
    (hxy : Q x = Q y) (hy : Q y ≠ 0)
    (hxS : ∀ z ∈ S, QuadraticMap.polar (⇑Q) z x = 0)
    (hyS : ∀ z ∈ S, QuadraticMap.polar (⇑Q) z y = 0) :
    ∃ r₁ r₂ : Q.IsometryEquiv Q,
      r₁ ∈ realQuadraticReflectionSubgroup Q ∧
      r₂ ∈ realQuadraticReflectionSubgroup Q ∧
      (∀ z ∈ S, r₁ z = z) ∧
      (∀ z ∈ S, r₂ z = z) ∧
      r₁ (r₂ y) = x := by
  let identity : Q.IsometryEquiv Q := realQuadraticIdentityIsometry Q
  have hidentity : identity ∈ realQuadraticReflectionSubgroup Q :=
    Subgroup.one_mem _
  have hidentity_apply (w : V) : identity w = w := by
    rfl
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨identity, identity, hidentity, hidentity,
      (fun z _ => hidentity_apply z),
      (fun z _ => hidentity_apply z), by
        rw [hidentity_apply, hidentity_apply]⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q x ≠ 0 := by simpa using hy
    let reflection := realQuadraticReflectionIsometry Q x hx
    have hreflection : reflection ∈ realQuadraticReflectionSubgroup Q :=
      realQuadraticReflectionIsometry_mem_subgroup Q x hx
    refine ⟨reflection, identity, hreflection, hidentity, ?_,
      (fun z _ => hidentity_apply z), ?_⟩
    · intro z hz
      change realQuadraticReflection Q x hx z = z
      exact realQuadraticReflection_apply_of_polar_eq_zero
        Q x z hx (hxS z hz)
    · change realQuadraticReflection Q x hx (identity (-x)) = x
      rw [hidentity_apply]
      exact realQuadraticReflection_self_apply_neg Q x hx
  by_cases hsub : Q (y - x) ≠ 0
  · have hpolar_sub : ∀ z ∈ S,
        QuadraticMap.polar (⇑Q) z (y - x) = 0 := by
      intro z hz
      rw [QuadraticMap.polar_sub_right, hyS z hz, hxS z hz]
      simp
    let reflection := realQuadraticReflectionIsometry Q (y - x) hsub
    have hreflection : reflection ∈ realQuadraticReflectionSubgroup Q :=
      realQuadraticReflectionIsometry_mem_subgroup Q (y - x) hsub
    refine ⟨identity, reflection, hidentity, hreflection,
      (fun z _ => hidentity_apply z), ?_, ?_⟩
    · intro z hz
      change realQuadraticReflection Q (y - x) hsub z = z
      exact realQuadraticReflection_apply_of_polar_eq_zero
        Q (y - x) z hsub (hpolar_sub z hz)
    · change identity (realQuadraticReflection Q (y - x) hsub y) = x
      rw [hidentity_apply]
      exact realQuadraticReflection_sub_apply_of_equal_Q Q x y hxy hsub
  · have hsub_zero : Q (y - x) = 0 := not_ne_iff.mp hsub
    have hadd : Q (y + x) ≠ 0 :=
      realQuadraticReflection_add_norm_of_sub_isotropic Q x y hxy hy hsub_zero
    have hpolar_add : ∀ z ∈ S,
        QuadraticMap.polar (⇑Q) z (y + x) = 0 := by
      intro z hz
      rw [QuadraticMap.polar_add_right, hyS z hz, hxS z hz]
      simp
    have hx : Q x ≠ 0 := by
      rw [hxy]
      exact hy
    let reflectionX := realQuadraticReflectionIsometry Q x hx
    let reflectionAdd := realQuadraticReflectionIsometry Q (y + x) hadd
    have hreflectionX : reflectionX ∈ realQuadraticReflectionSubgroup Q :=
      realQuadraticReflectionIsometry_mem_subgroup Q x hx
    have hreflectionAdd : reflectionAdd ∈ realQuadraticReflectionSubgroup Q :=
      realQuadraticReflectionIsometry_mem_subgroup Q (y + x) hadd
    refine ⟨reflectionX, reflectionAdd, hreflectionX, hreflectionAdd,
      ?_, ?_, ?_⟩
    · intro z hz
      change realQuadraticReflection Q x hx z = z
      exact realQuadraticReflection_apply_of_polar_eq_zero
        Q x z hx (hxS z hz)
    · intro z hz
      change realQuadraticReflection Q (y + x) hadd z = z
      exact realQuadraticReflection_apply_of_polar_eq_zero
        Q (y + x) z hadd (hpolar_add z hz)
    · change realQuadraticReflection Q x hx
        (realQuadraticReflection Q (y + x) hadd y) = x
      rw [realQuadraticReflection_add_apply_of_equal_Q Q x y hxy hadd]
      exact realQuadraticReflection_self_apply_neg Q x hx

theorem realQuadraticReflectionSubgroup_eq_top_of_orthogonal_spanning
    {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype ι]
    (Q : QuadraticForm ℝ V) (b : ι → V)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤)
    (hQ : ∀ i, Q (b i) ≠ 0)
    (horth : ∀ {i j}, i ≠ j →
      QuadraticMap.polar (⇑Q) (b i) (b j) = 0) :
    realQuadraticReflectionSubgroup Q = ⊤ := by
  classical
  apply top_unique
  intro f hf
  have hstep : ∀ s : Finset ι,
      ∃ h : Q.IsometryEquiv Q,
        h ∈ realQuadraticReflectionSubgroup Q ∧
        ∀ i ∈ s, h (f (b i)) = b i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        simp
    | @insert a s ha ih =>
        obtain ⟨h, hh, hmap⟩ := ih
        let y : V := h (f (b a))
        let S : Set V := b '' (↑s : Set ι)
        have hxy : Q (b a) = Q y := by
          dsimp [y]
          rw [h.map_app, f.map_app]
        have hy : Q y ≠ 0 := by
          rw [← hxy]
          exact hQ a
        have hxS : ∀ z ∈ S,
            QuadraticMap.polar (⇑Q) z (b a) = 0 := by
          intro z hz
          rcases hz with ⟨i, hi, rfl⟩
          have hia : i ≠ a := by
            intro hia
            apply ha
            simpa [hia] using hi
          exact horth hia
        have hyS : ∀ z ∈ S,
            QuadraticMap.polar (⇑Q) z y = 0 := by
          intro z hz
          rcases hz with ⟨i, hi, rfl⟩
          have hfi : h (f (b i)) = b i := hmap i hi
          have hpolar_h :
              QuadraticMap.polar (⇑Q)
                  (h (f (b i))) (h (f (b a))) =
                QuadraticMap.polar (⇑Q)
                  (f (b i)) (f (b a)) := by
            exact realQuadraticIsometry_preserves_polar
              Q h (f (b i)) (f (b a))
          calc
            QuadraticMap.polar (⇑Q) (b i) y =
                QuadraticMap.polar (⇑Q)
                  (h (f (b i))) (h (f (b a))) := by rw [hfi]
            _ = QuadraticMap.polar (⇑Q)
                  (f (b i)) (f (b a)) := hpolar_h
            _ = QuadraticMap.polar (⇑Q) (b i) (b a) :=
              realQuadraticIsometry_preserves_polar
                Q f (b i) (b a)
            _ = 0 := horth (by
              intro hia
              apply ha
              simpa [hia] using hi)
        obtain ⟨r₁, r₂, hr₁, hr₂, hrfix₁, hrfix₂, hmove⟩ :=
          realQuadraticReflectionSubgroup_shell_transitive_fixing_set
            Q S (b a) y hxy hy hxS hyS
        let hnew : Q.IsometryEquiv Q := r₁ * r₂ * h
        refine ⟨hnew,
          (realQuadraticReflectionSubgroup Q).mul_mem
            ((realQuadraticReflectionSubgroup Q).mul_mem
              hr₁ hr₂) hh,
          ?_⟩
        intro i hi
        by_cases hia : i = a
        · subst i
          change r₁ (r₂ (h (f (b a)))) = b a
          exact hmove
        · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
          have hfix₁i := hrfix₁ (b i) ⟨i, his, rfl⟩
          have hfix₂i := hrfix₂ (b i) ⟨i, his, rfl⟩
          change r₁ (r₂ (h (f (b i)))) = b i
          rw [hmap i his, hfix₂i, hfix₁i]
  obtain ⟨h, hh, hmap⟩ := hstep Finset.univ
  have hk : h * f = 1 := by
    apply DFunLike.ext _ _
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range b) := by
      rw [hspan]
      trivial
    refine Submodule.span_induction (p := fun x _ => (h * f) x = x)
      ?_ ?_ ?_ ?_ hv
    · rintro x ⟨i, rfl⟩
      change h (f (b i)) = b i
      exact hmap i (Finset.mem_univ _)
    · simp
    · intro x y _ _ hx hy
      change h (f (x + y)) = x + y
      have hx' : h (f x) = x := hx
      have hy' : h (f y) = y := hy
      rw [map_add, map_add, hx', hy']
    · intro r x _ hx
      change h (f (r • x)) = r • x
      have hx' : h (f x) = x := hx
      rw [map_smul, map_smul, hx']
  have hfmem : f ∈ realQuadraticReflectionSubgroup Q := by
    have hinv : h⁻¹ ∈ realQuadraticReflectionSubgroup Q :=
      (realQuadraticReflectionSubgroup Q).inv_mem hh
    have hfeq : f = h⁻¹ := by
      calc
        f = 1 * f := by simp
        _ = (h⁻¹ * h) * f := by rw [inv_mul_cancel]
        _ = h⁻¹ * (h * f) := by simp [mul_assoc]
        _ = h⁻¹ * 1 := by rw [hk]
        _ = h⁻¹ := by simp
    rw [hfeq]
    exact hinv
  exact hfmem

end InfoGeometry.Clifford
