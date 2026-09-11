import InfoGeometry.Clifford.Cl55WittOrthogonalBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittReflectionConjugation
import InfoGeometry.Clifford.Cl55WittCarrierFaithfulness

namespace InfoGeometry.Clifford.Clifford55

/-!
# Finite-basis Cartan--Dieudonné factorization for `Q55`

The proof uses the already verified two-reflection alignment lemma.  The
induction processes the ten orthogonal basis vectors one at a time, while
each new pair of reflections fixes the previously processed vectors.
-/

theorem quadraticIsometry_preserves_polar
    (f : Q55.IsometryEquiv Q55) (a b : V55) :
    QuadraticMap.polar (⇑Q55) (f a) (f b) =
      QuadraticMap.polar (⇑Q55) a b := by
  change Q55 (f a + f b) - Q55 (f a) - Q55 (f b) =
    Q55 (a + b) - Q55 a - Q55 b
  rw [← map_add f a b, f.map_app (a + b), f.map_app a, f.map_app b]

theorem quadraticReflectionSubgroup_eq_top :
    quadraticReflectionSubgroup = ⊤ := by
  apply top_unique
  intro g hg
  let f : Q55.IsometryEquiv Q55 := orthogonalGroup55ToIsometry g
  have hstep : ∀ s : Finset WittIndex,
      ∃ h : orthogonalGroup55, h ∈ quadraticReflectionSubgroup ∧
        ∀ i ∈ s, h.1 (f (wittBasis i)) = wittBasis i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        simp
    | @insert a s ha ih =>
        obtain ⟨h, hh, hmap⟩ := ih
        let y : V55 := h.1 (f (wittBasis a))
        let S : Set V55 := wittBasis '' (↑s : Set WittIndex)
        have hxy : Q55 (wittBasis a) = Q55 y := by
          dsimp [y]
          rw [h.2, f.map_app]
        have hy : Q55 y ≠ 0 := by
          rw [← hxy]
          exact wittBasis_Q_ne_zero a
        have hxS : ∀ z ∈ S,
            QuadraticMap.polar (⇑Q55) z (wittBasis a) = 0 := by
          intro z hz
          rcases hz with ⟨i, hi, rfl⟩
          have hia : i ≠ a := by
            intro hia
            apply ha
            simpa [hia] using hi
          exact wittBasis_pairwise_orthogonal hia
        have hyS : ∀ z ∈ S,
            QuadraticMap.polar (⇑Q55) z y = 0 := by
          intro z hz
          rcases hz with ⟨i, hi, rfl⟩
          have his : i ∈ s := hi
          have hfi : h.1 (f (wittBasis i)) = wittBasis i :=
            hmap i his
          have hpolar_h :
              QuadraticMap.polar (⇑Q55)
                  (h.1 (f (wittBasis i)))
                  (h.1 (f (wittBasis a))) =
                QuadraticMap.polar (⇑Q55)
                  (f (wittBasis i)) (f (wittBasis a)) := by
            exact (quadraticIsometry_preserves_polar
              (orthogonalGroup55ToIsometry h)
              (f (wittBasis i)) (f (wittBasis a)))
          calc
            QuadraticMap.polar (⇑Q55) (wittBasis i) y =
                QuadraticMap.polar (⇑Q55)
                  (h.1 (f (wittBasis i)))
                  (h.1 (f (wittBasis a))) := by rw [hfi]
            _ = QuadraticMap.polar (⇑Q55)
                  (f (wittBasis i)) (f (wittBasis a)) := hpolar_h
            _ = QuadraticMap.polar (⇑Q55)
                  (wittBasis i) (wittBasis a) :=
              quadraticIsometry_preserves_polar f _ _
            _ = 0 := by
              exact wittBasis_pairwise_orthogonal (by
                intro hia
                apply ha
                simpa [hia] using hi)
        obtain ⟨r₁, r₂, hr₁, hr₂, hfix₁, hfix₂, hmove⟩ :=
          quadraticReflectionSubgroup_shell_transitive_fixing_set
            S (wittBasis a) y hxy hy hxS hyS
        let hnew : orthogonalGroup55 := r₁ * r₂ * h
        refine ⟨hnew,
          quadraticReflectionSubgroup.mul_mem
            (quadraticReflectionSubgroup.mul_mem hr₁ hr₂) hh, ?_⟩
        intro i hi
        by_cases hia : i = a
        · subst i
          change r₁.1 (r₂.1 (h.1 (f (wittBasis a)))) = wittBasis a
          exact hmove
        · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
          have hfix₁i := hfix₁ (wittBasis i)
            ⟨i, his, rfl⟩
          have hfix₂i := hfix₂ (wittBasis i)
            ⟨i, his, rfl⟩
          change r₁.1 (r₂.1 (h.1 (f (wittBasis i)))) = wittBasis i
          rw [hmap i his, hfix₂i, hfix₁i]
  obtain ⟨h, hh, hmap⟩ := hstep Finset.univ
  let fg : orthogonalGroup55 := orthogonalGroup55FromIsometry f
  let k : orthogonalGroup55 := h * fg
  have hk : k = 1 := by
    apply orthogonalGroup55_eq_one_of_fix_witt_coordinates
    · intro i
      change h.1 (fg.1 (e_pos i)) = e_pos i
      simpa [fg, f, wittBasis] using
        hmap (Sum.inl i) (Finset.mem_univ _)
    · intro i
      change h.1 (fg.1 (f_neg i)) = f_neg i
      simpa [fg, f, wittBasis] using
        hmap (Sum.inr i) (Finset.mem_univ _)
  have hfg : fg ∈ quadraticReflectionSubgroup := by
    have hinv : h⁻¹ ∈ quadraticReflectionSubgroup :=
      quadraticReflectionSubgroup.inv_mem hh
    have hfg_eq : fg = h⁻¹ := by
      dsimp [k] at hk
      calc
        fg = 1 * fg := by simp
        _ = (h⁻¹ * h) * fg := by rw [inv_mul_cancel]
        _ = h⁻¹ * (h * fg) := by simp [mul_assoc]
        _ = h⁻¹ * 1 := by rw [hk]
        _ = h⁻¹ := by simp
    rw [hfg_eq]
    exact hinv
  simpa [fg, f] using hfg

end InfoGeometry.Clifford.Clifford55
