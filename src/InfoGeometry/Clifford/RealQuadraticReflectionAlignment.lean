import InfoGeometry.Clifford.RealQuadraticReflection
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford

/-!
# Generic reflection alignment for real quadratic forms

These are the local two-reflection identities used in a
Cartan--Dieudonné argument.  They require no signature property and do
not claim that reflections generate the whole isometry group.
-/

noncomputable def realQuadraticIdentityIsometry
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) : Q.IsometryEquiv Q :=
  QuadraticMap.IsometryEquiv.mk (LinearEquiv.refl ℝ V) (by
    intro x
    rfl)

theorem realQuadraticReflection_apply_of_polar_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v z : V) (hv : Q v ≠ 0)
    (hp : QuadraticMap.polar (⇑Q) z v = 0) :
    realQuadraticReflection Q v hv z = z := by
  rw [realQuadraticReflection_apply, hp]
  simp

theorem realQuadraticReflection_sub_apply_of_equal_Q
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (x y : V) (hxy : Q x = Q y)
    (hu : Q (y - x) ≠ 0) :
    realQuadraticReflection Q (y - x) hu (y) = x := by
  rw [realQuadraticReflection_apply]
  have hpolar :
      QuadraticMap.polar (⇑Q) y (y - x) = Q (y - x) := by
    calc
      QuadraticMap.polar (⇑Q) y (y - x) =
          QuadraticMap.polar (⇑Q) y y -
            QuadraticMap.polar (⇑Q) y x :=
        QuadraticMap.polar_sub_right Q y y x
      _ = 2 * Q y - QuadraticMap.polar (⇑Q) y x := by
        rw [QuadraticMap.polar_self]
        norm_num [smul_eq_mul]
      _ = Q y + Q x - QuadraticMap.polar (⇑Q) y x := by
        rw [hxy]
        ring
      _ = Q y + Q (-x) +
          QuadraticMap.polar (⇑Q) y (-x) := by
        rw [QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
        ring
      _ = Q (y + (-x)) :=
        (QuadraticMap.map_add (⇑Q) y (-x)).symm
      _ = Q (y - x) := by rw [sub_eq_add_neg]
  rw [hpolar, div_self hu]
  module

theorem realQuadraticReflection_add_apply_of_equal_Q
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (x y : V) (hxy : Q x = Q y)
    (hu : Q (y + x) ≠ 0) :
    realQuadraticReflection Q (y + x) hu y = -x := by
  rw [realQuadraticReflection_apply]
  have hpolar :
      QuadraticMap.polar (⇑Q) y (y + x) = Q (y + x) := by
    calc
      QuadraticMap.polar (⇑Q) y (y + x) =
          QuadraticMap.polar (⇑Q) y y +
            QuadraticMap.polar (⇑Q) y x :=
        QuadraticMap.polar_add_right Q y y x
      _ = 2 * Q y + QuadraticMap.polar (⇑Q) y x := by
        rw [QuadraticMap.polar_self]
        norm_num [smul_eq_mul]
      _ = Q y + Q x + QuadraticMap.polar (⇑Q) y x := by
        rw [hxy]
        ring
      _ = Q (y + x) :=
        (QuadraticMap.map_add (⇑Q) y x).symm
  rw [hpolar, div_self hu]
  module

theorem realQuadraticReflection_self_apply_neg
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (x : V) (hx : Q x ≠ 0) :
    realQuadraticReflection Q x hx (-x) = x := by
  rw [realQuadraticReflection_apply, QuadraticMap.polar_neg_left,
    QuadraticMap.polar_self]
  rw [two_smul]
  field_simp [hx]
  module

theorem realQuadraticReflection_add_norm_of_sub_isotropic
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (x y : V) (hxy : Q x = Q y)
    (hy : Q y ≠ 0) (hsub : Q (y - x) = 0) :
    Q (y + x) ≠ 0 := by
  intro hsum
  have hfour : Q (y + x) + Q (y - x) = 4 * Q y := by
    have hplus : Q (y + x) =
        Q y + Q x + QuadraticMap.polar (⇑Q) y x :=
      QuadraticMap.map_add (⇑Q) y x
    have hminus : Q (y - x) =
        Q y + Q x - QuadraticMap.polar (⇑Q) y x := by
      rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q),
        QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
      abel
    rw [hplus, hminus]
    rw [hxy]
    ring
  rw [hsum, hsub] at hfour
  exact hy (by linarith)

theorem realQuadraticReflection_alignment
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (x y : V) (hxy : Q x = Q y)
    (hy : Q y ≠ 0) :
    ∃ r₁ r₂ : Q.IsometryEquiv Q, r₁ (r₂ y) = x := by
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨realQuadraticIdentityIsometry Q,
      realQuadraticIdentityIsometry Q, rfl⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q x ≠ 0 := by
      simpa using hy
    refine ⟨realQuadraticReflectionIsometry Q x hx,
      realQuadraticIdentityIsometry Q, ?_⟩
    change realQuadraticReflection Q x hx (-x) = x
    simpa using realQuadraticReflection_self_apply_neg Q x hx
  by_cases hsub : Q (y - x) ≠ 0
  · refine ⟨realQuadraticIdentityIsometry Q,
      realQuadraticReflectionIsometry Q (y - x) hsub, ?_⟩
    change realQuadraticReflection Q (y - x) hsub y = x
    exact realQuadraticReflection_sub_apply_of_equal_Q Q x y hxy hsub
  · have hsub_zero : Q (y - x) = 0 := not_ne_iff.mp hsub
    have hadd : Q (y + x) ≠ 0 :=
      realQuadraticReflection_add_norm_of_sub_isotropic Q x y hxy hy hsub_zero
    have hx : Q x ≠ 0 := by
      rw [hxy]
      exact hy
    refine ⟨realQuadraticReflectionIsometry Q x hx,
      realQuadraticReflectionIsometry Q (y + x) hadd, ?_⟩
    change realQuadraticReflection Q x hx
      (realQuadraticReflection Q (y + x) hadd y) = x
    rw [realQuadraticReflection_add_apply_of_equal_Q Q x y hxy hadd]
    exact realQuadraticReflection_self_apply_neg Q x hx

theorem realQuadraticReflection_alignment_fixing_orthogonal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (z x y : V) (hxy : Q x = Q y)
    (hy : Q y ≠ 0)
    (hzx : QuadraticMap.polar (⇑Q) z x = 0)
    (hzy : QuadraticMap.polar (⇑Q) z y = 0) :
    ∃ r₁ r₂ : Q.IsometryEquiv Q,
      r₁ (r₂ y) = x ∧ r₁ z = z ∧ r₂ z = z := by
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨realQuadraticIdentityIsometry Q,
      realQuadraticIdentityIsometry Q, rfl, rfl, rfl⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q x ≠ 0 := by
      simpa using hy
    refine ⟨realQuadraticReflectionIsometry Q x hx,
      realQuadraticIdentityIsometry Q, ?_, ?_, ?_⟩
    · change realQuadraticReflection Q x hx (-x) = x
      simpa using realQuadraticReflection_self_apply_neg Q x hx
    · exact realQuadraticReflection_apply_of_polar_eq_zero Q x z hx hzx
    · rfl
  by_cases hsub : Q (y - x) ≠ 0
  · have hpolar_sub :
        QuadraticMap.polar (⇑Q) z (y - x) = 0 := by
      rw [QuadraticMap.polar_sub_right]
      rw [hzy, hzx]
      simp
    refine ⟨realQuadraticIdentityIsometry Q,
      realQuadraticReflectionIsometry Q (y - x) hsub, ?_, ?_, ?_⟩
    · change realQuadraticReflection Q (y - x) hsub y = x
      exact realQuadraticReflection_sub_apply_of_equal_Q Q x y hxy hsub
    · rfl
    · exact realQuadraticReflection_apply_of_polar_eq_zero
        Q (y - x) z hsub hpolar_sub
  · have hsub_zero : Q (y - x) = 0 := not_ne_iff.mp hsub
    have hadd : Q (y + x) ≠ 0 :=
      realQuadraticReflection_add_norm_of_sub_isotropic Q x y hxy hy hsub_zero
    have hpolar_add :
        QuadraticMap.polar (⇑Q) z (y + x) = 0 := by
      rw [QuadraticMap.polar_add_right]
      rw [hzy, hzx]
      simp
    have hx : Q x ≠ 0 := by
      rw [hxy]
      exact hy
    refine ⟨realQuadraticReflectionIsometry Q x hx,
      realQuadraticReflectionIsometry Q (y + x) hadd, ?_, ?_, ?_⟩
    · change realQuadraticReflection Q x hx
        (realQuadraticReflection Q (y + x) hadd y) = x
      rw [realQuadraticReflection_add_apply_of_equal_Q Q x y hxy hadd]
      exact realQuadraticReflection_self_apply_neg Q x hx
    · exact realQuadraticReflection_apply_of_polar_eq_zero Q x z hx hzx
    · exact realQuadraticReflection_apply_of_polar_eq_zero
        Q (y + x) z hadd hpolar_add

theorem realQuadraticReflection_alignment_fixing_set
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (S : Set V) (x y : V)
    (hxy : Q x = Q y) (hy : Q y ≠ 0)
    (hxS : ∀ z ∈ S, QuadraticMap.polar (⇑Q) z x = 0)
    (hyS : ∀ z ∈ S, QuadraticMap.polar (⇑Q) z y = 0) :
    ∃ r₁ r₂ : Q.IsometryEquiv Q,
      (∀ z ∈ S, r₁ z = z) ∧
      (∀ z ∈ S, r₂ z = z) ∧
      r₁ (r₂ y) = x := by
  let identity : Q.IsometryEquiv Q := realQuadraticIdentityIsometry Q
  have hidentity_apply (w : V) : identity w = w := by
    rfl
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨identity, identity,
      (fun z _ => hidentity_apply z),
      (fun z _ => hidentity_apply z), by
        rw [hidentity_apply, hidentity_apply]⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q x ≠ 0 := by simpa using hy
    refine ⟨realQuadraticReflectionIsometry Q x hx, identity, ?_,
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
    refine ⟨identity,
      realQuadraticReflectionIsometry Q (y - x) hsub,
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
    refine ⟨realQuadraticReflectionIsometry Q x hx,
      realQuadraticReflectionIsometry Q (y + x) hadd, ?_, ?_, ?_⟩
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

end InfoGeometry.Clifford
