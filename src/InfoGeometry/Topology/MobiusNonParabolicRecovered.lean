import InfoGeometry.Topology.MobiusThreeTransitiveRecovered
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# MobiusNonParabolicRecovered

Recovered proof of the non-parabolic Möbius normal form.  The proof is kept in a
separate owner file because it depends on the recovered inverse/composition
machinery and the recovered strict 3-transitivity theorem.
-/

namespace InfoGeometry

open Classical

/-- On the Riemann sphere, every two distinct points admit a third distinct point. -/
lemma exists_third_riemannSphere (z1 z2 : RiemannSphere) (h12 : z1 ≠ z2) :
    ∃ z3 : RiemannSphere, z1 ≠ z3 ∧ z3 ≠ z2 ∧ z2 ≠ z3 := by
  cases z1 with
  | none =>
      cases z2 with
      | none => exact (h12 rfl).elim
      | some w =>
          by_cases hw0 : w = 0
          · refine ⟨some 1, ?_, ?_, ?_⟩
            · intro h
              cases h
            · intro h
              have h1w : (1 : ℂ) = w := Option.some.inj h
              rw [hw0] at h1w
              exact one_ne_zero h1w
            · intro h
              have hw1 : w = (1 : ℂ) := Option.some.inj h
              rw [hw0] at hw1
              exact one_ne_zero hw1.symm
          · refine ⟨some 0, ?_, ?_, ?_⟩
            · intro h
              cases h
            · intro h
              exact hw0 (Option.some.inj h).symm
            · intro h
              exact hw0 (Option.some.inj h)
  | some w =>
      cases z2 with
      | none =>
          by_cases hw0 : w = 0
          · refine ⟨some 1, ?_, ?_, ?_⟩
            · intro h
              have hw1 : w = (1 : ℂ) := Option.some.inj h
              rw [hw0] at hw1
              exact one_ne_zero hw1.symm
            · intro h
              cases h
            · intro h
              cases h
          · refine ⟨some 0, ?_, ?_, ?_⟩
            · intro h
              exact hw0 (Option.some.inj h)
            · intro h
              cases h
            · intro h
              cases h
      | some v =>
          refine ⟨none, ?_, ?_, ?_⟩
          · intro h
            cases h
          · intro h
            cases h
          · intro h
            cases h

/-- A Möbius transformation fixing infinity has zero lower-left coefficient. -/
lemma c_eq_zero_of_fixed_infinity (M : MobiusTransform) (h : M.is_fixed_point none) :
    M.c = 0 := by
  by_contra hc
  have hbad : some (M.a / M.c) = none := by
    simpa [MobiusTransform.is_fixed_point, MobiusTransform.eval, hc] using h
  cases hbad

/-- If `c = 0`, then the diagonal entries are nonzero in a valid Möbius matrix. -/
lemma a_ne_zero_of_c_eq_zero (M : MobiusTransform) (hc : M.c = 0) : M.a ≠ 0 := by
  intro ha
  have hdet : M.a * M.d - M.b * M.c = 0 := by
    simp [ha, hc]
  exact M.det_ne_zero hdet

/-- If `c = 0`, then the lower-right entry is nonzero in a valid Möbius matrix. -/
lemma d_ne_zero_of_c_eq_zero (M : MobiusTransform) (hc : M.c = 0) : M.d ≠ 0 := by
  intro hd
  have hdet : M.a * M.d - M.b * M.c = 0 := by
    simp [hd, hc]
  exact M.det_ne_zero hdet

/-- A Möbius transformation fixing zero and infinity has zero upper-right coefficient. -/
lemma b_eq_zero_of_fixed_zero_of_c_eq_zero (M : MobiusTransform)
    (hc : M.c = 0) (h0 : M.is_fixed_point (some 0)) : M.b = 0 := by
  have hd : M.d ≠ 0 := d_ne_zero_of_c_eq_zero M hc
  have hbdiv : M.b / M.d = 0 := by
    have hraw : M.eval (some 0) = some 0 := h0
    dsimp [MobiusTransform.eval] at hraw
    rw [hc, zero_mul, zero_add, if_neg hd] at hraw
    have hsome : some (M.b / M.d) = some (0 : ℂ) := by
      simpa only [mul_zero, zero_mul, zero_add] using hraw
    exact Option.some.inj hsome
  exact (div_eq_zero_iff.mp hbdiv).resolve_right hd

/-- A Möbius transformation fixing zero and infinity acts as a dilation. -/
lemma eval_eq_dilation_of_fixed_zero_infinity (M : MobiusTransform)
    (h0 : M.is_fixed_point (some 0)) (hinf : M.is_fixed_point none) :
    let k : ℂ := M.a / M.d
    k ≠ 0 ∧ ∀ z : RiemannSphere, M.eval z = (dilation_transform k (by
      dsimp [k]
      exact div_ne_zero (a_ne_zero_of_c_eq_zero M (c_eq_zero_of_fixed_infinity M hinf))
        (d_ne_zero_of_c_eq_zero M (c_eq_zero_of_fixed_infinity M hinf)))).eval z := by
  intro k
  let hc : M.c = 0 := c_eq_zero_of_fixed_infinity M hinf
  have ha : M.a ≠ 0 := a_ne_zero_of_c_eq_zero M hc
  have hd : M.d ≠ 0 := d_ne_zero_of_c_eq_zero M hc
  have hb : M.b = 0 := b_eq_zero_of_fixed_zero_of_c_eq_zero M hc h0
  have hk0 : k ≠ 0 := by
    dsimp [k]
    exact div_ne_zero ha hd
  constructor
  · exact hk0
  · intro z
    cases z with
    | none =>
        simp [MobiusTransform.eval, dilation_transform, hc]
    | some z =>
        have hq : (M.a * z + M.b) / M.d = k * z := by
          dsimp [k]
          rw [hb, add_zero]
          field_simp [hd]
        simp [MobiusTransform.eval, dilation_transform, hc, hd, hq]

/-- If the normalized two-fixed-point transform had multiplier `1`, it would be identity. -/
lemma eq_id_of_fixed_zero_infinity_multiplier_one (M : MobiusTransform)
    (h0 : M.is_fixed_point (some 0)) (hinf : M.is_fixed_point none)
    (hk : M.a / M.d = 1) :
    ∀ z : RiemannSphere, M.eval z = z := by
  have hc : M.c = 0 := c_eq_zero_of_fixed_infinity M hinf
  have hd : M.d ≠ 0 := d_ne_zero_of_c_eq_zero M hc
  have hb : M.b = 0 := b_eq_zero_of_fixed_zero_of_c_eq_zero M hc h0
  have had : M.a = M.d := by
    rw [div_eq_one_iff_eq hd] at hk
    exact hk
  intro z
  cases z with
  | none =>
      simp [MobiusTransform.eval, hc]
  | some z =>
      have hq : (M.a * z + M.b) / M.d = z := by
        rw [hb, add_zero, had]
        exact mul_div_cancel_left₀ z hd
      simp [MobiusTransform.eval, hc, hd, hq]

/-- Non-parabolic normal form: a non-identity Möbius transformation with two
distinct fixed points is conjugate to a nontrivial dilation `z ↦ k*z`. -/
theorem non_parabolic_normal_form (M : MobiusTransform) (z1 z2 : RiemannSphere)
    (h_distinct : z1 ≠ z2) (f1 : M.is_fixed_point z1) (f2 : M.is_fixed_point z2)
    (h_nonid : ¬ ∀ z, M.eval z = z) :
    ∃ k : ℂ, k ≠ 0 ∧ k ≠ 1 ∧
      ∃ M_k : MobiusTransform,
        (∀ z : ℂ, M_k.eval (some z) = some (k * z)) ∧
        is_conjugate M M_k := by
  obtain ⟨z3, hz13, hz32, _hz23⟩ := exists_third_riemannSphere z1 z2 h_distinct
  have h01 : (some (0 : ℂ) : RiemannSphere) ≠ some 1 := by
    intro h
    exact zero_ne_one (Option.some.inj h)
  have h1inf : (some (1 : ℂ) : RiemannSphere) ≠ none := by
    intro h
    cases h
  have h0inf : (some (0 : ℂ) : RiemannSphere) ≠ none := by
    intro h
    cases h
  obtain ⟨T, hTz1, _hTz3, hTz2, _hTunique⟩ :=
    strictly_three_transitive z1 z3 z2 hz13 hz32 h_distinct
      (some 0) (some 1) none h01 h1inf h0inf
  let N : MobiusTransform := comp T (comp M (inv T))
  have hN0 : N.is_fixed_point (some 0) := by
    dsimp [MobiusTransform.is_fixed_point]
    calc
      N.eval (some 0) = T.eval (M.eval ((inv T).eval (some 0))) := by
        simp [N, eval_comp]
      _ = T.eval (M.eval z1) := by
        have h_inv : (inv T).eval (T.eval z1) = z1 := eval_inv_left T z1
        rw [hTz1] at h_inv
        rw [h_inv]
      _ = T.eval z1 := by rw [f1]
      _ = some 0 := hTz1
  have hNinf : N.is_fixed_point none := by
    dsimp [MobiusTransform.is_fixed_point]
    calc
      N.eval none = T.eval (M.eval ((inv T).eval none)) := by
        simp [N, eval_comp]
      _ = T.eval (M.eval z2) := by
        have h_inv : (inv T).eval (T.eval z2) = z2 := eval_inv_left T z2
        rw [hTz2] at h_inv
        rw [h_inv]
      _ = T.eval z2 := by rw [f2]
      _ = none := hTz2
  let k : ℂ := N.a / N.d
  obtain ⟨hk0, hN_dilation⟩ := eval_eq_dilation_of_fixed_zero_infinity N hN0 hNinf
  have hk_ne_one : k ≠ 1 := by
    intro hk
    apply h_nonid
    intro z
    have hNid : ∀ w : RiemannSphere, N.eval w = w :=
      eq_id_of_fixed_zero_infinity_multiplier_one N hN0 hNinf hk
    have hT_eq : T.eval (M.eval z) = T.eval z := by
      have h := hNid (T.eval z)
      have h_expand :
          N.eval (T.eval z) = T.eval (M.eval z) := by
        calc
          N.eval (T.eval z) = T.eval (M.eval ((inv T).eval (T.eval z))) := by
            simp [N, eval_comp]
          _ = T.eval (M.eval z) := by
            rw [eval_inv_left T z]
      rw [h_expand] at h
      exact h
    have h_inv := congrArg (fun w : RiemannSphere => (inv T).eval w) hT_eq
    simpa [eval_inv_left] using h_inv
  refine ⟨k, hk0, hk_ne_one, dilation_transform k hk0, ?_, ?_⟩
  · intro z
    exact dilation_transform_eval_some k z hk0
  · refine ⟨inv T, T, ?_, ?_⟩
    · intro z
      exact eval_inv_left T z
    · intro z
      have hN_eq : N.eval (T.eval z) = (dilation_transform k hk0).eval (T.eval z) := by
        simpa [k] using hN_dilation (T.eval z)
      have h_expand :
          N.eval (T.eval z) = T.eval (M.eval z) := by
        calc
          N.eval (T.eval z) = T.eval (M.eval ((inv T).eval (T.eval z))) := by
            simp [N, eval_comp]
          _ = T.eval (M.eval z) := by
            rw [eval_inv_left T z]
      have hT :
          T.eval (M.eval z) = (dilation_transform k hk0).eval (T.eval z) := by
        rw [← h_expand]
        exact hN_eq
      have h_inv := congrArg (fun w : RiemannSphere => (inv T).eval w) hT
      simpa [eval_inv_left] using h_inv

end InfoGeometry
