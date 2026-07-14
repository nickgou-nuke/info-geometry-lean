import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open Complex

def RiemannSphere := Option ℂ

structure MobiusTransform where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

noncomputable def MobiusTransform.eval (M : MobiusTransform) (z : RiemannSphere) : RiemannSphere :=
  match z with
  | none => if M.c = 0 then none else some (M.a / M.c)
  | some z' =>
      let denom := M.c * z' + M.d
      if denom = 0 then none else some ((M.a * z' + M.b) / denom)

noncomputable def cross_ratio_ext (z1 z2 z3 z4 : RiemannSphere) : RiemannSphere :=
  match z1, z2, z3, z4 with
  | none, none, none, none => none
  | none, none, none, some d => none
  | none, none, some c, none => none
  | none, none, some c, some d => some 1
  | none, some b, none, none => none
  | none, some b, none, some d => some 0
  | none, some b, some c, none => none
  | none, some b, some c, some d => if b - c = 0 then none else some ((b - d) / (b - c))
  | some a, none, none, none => none
  | some a, none, none, some d => none
  | some a, none, some c, none => some 0
  | some a, none, some c, some d => if a - d = 0 then none else some ((a - c) / (a - d))
  | some a, some b, none, none => some 1
  | some a, some b, none, some d => if a - d = 0 then none else some ((b - d) / (a - d))
  | some a, some b, some c, none => if b - c = 0 then none else some ((a - c) / (b - c))
  | some a, some b, some c, some d => if (b - c) * (a - d) = 0 then none else some (((a - c) * (b - d)) / ((b - c) * (a - d)))

lemma if_mul_eq_if (x y c : ℂ) (hc : c ≠ 0) :
  (if x = 0 then (none : RiemannSphere) else some (y / x)) =
  (if c * x = 0 then none else some ((c * y) / (c * x))) := by
  by_cases h : x = 0
  · have h2 : c * x = 0 := by rw [h, mul_zero]
    rw [if_pos h, if_pos h2]
  · have h2 : c * x ≠ 0 := mul_ne_zero hc h
    rw [if_neg h, if_neg h2]
    congr 1
    rw [mul_div_mul_left y x hc]

lemma if_mul_eq_if_right (x y c : ℂ) (hc : c ≠ 0) :
  (if x = 0 then (none : RiemannSphere) else some (y / x)) =
  (if x * c = 0 then none else some ((y * c) / (x * c))) := by
  by_cases h : x = 0
  · have h2 : x * c = 0 := by rw [h, zero_mul]
    rw [if_pos h, if_pos h2]
  · have h2 : x * c ≠ 0 := mul_ne_zero h hc
    rw [if_neg h, if_neg h2]
    congr 1
    rw [mul_div_mul_right y x hc]

theorem cross_ratio_preserving (M : MobiusTransform) (z1 z2 z3 z4 : RiemannSphere) :
    cross_ratio_ext z1 z2 z3 z4 =
    cross_ratio_ext (M.eval z1) (M.eval z2) (M.eval z3) (M.eval z4) := by
  let to_proj (z : RiemannSphere) : ℂ × ℂ :=
    match z with | none => (1, 0) | some z' => (z', 1)
  let proj_cr (p1 p2 p3 p4 : ℂ × ℂ) : RiemannSphere :=
    let num := (p1.1 * p3.2 - p3.1 * p1.2) * (p2.1 * p4.2 - p4.1 * p2.2)
    let den := (p2.1 * p3.2 - p3.1 * p2.2) * (p1.1 * p4.2 - p4.1 * p1.2)
    if den = 0 then none else some (num / den)
  
  have h_eq : ∀ w1 w2 w3 w4 : RiemannSphere, cross_ratio_ext w1 w2 w3 w4 = proj_cr (to_proj w1) (to_proj w2) (to_proj w3) (to_proj w4) := by
    intro w1 w2 w3 w4
    cases w1 <;> cases w2 <;> cases w3 <;> cases w4 <;> {
      dsimp [cross_ratio_ext, proj_cr, to_proj]
      simp only [mul_one, mul_zero, sub_zero, zero_sub, one_mul, zero_mul, sub_self, neg_mul_neg]
      try {
        have h_neg1 : (-1 : ℂ) ≠ 0 := by norm_num
        rw [if_mul_eq_if _ _ (-1) h_neg1]
      }
      try {
        have h_neg1 : (-1 : ℂ) ≠ 0 := by norm_num
        rw [if_mul_eq_if_right _ _ (-1) h_neg1]
      }
      try {
        by_cases h : (-1 : ℂ) = 0
        · exfalso; revert h; norm_num
        simp only [h, mul_eq_zero, false_or, or_false, if_false, div_self h]
        have hz : (0 : ℂ) / -1 = 0 := by norm_num
        rw [hz]
      }
      try {
        by_cases h : (1 : ℂ) = 0
        · exfalso; revert h; norm_num
        simp only [h, mul_eq_zero, false_or, or_false, if_false, div_self h]
      }
      try {
        congr 1
        funext hc
        congr 1
        field_simp
        ring
      }
      try rfl
    }
  
  rw [h_eq z1 z2 z3 z4, h_eq (M.eval z1) (M.eval z2) (M.eval z3) (M.eval z4)]
  let M_act (p : ℂ × ℂ) : ℂ × ℂ := (M.a * p.1 + M.b * p.2, M.c * p.1 + M.d * p.2)
  
  have h_eval_act : ∀ z : RiemannSphere, ∃ lam : ℂ, lam ≠ 0 ∧ (to_proj (M.eval z)).1 = lam * (M_act (to_proj z)).1 ∧ (to_proj (M.eval z)).2 = lam * (M_act (to_proj z)).2 := by
    intro z
    cases z with
    | none =>
      dsimp [MobiusTransform.eval, to_proj, M_act]
      by_cases hc : M.c = 0
      · rw [if_pos hc]
        use (1 / M.a)
        have ha : M.a ≠ 0 := by
          intro h
          have : M.a * M.d - M.b * M.c = 0 := by rw [h, hc]; ring
          exact M.det_ne_zero this
        constructor
        · exact one_div_ne_zero ha
        · constructor
          · rw [hc]; field_simp; ring
          · rw [hc]; field_simp; ring
      · rw [if_neg hc]
        use (1 / M.c)
        constructor
        · exact one_div_ne_zero hc
        · constructor
          · rw [hc]; field_simp; ring
          · rw [hc]; field_simp; ring
    | some z' =>
      dsimp [MobiusTransform.eval, to_proj, M_act]
      by_cases hd : M.c * z' + M.d = 0
      · rw [if_pos hd]
        use (1 / (M.a * z' + M.b))
        have ha : M.a * z' + M.b ≠ 0 := by
          intro h
          have h1 : M.d * (M.a * z' + M.b) - M.b * (M.c * z' + M.d) = 0 := by rw [h, hd]; ring
          have h2 : M.d * (M.a * z' + M.b) - M.b * (M.c * z' + M.d) = (M.a * M.d - M.b * M.c) * z' := by ring
          rw [h2] at h1
          have hz : z' = 0 := by
            cases mul_eq_zero.mp h1 with
            | inl hdet => exact (M.det_ne_zero hdet).elim
            | inr hz => exact hz
          rw [hz] at h hd
          have hb : M.b = 0 := by
            calc M.b = M.a * 0 + M.b := by ring
                 _ = 0 := h
          have hm_d : M.d = 0 := by
            calc M.d = M.c * 0 + M.d := by ring
                 _ = 0 := hd
          have hdet : M.a * M.d - M.b * M.c = 0 := by rw [hb, hm_d]; ring
          exact M.det_ne_zero hdet
        constructor
        · exact one_div_ne_zero ha
        · constructor
          · rw [hd]; field_simp; ring
          · rw [hd]; field_simp; ring
      · rw [if_neg hd]
        use (1 / (M.c * z' + M.d))
        constructor
        · exact one_div_ne_zero hd
        · constructor
          · field_simp; ring
          · field_simp; ring

  rcases h_eval_act z1 with ⟨L1, hL1, hz1_1, hz1_2⟩
  rcases h_eval_act z2 with ⟨L2, hL2, hz2_1, hz2_2⟩
  rcases h_eval_act z3 with ⟨L3, hL3, hz3_1, hz3_2⟩
  rcases h_eval_act z4 with ⟨L4, hL4, hz4_1, hz4_2⟩

  have h_det : ∀ u v : ℂ × ℂ, (M_act u).1 * (M_act v).2 - (M_act v).1 * (M_act u).2 = (M.a * M.d - M.b * M.c) * (u.1 * v.2 - v.1 * u.2) := by
    intro u v
    dsimp [M_act]
    ring

  have h_diff : ∀ u v Lu Lv pu pv, pu.1 = Lu * (M_act u).1 → pu.2 = Lu * (M_act u).2 → pv.1 = Lv * (M_act v).1 → pv.2 = Lv * (M_act v).2 →
    pu.1 * pv.2 - pv.1 * pu.2 = Lu * Lv * (M.a * M.d - M.b * M.c) * (u.1 * v.2 - v.1 * u.2) := by
    intro u v Lu Lv pu pv hu1 hu2 hv1 hv2
    rw [hu1, hu2, hv1, hv2]
    have : (Lu * (M_act u).1) * (Lv * (M_act v).2) - (Lv * (M_act v).1) * (Lu * (M_act u).2) = Lu * Lv * ((M_act u).1 * (M_act v).2 - (M_act v).1 * (M_act u).2) := by ring
    rw [this, h_det]
    ring

  have num_eq : ((to_proj (M.eval z1)).1 * (to_proj (M.eval z3)).2 - (to_proj (M.eval z3)).1 * (to_proj (M.eval z1)).2) *
                ((to_proj (M.eval z2)).1 * (to_proj (M.eval z4)).2 - (to_proj (M.eval z4)).1 * (to_proj (M.eval z2)).2) =
                (L1 * L2 * L3 * L4 * (M.a * M.d - M.b * M.c)^2) *
                (((to_proj z1).1 * (to_proj z3).2 - (to_proj z3).1 * (to_proj z1).2) * ((to_proj z2).1 * (to_proj z4).2 - (to_proj z4).1 * (to_proj z2).2)) := by
    rw [h_diff (to_proj z1) (to_proj z3) L1 L3 (to_proj (M.eval z1)) (to_proj (M.eval z3)) hz1_1 hz1_2 hz3_1 hz3_2]
    rw [h_diff (to_proj z2) (to_proj z4) L2 L4 (to_proj (M.eval z2)) (to_proj (M.eval z4)) hz2_1 hz2_2 hz4_1 hz4_2]
    ring

  have den_eq : ((to_proj (M.eval z2)).1 * (to_proj (M.eval z3)).2 - (to_proj (M.eval z3)).1 * (to_proj (M.eval z2)).2) *
                ((to_proj (M.eval z1)).1 * (to_proj (M.eval z4)).2 - (to_proj (M.eval z4)).1 * (to_proj (M.eval z1)).2) =
                (L1 * L2 * L3 * L4 * (M.a * M.d - M.b * M.c)^2) *
                (((to_proj z2).1 * (to_proj z3).2 - (to_proj z3).1 * (to_proj z2).2) * ((to_proj z1).1 * (to_proj z4).2 - (to_proj z4).1 * (to_proj z1).2)) := by
    rw [h_diff (to_proj z2) (to_proj z3) L2 L3 (to_proj (M.eval z2)) (to_proj (M.eval z3)) hz2_1 hz2_2 hz3_1 hz3_2]
    rw [h_diff (to_proj z1) (to_proj z4) L1 L4 (to_proj (M.eval z1)) (to_proj (M.eval z4)) hz1_1 hz1_2 hz4_1 hz4_2]
    ring

  let num1 := (((to_proj z1).1 * (to_proj z3).2 - (to_proj z3).1 * (to_proj z1).2) * ((to_proj z2).1 * (to_proj z4).2 - (to_proj z4).1 * (to_proj z2).2))
  let den1 := (((to_proj z2).1 * (to_proj z3).2 - (to_proj z3).1 * (to_proj z2).2) * ((to_proj z1).1 * (to_proj z4).2 - (to_proj z4).1 * (to_proj z1).2))
  let factor := (L1 * L2 * L3 * L4 * (M.a * M.d - M.b * M.c)^2)
  have h_factor_ne_zero : factor ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero 2 M.det_ne_zero)
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hL1 hL2) hL3) hL4

  change proj_cr (to_proj z1) (to_proj z2) (to_proj z3) (to_proj z4) = if factor * den1 = 0 then none else some (factor * num1 / (factor * den1))
  dsimp [proj_cr]
  by_cases hden : den1 = 0
  · have hden2 : factor * den1 = 0 := by rw [hden, mul_zero]
    rw [if_pos hden, if_pos hden2]
  · have hden2 : factor * den1 ≠ 0 := mul_ne_zero h_factor_ne_zero hden
    rw [if_neg hden, if_neg hden2]
    congr 1
    rw [mul_div_mul_left num1 den1 h_factor_ne_zero]

