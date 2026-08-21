import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2CyclotomicWeylBridge
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- The Coxeter element c of order 6 in SplitOctF2Aut. -/
noncomputable def c : SplitOctF2Aut := swapCartanAut * cycle012Aut

/-- The simple reflection s of order 2 in SplitOctF2Aut. -/
noncomputable def s : SplitOctF2Aut := swap01Aut

/-- The second simple reflection t of order 2 in SplitOctF2Aut. -/
noncomputable def t : SplitOctF2Aut := s * c

theorem s_sq : s * s = 1 := by
  exact swap01Aut_sq

theorem c_pow_six : c ^ 6 = 1 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> rfl

theorem c_sq_up0 : (c ^ 2).1 up0 = up1 := by
  simp [c, pow_two, cycle012Aut_apply, cycle012Fun, swapCartanAut,
    swapCartanEquiv, swapCartanFun, up0, up1]

theorem c_cube_up0 : (c ^ 3).1 up0 = down0 := by
  simp [c, pow_succ, cycle012Aut_apply, cycle012Fun, swapCartanAut,
    swapCartanEquiv, swapCartanFun, up0, down0]

theorem c_pow_two_ne_one : c ^ 2 ≠ 1 := by
  intro h
  have h' := congrArg (fun f : SplitOctF2Aut => f.1 up0) h
  change (c ^ 2).1 up0 = (1 : SplitOctF2Aut).1 up0 at h'
  rw [c_sq_up0] at h'
  exact Bool.noConfusion (congrArg SplitOctF2.x1 h')

theorem c_pow_three_ne_one : c ^ 3 ≠ 1 := by
  intro h
  have h' := congrArg (fun f : SplitOctF2Aut => f.1 up0) h
  change (c ^ 3).1 up0 = (1 : SplitOctF2Aut).1 up0 at h'
  rw [c_cube_up0] at h'
  exact Bool.noConfusion (congrArg SplitOctF2.x0 h')

theorem c_orderOf : orderOf c = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (n := 6)
  · norm_num
  · exact c_pow_six
  · intro p hp hdiv
    have hp_le : p ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · simpa using c_pow_three_ne_one
    · simpa using c_pow_two_ne_one
    · norm_num at hdiv
    · norm_num at hdiv
    · norm_num at hp

theorem c_inv_eq_pow_five : c⁻¹ = c ^ 5 := by
  have h : c ^ 5 * c = 1 := by
    calc
      c ^ 5 * c = c ^ 6 := by rw [← pow_succ]
      _ = 1 := c_pow_six
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem c_pow_five_mul_c : c ^ 5 * c = 1 := by
  calc
    c ^ 5 * c = c ^ 6 := by rw [← pow_succ]
    _ = 1 := c_pow_six

theorem c_pow_mod (n : ℕ) : c ^ (n % 6) = c ^ n := by
  have h := pow_mod_orderOf c n
  rw [c_orderOf] at h
  exact h

theorem c_pow_add_mod (m n : ℕ) :
    c ^ m * c ^ n = c ^ ((m + n) % 6) := by
  rw [← pow_add, ← c_pow_mod]

theorem c_mul_pow_five : c * c ^ 5 = 1 := by
  calc
    c * c ^ 5 = c ^ 6 := by rw [← pow_succ']
    _ = 1 := c_pow_six

theorem c_pow_inv_fin (i : Fin 6) :
    (c ^ (i : ℕ))⁻¹ = c ^ ((6 - (i : ℕ)) % 6) := by
  have h : c ^ (i : ℕ) * c ^ ((6 - (i : ℕ)) % 6) = 1 := by
    fin_cases i <;> norm_num [c_pow_add_mod, c_pow_six,
      c_mul_pow_five, c_pow_five_mul_c, c_inv_eq_pow_five]
  exact inv_eq_of_mul_eq_one_right h

theorem c_pow_injective :
    Function.Injective (fun k : Fin 6 => c ^ (k : ℕ)) := by
  intro i j h
  have hmod : (i : ℕ) ≡ (j : ℕ) [MOD orderOf c] :=
    (pow_eq_pow_iff_modEq.mp h)
  rw [c_orderOf] at hmod
  apply Fin.ext
  exact hmod.eq_of_lt_of_lt i.isLt j.isLt

theorem one_apply (X : SplitOctF2) :
    (1 : SplitOctF2Aut).1 X = X := by
  rfl

theorem s_ne_c_pow (k : Fin 6) : s ≠ c ^ (k : ℕ) := by
  fin_cases k <;> intro h
  all_goals
    have h' := congrArg
      (fun f : SplitOctF2Aut =>
        (f.1 ePlus, f.1 up0, f.1 up1, f.1 up2, f.1 down0, f.1 down1, f.1 down2)) h
    norm_num [s, c, pow_succ, swap01Aut_apply, cycle012Aut_apply,
      cycle012Fun, swap01Fun, swapCartanAut, swapCartanEquiv, swapCartanFun,
      ePlus, up0, up1, up2, down0, down1, down2,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one, one_apply] at h'

theorem s_c_s : s * c * s = c⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> rfl

theorem s_conj_c_pow (n : ℕ) :
    s * c ^ n * s = (c ^ n)⁻¹ := by
  induction n with
  | zero => simp [s_sq]
  | succ n ih =>
      rw [pow_succ]
      calc
        s * (c ^ n * c) * s =
            (s * c ^ n * s) * (s * c * s) := by
              calc
                s * (c ^ n * c) * s = s * c ^ n * (c * s) := by
                  simp [mul_assoc]
                _ = s * c ^ n * (s * s) * (c * s) := by
                  rw [s_sq]
                  simp
                _ = (s * c ^ n * s) * (s * c * s) := by
                  simp [mul_assoc]
        _ = (c ^ n)⁻¹ * c⁻¹ := by rw [ih, s_c_s]
        _ = (c ^ n * c)⁻¹ := by group

theorem c_pow_mul_s (n : ℕ) :
    c ^ n * s = s * (c ^ n)⁻¹ := by
  calc
    c ^ n * s = s * (s * c ^ n * s) := by
      calc
        c ^ n * s = (s * s) * c ^ n * s := by
          rw [s_sq]
          simp
        _ = s * (s * c ^ n * s) := by simp [mul_assoc]
    _ = s * (c ^ n)⁻¹ := by rw [s_conj_c_pow]

theorem c_pow_mul_s_mul_c_pow (i j : Fin 6) :
    c ^ (i : ℕ) * (s * c ^ (j : ℕ)) =
      s * c ^ (((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6) := by
  calc
    c ^ (i : ℕ) * (s * c ^ (j : ℕ)) =
        (c ^ (i : ℕ) * s) * c ^ (j : ℕ) := by simp [mul_assoc]
    _ = (s * (c ^ (i : ℕ))⁻¹) * c ^ (j : ℕ) := by
      rw [c_pow_mul_s]
    _ = s * (c ^ ((6 - (i : ℕ)) % 6) * c ^ (j : ℕ)) := by
      rw [c_pow_inv_fin]
      simp [mul_assoc]
    _ = s * c ^ (((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6) := by
      rw [c_pow_add_mod]

theorem c_pow_mul_c_pow (i j : Fin 6) :
    c ^ (i : ℕ) * c ^ (j : ℕ) =
      c ^ (((i : ℕ) + (j : ℕ)) % 6) := by
  exact c_pow_add_mod (i : ℕ) (j : ℕ)

theorem s_mul_c_pow_mul_c_pow (i j : Fin 6) :
    (s * c ^ (i : ℕ)) * c ^ (j : ℕ) =
      s * c ^ (((i : ℕ) + (j : ℕ)) % 6) := by
  rw [mul_assoc, c_pow_add_mod]

theorem s_mul_c_pow_mul_s_mul_c_pow (i j : Fin 6) :
    (s * c ^ (i : ℕ)) * (s * c ^ (j : ℕ)) =
      c ^ (((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6) := by
  calc
    (s * c ^ (i : ℕ)) * (s * c ^ (j : ℕ)) =
        (s * c ^ (i : ℕ) * s) * c ^ (j : ℕ) := by simp [mul_assoc]
    _ = (c ^ (i : ℕ))⁻¹ * c ^ (j : ℕ) := by rw [s_conj_c_pow]
    _ = c ^ ((6 - (i : ℕ)) % 6) * c ^ (j : ℕ) := by
      rw [c_pow_inv_fin]
    _ = c ^ (((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6) := by
      rw [c_pow_add_mod]

theorem t_sq : t * t = 1 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> rfl

theorem st_order_six : (s * t) ^ 6 = 1 := by
  have hst : s * t = c := by
    dsimp [t]
    calc
      s * (s * c) = (s * s) * c := by simp [mul_assoc]
      _ = 1 * c := by rw [s_sq]
      _ = c := by simp
  rw [hst]
  exact c_pow_six

/-- The explicit 12 Weyl normal form elements indexed by ZMod 6 × Bool. -/
noncomputable def weylNF (k : ZMod 6) (refl : Bool) : SplitOctF2Aut :=
  if refl then s * c ^ k.val else c ^ k.val

/-- All 12 Weyl normal form elements are strictly distinct. -/
theorem c_pow_zmod_injective :
    Function.Injective (fun k : ZMod 6 => c ^ k.val) := by
  intro i j h
  have hk : c ^ (i.val : ℕ) = c ^ (j.val : ℕ) := h
  have hij : (⟨i.val, i.isLt⟩ : Fin 6) = ⟨j.val, j.isLt⟩ :=
    c_pow_injective hk
  exact (ZMod.val_injective 6) (congrArg Fin.val hij)

theorem refl_pow_ne_rot_pow (i j : Fin 6) :
    s * c ^ (i : ℕ) ≠ c ^ (j : ℕ) := by
  intro h
  have hs : s = c ^ (j : ℕ) * (c ^ (i : ℕ))⁻¹ := by
    calc
      s = s * 1 := by simp
      _ = s * (c ^ (i : ℕ) * (c ^ (i : ℕ))⁻¹) := by simp
      _ = (s * c ^ (i : ℕ)) * (c ^ (i : ℕ))⁻¹ := by
        simp [mul_assoc]
      _ = c ^ (j : ℕ) * (c ^ (i : ℕ))⁻¹ := by rw [h]
  rw [c_pow_inv_fin i] at hs
  let k : Fin 6 :=
    ⟨((j : ℕ) + (6 - (i : ℕ)) % 6) % 6,
      Nat.mod_lt _ (by norm_num)⟩
  have hsk : s = c ^ (k : ℕ) := by
    simpa [k] using hs.trans (c_pow_add_mod (j : ℕ) ((6 - (i : ℕ)) % 6))
  exact s_ne_c_pow k hsk

theorem weylNF_injective :
    Function.Injective (fun (p : ZMod 6 × Bool) => weylNF p.1 p.2) := by
  rintro ⟨k₁, b₁⟩ ⟨k₂, b₂⟩ h
  cases b₁ <;> cases b₂
  · exact Prod.ext (c_pow_zmod_injective h) rfl
  · exfalso
    have h' : c ^ k₁.val = s * c ^ k₂.val := by
      simpa [weylNF] using h
    exact refl_pow_ne_rot_pow
      ⟨k₂.val, k₂.isLt⟩ ⟨k₁.val, k₁.isLt⟩ h'.symm
  · exfalso
    have h' : s * c ^ k₁.val = c ^ k₂.val := by
      simpa [weylNF] using h
    exact refl_pow_ne_rot_pow
      ⟨k₁.val, k₁.isLt⟩ ⟨k₂.val, k₂.isLt⟩ h'
  · have hk := congrArg (fun f : SplitOctF2Aut => s⁻¹ * f) h
    simp [weylNF] at hk
    exact Prod.ext (c_pow_zmod_injective hk) rfl

noncomputable def weylNFEquiv :
    (ZMod 6 × Bool) ≃ Set.range (fun p : ZMod 6 × Bool => weylNF p.1 p.2) :=
  Equiv.ofInjective _ weylNF_injective

noncomputable instance : Fintype (Set.range (fun p : ZMod 6 × Bool => weylNF p.1 p.2)) :=
  Set.Finite.fintype (Set.finite_range _)

theorem weylNF_image_card :
    Fintype.card (Set.range (fun p : ZMod 6 × Bool => weylNF p.1 p.2)) = 12 := by
  calc
    Fintype.card (Set.range (fun p : ZMod 6 × Bool => weylNF p.1 p.2)) =
        Fintype.card (ZMod 6 × Bool) := (Fintype.card_congr weylNFEquiv).symm
    _ = 12 := by rw [Fintype.card_prod, ZMod.card, Fintype.card_bool]

/-- The 12-element Weyl group W(G₂) as a concrete subtype of SplitOctF2Aut. -/
def weylG2Subgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure {s, t}

theorem s_mem_weylG2Subgroup : s ∈ weylG2Subgroup := by
  exact Subgroup.subset_closure (by simp)

theorem t_mem_weylG2Subgroup : t ∈ weylG2Subgroup := by
  exact Subgroup.subset_closure (by simp)

theorem c_mem_weylG2Subgroup : c ∈ weylG2Subgroup := by
  have hs : s ∈ Subgroup.closure {s, t} := s_mem_weylG2Subgroup
  have ht : t ∈ Subgroup.closure {s, t} := t_mem_weylG2Subgroup
  have hst : c = s * t := by
    dsimp [t]
    calc
      c = (s * s) * c := by rw [s_sq]; simp
      _ = s * (s * c) := by simp [mul_assoc]
  rw [hst]
  exact Subgroup.mul_mem _ hs ht

theorem weylNF_mem_weylG2Subgroup
    (k : ZMod 6) (refl : Bool) :
    weylNF k refl ∈ weylG2Subgroup := by
  by_cases h : refl
  · simp [weylNF, h]
    exact Subgroup.mul_mem _ s_mem_weylG2Subgroup
      (Subgroup.pow_mem _ c_mem_weylG2Subgroup _)
  · simp [weylNF, h]
    exact Subgroup.pow_mem _ c_mem_weylG2Subgroup _

theorem weylNF_mul_rot_rot (k l : ZMod 6) :
    weylNF k false * weylNF l false = weylNF (k + l) false := by
  simp [weylNF, c_pow_add_mod, ZMod.val_add]

theorem weylNF_mul_refl_rot (k l : ZMod 6) :
    weylNF k true * weylNF l false = weylNF (k + l) true := by
  simp [weylNF, c_pow_add_mod, ZMod.val_add, mul_assoc]

theorem weylNF_mul_rot_refl_exists (k l : ZMod 6) :
    ∃ m : ZMod 6,
      weylNF k false * weylNF l true = weylNF m true := by
  let i : Fin 6 := ⟨k.val, k.isLt⟩
  let j : Fin 6 := ⟨l.val, l.isLt⟩
  let n : ℕ := ((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6
  let m : ZMod 6 := n
  refine ⟨m, ?_⟩
  have hn : n < 6 := by
    dsimp [n]
    exact Nat.mod_lt _ (by norm_num)
  have hm : m.val = n := by
    rw [show m = (n : ZMod 6) by rfl, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hn
  change c ^ k.val * (s * c ^ l.val) = s * c ^ m.val
  rw [hm]
  simpa [i, j, n] using c_pow_mul_s_mul_c_pow i j

theorem weylNF_mul_refl_refl_exists (k l : ZMod 6) :
    ∃ m : ZMod 6,
      weylNF k true * weylNF l true = weylNF m false := by
  let i : Fin 6 := ⟨k.val, k.isLt⟩
  let j : Fin 6 := ⟨l.val, l.isLt⟩
  let n : ℕ := ((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6
  let m : ZMod 6 := n
  refine ⟨m, ?_⟩
  have hn : n < 6 := by
    dsimp [n]
    exact Nat.mod_lt _ (by norm_num)
  have hm : m.val = n := by
    rw [show m = (n : ZMod 6) by rfl, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hn
  change (s * c ^ k.val) * (s * c ^ l.val) = c ^ m.val
  rw [hm]
  simpa [i, j, n] using s_mul_c_pow_mul_s_mul_c_pow i j

theorem weylNF_mul_exists
    (k l : ZMod 6) (b d : Bool) :
    ∃ m : ZMod 6, ∃ e : Bool,
      weylNF k b * weylNF l d = weylNF m e := by
  cases b <;> cases d
  · exact ⟨k + l, false, weylNF_mul_rot_rot k l⟩
  · obtain ⟨m, hm⟩ := weylNF_mul_rot_refl_exists k l
    exact ⟨m, true, hm⟩
  · exact ⟨k + l, true, weylNF_mul_refl_rot k l⟩
  · obtain ⟨m, hm⟩ := weylNF_mul_refl_refl_exists k l
    exact ⟨m, false, hm⟩

theorem weylNF_inv_exists (k : ZMod 6) (b : Bool) :
    ∃ m : ZMod 6, ∃ e : Bool,
      (weylNF k b)⁻¹ = weylNF m e := by
  cases b
  · let i : Fin 6 := ⟨k.val, k.isLt⟩
    let n : ℕ := (6 - (i : ℕ)) % 6
    let m : ZMod 6 := n
    refine ⟨m, false, ?_⟩
    have hn : n < 6 := by
      dsimp [n]
      exact Nat.mod_lt _ (by norm_num)
    have hm : m.val = n := by
      rw [show m = (n : ZMod 6) by rfl, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt hn
    change (c ^ k.val)⁻¹ = c ^ m.val
    rw [hm]
    simpa [i, n] using c_pow_inv_fin i
  · refine ⟨k, true, ?_⟩
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    change (s * c ^ k.val) * (s * c ^ k.val) = 1
    let i : Fin 6 := ⟨k.val, k.isLt⟩
    have h := s_mul_c_pow_mul_s_mul_c_pow i i
    have hz : ((6 - (i : ℕ)) % 6 + (i : ℕ)) % 6 = 0 := by
      omega
    simpa [i, hz] using h

theorem weylG2Subgroup_coverage (x : SplitOctF2Aut)
    (hx : x ∈ weylG2Subgroup) :
    ∃ k : ZMod 6, ∃ b : Bool, x = weylNF k b := by
  refine @Subgroup.closure_induction SplitOctF2Aut _ {s, t}
    (fun x _ => ∃ k : ZMod 6, ∃ b : Bool, x = weylNF k b)
    ?_ ?_ ?_ ?_ x hx
  · intro y hy
    rcases hy with rfl | rfl
    · exact ⟨0, true, by simp [weylNF, s]
        ⟩
    · refine ⟨1, true, ?_⟩
      change s * c = s * c ^ (1 : ℕ)
      simp
  · exact ⟨0, false, by simp [weylNF]
      ⟩
  · intro y z _ _ hy hz
    rcases hy with ⟨k, b, hy⟩
    rcases hz with ⟨l, d, hz⟩
    obtain ⟨m, e, h⟩ := weylNF_mul_exists k l b d
    exact ⟨m, e, by rw [hy, hz, h]⟩
  · intro y _ ⟨k, b, h⟩
    obtain ⟨m, e, hi⟩ := weylNF_inv_exists k b
    exact ⟨m, e, h ▸ hi⟩

theorem weylG2Subgroup_coverage_pair (x : weylG2Subgroup) :
    ∃ p : ZMod 6 × Bool, x.1 = weylNF p.1 p.2 := by
  rcases weylG2Subgroup_coverage x.1 x.2 with ⟨k, b, h⟩
  exact ⟨(k, b), h⟩

noncomputable instance : Finite weylG2Subgroup :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance : Fintype weylG2Subgroup := Fintype.ofFinite _

noncomputable def weylNFCoordinates (x : weylG2Subgroup) : ZMod 6 × Bool :=
  Classical.choose (weylG2Subgroup_coverage_pair x)

theorem weylNFCoordinates_spec (x : weylG2Subgroup) :
    x.1 = weylNF (weylNFCoordinates x).1 (weylNFCoordinates x).2 :=
  Classical.choose_spec (weylG2Subgroup_coverage_pair x)

theorem weylNFCoordinates_injective :
    Function.Injective weylNFCoordinates := by
  intro x y h
  apply Subtype.ext
  calc
    x.1 = weylNF (weylNFCoordinates x).1 (weylNFCoordinates x).2 :=
      weylNFCoordinates_spec x
    _ = weylNF (weylNFCoordinates y).1 (weylNFCoordinates y).2 := by
      exact congrArg (fun p : ZMod 6 × Bool => weylNF p.1 p.2) h
    _ = y.1 := (weylNFCoordinates_spec y).symm

theorem weylG2_card_le_twelve :
    Fintype.card weylG2Subgroup ≤ 12 := by
  calc
    Fintype.card weylG2Subgroup ≤ Fintype.card (ZMod 6 × Bool) :=
      Fintype.card_le_of_injective _ weylNFCoordinates_injective
    _ = 12 := by rw [Fintype.card_prod, ZMod.card, Fintype.card_bool]

theorem weylG2_card_ge_twelve :
    12 ≤ Fintype.card weylG2Subgroup := by
  have hinj : Function.Injective
      (fun p : ZMod 6 × Bool =>
        (⟨weylNF p.1 p.2, weylNF_mem_weylG2Subgroup p.1 p.2⟩ : weylG2Subgroup)) := by
    intro p q h
    apply weylNF_injective
    exact congrArg Subtype.val h
  calc
    12 = Fintype.card (ZMod 6 × Bool) := by
      rw [Fintype.card_prod, ZMod.card, Fintype.card_bool]
    _ ≤ Fintype.card weylG2Subgroup := Fintype.card_le_of_injective _ hinj

theorem weylG2_card_eq_twelve :
    Fintype.card weylG2Subgroup = 12 := by
  exact le_antisymm weylG2_card_le_twelve weylG2_card_ge_twelve

theorem weyl_param_card_eq_twelve : Fintype.card (ZMod 6 × Bool) = 12 := by
  rw [Fintype.card_prod, ZMod.card, Fintype.card_bool]

end InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
