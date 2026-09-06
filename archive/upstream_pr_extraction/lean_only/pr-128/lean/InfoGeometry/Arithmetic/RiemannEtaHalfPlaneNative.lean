import InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-!
# Native eta--zeta identity on the absolutely convergent half-plane

This owner proves only the `Re(s) > 1` identity by parity splitting of an
absolutely summable Dirichlet series.  It does not extend the identity across
the line `Re(s) = 1` and does not discharge the analytic-continuation debt.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannEtaHalfPlaneNative

open InfoGeometry.Arithmetic.RiemannZetaEquivalences

private theorem odd_shift_term (n : ℕ) (s : ℂ) :
    (1 : ℂ) / ((((2 * n + 1 : ℕ) : ℂ) + 1) ^ s) =
      (2 : ℂ) ^ (-s) * (1 / (((n : ℂ) + 1) ^ s)) := by
  have hnat : (((2 * n + 1 : ℕ) : ℂ) + 1) =
      (2 : ℂ) * ((n : ℂ) + 1) := by
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring
  have hmul : ((2 : ℂ) * ((n : ℂ) + 1)) ^ s =
      (2 : ℂ) ^ s * (((n : ℂ) + 1) ^ s) := by
    simpa using
      (Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ))
        (b := (n : ℝ) + 1) (r := s) (by norm_num) (by positivity))
  rw [hnat, hmul, div_eq_mul_inv, mul_inv_rev]
  simp [Complex.cpow_neg, one_div]
  ac_rfl

theorem dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta
    (s : ℂ) (hs : 1 < s.re) :
    dirichletEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  let f : ℕ → ℂ := fun n => 1 / (((n : ℂ) + 1) ^ s)
  let g : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * f n
  have hf : Summable f := by
    have h0 : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ s)) :=
      (Complex.summable_one_div_nat_cpow (p := s)).2 hs
    have h1 : Summable (fun n : ℕ =>
        1 / (((n + 1 : ℕ) : ℂ) ^ s)) :=
      (summable_nat_add_iff
        (f := fun n : ℕ => 1 / ((n : ℂ) ^ s)) (k := 1)).2 h0
    simpa [f, Nat.cast_add, add_comm, add_left_comm, add_assoc] using h1
  have hfeven : Summable (fun k : ℕ => f (2 * k)) :=
    hf.comp_injective (fun a b h => Nat.mul_left_cancel (by decide : 0 < 2) h)
  have hfodd : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hf.comp_injective (fun a b h => by
      apply Nat.mul_left_cancel (by decide : 0 < 2)
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one, Nat.mul_add,
        add_assoc, add_comm, add_left_comm] using h))
  have hodd : (∑' k : ℕ, f (2 * k + 1)) =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
    have hsum : (∑' k : ℕ, f (2 * k + 1)) =
        ∑' k : ℕ, (2 : ℂ) ^ (-s) *
          (1 / (((k : ℂ) + 1) ^ s)) := by
      refine tsum_congr ?_
      intro n
      simpa [f] using odd_shift_term n s
    calc
      (∑' k : ℕ, f (2 * k + 1)) =
          ∑' k : ℕ, (2 : ℂ) ^ (-s) *
            (1 / (((k : ℂ) + 1) ^ s)) := hsum
      _ = (2 : ℂ) ^ (-s) * ∑' k : ℕ,
          (1 / (((k : ℕ) : ℂ) + 1) ^ s) := by rw [tsum_mul_left]
      _ = (2 : ℂ) ^ (-s) * riemannZeta s := by
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) hs]
  have hg : Summable g := by
    apply Summable.of_norm
    have hnorm := hf.norm
    simpa [g, f, norm_mul] using hnorm
  have hgeven : Summable (fun k : ℕ => g (2 * k)) :=
    hg.comp_injective (fun a b h => Nat.mul_left_cancel (by decide : 0 < 2) h)
  have hgeodd : Summable (fun k : ℕ => g (2 * k + 1)) :=
    hg.comp_injective (fun a b h => by
      apply Nat.mul_left_cancel (by decide : 0 < 2)
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one, Nat.mul_add,
        add_assoc, add_comm, add_left_comm] using h))
  have hdecomp : (∑' k : ℕ, g (2 * k)) +
      ∑' k : ℕ, g (2 * k + 1) = ∑' k : ℕ, g k :=
    tsum_even_add_odd hgeven hgeodd
  have heven : (∑' k : ℕ, g (2 * k)) = ∑' k : ℕ, f (2 * k) := by
    refine tsum_congr ?_
    intro n
    simp [g, f]
  have hgod : (∑' k : ℕ, g (2 * k + 1)) =
      -∑' k : ℕ, f (2 * k + 1) := by
    rw [← tsum_neg]
    refine tsum_congr ?_
    intro n
    have hp : (-1 : ℂ) ^ (2 * n + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    simp [g, f, hp]
  have hsum_f : (∑' k : ℕ, f (2 * k)) +
      ∑' k : ℕ, f (2 * k + 1) = riemannZeta s := by
    calc
      (∑' k : ℕ, f (2 * k)) + ∑' k : ℕ, f (2 * k + 1) =
          ∑' k : ℕ, f k := tsum_even_add_odd hfeven hfodd
      _ = riemannZeta s := by
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) hs]
  calc
    dirichletEta s = ∑' k : ℕ, g k := by
      simp [dirichletEta, g, f, div_eq_mul_inv]
    _ = (∑' k : ℕ, g (2 * k)) + ∑' k : ℕ, g (2 * k + 1) :=
      hdecomp.symm
    _ = (∑' k : ℕ, f (2 * k)) - ∑' k : ℕ, f (2 * k + 1) := by
      rw [heven, hgod]
      ring
    _ = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
      rw [eq_sub_of_add_eq hsum_f, hodd]
      ring
    _ = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
      have hpow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
        rw [show (1 : ℂ) - s = 1 + (-s) by ring,
          Complex.cpow_add _ _ (by norm_num)]
        simp [Complex.cpow_neg]
      rw [hpow]

/-!
The quotient form is valid on the same absolute-convergence half-plane, but
requires a genuine nonvanishing proof for the Euler factor.  This is not an
analytic-continuation theorem: the strict inequality `1 < Re(s)` is retained.
-/

theorem two_cpow_one_sub_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
  have hnorm : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have hexp : 1 - s.re < 0 := by linarith
  have hlt : (2 : ℝ) ^ (1 - s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hne : (2 : ℂ) ^ (1 - s) ≠ 1 := by
    intro h
    rw [h, norm_one] at hnorm
    linarith
  exact sub_ne_zero.mpr hne.symm

theorem riemannZeta_eq_two_cpow_factor_inv_mul_dirichletEta_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s =
      (1 - (2 : ℂ) ^ (1 - s))⁻¹ * dirichletEta s := by
  rw [dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta s hs]
  field_simp [two_cpow_one_sub_ne_zero_of_one_lt_re hs]

end InfoGeometry.Arithmetic.RiemannEtaHalfPlaneNative
