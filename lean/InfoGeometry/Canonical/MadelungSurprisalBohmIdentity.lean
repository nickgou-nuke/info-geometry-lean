import InfoGeometry.Canonical.MadelungScaleQuantum
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Bohm potential as a surprisal differential readout

For a positive density written as `ρ = exp (-K)`, this file records the
one-dimensional logarithmic identity expressing the Madelung/Bohm potential
through the first two derivatives of the surprisal `K`.

This is deliberately independent of modular Berezinians and of any coupled
two-sheet construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.MadelungSurprisalBohmIdentity

open InfoGeometry.Canonical.MadelungScaleQuantum

theorem madelungQuantumPotential_exp_neg_surprisal
    (K : ℝ → ℝ) (ℏ m q : ℝ) (hm : m ≠ 0)
    (hK : HasDerivAt K (deriv K q) q)
    (hK2 : HasDerivAt (deriv K) (deriv (deriv K) q) q)
    (hderiv : ∀ x,
      deriv (fun y => Real.exp (-K y / 2)) x =
        Real.exp (-K x / 2) * (-(deriv K x) / 2)) :
    madelungQuantumPotential (fun x => Real.exp (-K x)) ℏ m q =
      (ℏ ^ 2 / (4 * m)) * deriv (deriv K) q -
        (ℏ ^ 2 / (8 * m)) * (deriv K q) ^ 2 := by
  have hhalf : HasDerivAt (fun x => -K x / 2)
      (-(deriv K q) / 2) q := by
    simpa [smul_eq_mul, div_eq_mul_inv] using
      (hK.neg.div_const (2 : ℝ))
  have hsqrt : (fun x => Real.sqrt (Real.exp (-K x))) =
      (fun x => Real.exp (-K x / 2)) := by
    funext x
    rw [← Real.exp_half]
  have hf : HasDerivAt (fun x => Real.exp (-K x / 2))
      (Real.exp (-K q / 2) * (-(deriv K q) / 2)) q := by
    simpa using hhalf.exp
  have hsecond : HasDerivAt (deriv (fun x => Real.exp (-K x / 2)))
      (Real.exp (-K q / 2) * (-(deriv (deriv K) q) / 2) +
        (Real.exp (-K q / 2) * (-(deriv K q) / 2)) *
          (-(deriv K q) / 2)) q := by
    have hinner : HasDerivAt (fun x => -(deriv K x) / 2)
        (-(deriv (deriv K) q) / 2) q := by
      simpa [smul_eq_mul, div_eq_mul_inv] using hK2.neg.div_const (2 : ℝ)
    have hmul := hf.mul hinner
    have hfun : deriv (fun x => Real.exp (-K x / 2)) =
        (fun x => Real.exp (-K x / 2) * (-(deriv K x) / 2)) := by
      funext x
      exact hderiv x
    rw [hfun]
    convert hmul using 1 <;>
      simp [Pi.mul_apply, mul_add, add_mul, mul_assoc,
        mul_comm, mul_left_comm] <;>
      ring
  rw [madelungQuantumPotential, hsqrt]
  rw [hsecond.deriv]
  have hne : Real.exp (-K q / 2) ≠ 0 := Real.exp_ne_zero _
  rw [← Real.exp_half]
  field_simp [hne, hm]
  ring

end InfoGeometry.Canonical.MadelungSurprisalBohmIdentity
