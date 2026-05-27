import Mathlib

/-!
# InfoGeometry.Canonical.CantorModularScoreFunctional

Finite dyadic-cylinder modular score functional:

* local density `Δ_{w,n} = 2^n * 1_{ {w} }`,
* centered score `Y_{w,n} = Δ_{w,n} - 1`,
* functional `η_{w,n}(f) = ∫ f Y_{w,n} dμ_n`.

Here `μ_n` is the uniform measure on `Fin (2^n)`.
-/

namespace InfoGeometry.Canonical.CantorModularScoreFunctional

open scoped BigOperators

noncomputable section

/-- Uniform finite average on `Fin (2^n)`. -/
def muAvg (n : ℕ) (f : Fin (2 ^ n) → ℝ) : ℝ :=
  ((2 ^ n : ℝ)⁻¹) * ∑ i : Fin (2 ^ n), f i

/-- Local point-state density `Δ_{w,n}`. -/
def deltaDensity (n : ℕ) (w : Fin (2 ^ n)) : Fin (2 ^ n) → ℝ :=
  fun i => if i = w then (2 ^ n : ℝ) else 0

/-- Centered modular score `Y_{w,n} = Δ_{w,n} - 1`. -/
def centeredScore (n : ℕ) (w : Fin (2 ^ n)) : Fin (2 ^ n) → ℝ :=
  fun i => deltaDensity n w i - 1

/-- Finite modular score functional `η_{w,n}`. -/
def eta (n : ℕ) (w : Fin (2 ^ n)) (f : Fin (2 ^ n) → ℝ) : ℝ :=
  muAvg n (fun i => f i * centeredScore n w i)

/--
Exact finite score identity:
`η_{w,n}(f) = f(w) - μ_n(f)`.
-/
theorem eta_eq_eval_sub_avg
    (n : ℕ) (w : Fin (2 ^ n)) (f : Fin (2 ^ n) → ℝ) :
    eta n w f = f w - muAvg n f := by
  unfold eta muAvg centeredScore deltaDensity
  have hN : (2 ^ n : ℝ) ≠ 0 := by positivity
  have hsumDelta :
      ∑ i : Fin (2 ^ n), f i * (if i = w then (2 ^ n : ℝ) else 0) = f w * (2 ^ n : ℝ) := by
    simpa [Finset.mul_sum] using
      (Finset.sum_ite_eq (fun i : Fin (2 ^ n) => f i * (2 ^ n : ℝ)) w)
  calc
    (↑(2 ^ n))⁻¹ * ∑ i : Fin (2 ^ n), (f i * ((if i = w then ↑(2 ^ n) else 0) - 1))
        = (↑(2 ^ n))⁻¹ *
            (∑ i : Fin (2 ^ n), f i * (if i = w then ↑(2 ^ n) else 0)
              - ∑ i : Fin (2 ^ n), f i) := by
              simp [mul_sub, Finset.sum_sub_distrib]
    _ = (↑(2 ^ n))⁻¹ * (f w * (2 ^ n : ℝ) - ∑ i : Fin (2 ^ n), f i) := by
          rw [hsumDelta]
    _ = (↑(2 ^ n))⁻¹ * (f w * (2 ^ n : ℝ)) - (↑(2 ^ n))⁻¹ * ∑ i : Fin (2 ^ n), f i := by
          ring
    _ = f w - (↑(2 ^ n))⁻¹ * ∑ i : Fin (2 ^ n), f i := by
          field_simp [hN]
    _ = f w - muAvg n f := by rfl

/-- Centered score has zero total mass on the constant observable `1`. -/
theorem eta_one_eq_zero
    (n : ℕ) (w : Fin (2 ^ n)) :
    eta n w (fun _ => (1 : ℝ)) = 0 := by
  rw [eta_eq_eval_sub_avg]
  unfold muAvg
  simp

end

end InfoGeometry.Canonical.CantorModularScoreFunctional
