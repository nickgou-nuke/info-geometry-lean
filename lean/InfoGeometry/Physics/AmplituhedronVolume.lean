import Mathlib
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Amplituhedron volume — colimit statement surface

The old file depended on an unavailable log-CFT monodromy packet and promoted a
formal trace calculation into a zeta/amplituhedron theorem.  This replacement
keeps only the Dirichlet-term expression and records the zeta identification as
a categorical/Hestenes--Krein colimit statement socket.
-/

namespace InfoGeometry.Physics.AmplituhedronVolume

open InfoGeometry.Clifford.LogCftMonodromy

/-- Conformal weight attached to the spectral integer `n`. -/
noncomputable def conformalWeight (β : ℂ) (n : ℕ) : ℂ :=
  - (Complex.I * β * Real.log (n : ℝ)) / (2 * Real.pi)

/-- The formal Dirichlet term used by the volume readout. -/
noncomputable def dirichletTerm (β : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-β * Real.log (n : ℝ))

/-- The normalized trace of the rank-two logarithmic-CFT monodromy is exactly
the corresponding Dirichlet term. This is a termwise algebraic identity and
does not assert a global zeta/amplituhedron comparison. -/
theorem normalized_trace_eq_dirichlet_term (β : ℂ) (n : ℕ) :
    (1 / 2 : ℂ) *
        (hadjiivanovMonodromy (conformalWeight β n)).trace =
      Complex.exp (-β * Real.log (n : ℝ)) := by
  simp [hadjiivanovMonodromy, upperJordan, lcftPhase, conformalWeight]
  field_simp
  rw [Complex.I_sq]
  ring

/-- The formal amplituhedron-style trace sum, represented only as its intended
Dirichlet series expression. -/
noncomputable def amplituhedronVolume (β : ℂ) : ℂ :=
  ∑' n : ℕ, dirichletTerm β (n + 1)

/-- Readout of the formal volume series. -/
theorem amplituhedronVolume_eq_zeta_sum (β : ℂ) :
    amplituhedronVolume β = ∑' n : ℕ, Complex.exp (-β * Real.log ((n + 1 : ℕ) : ℝ)) := by
  simp [amplituhedronVolume, dirichletTerm]

/-- Statement shape for the missing categorical/Hestenes--Krein colimit
 identification with the Riemann zeta readout on its guarded domain. -/
def amplituhedronVolume_zeta_statement : Prop :=
  ∀ β : ℂ, 1 < β.re → amplituhedronVolume β = riemannZeta β

/-! ### Zeta identification theorem

This closes the statement socket: the formal amplituhedron volume series
is exactly the Riemann zeta function on the half-plane `1 < β.re`.

The proof mirrors `bostConnesPartition_eq_riemannZeta_re` but works directly
over `ℂ` (no real-part extraction), because `amplituhedronVolume` is already
defined as a complex Dirichlet series.
-/

/-- The Dirichlet term equals the complex power `1 / ((n+1) : ℂ)^β`.

This is the complex analogue of the real-power identity used in
`bostConnesPartition_eq_riemannZeta_re`. It relies on
`Complex.ofReal_log` to identify `Complex.log ((n+1 : ℕ) : ℂ)` with
`(Real.log ((n+1 : ℕ) : ℝ) : ℂ)` for positive integers `n+1`.
-/
theorem dirichletTerm_eq_inv_cpow (β : ℂ) (n : ℕ) :
    dirichletTerm β (n + 1) = 1 / (((n + 1 : ℕ) : ℂ) ^ β) := by
  dsimp [dirichletTerm]
  have hn_pos : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have h_log : (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) = Complex.log ((n + 1 : ℕ) : ℂ) := by
    rw [Complex.ofReal_log hn_pos]
    push_cast
    rfl
  have hnz : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    norm_cast
  have hpow : (((n + 1 : ℕ) : ℂ) ^ β) = Complex.exp (Complex.log ((n + 1 : ℕ) : ℂ) * β) :=
    Complex.cpow_def_of_ne_zero hnz β
  rw [hpow]
  rw [one_div, ← Complex.exp_neg]
  congr 1
  rw [h_log]
  simp [mul_comm]

/-- The formal amplituhedron volume equals the Riemann zeta function
on the half-plane `1 < β.re`.

This is the complex Dirichlet series identity:
`Σ' n : ℕ, (n+1)^(-β) = ζ(β)` for `1 < β.re`.
-/
theorem amplituhedronVolume_zeta (β : ℂ) (hβ : 1 < β.re) :
    amplituhedronVolume β = riemannZeta β := by
  rw [amplituhedronVolume_eq_zeta_sum]
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ β)) :=
    (Complex.summable_one_div_nat_cpow.mpr hβ)
  have hsum : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) ^ β)) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1 (G := ℂ)).mpr hbase)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hβ]
  apply tsum_congr
  intro n
  simpa [dirichletTerm, Nat.cast_add, Nat.cast_one] using dirichletTerm_eq_inv_cpow β n

end InfoGeometry.Physics.AmplituhedronVolume
