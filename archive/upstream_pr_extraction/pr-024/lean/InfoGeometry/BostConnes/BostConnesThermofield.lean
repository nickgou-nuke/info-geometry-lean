import Mathlib.NumberTheory.LSeries.Dirichlet
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.BostConnes.BostConnesParity

/-!
# Bost-Connes Thermofield Dynamics: Liouville Grading & Modular Flow

This file records a theorem-honest arithmetic model for the commutation of the
Liouville grading Γ with modular flow σₜ, using the arithmetic foundation from
`BostConnesParity.lean`.

Key results:
  1. Γ = liouville n = (-1)^Ω(n) (everywhere-defined chiral grading)
  2. μ(n) = squarefreeProj n * liouville n (Möbius = squarefree projection)
  3. σₜ(μₙ) = n^(it) μₙ (KMS time evolution)
  4. [Γ, σₜ] = 0 (commutation theorem)
  5. Witten index W = Σ μ(n) n^{-β} = 1/ζ(β) (Fredholm determinant)

Interpretive glossary used in this file:
  - λ(n) is the full Z₂ grading by prime-factor parity
  - squarefreeProj n is the squarefree projector
  - μ(n) is the product of those two arithmetic factors

References:
  - BostConnesModularFlow.lean (existing modular flow)
  - BostConnesParity.lean (μ = squarefreeProj × λ theorem)
  - BostConnesSystem.lean (liouville definition)
-/

open ArithmeticFunction BigOperators InfoGeometry.Arithmetic.BostConnesSystem
open scoped ArithmeticFunction.Moebius
open scoped LSeries.notation

namespace BostConnesThermofield

/--
Bost-Connes algebra generators.

μₙ: isometry for sector n, satisfying μₙ*μₙ = 1
e(r): additive group element for r ∈ ℚ/ℤ
-/
structure BostConnesGenerator where
  mu_n : ℕ  -- sector index
  sector_pos : 0 < mu_n

namespace BostConnesGenerator

theorem sector_ne_zero (g : BostConnesGenerator) : g.mu_n ≠ 0 :=
  Nat.ne_of_gt g.sector_pos

end BostConnesGenerator

/--
Modular flow σₜ: KMS time evolution at inverse temperature β.

Action on generators:
  σₜ(μₙ) = n^(it) μₙ
  σₜ(e(r)) = e(n^t r)
-/
noncomputable def modular_flow (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * t * Real.log n)

/--
Modular flow phase factor χₜ(n) = n^(it).

This is the diagonal action on the Bost-Connes algebra generators.
-/
noncomputable def modular_phase (t : ℝ) (n : ℕ) : ℂ :=
  modular_flow t n

/-- The modular phase at time `0` is `1`. -/
theorem modular_phase_zero (n : ℕ) : modular_phase 0 n = 1 := by
  simp [modular_phase, modular_flow]

/--
Commutation statement for the scalar grading and modular phase.

The Liouville grading commutes with modular flow because
λ(n) ∈ {±1} is a central scalar in ℂ.
-/
theorem liouville_commutes_modular_flow (n : ℕ) (t : ℝ) :
    (InfoGeometry.BostConnes.liouvilleParity n : ℂ) * modular_phase t n =
      modular_phase t n * (InfoGeometry.BostConnes.liouvilleParity n : ℂ) := by
  rw [mul_comm]

/--
Witten-index-style Dirichlet series attached to μ(n).

W(β) = Σ_{n=1}^∞ μ(n) n^{-β} = 1/ζ(β)

This file uses the standard arithmetic Dirichlet series expression and records
its intended interpretation separately from the proved identity.
-/
noncomputable def witten_index (beta : ℝ) : ℝ :=
  ∑' n : ℕ+, (ArithmeticFunction.moebius n.val : ℝ) * (n.val : ℝ) ^ (-beta)

/--
Reciprocal-zeta identity for the Möbius L-series.

This follows from the Dirichlet series identity:
  Σ μ(n) n^{-s} = 1/ζ(s)

and the Euler product over primes:
  1/ζ(s) = ∏_p (1 - p^{-s})

The final phrase is interpretive background rather than additional formal
content of the theorem.
-/
theorem witten_index_eq_reciprocal_zeta (beta : ℝ) (hbeta : beta > 1) :
    L ↗μ (beta : ℂ) = (riemannZeta (beta : ℂ))⁻¹ := by
  /-
  The exact mathlib identity is for the Möbius L-series:
    L 1 s * L ↗μ s = 1.
  We transport it to the reciprocal zeta statement via
  `L 1 s = riemannZeta s`.
  -/
  have hs : 1 < (beta : ℂ).re := by simpa using hbeta
  have hmul : riemannZeta (beta : ℂ) * L ↗μ (beta : ℂ) = 1 := by
    have h := LSeries_one_mul_Lseries_moebius (s := (beta : ℂ)) hs
    rw [LSeries_one_eq_riemannZeta hs] at h
    simpa [mul_comm] using h
  have hmul' : L ↗μ (beta : ℂ) * riemannZeta (beta : ℂ) = 1 := by
    simpa [mul_comm] using hmul
  have hz : riemannZeta (beta : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  exact (mul_eq_one_iff_eq_inv₀ hz).mp hmul'

theorem thermal_anomaly_protection :
    ∀ t : ℝ, ∀ n : ℕ,
      (InfoGeometry.BostConnes.liouvilleParity n : ℂ) * modular_phase t n =
        modular_phase t n * (InfoGeometry.BostConnes.liouvilleParity n : ℂ) := by
  intro t n
  exact liouville_commutes_modular_flow n t

/--
Möbius/Liouville decomposition statement.

The Möbius function decomposes as:
  μ(n) = squarefreeProj n × λ(n)

where:
  - λ(n) = (-1)^Ω(n) is the everywhere-defined parity factor
  - squarefreeProj n = 1 if n is squarefree, 0 otherwise

This shows μ is the squarefree projection of the full parity grading.
-/
theorem moebius_decomposition (n : ℕ) :
    ArithmeticFunction.moebius n =
      InfoGeometry.BostConnes.squarefreeProj n *
        InfoGeometry.BostConnes.liouvilleParity n := by
  exact InfoGeometry.BostConnes.moebius_eq_squarefreeProj_mul_liouvilleParity n

/--
Fermionic sectors: μ(n) ≠ 0 (squarefree integers).

This is the squarefree sector selected by the arithmetic predicate.
-/
def is_fermionic_sector (n : ℕ) : Prop :=
  Squarefree n

/--
Even-parity sectors: λ(n) = +1.

Note: this includes both squarefree and non-squarefree integers.
-/
def is_bosonic_sector (n : ℕ) : Prop :=
  InfoGeometry.BostConnes.liouvilleParity n = 1

/--
Negative Möbius sectors: μ(n) = -1 (odd ω(n), squarefree).

This is the negative squarefree branch of the arithmetic decomposition.
-/
def is_mobius_fermionic_sector (n : ℕ) : Prop :=
  ArithmeticFunction.moebius n = -1

/--
Positive Möbius sectors: μ(n) = +1 (even ω(n), squarefree).
-/
def is_mobius_bosonic_sector (n : ℕ) : Prop :=
  ArithmeticFunction.moebius n = 1

/--
Vanishing of Möbius on non-squarefree integers.

On non-squarefree integers, μ(n) = 0 because the Pauli projector
annihilates states with repeated prime occupation.

The exterior-algebra analogy is interpretive background only.
-/
theorem pauli_exclusion (n : ℕ) :
    ¬Squarefree n → ArithmeticFunction.moebius n = 0 := by
  intro h
  exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree h

/--
Count fermionic (squarefree) sectors up to N.

This counts the squarefree branch up to N.
-/
noncomputable def count_fermionic (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (fun n => n > 0 ∧ Squarefree n) |>.card

/--
Count bosonic sectors (λ = +1) up to N.
-/
noncomputable def count_bosonic (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter
      (fun n => n > 0 ∧ InfoGeometry.BostConnes.liouvilleParity n = 1) |>.card

noncomputable def witten_index_approx (N : ℕ) (beta : ℝ) : ℝ :=
  ((Finset.range (N + 1)).filter (fun n => n > 0)).sum
    (fun n => (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-beta))

/-- The Liouville grading has unit square, so it is a genuine `±1` parity. -/
theorem liouvilleParity_sq (n : ℕ) :
    (InfoGeometry.BostConnes.liouvilleParity n : ℤ) *
      InfoGeometry.BostConnes.liouvilleParity n = 1 := by
  rw [InfoGeometry.BostConnes.liouvilleParity]
  rw [← pow_add]
  have h : ArithmeticFunction.cardFactors n + ArithmeticFunction.cardFactors n =
      2 * ArithmeticFunction.cardFactors n := by omega
  rw [h, pow_mul]
  norm_num

/-- The duplicated grading statement is reduced to `liouvilleParity_sq`. -/
theorem thermofield_preserves_grading (n : ℕ) :
    (InfoGeometry.BostConnes.liouvilleParity n : ℤ) *
      InfoGeometry.BostConnes.liouvilleParity n = 1 := by
  exact liouvilleParity_sq n

end BostConnesThermofield
