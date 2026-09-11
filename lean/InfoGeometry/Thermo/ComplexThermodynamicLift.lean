import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Thermo.ComplexThermodynamicLift

Proof-only complex lift of the elementary thermodynamic algebra.

This module formalizes the rule:

  real thermodynamic formulas that are algebraic identities
  may be lifted to complex coordinates.

It proves only algebraic identities over `ℂ`.

No zeta theorem.
No analytic continuation.
No self-concordance claim.
No Hilbert--Pólya claim.
No socket.
No certificate.
-/

noncomputable section

namespace InfoGeometry.Thermo.ComplexThermodynamicLift


/-! ## 1. Complex first law algebra -/

/--
Complexified first-law datum.

`β` is inverse temperature / modular scale.
`T` is temperature.
`dS = β dQ`.
`T = β⁻¹`.

This is an algebraic complex lift of the reversible scalar identity.
-/
@[rep_depth thermo]
structure ComplexFirstLawDatum where
  dQ : ℂ
  dS : ℂ
  β : ℂ
  T : ℂ
  firstLaw_inverse : dS = β * dQ
  temperature_eq_inv_beta : T = β⁻¹

namespace ComplexFirstLawDatum

variable (D : ComplexFirstLawDatum)

/--
If `β ≠ 0`, then `T dS = dQ`.

This is the complex algebraic lift of `δQ = T dS`.
-/
@[rep_depth thermo]
theorem temperature_mul_entropy_eq_heat
    (hβ : D.β ≠ 0) :
    D.T * D.dS = D.dQ := by
  rw [D.temperature_eq_inv_beta, D.firstLaw_inverse]
  field_simp [hβ]

/--
If `dQ ≠ 0`, then `β = dS / dQ`.

This is the complex algebraic lift of `β = dS / δQ`.
-/
@[rep_depth thermo]
theorem beta_eq_entropy_div_heat
    (hQ : D.dQ ≠ 0) :
    D.β = D.dS / D.dQ := by
  rw [D.firstLaw_inverse]
  field_simp [hQ]

/--
If `β ≠ 0`, then `T⁻¹ = β`.
-/
@[rep_depth thermo]
theorem inv_temperature_eq_beta
    (hβ : D.β ≠ 0) :
    D.T⁻¹ = D.β := by
  rw [D.temperature_eq_inv_beta]
  field_simp [hβ]

/--
If `β ≠ 0` and `dQ ≠ 0`, then `T⁻¹ = dS / dQ`.
-/
@[rep_depth thermo]
theorem inv_temperature_eq_entropy_div_heat
    (hβ : D.β ≠ 0)
    (hQ : D.dQ ≠ 0) :
    D.T⁻¹ = D.dS / D.dQ := by
  rw [D.inv_temperature_eq_beta hβ]
  exact D.beta_eq_entropy_div_heat hQ

end ComplexFirstLawDatum


/-! ## 2. Complex Bregman algebra -/

/--
Complex Bregman expression associated to an arbitrary potential `Φ`
and an arbitrary gradient field `grad`.

`DΦ(z,w) = Φ z - Φ w - grad w * (z - w)`.

This is only the algebraic expression. Convexity/positivity is not asserted
over `ℂ`.
-/
@[rep_depth thermo]
def complexBregman
    (Φ grad : ℂ → ℂ)
    (z w : ℂ) : ℂ :=
  Φ z - Φ w - grad w * (z - w)

/--
The complex Bregman expression vanishes on the diagonal.
-/
@[rep_depth thermo]
theorem complexBregman_self
    (Φ grad : ℂ → ℂ)
    (z : ℂ) :
    complexBregman Φ grad z z = 0 := by
  unfold complexBregman
  ring

/--
Three-point identity for the complex Bregman expression.

`D(x,z) = D(x,y) + D(y,z) + (grad y - grad z) * (x - y)`.
-/
@[rep_depth thermo]
theorem complexBregman_three_point
    (Φ grad : ℂ → ℂ)
    (x y z : ℂ) :
    complexBregman Φ grad x z =
      complexBregman Φ grad x y
        + complexBregman Φ grad y z
        + (grad y - grad z) * (x - y) := by
  unfold complexBregman
  ring

/--
Symmetrized complex Bregman expression.

`D(z,w) + D(w,z) = (grad z - grad w) * (z - w)`.
-/
@[rep_depth thermo]
theorem complexBregman_symm_sum
    (Φ grad : ℂ → ℂ)
    (z w : ℂ) :
    complexBregman Φ grad z w
      + complexBregman Φ grad w z =
        (grad z - grad w) * (z - w) := by
  unfold complexBregman
  ring


/-! ## 3. Cayley functional-equation algebra -/

/--
Cayley coordinate for the functional-equation involution.

`w = (s - 1) / s`.
-/
@[rep_depth projective]
def cayleyFE (s : ℂ) : ℂ :=
  (s - 1) / s

/--
Inverse Cayley coordinate.

`s = 1 / (1 - w)`.
-/
@[rep_depth projective]
def invCayleyFE (w : ℂ) : ℂ :=
  1 / (1 - w)

/--
The reflection `s ↦ 1 - s` becomes inversion in Cayley coordinate.

This is a purely algebraic theorem over `ℂ`.
-/
@[rep_depth projective]
theorem cayley_reflection_eq_inv
    (s : ℂ)
    (h1s : 1 - s ≠ 0)
    (hsm1 : s - 1 ≠ 0) :
    cayleyFE (1 - s) = (cayleyFE s)⁻¹ := by
  unfold cayleyFE
  field_simp [h1s, hsm1]
  ring

/--
`invCayleyFE` is a left inverse to `cayleyFE` away from the excluded points.
-/
@[rep_depth projective]
theorem invCayley_cayley
    (s : ℂ)
    (hs0 : s ≠ 0) :
    invCayleyFE (cayleyFE s) = s := by
  unfold invCayleyFE cayleyFE
  field_simp [hs0]
  ring

/--
`cayleyFE` is a left inverse to `invCayleyFE` away from the excluded point.
-/
@[rep_depth projective]
theorem cayley_invCayley
    (w : ℂ)
    (hw : 1 - w ≠ 0) :
    cayleyFE (invCayleyFE w) = w := by
  unfold cayleyFE invCayleyFE
  field_simp [hw]
  ring

/-! ## 4. Direct Cayley compactification chart -/

/--
Direct Cayley compactification coordinate.

`C(x) = (1 + x) / (1 - x)`.
-/
@[rep_depth projective]
def cayleyCompact (x : ℂ) : ℂ :=
  (1 + x) / (1 - x)

/--
Inverse direct Cayley compactification coordinate.

`C⁻¹(y) = (y - 1) / (y + 1)`.
-/
@[rep_depth projective]
def invCayleyCompact (y : ℂ) : ℂ :=
  (y - 1) / (y + 1)

/--
The inverse Cayley compactification coordinate is a left inverse away from the
Cayley pole `x = 1`.
-/
@[rep_depth projective]
theorem cayley_inverse_left
    (x : ℂ) (hx : 1 - x ≠ 0) :
    invCayleyCompact (cayleyCompact x) = x := by
  unfold invCayleyCompact cayleyCompact
  field_simp [hx]
  ring

/--
The direct Cayley compactification coordinate is a left inverse to its inverse
away from the inverse-chart pole `y = -1`.
-/
@[rep_depth projective]
theorem cayley_inverse_right
    (y : ℂ) (hy : y + 1 ≠ 0) :
    cayleyCompact (invCayleyCompact y) = y := by
  unfold invCayleyCompact cayleyCompact
  field_simp [hy]
  ring


/-! ## 5. Two-phase Yang--Lee algebra -/

/-- Algebraic free-energy gap `ΔF = ΔE - T ΔS`. -/
@[rep_depth thermo]
def freeEnergyGap
    (energyGap entropyGap temperature : ℂ) : ℂ :=
  energyGap - temperature * entropyGap

/-- The free-energy gap transparently decomposes into energy and entropy terms. -/
@[rep_depth thermo]
theorem freeEnergyGap_eq_energy_sub_temperature_mul_entropy
    (energyGap entropyGap temperature : ℂ) :
    freeEnergyGap energyGap entropyGap temperature =
      energyGap - temperature * entropyGap := rfl

/-- Two polarized complex phases contributing to a finite partition function. -/
@[rep_depth thermo]
def twoPhasePartition
    (β Fplus Fminus : ℂ) : ℂ :=
  Complex.exp (-β * Fplus) + Complex.exp (-β * Fminus)

/-- Factorization by the `+` phase: `Z = exp(-βF₊)(1 + exp(-β(F₋-F₊)))`. -/
@[rep_depth thermo]
theorem twoPhasePartition_factor
    (β Fplus Fminus : ℂ) :
    twoPhasePartition β Fplus Fminus =
      Complex.exp (-β * Fplus) *
        (1 + Complex.exp (-β * (Fminus - Fplus))) := by
  unfold twoPhasePartition
  have hminus : Complex.exp (-β * Fminus) =
      Complex.exp (-β * Fplus) * Complex.exp (-β * (Fminus - Fplus)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hminus]
  ring

/--
Finite two-phase Yang--Lee zero criterion: cancellation occurs exactly when the
relative Boltzmann factor is `-1`.
-/
@[rep_depth thermo]
theorem twoPhasePartition_eq_zero_iff
    (β Fplus Fminus : ℂ) :
    twoPhasePartition β Fplus Fminus = 0 ↔
      Complex.exp (-β * (Fminus - Fplus)) = -1 := by
  have hfac := twoPhasePartition_factor β Fplus Fminus
  have hnonzero : Complex.exp (-β * Fplus) ≠ 0 := Complex.exp_ne_zero _
  constructor
  · intro h
    have hprod : Complex.exp (-β * Fplus) *
        (1 + Complex.exp (-β * (Fminus - Fplus))) = 0 := by
      rwa [hfac] at h
    have hsum : 1 + Complex.exp (-β * (Fminus - Fplus)) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hnonzero
    rw [add_comm] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  · intro h
    rw [hfac, h]
    ring

/--
At a finite two-phase Yang--Lee zero, the complex free-energy difference has an
odd imaginary Matsubara phase: `β(F₋ - F₊) = (2n+1)πi`.
-/
@[rep_depth thermo]
theorem yangLeeZero_freeEnergyGap
    {β Fplus Fminus : ℂ}
    (hzero : twoPhasePartition β Fplus Fminus = 0) :
    ∃ n : ℤ,
      β * (Fminus - Fplus) =
        (((2 * n + 1 : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  have hexpneg : Complex.exp (-β * (Fminus - Fplus)) = -1 :=
    (twoPhasePartition_eq_zero_iff β Fplus Fminus).mp hzero
  have hexp : Complex.exp (-β * (Fminus - Fplus)) =
      Complex.exp ((Real.pi : ℂ) * Complex.I) :=
    hexpneg.trans Complex.exp_pi_mul_I.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨-n - 1, ?_⟩
  have hneg : β * (Fminus - Fplus) =
      -(((Real.pi : ℂ) * Complex.I) + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    rw [← hn]
    ring
  rw [hneg]
  simp only [Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat,
    Int.cast_one]
  ring

/--
For real nonzero inverse temperature, a finite two-phase Yang--Lee zero separates
into equal real free energies and an odd destructive imaginary phase.
-/
@[rep_depth thermo]
theorem yangLeeZero_realPhaseConditions
    {β : ℝ} {Fplus Fminus : ℂ}
    (hβ : β ≠ 0)
    (hzero : twoPhasePartition (β : ℂ) Fplus Fminus = 0) :
    ∃ n : ℤ,
      (Fminus - Fplus).re = 0 ∧
        β * (Fminus - Fplus).im = ((2 * n + 1 : ℤ) : ℝ) * Real.pi := by
  obtain ⟨n, hn⟩ := yangLeeZero_freeEnergyGap hzero
  refine ⟨n, ?_, ?_⟩
  · have hre := congrArg Complex.re hn
    simp at hre
    simpa using hre.resolve_left hβ
  · have him := congrArg Complex.im hn
    simpa [mul_assoc, mul_comm, mul_left_comm] using him


end InfoGeometry.Thermo.ComplexThermodynamicLift
