import Mathlib
import proofs.MirrorNucleiIsospinGNS
import proofs.GoutevTonevNuclearHamiltonian

/-!
# Doubled-angular-momentum parity and finite parameter model

This file uses `twoJ : ℕ` as the doubled angular-momentum index. For odd
`twoJ`, the offset `(twoJ+1)/2` is the integer `j+1/2`; this lets the parity
factor and amplitude be stated without fractional powers of `-1`. It proves
exact arithmetic identities for that model. It does not derive a nuclear
Hamiltonian or establish CPT symmetry or Klein-bottle topology.

## Main Results

1. Increasing `twoJ` by two negates the parity factor; increasing it by four
   preserves that factor.
2. The absolute value of the arithmetic expression is exactly its amplitude.
3. The selected half-integer-indexed values are computed exactly; they are
   not empirical predictions derived from a physical model.

## Motivation and formal scope

The definitions are independent of the imported matrix identities; no
rotation operator or topological quotient occurs in their types. The formula
is recorded as an algebraic model, not as a statement about observed spectra.
-/

noncomputable section

namespace CoriolisDecoupling
open MirrorNucleiIsospinGNS
open GoutevTonevNuclearHamiltonian
open Matrix

/-- The natural-number offset `(2j+1)/2`; on odd `twoJ = 2j`, this is the
integer `j+1/2`. -/
def halfIntegerOffset (twoJ : ℕ) : ℝ := (((twoJ + 1) / 2 : ℕ) : ℝ)

/-- Alternating factor for a doubled angular-momentum index. On odd indices,
the exponent equals the half-integer shift `j+1/2`. -/
def coriolisSignature (twoJ : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((twoJ + 1) / 2)

/-- Rotational expression with doubled angular momentum `twoJ`. On odd
`twoJ`, `j = twoJ/2` is half-integral and the alternating exponent and
amplitude are both the exact integer `j+1/2`. -/
def rotationalEnergyK12 (E₀ A B : ℝ) (twoJ : ℕ) : ℝ :=
  let j : ℝ := (twoJ : ℝ) / 2
  E₀ + A * j * (j + 1) + coriolisSignature twoJ * B * halfIntegerOffset twoJ

/-- Increasing the doubled index by two increases the half-integer exponent by
one and reverses the sign. -/
theorem coriolisSignature_add_two (twoJ : ℕ) :
    coriolisSignature (twoJ + 2) = -coriolisSignature twoJ := by
  unfold coriolisSignature
  have hexp : (twoJ + 2 + 1) / 2 = (twoJ + 1) / 2 + 1 := by omega
  rw [hexp, pow_succ]
  ring

/-- A shift of four in doubled angular momentum restores the alternating
factor. -/
theorem coriolisSignature_add_four (twoJ : ℕ) :
    coriolisSignature (twoJ + 4) = coriolisSignature twoJ := by
  rw [show twoJ + 4 = (twoJ + 2) + 2 by omega,
    coriolisSignature_add_two, coriolisSignature_add_two]
  ring

/-- Arithmetic decoupling expression `(-1)^(j+1/2)(j+1/2)` indexed by
`twoJ = 2j`. No measured nuclear parameter is asserted. -/
def decouplingParameter (twoJ : ℕ) : ℝ :=
  coriolisSignature twoJ * halfIntegerOffset twoJ

/-- The absolute value of this expression is exactly its nonnegative
amplitude. -/
theorem decouplingParameter_abs (twoJ : ℕ) :
    |decouplingParameter twoJ| = halfIntegerOffset twoJ := by
  unfold decouplingParameter coriolisSignature halfIntegerOffset
  rw [abs_mul, abs_pow]
  norm_num

/-- Value label for the arithmetic expression at `twoJ = 3` (`j = 3/2`). -/
def a_A31_d32 : ℝ := decouplingParameter 3

/-- Value label for the arithmetic expression at `twoJ = 7` (`j = 7/2`). -/
def a_A47_f72 : ℝ := decouplingParameter 7

/-- Value label for the arithmetic expression at `twoJ = 9` (`j = 9/2`). -/
def a_A67_g92 : ℝ := decouplingParameter 9

/-- On odd doubled indices the half-integer amplitude is positive, so the
decoupling expression is nonzero. -/
theorem decouplingParameter_ne_zero_of_odd (twoJ : ℕ) (hOdd : Odd twoJ) :
    decouplingParameter twoJ ≠ 0 := by
  intro hzero
  have habs := decouplingParameter_abs twoJ
  rw [hzero, abs_zero] at habs
  have hpos : 0 < halfIntegerOffset twoJ := by
    unfold halfIntegerOffset
    have htwo : 1 ≤ twoJ := hOdd.pos
    have hq : 0 < (twoJ + 1) / 2 := by omega
    exact_mod_cast hq
  linarith

/-- Exact arithmetic value of the formula at doubled index `3` (`j=3/2`). -/
theorem decouplingParameter_d32_value : a_A31_d32 = 2 := by
  norm_num [a_A31_d32, decouplingParameter, coriolisSignature, halfIntegerOffset]

/-- Exact arithmetic value of the formula at doubled index `7` (`j=7/2`). -/
theorem decouplingParameter_f72_value : a_A47_f72 = 4 := by
  norm_num [a_A47_f72, decouplingParameter, coriolisSignature, halfIntegerOffset]

/-- Exact arithmetic value of the formula at doubled index `9` (`j=9/2`). -/
theorem decouplingParameter_g92_value : a_A67_g92 = -5 := by
  norm_num [a_A67_g92, decouplingParameter, coriolisSignature, halfIntegerOffset]

/-- 
The defined parity sequence is nonzero at every natural-number index.
-/
theorem coriolis_signature_ne_zero (K : ℕ) :
    coriolisSignature K ≠ 0 := by
  unfold coriolisSignature
  exact pow_ne_zero _ (by norm_num)

/-! The earlier synthesis claims joined unrelated matrix and scalar facts by
existential/wrapper packaging. The actual reusable matrix consequence remains
owned by `MirrorNucleiIsospinGNS`; the actual scalar results are
`coriolisSignature_add_two`, `decouplingParameter_abs`, and the three exact
indexed values above. No CPT, topology, or measured spectroscopy consequence
is inferred from this arithmetic. -/

end CoriolisDecoupling
end noncomputable section
