import Mathlib

/-!
# Bender--Brody--Müller zeta Hamiltonian: finite-safe algebraic slice

This module records only theorem-safe algebra from arXiv:1608.03679v4,
"Hamiltonian for the zeros of the Riemann zeta function".

The paper proposes
`H = (1 - exp(-i p))⁻¹ (x p + p x) (1 - exp(-i p))` and observes that in the
commutative/classical limit the similarity factors cancel and `x p + p x = 2 x p`.
That finite algebraic cancellation is formalized below over `ℚ`.

No theorem here asserts RH, self-adjointness of the infinite-dimensional operator,
existence of the metric operator, Hurwitz-zeta eigenfunction completeness, or a
Hilbert--Pólya spectral theorem.
-/

namespace InfoGeometry.Topology.BenderZeta

/--
Abstract hypothesis packet for the proposed Hilbert--Pólya-style Hamiltonian.
The fields are assumptions/data, not proved closure.
-/
structure ZetaHamiltonian (H : Type*) where
  /-- The Hamiltonian operator. -/
  op : H
  /-- The operator `iH` is PT symmetric. -/
  is_iH_PT_symmetric : Prop
  /-- Broken PT symmetry would force the relevant spectral readout to be real. -/
  broken_PT_implies_real_spectrum : Prop

/--
Non-vacuous packet readout: this is exactly the conjunction of the recorded
hypotheses.  It deliberately does not fill a Hilbert--Pólya/RH claim with `True`.
-/
def hilbert_polya_conjecture_link (H : Type*) (zh : ZetaHamiltonian H) : Prop :=
  zh.is_iH_PT_symmetric ∧ zh.broken_PT_implies_real_spectrum

/-- In a commutative classical algebra, `xp + px` collapses to `2xp`. -/
theorem berry_keating_commutative_core (x p : ℚ) :
    x * p + p * x = 2 * x * p := by
  ring

/--
Finite-safe classical-limit theorem for the Bender--Brody--Müller Hamiltonian:
for any nonzero scalar similarity factor `S`, the commutative shadow of
`S⁻¹ (xp + px) S` is exactly `2xp`.
-/
theorem bender_classical_similarity_cancel (x p S : ℚ) (hS : S ≠ 0) :
    S⁻¹ * (x * p + p * x) * S = 2 * x * p := by
  field_simp [hS]
  ring

end InfoGeometry.Topology.BenderZeta
