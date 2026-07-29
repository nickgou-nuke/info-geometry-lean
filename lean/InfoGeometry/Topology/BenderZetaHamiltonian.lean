import Mathlib.Tactic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bender--Brody--Müller zeta Hamiltonian: finite-safe algebraic slice

This module records theorem-safe operator algebra from arXiv:1608.03679v4,
"Hamiltonian for the zeros of the Riemann zeta function".

The paper proposes
`H = (1 - exp(-i p))⁻¹ (x p + p x) (1 - exp(-i p))` and observes that in the
commutative/classical limit the similarity factors cancel and `x p + p x = 2 x p`.
That cancellation is formalized below in an arbitrary noncommutative ring,
under the exact commutation and inner-invariance hypotheses it requires.

No theorem here asserts RH, self-adjointness of the infinite-dimensional operator,
existence of the metric operator, Hurwitz-zeta eigenfunction completeness, or a
Hilbert--Pólya spectral theorem.
-/

namespace InfoGeometry.Topology.BenderZeta

/-- Operator-level PT-symmetric Hilbert--Pólya candidate. -/
structure ZetaHamiltonian
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- Candidate bounded Hamiltonian. -/
  op : H →L[ℂ] H
  /-- Real-linear isometric PT action on the operator algebra. -/
  pt : (H →L[ℂ] H) ≃ₗᵢ[ℝ] (H →L[ℂ] H)
  /-- PT is an involution. -/
  pt_involutive : Function.Involutive pt
  /-- Concrete PT symmetry equation for `iH`. -/
  i_mul_pt_symmetric : pt (Complex.I • op) = Complex.I • op
  /-- The spectral-reality owner hypothesis. -/
  selfAdjoint : IsSelfAdjoint op

/-- The spectrum of an operator-level zeta Hamiltonian is real. -/
theorem spectrum_is_real
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Z : ZetaHamiltonian H)
    (z : ℂ) (hz : z ∈ spectrum ℂ Z.op) :
    z.im = 0 :=
  Z.selfAdjoint.im_eq_zero_of_mem_spectrum hz

/--
Concrete replacement for the former unconstrained
`is_iH_PT_symmetric : Prop` field.
-/
def ZetaHamiltonian.is_iH_PT_symmetric
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Z : ZetaHamiltonian H) : Prop :=
  Z.pt (Complex.I • Z.op) = Complex.I • Z.op

/-- The installed PT equation proves the derived PT-symmetry predicate. -/
theorem ZetaHamiltonian.is_iH_PT_symmetric_holds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Z : ZetaHamiltonian H) :
    Z.is_iH_PT_symmetric :=
  Z.i_mul_pt_symmetric

/--
Compatibility replacement for the former
`broken_PT_implies_real_spectrum : Prop` field.  The historical name now
denotes only the precise spectral-reality conclusion, which follows here from
self-adjointness and does not assert a theorem about broken PT phases.
-/
def ZetaHamiltonian.broken_PT_implies_real_spectrum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Z : ZetaHamiltonian H) : Prop :=
  ∀ z : ℂ, z ∈ spectrum ℂ Z.op → z.im = 0

/-- Self-adjointness proves the derived real-spectrum predicate. -/
theorem ZetaHamiltonian.broken_PT_implies_real_spectrum_holds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Z : ZetaHamiltonian H) :
    Z.broken_PT_implies_real_spectrum := by
  intro z hz
  exact spectrum_is_real Z z hz

/-- Restored non-vacuous readout of the two historical packet obligations. -/
def hilbert_polya_conjecture_link
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Z : ZetaHamiltonian H) : Prop :=
  Z.is_iH_PT_symmetric ∧ Z.broken_PT_implies_real_spectrum

/-- Every operator-level owner satisfies the restored packet readout. -/
theorem hilbert_polya_conjecture_link_holds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Z : ZetaHamiltonian H) :
    hilbert_polya_conjecture_link Z :=
  ⟨Z.is_iH_PT_symmetric_holds,
    Z.broken_PT_implies_real_spectrum_holds⟩

/-- A Hilbert--Pólya realization identifies completed-zeta zeros with spectrum. -/
def HilbertPolyaSpectralRealization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Z : ZetaHamiltonian H) (Xi : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Xi z = 0 ↔ z ∈ spectrum ℂ Z.op

/-- Every zero in a Hilbert--Pólya spectral realization has real parameter. -/
theorem zero_parameter_is_real
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Z : ZetaHamiltonian H) (Xi : ℂ → ℂ)
    (hHP : HilbertPolyaSpectralRealization Z Xi)
    (z : ℂ) (hz : Xi z = 0) :
    z.im = 0 :=
  spectrum_is_real Z z ((hHP z).1 hz)

/--
If position and momentum commute in an arbitrary ring, the symmetrized
Berry--Keating product collapses to twice their ordered product.
-/
theorem berry_keating_commutative_core
    {R : Type*} [Ring R] (x p : R) (hxp : Commute x p) :
    x * p + p * x = (2 : R) * (x * p) := by
  rw [← hxp.eq]
  exact (two_mul (x * p)).symm

/--
Operator-level similarity cancellation for the Bender--Brody--Müller core.

The first hypothesis is the classical commutation relation.  The second is the
exact statement that the ordered product is fixed by conjugation with the
chosen unit; no scalar or diagonal specialization is used.
-/
theorem bender_classical_similarity_cancel
    {R : Type*} [Ring R] (x p : R) (S : Rˣ)
    (hxp : Commute x p)
    (hS : ((S⁻¹ : Rˣ) : R) * (x * p) * (S : R) = x * p) :
    ((S⁻¹ : Rˣ) : R) * (x * p + p * x) * (S : R) =
      (2 : R) * (x * p) := by
  rw [berry_keating_commutative_core x p hxp]
  calc
    ((S⁻¹ : Rˣ) : R) * ((2 : R) * (x * p)) * (S : R) =
        (2 : R) * (((S⁻¹ : Rˣ) : R) * (x * p) * (S : R)) := by
          noncomm_ring
    _ = (2 : R) * (x * p) := by rw [hS]

end InfoGeometry.Topology.BenderZeta
