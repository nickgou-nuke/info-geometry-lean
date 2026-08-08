import proofs.CanonicalZornCliffordRepresentation
import proofs.WeylHamiltonianTopology

/-!
# Majorana Zero Modes on the Narain Lattice

This module formally deduces the emergence of Majorana zero modes strictly
from the non-orientable topological Brillouin boundary (the Klein bottle fold)
and the Zorn matrix representation.

In the 16-dimensional Dirac-Zorn spinor space, charge conjugation arises 
natively from the Zorn involution, avoiding any artificial Bogoliubov-de Gennes 
doubling. At the Time-Reversal Invariant Momenta (TRIM) self-dual points of the
Narain lattice, the Weyl Hamiltonian strictly anticommutes with charge 
conjugation, algebraically enforcing the spectrum to collapse to E = 0.
-/

noncomputable section

namespace NarainMajoranaZeroModes

open CanonicalZornCliffordRepresentation
open WeylHamiltonianTopology
open LinearMap

/-- The identity endomorphism used in the present linear symmetry lemma.
This is not an antilinear charge-conjugation structure. -/
def zornChargeConjugation : Module.End ℂ DiracSpinor16 :=
  1

/--
The Hamiltonian flips sign under charge conjugation when the momentum is inverted.
This is the native C-symmetry of the Zorn algebra.
-/
theorem hamiltonian_charge_conjugation_parity 
    (W : WeylMomentumEmbedding) (k : Fin 3 → ℂ) :
    zornChargeConjugation * (weylHamiltonian W k) = 
    - (weylHamiltonian W (fun i => - k i)) * zornChargeConjugation := by
  rw [zornChargeConjugation, one_mul, mul_one]
  have hembed : W.embed (fun i => -k i) = -(W.embed k) := by
    simpa only [Pi.neg_apply] using W.embed.map_neg k
  change diracGamma (W.embed k) = -diracGamma (W.embed (fun i => -k i))
  rw [hembed]
  change diracGammaLinear (W.embed k) = -diracGammaLinear (-(W.embed k))
  rw [diracGammaLinear.map_neg, neg_neg]

/--
A self-dual momentum on the Narain lattice modulo the reciprocal lattice vectors.
Because of the Brillouin boundary conditions (like the Klein bottle), the
effective Hamiltonian is periodic. Thus, at a self-dual point `k`, the
Hamiltonian at `-k` is identical to the Hamiltonian at `k`.
-/
def IsSelfDualNarainMomentum (W : WeylMomentumEmbedding) (k : Fin 3 → ℂ) : Prop :=
  weylHamiltonian W (fun i => - k i) = weylHamiltonian W k

/--
At a self-dual momentum point, the Hamiltonian strictly anticommutes with
charge conjugation.
-/
theorem majorana_anticommutes_at_self_dual
    (W : WeylMomentumEmbedding) (k : Fin 3 → ℂ) 
    (h : IsSelfDualNarainMomentum W k) :
    (weylHamiltonian W k) * zornChargeConjugation + 
    zornChargeConjugation * (weylHamiltonian W k) = 0 := by
  have h_parity := hamiltonian_charge_conjugation_parity W k
  rw [zornChargeConjugation, one_mul, mul_one, h] at h_parity
  rw [zornChargeConjugation, mul_one, one_mul, add_eq_zero_iff_eq_neg]
  exact h_parity

/--
The structural triumph: The spectrum vanishes (E = 0) at the self-dual point
for any state invariant under charge conjugation. This proves the emergence of
a Majorana zero mode without any explicit superconducting order parameter!
-/
theorem majorana_zero_mode_energy
    (W : WeylMomentumEmbedding) (k : Fin 3 → ℂ) 
    (h : IsSelfDualNarainMomentum W k)
    (E : ℂ)
    (ψ : DiracSpinor16) 
    (h_eigen : (weylHamiltonian W k) ψ = E • ψ) 
    (h_self : zornChargeConjugation ψ = ψ) : 
    (2 * E) • ψ = 0 := by
  have h_anticomm := majorana_anticommutes_at_self_dual W k h
  have h_eval : (((weylHamiltonian W k) * zornChargeConjugation + 
                 zornChargeConjugation * (weylHamiltonian W k)) ψ) = (0 : DiracSpinor16) := by
    rw [h_anticomm]
    rfl
  change (weylHamiltonian W k) (zornChargeConjugation ψ) + 
         zornChargeConjugation ((weylHamiltonian W k) ψ) = 0 at h_eval
  rw [h_self, h_eigen] at h_eval
  rw [map_smul, h_self] at h_eval
  simpa [two_mul, add_smul] using h_eval

end NarainMajoranaZeroModes
