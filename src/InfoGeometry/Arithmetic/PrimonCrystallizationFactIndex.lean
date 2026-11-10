/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.HomologicalProbability
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PrimonCoulombGas
import InfoGeometry.Canonical.VandermondeExclusionBridge
import InfoGeometry.Arithmetic.PrimeLatticeGasVariational
import InfoGeometry.Arithmetic.SpectorPrimonGasBridge

namespace InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

open scoped BigOperators

/-- Non-commutative local boson/signed-fermion factor closure over any `[DivisionRing D]`. -/
theorem divisionRing_boson_signed_factor_closure
    {D : Type*} [DivisionRing D]
    {x : D} (hx : 1 - x ≠ 0) :
    (1 - x)⁻¹ * (1 - x) = 1 ∧
      (1 - x)⁻¹ * (1 - x * x) = 1 + x :=
  ⟨InfoGeometry.Arithmetic.PrimeBosonFermionGas.divisionRing_boson_mul_signedFermion_factor hx,
   InfoGeometry.Arithmetic.PrimeBosonFermionGas.divisionRing_boson_mul_square_signedFermion_factor hx⟩

/-- Finite boson/signed-fermion closure re-exported from the Spector primon-gas bridge. -/
theorem boson_signed_closure
    {ι R : Type*} [Field R]
    (S : Finset ι) (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    InfoGeometry.Arithmetic.PrimeBosonFermionGas.bosonPartition S x *
        InfoGeometry.Arithmetic.PrimeBosonFermionGas.signedFermionPartition S x = 1 :=
  InfoGeometry.Arithmetic.SpectorPrimonGasBridge.spector_finite_boson_signed_closure S x h

/-- Finite free-energy minimizer re-exported from the quasicrystal/RH packet. -/
theorem gibbs_kms_free_energy_minimizer
    (gk : InfoGeometry.Probability.Homological.GibbsKMSPacket)
    (ρ : gk.ObservableAlgebra)
    (hrel : 0 ≤ gk.relativeEntropyToGibbs ρ)
    (hβ : 0 < gk.beta) :
    gk.freeEnergy gk.gibbsState ≤ gk.freeEnergy ρ :=
  InfoGeometry.Probability.Homological.GibbsKMSPacket.freeEnergy_ge_gibbs_of_relativeEntropy_nonneg gk ρ hrel hβ

/-- Finite Dyson/Vandermonde logarithmic repulsion re-exported from the quasicrystal packet. -/
theorem finite_dyson_vandermonde_potential
    {N : ℕ} (lam : Fin N → ℝ) (V : ℝ → ℝ)
    (hsep : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, lam j ≠ lam i) :
    InfoGeometry.Canonical.PrimonCoulombGas.dyson_hamiltonian lam V =
      InfoGeometry.Canonical.PrimonCoulombGas.external_potential_energy lam V -
        Real.log ((InfoGeometry.Canonical.PrimonCoulombGas.vandermonde_product_abs lam) ^ 2) :=
  InfoGeometry.Canonical.PrimonCoulombGas.dyson_to_vandermonde_bridge lam V hsep

/-- Finite Vandermonde noncollision criterion re-exported from the quasicrystal packet. -/
theorem finite_vandermonde_nonzero_iff_injective
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (W : Fin n → R) :
    InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant W ≠ 0 ↔
      Function.Injective W :=
  InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant_ne_zero_iff_injective W

/-- Finite Vandermonde collision locus re-exported from the quasicrystal packet. -/
theorem finite_vandermonde_zero_iff_collision
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (W : Fin n → R) :
    InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant W = 0 ↔
      ∃ i j : Fin n, W i = W j ∧ i ≠ j :=
  InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant_eq_zero_iff_collision W

/-- Finite prime-lattice entropy maximizer re-exported from the lattice gas packet. -/
theorem finite_prime_lattice_entropy_maximizer
    (M : ℕ) :
    let n := Fintype.card (InfoGeometry.Arithmetic.PrimeLatticeGasVariational.Configuration M)
    ∀ q : Fin n → ℝ,
      q ∈ InfoGeometry.MaxEnt.MaxEntConstraint (n := n) (fun _ : Fin n => (0 : ℝ)) 0 →
        InfoGeometry.MaxEnt.ShannonEntropy q ≤
          InfoGeometry.MaxEnt.ShannonEntropy
            (InfoGeometry.MaxEnt.gibbs (fun _ : Fin n => (0 : ℝ)) 0) :=
  InfoGeometry.Arithmetic.PrimeLatticeGasVariational.primeLatticeGas_zeroFeature_entropy_maximizer M

end InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex
