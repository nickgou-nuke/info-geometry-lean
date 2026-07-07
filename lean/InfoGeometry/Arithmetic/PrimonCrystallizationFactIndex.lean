import InfoGeometry.Arithmetic.QuasicrystalRHExplicitFormula
import InfoGeometry.Arithmetic.PrimeLatticeGasVariational
import InfoGeometry.Arithmetic.SpectorPrimonGasBridge

namespace InfoGeometry.Arithmetic.PrimonCrystallizationFactIndex

open scoped BigOperators

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
  InfoGeometry.Arithmetic.QuasicrystalRHExplicitFormula.gibbs_kms_free_energy_minimizer gk ρ hrel hβ

/-- Finite Dyson/Vandermonde logarithmic repulsion re-exported from the quasicrystal packet. -/
theorem finite_dyson_vandermonde_potential
    {N : ℕ} (lam : Fin N → ℝ) (V : ℝ → ℝ)
    (hsep : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, lam j ≠ lam i) :
    InfoGeometry.Canonical.PrimonCoulombGas.dyson_hamiltonian lam V =
      InfoGeometry.Canonical.PrimonCoulombGas.external_potential_energy lam V -
        Real.log ((InfoGeometry.Canonical.PrimonCoulombGas.vandermonde_product_abs lam) ^ 2) :=
  InfoGeometry.Arithmetic.QuasicrystalRHExplicitFormula.finite_dyson_vandermonde_potential lam V hsep

/-- Finite Vandermonde noncollision criterion re-exported from the quasicrystal packet. -/
theorem finite_vandermonde_nonzero_iff_injective
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (W : InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness
      (R := R) (n := n)) :
    W.determinant ≠ 0 ↔ Function.Injective W.nodes :=
  InfoGeometry.Arithmetic.QuasicrystalRHExplicitFormula.finite_vandermonde_nonzero_iff_injective W

/-- Finite Vandermonde collision locus re-exported from the quasicrystal packet. -/
theorem finite_vandermonde_zero_iff_collision
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (W : InfoGeometry.Canonical.VandermondeExclusionBridge.FiniteVandermondeExclusionWitness
      (R := R) (n := n)) :
    W.determinant = 0 ↔ ∃ i j : Fin n, W.nodes i = W.nodes j ∧ i ≠ j :=
  InfoGeometry.Arithmetic.QuasicrystalRHExplicitFormula.finite_vandermonde_zero_iff_collision W

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
