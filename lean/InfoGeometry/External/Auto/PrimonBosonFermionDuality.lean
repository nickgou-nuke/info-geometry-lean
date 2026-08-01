import InfoGeometry.External.Auto.BosonicPrimonPartition
import InfoGeometry.External.Auto.FermionicPrimonPartition
import InfoGeometry.External.Auto.MajoranaPrimonSpectralBridge


/-!
# Finite primon boson–fermion–Möbius identities

Three primon sectors at a single prime p:
- **Bosonic**: Z_boson_K(p,β) = Σ_{k=0}^K p^{-kβ}
- **Fermionic**: Z_fermion(p,β) = 1 + p^{-β}
- **Möbius**: Z_mobius(p,β) = 1 - p^{-β}

Core finite duality:
  Z_K^boson · Z_mobius = 1 - p^{-(K+1)β}

The product `(1+a)(1-a) = 1-a²` gives the finite fermion–Möbius identity.
The module also re-exports the existing algebraic fixed-point characterization
of the CPT spectral map.
-/

noncomputable section

namespace PrimonBosonFermionDuality

/-! ## Möbius (signed) fermionic sector -/

def singlePrimeMobiusPartition (p : ℕ) (β : ℝ) : ℝ :=
  1 - primeBoltzmannWeight p β

/-! ## Core identities -/

/-- **Finite Boson–Möbius duality.**
  (Σ_{k=0}^K a^k) · (1-a) = 1 - a^{K+1}
where a = p^{-β}.  Proof by induction: the sum telescopes. -/
theorem finite_boson_mobius_duality (p : ℕ) (β : ℝ) (K : ℕ) :
    singlePrimeBosonPartition p β K * singlePrimeMobiusPartition p β =
    1 - (primeBoltzmannWeight p β) ^ (K + 1) := by
  dsimp [singlePrimeMobiusPartition, singlePrimeBosonPartition, bosonOccupationWeight]
  set a := primeBoltzmannWeight p β
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    simp [pow_succ]
    ring

/-- **Fermion–Möbius product identity.**
  (1+a)(1-a) = 1-a²  where a = p^{-β}. -/
theorem fermion_mobius_product (p : ℕ) (β : ℝ) :
    singlePrimeFermionPartition p β * singlePrimeMobiusPartition p β =
    1 - (primeBoltzmannWeight p β) ^ 2 := by
  rw [singlePrimeFermionPartition_eq, singlePrimeMobiusPartition]
  set x := primeBoltzmannWeight p β
  calc
    (1 + x) * (1 - x) = 1 - x ^ 2 := by ring
    _ = 1 - (primeBoltzmannWeight p β) ^ 2 := rfl

/-- Finite zero-temperature specialization of the fermion–Möbius product. -/
theorem mobius_zero_at_hagedorn (p : ℕ) :
    singlePrimeMobiusPartition p 0 = 0 := by
  simp [singlePrimeMobiusPartition, primeBoltzmannWeight]


end PrimonBosonFermionDuality

end noncomputable section
