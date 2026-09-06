import proofs.BosonicPrimonPartition
import proofs.FermionicPrimonPartition
import proofs.MajoranaPrimonSpectralBridge

noncomputable section

namespace PrimonBosonFermionDuality

def singlePrimeMobiusPartition (p : ℕ) (β : ℝ) : ℝ :=
  1 - primeBoltzmannWeight p β

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

theorem fermion_mobius_product (p : ℕ) (β : ℝ) :
    singlePrimeFermionPartition p β * singlePrimeMobiusPartition p β =
    1 - (primeBoltzmannWeight p β) ^ 2 := by
  rw [singlePrimeFermionPartition_eq, singlePrimeMobiusPartition]
  set x := primeBoltzmannWeight p β
  calc
    (1 + x) * (1 - x) = 1 - x ^ 2 := by ring
    _ = 1 - (primeBoltzmannWeight p β) ^ 2 := rfl

theorem mobius_zero_at_hagedorn (p : ℕ) :
    singlePrimeMobiusPartition p 0 = 0 := by
  simp [singlePrimeMobiusPartition, primeBoltzmannWeight]

theorem primon_boson_fermion_duality_synthesis
    (p : ℕ) (β : ℝ) (K : ℕ) (s : ℂ) :
    -- Finite boson-mobius duality
    singlePrimeBosonPartition p β K * singlePrimeMobiusPartition p β =
      1 - (primeBoltzmannWeight p β) ^ (K + 1) ∧
    -- Fermion-mobius product
    singlePrimeFermionPartition p β * singlePrimeMobiusPartition p β =
      1 - (primeBoltzmannWeight p β) ^ 2 ∧
    -- Hagedorn singularity
    singlePrimeMobiusPartition p 0 = 0 ∧
    -- CPT fixed point: Re(s) = 1/2 (from MajoranaPrimonSpectralBridge)
    (MajoranaPrimonSpectralBridge.cptSpectralMap s = s ↔ s.re = 1/2) := by
  exact ⟨finite_boson_mobius_duality p β K,
    fermion_mobius_product p β,
    mobius_zero_at_hagedorn p,
    MajoranaPrimonSpectralBridge.cpt_fixed_point_iff_critical_line s⟩

end PrimonBosonFermionDuality

end noncomputable section
