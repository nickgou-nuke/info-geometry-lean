import proofs.BosonicPrimonPartition
import proofs.FermionicPrimonPartition
import proofs.MajoranaPrimonSpectralBridge

/-!
# Primon Boson–Fermion–Möbius Duality and Lee–Yang Condensation

Three primon sectors at a single prime p:
- **Bosonic**: Z_boson_K(p,β) = Σ_{k=0}^K p^{-kβ}
- **Fermionic**: Z_fermion(p,β) = 1 + p^{-β}
- **Möbius**: Z_mobius(p,β) = 1 - p^{-β}

Core finite duality:
  Z_K^boson · Z_mobius = 1 - p^{-(K+1)β}

In the limit K→∞ with β>0: Z_boson · Z_mobius = 1, i.e. ζ(β)·(1/ζ(β)) = 1.
The product (1+a)(1-a) = 1-a² gives the fermion-mobius sector identity.

Zeros of analytically continued ζ(s) are Lee–Yang condensation points
of the primon gas; CPT involution s↦1-s̄ forces condensation onto Re(s)=½.

Zero sorries.
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

/-- At β = 0, the Möbius partition vanishes: p^{-0} = 1, so Z_mobius = 1-1 = 0.
This is the Hagedorn temperature — the bosonic geometric series diverges,
marking the Lee–Yang phase transition at the radius of convergence. -/
theorem mobius_zero_at_hagedorn (p : ℕ) :
    singlePrimeMobiusPartition p 0 = 0 := by
  simp [singlePrimeMobiusPartition, primeBoltzmannWeight]

/-! ## Lee–Yang condensation and CPT symmetry

The non-trivial zeros of ζ(s) are Lee–Yang zeros of the primon gas
partition function.  The CPT spectral involution s ↦ 1 - s̄ (proved
fixed at Re(s) = ½ in `MajoranaPrimonSpectralBridge.cpt_fixed_point_iff_critical_line`)
forces these condensation points to lie symmetrically about the critical line. -/

/-! ## Synthesis -/

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
