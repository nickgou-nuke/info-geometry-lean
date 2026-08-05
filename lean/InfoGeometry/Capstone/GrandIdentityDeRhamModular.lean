import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.DeRhamBoltzmannModular
import InfoGeometry.Canonical.Cl11MonodromyDictionaryConstruction

noncomputable section

namespace InfoGeometry.Capstone.GrandIdentityDeRhamModular

open InfoGeometry

/-!
# GrandIdentityDeRhamModular

This file contains a theorem-honest local packet behind the slogan
"Grand Identity".

What is formalized here:
- a scalar partition function `Q`
- the Boltzmann potential `log Q`
- an abstract expectation observable `Kexp`
- the Legendre-style decomposition `S_vN = S_B + β * Kexp`
- the exact derivative consequence obtained when `deriv S_B = 0`

What is not formalized here:
- a global de Rham cohomology computation,
- an operator-algebraic Tomita-Takesaki construction,
- a proof that physical time, modular flow, and de Rham winding coincide.

## Relationship to Cl(1,1) Monodromy Dictionary

The concrete Cl(1,1) monodromy construction in
`InfoGeometry.Canonical.Cl11MonodromyDictionaryConstruction` provides:

- A square-zero modular Hamiltonian `K` (nilpotent generator)
- A commutator residue operator `Res(X) = [K, X]`
- A characterization: `Res²(X) = 0` iff `K X K = 0`

This scalar capstone packet is compatible with that construction but does not
identify its abstract `Kexp` with the operator-algebraic modular Hamiltonian.
The scalar model can be viewed as a "shadow" or expectation-value readout of
the deeper noncommutative structure.
-/

/-- Boltzmann potential `S_B(β) = log(Q(β))`. -/
def boltzmannEntropy (Q : ℝ → ℝ) (β : ℝ) : ℝ :=
  Real.log (Q β)

/-- Legendre-style packet for the von Neumann entropy readout. -/
def vonNeumannEntropy (Q Kexp : ℝ → ℝ) (β : ℝ) : ℝ :=
  boltzmannEntropy Q β + β * Kexp β

@[simp] theorem boltzmannEntropy_eq_log (Q : ℝ → ℝ) (β : ℝ) :
    boltzmannEntropy Q β = Real.log (Q β) := rfl

/-- Exact decomposition packaged under the name `vonNeumannEntropy`. -/
@[simp] theorem vonNeumannEntropy_eq_boltzmann_plus_beta_expectation
    (Q Kexp : ℝ → ℝ) (β : ℝ) :
    vonNeumannEntropy Q Kexp β = boltzmannEntropy Q β + β * Kexp β := rfl

/--
Conditional first-law identity for the packaged scalar model.

This theorem is purely formal: if the Boltzmann term has zero derivative at `β`,
then differentiating the Legendre packet leaves only the product-rule term.
-/
theorem first_law_modular_thermodynamics
    (Q Kexp : ℝ → ℝ) (β : ℝ)
    (hB : DifferentiableAt ℝ (boltzmannEntropy Q) β)
    (hK : DifferentiableAt ℝ Kexp β)
    (hBoltzFlat : deriv (boltzmannEntropy Q) β = 0) :
    deriv (vonNeumannEntropy Q Kexp) β = Kexp β + β * deriv Kexp β := by
  change deriv (fun x => boltzmannEntropy Q x + x * Kexp x) β =
    Kexp β + β * deriv Kexp β
  have hfun : (fun x => boltzmannEntropy Q x + x * Kexp x) =
      (fun x => boltzmannEntropy Q x + Kexp x * x) := by
    funext x
    ring
  rw [hfun]
  change deriv ((boltzmannEntropy Q) + (Kexp * fun x => x)) β =
    Kexp β + β * deriv Kexp β
  have hProd : HasDerivAt (Kexp * fun x => x) (Kexp β + β * deriv Kexp β) β := by
    simpa [one_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
      using hK.hasDerivAt.mul (hasDerivAt_id' β)
  have hSum : HasDerivAt ((boltzmannEntropy Q) + (Kexp * fun x => x))
      (0 + (Kexp β + β * deriv Kexp β)) β := by
    simpa [hBoltzFlat] using hB.hasDerivAt.add hProd
  simpa using hSum.deriv

/--
The corresponding concrete Boltzmann potential from
`InfoGeometry.Canonical.DeRhamBoltzmannModular`.
-/
@[simp] theorem twoLevel_boltzmannEntropy_eq
    (r β : ℝ) :
    boltzmannEntropy (partitionQ r) β = entropyPotential r β := by
  rfl

/--
The concrete two-level partition function is positive, so the logarithm is
well-defined pointwise.
-/
theorem twoLevelPartition_pos (r β : ℝ) : 0 < partitionQ r β :=
  partitionQ_pos r β

/--
The scalar two-level packet gives a concrete witness that the capstone surface is
nonempty: there exists a partition function with positive values and a well-defined
Boltzmann potential.
-/
theorem exists_twoLevel_capstone_packet :
    ∃ Q : ℝ → ℝ, (∀ β : ℝ, 0 < Q β) := by
  refine ⟨partitionQ 1, ?_⟩
  intro β
  exact twoLevelPartition_pos 1 β

/--
The concrete Cl(1,1) monodromy construction supplies a square-zero modular
generator, validating that the operator-algebraic side of the "Grand Identity"
slogan is non-vacuous.

This theorem conservatively records the existence of the concrete nilpotent
generator. The connection between the scalar thermodynamic packet and the
operator-algebraic modular Hamiltonian remains a calibration choice, not a
definition.
-/
theorem cl11_nilpotent_generator_exists :
    ∃ K : InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier,
      K * K = 0 := by
  refine ⟨InfoGeometry.Canonical.Cl11MonodromyDictionaryConstruction.modularHamiltonian, ?_⟩
  exact InfoGeometry.Canonical.Cl11MonodromyDictionaryConstruction.modularHamiltonian_sq

end InfoGeometry.Capstone.GrandIdentityDeRhamModular
