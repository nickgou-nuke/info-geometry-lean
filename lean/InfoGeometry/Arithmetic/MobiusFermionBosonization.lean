import Mathlib
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge

/-!
# InfoGeometry.Arithmetic.MobiusFermionBosonization

Finite bosonization dictionary for Möbius fermions.

This file formalizes the conservative finite algebra behind the corrected CFT
dictionary:

* the CFT fermion charge is separated from arithmetic energy;
* fermionic states are square-free/exterior subsets of prime modes;
* repeated occupation is killed by the exterior product;
* disjoint states multiply by union;
* the graded finite trace is the Euler/Weyl denominator.

No infinite CFT, OPE analytic limit, zeta analytic continuation, or RH theorem
is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.MobiusFermionBosonization

open InfoGeometry.Arithmetic.PrimonFinite

/-! ## 1. Charge/energy separation -/

/--
CFT charge of one Möbius fermion vertex.

The corrected bosonization dictionary uses unit charge for fermionic locality;
the arithmetic energy is stored separately.
-/
def cftFermionCharge
    {PrimeLabel : Type*}
    (_p : PrimeLabel) : ℝ :=
  1

/--
Arithmetic one-particle energy.

For actual primes this is read as `log p`; we keep it as a supplied function at
this finite algebraic layer.
-/
def arithmeticEnergy
    {PrimeLabel : Type*}
    (E : PrimeLabel → ℝ)
    (p : PrimeLabel) : ℝ :=
  E p

/--
Finite fermionic arithmetic Hamiltonian on a square-free state.

This is the finite form of `H = sum_p (log p) N_p`.
-/
def exteriorArithmeticHamiltonian
    {PrimeLabel : Type*}
    (E : PrimeLabel → ℝ)
    (S : FState PrimeLabel) : ℝ :=
  ∑ p ∈ S, E p

/-- Energy is additive on disjoint exterior states. -/
theorem exteriorArithmeticHamiltonian_union_of_disjoint
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (E : PrimeLabel → ℝ)
    {S T : FState PrimeLabel}
    (h : Disjoint S T) :
    exteriorArithmeticHamiltonian E (S ∪ T) =
      exteriorArithmeticHamiltonian E S + exteriorArithmeticHamiltonian E T := by
  unfold exteriorArithmeticHamiltonian
  simpa using Finset.sum_union h

/-! ## 2. Exterior/OPE multiplication -/

/--
Exterior product of two square-free states.

If supports overlap, repeated occupation would occur, so the product is killed.
If supports are disjoint, the product is their union.
-/
def exteriorProduct
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (S T : FState PrimeLabel) : Option (FState PrimeLabel) :=
  if Disjoint S T then some (S ∪ T) else none

/-- Disjoint exterior states multiply to their union. -/
theorem exteriorProduct_eq_some_union_of_disjoint
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    {S T : FState PrimeLabel}
    (h : Disjoint S T) :
    exteriorProduct S T = some (S ∪ T) := by
  simp [exteriorProduct, h]

/-- Overlapping exterior states multiply to zero/none. -/
theorem exteriorProduct_eq_none_of_not_disjoint
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    {S T : FState PrimeLabel}
    (h : ¬ Disjoint S T) :
    exteriorProduct S T = none := by
  simp [exteriorProduct, h]

/--
If the two square-free states have a common occupied mode, their exterior/OPE
product vanishes.
-/
theorem exteriorProduct_eq_none_of_mem_inter
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    {S T : FState PrimeLabel}
    {p : PrimeLabel}
    (hS : p ∈ S)
    (hT : p ∈ T) :
    exteriorProduct S T = none := by
  apply exteriorProduct_eq_none_of_not_disjoint
  intro h
  rw [Finset.disjoint_left] at h
  exact h hS hT

/-- Fermion parity is multiplicative on disjoint exterior unions. -/
theorem parity_union_of_disjoint
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    {S T : FState PrimeLabel}
    (h : Disjoint S T) :
    parity (R := R) (S ∪ T) =
      parity (R := R) S * parity (R := R) T := by
  unfold parity
  rw [Finset.card_union_of_disjoint h]
  rw [pow_add]

/-- Multiplicative weights multiply on disjoint exterior unions. -/
theorem weight_union_of_disjoint
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (q : PrimeLabel → R)
    {S T : FState PrimeLabel}
    (h : Disjoint S T) :
    weight q (S ∪ T) = weight q S * weight q T := by
  unfold weight
  simpa using Finset.prod_union h

/-! ## 3. Finite trace readouts -/

/--
Finite Möbius-fermion graded partition.

This is the same finite exterior supertrace from `PrimonFinite`, exposed under
the bosonization dictionary.
-/
def finiteMobiusFermionGradedPartition
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (modes : Finset PrimeLabel)
    (q : PrimeLabel → R) : R :=
  STrF modes q

/-- Finite Möbius-fermion graded partition equals the Euler/Weyl denominator. -/
theorem finiteMobiusFermionGradedPartition_eq_denominator
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (modes : Finset PrimeLabel)
    (q : PrimeLabel → R) :
    finiteMobiusFermionGradedPartition modes q =
      ∏ p ∈ modes, (1 - q p) := by
  exact STrF_eq_prod modes q

/-! ## 4. Determinant and scale-density guardrails -/

/--
Finite diagonal fermionic determinant readout.

For a diagonal one-particle operator with eigenvalues `q p`, this is the finite
determinant-like product `det(1 - Q)`.
-/
def finiteDiagonalFermionDeterminant
    {PrimeLabel R : Type*} [CommRing R]
    (modes : Finset PrimeLabel)
    (q : PrimeLabel → R) : R :=
  ∏ p ∈ modes, (1 - q p)

/--
The finite graded Möbius-fermion partition is the diagonal fermion determinant.

This is the precise finite statement behind the Euler/Weyl denominator
language.  A literal Vandermonde determinant requires an additional coordinate
or Slater-determinant model.
-/
theorem finiteMobiusFermionGradedPartition_eq_diagonalDeterminant
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (modes : Finset PrimeLabel)
    (q : PrimeLabel → R) :
    finiteMobiusFermionGradedPartition modes q =
      finiteDiagonalFermionDeterminant modes q := by
  exact finiteMobiusFermionGradedPartition_eq_denominator modes q

/--
Finite arithmetic scale-density readout.

This is the finite response-like quantity `sum E_p q_p`.  In the analytic
limit it is related to logarithmic derivatives and von Mangoldt-type response
lanes, but it is not a Virasoro central charge.
-/
def finiteArithmeticScaleDensity
    {PrimeLabel : Type*}
    (modes : Finset PrimeLabel)
    (E q : PrimeLabel → ℝ) : ℝ :=
  ∑ p ∈ modes, E p * q p

/--
Central-charge interpretation guardrail.

The actual Virasoro central charge is a separate CFT datum.  The arithmetic
scale-density response is stored separately so it cannot be silently identified
with that central extension.
-/
structure CentralChargeGuardrail
    (CFTCentralCharge ScaleDensityReadout : Type*) where
  centralCharge : CFTCentralCharge
  scaleDensity : ScaleDensityReadout
  not_definitional_equality : Prop

/--
Determinant/Vandermonde comparison gate.

The Euler product is owned here as a diagonal fermion determinant.  Any
Vandermonde or Slater-determinant interpretation must supply a comparison law.
-/
structure DeterminantVandermondeComparisonGate
    (DeterminantReadout VandermondeReadout : Type*) where
  determinant : DeterminantReadout
  vandermonde : VandermondeReadout
  compare : DeterminantReadout → VandermondeReadout → Prop
  comparison_law : compare determinant vandermonde

namespace DeterminantVandermondeComparisonGate

/-- Re-export of the supplied determinant/Vandermonde comparison. -/
theorem valid
    {DeterminantReadout VandermondeReadout : Type*}
    (G : DeterminantVandermondeComparisonGate
      DeterminantReadout VandermondeReadout) :
    G.compare G.determinant G.vandermonde :=
  G.comparison_law

end DeterminantVandermondeComparisonGate

/--
Bosonization interpretation gate.

The Klein-factor anticommutation, vertex-operator OPE, and analytic CFT
realization are supplied by an owner model.  This finite module only owns the
exterior-state algebra and trace product.
-/
structure MobiusFermionBosonizationGate
    (PrimeLabel KleinFactor VertexOperator
      DeterminantReadout VandermondeReadout
      CFTCentralCharge ScaleDensityReadout : Type*) where
  cft_charge_unit : Prop
  arithmetic_energy_separate : Prop
  klein_anticommutation_law : Prop
  vertex_ope_law : Prop
  determinant_vandermonde :
    DeterminantVandermondeComparisonGate
      DeterminantReadout VandermondeReadout
  central_charge_guardrail :
    CentralChargeGuardrail CFTCentralCharge ScaleDensityReadout
  certificate :
    cft_charge_unit ∧
      arithmetic_energy_separate ∧
        klein_anticommutation_law ∧
          vertex_ope_law

namespace MobiusFermionBosonizationGate

/-- Re-export of the supplied Klein-factor anticommutation law. -/
theorem klein_anticommutation
    {PrimeLabel KleinFactor VertexOperator
      DeterminantReadout VandermondeReadout
      CFTCentralCharge ScaleDensityReadout : Type*}
    (G : MobiusFermionBosonizationGate
      PrimeLabel KleinFactor VertexOperator
      DeterminantReadout VandermondeReadout
      CFTCentralCharge ScaleDensityReadout) :
    G.klein_anticommutation_law :=
  G.certificate.2.2.1

/-- Re-export of the supplied vertex-OPE law. -/
theorem vertex_ope
    {PrimeLabel KleinFactor VertexOperator
      DeterminantReadout VandermondeReadout
      CFTCentralCharge ScaleDensityReadout : Type*}
    (G : MobiusFermionBosonizationGate
      PrimeLabel KleinFactor VertexOperator
      DeterminantReadout VandermondeReadout
      CFTCentralCharge ScaleDensityReadout) :
    G.vertex_ope_law :=
  G.certificate.2.2.2

/-- Re-export of the supplied determinant/Vandermonde comparison. -/
theorem determinant_vandermonde_valid
    {PrimeLabel KleinFactor VertexOperator
      DeterminantReadout VandermondeReadout
      CFTCentralCharge ScaleDensityReadout : Type*}
    (G : MobiusFermionBosonizationGate
      PrimeLabel KleinFactor VertexOperator
      DeterminantReadout VandermondeReadout
      CFTCentralCharge ScaleDensityReadout) :
    G.determinant_vandermonde.compare
      G.determinant_vandermonde.determinant
      G.determinant_vandermonde.vandermonde :=
  G.determinant_vandermonde.valid

end MobiusFermionBosonizationGate

end InfoGeometry.Arithmetic.MobiusFermionBosonization
