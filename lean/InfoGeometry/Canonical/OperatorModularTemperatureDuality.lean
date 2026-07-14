import Mathlib
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Canonical.OperatorFenchelRegularCone
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.OperatorModularTemperatureDuality

Operator-valued modular Hamiltonian / beta-temperature duality.

This file formulates the theorem-safe operator Fenchel/Frobenius socket:

* `K` is a modular Hamiltonian/operator generator;
* `Β` is an operator-valued inverse-temperature/geometric-temperature coordinate;
* their thermodynamic action is read through a Frobenius trace pairing
  `τ (Β ⋆ K)`;
* the Fenchel contact and gap laws are explicit proof fields.

No full noncommutative Fenchel theorem, KMS theorem, Tomita theorem, or
Frobenius classification theorem is asserted here.
-/

noncomputable section

namespace OperatorModularTemperatureDuality

/--
Closed operator product with Frobenius trace.

`Op` is deliberately abstract. In concrete lanes it may be a continuous-linear
operator algebra, a Drazin-regular block, a finite matrix algebra, or a
localized Frobenius algebra.
-/
structure OperatorFrobeniusClosure (Op : Type*) where
  /-- Closed product on the operator carrier. -/
  product : Op → Op → Op

  /-- Trace/volume/readout functional. -/
  trace : Op → ℝ

  /-- Distinguished unit-like element, if the model supplies one. -/
  unit : Op

  /-- Closure predicate for admissible regular operators. -/
  closed : Op → Prop

  /-- Product closure on the admissible sector. -/
  product_closed :
    ∀ X Y : Op, closed X → closed Y → closed (product X Y)

  /-- Frobenius associativity of the trace pairing. -/
  frobenius_trace :
    ∀ X Y Z : Op,
      trace (product (product X Y) Z) =
        trace (product X (product Y Z))

  /-- Optional symmetry/Jordan trace law. This is not automatic. -/
  trace_comm :
    ∀ X Y : Op, trace (product X Y) = trace (product Y X)

namespace OperatorFrobeniusClosure

variable {Op : Type*}
variable (F : OperatorFrobeniusClosure Op)

/-- Frobenius pairing induced by the chosen product and trace. -/
def pairing (X Y : Op) : ℝ :=
  F.trace (F.product X Y)

/-- Re-export product closure. -/
theorem product_mem_closed
    {X Y : Op}
    (hX : F.closed X) (hY : F.closed Y) :
    F.closed (F.product X Y) :=
  F.product_closed X Y hX hY

/-- Frobenius pairing is symmetric when the supplied trace-commutativity law holds. -/
theorem pairing_comm
    (X Y : Op) :
    F.pairing X Y = F.pairing Y X :=
  F.trace_comm X Y

/-- Frobenius invariance of the pairing under product reassociation. -/
theorem pairing_product_left
    (X Y Z : Op) :
    F.pairing (F.product X Y) Z =
      F.pairing X (F.product Y Z) :=
  F.frobenius_trace X Y Z

end OperatorFrobeniusClosure

/--
Operator-valued modular Hamiltonian / beta-temperature Fenchel pair.

`betaOperator` is the operator-valued inverse-temperature/geometric-temperature
coordinate. `modularHamiltonian` is the dual modular generator. The contact law
is the operator analogue of

`Ψ(β) + Φ(K) = <β,K>`.
-/
structure Duality (Op : Type*) where
  /-- Closed Frobenius operator algebra/readout surface. -/
  frobenius : OperatorFrobeniusClosure Op

  /-- Operator-valued inverse temperature / geometric temperature. -/
  betaOperator : Op

  /-- Modular Hamiltonian / log-density generator. -/
  modularHamiltonian : Op

  /-- Beta coordinate is in the closed regular sector. -/
  beta_closed : frobenius.closed betaOperator

  /-- Modular Hamiltonian is in the closed regular sector. -/
  modularHamiltonian_closed : frobenius.closed modularHamiltonian

  /-- Massieu/log-partition potential evaluated at the beta operator. -/
  massieu : ℝ

  /-- Dual entropy/free-energy potential evaluated at the modular Hamiltonian. -/
  dualPotential : ℝ

  /-- Operator action/readout `τ(Β ⋆ K)`. -/
  action : ℝ

  /-- Action is the Frobenius pairing of beta and modular Hamiltonian. -/
  action_eq_pairing :
    action =
      frobenius.pairing betaOperator modularHamiltonian

  /-- Fenchel contact law at the modular beta/K pair. -/
  fenchel_contact :
    massieu + dualPotential = action

  /--
  Fenchel gap law for arbitrary test modular Hamiltonians.

  This is a proof field because full operator Fenchel duality is not derived
  here.
  -/
  fenchel_gap_nonneg :
    ∀ K' : Op,
      frobenius.closed K' →
        0 ≤ massieu + dualPotential - frobenius.pairing betaOperator K'

variable {Op : Type*}
variable (D : Duality Op)

/-- The modular beta/K action is the Frobenius trace of their product. -/
theorem action_eq_trace_product :
    D.action =
      D.frobenius.trace
        (D.frobenius.product D.betaOperator D.modularHamiltonian) :=
  D.action_eq_pairing

/-- The beta/K pair satisfies the operator Fenchel contact identity. -/
theorem contact_balance :
    D.massieu + D.dualPotential =
      D.frobenius.pairing D.betaOperator D.modularHamiltonian := by
  rw [← D.action_eq_pairing]
  exact D.fenchel_contact

/-- The Fenchel gap at the contact modular Hamiltonian is zero. -/
theorem fenchel_gap_eq_zero_at_contact :
    D.massieu + D.dualPotential -
      D.frobenius.pairing D.betaOperator D.modularHamiltonian = 0 := by
  rw [← contact_balance D]
  ring

/-- Re-export the supplied Fenchel-gap nonnegativity law. -/
theorem fenchel_gap_nonneg_of_closed
    (K' : Op) (hK' : D.frobenius.closed K') :
    0 ≤ D.massieu + D.dualPotential -
      D.frobenius.pairing D.betaOperator K' :=
  D.fenchel_gap_nonneg K' hK'

/-- The beta/K product remains in the closed regular operator sector. -/
theorem beta_mul_modularHamiltonian_closed :
    D.frobenius.closed
      (D.frobenius.product D.betaOperator D.modularHamiltonian) :=
  D.frobenius.product_closed
    D.betaOperator D.modularHamiltonian
    D.beta_closed D.modularHamiltonian_closed

/--
Modular-flow realization of the operator duality.

This adds the Connes/modular flow side: the modular Hamiltonian generates a
one-parameter automorphism flow, and the beta operator is a closed observable
whose product with the generator gives the action.
-/
structure ModularFlowOperatorDuality
    (H Op : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  /-- Operator duality packet. -/
  duality : Duality Op

  /-- Carrier map into the doubled-space endomorphism algebra used by ConnesCocycle. -/
  toAlgebraEnd :
    Op → InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H

  /-- The modular Hamiltonian as an endomorphism generator. -/
  generator :
    InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H

  /-- The abstract modular Hamiltonian maps to the flow generator. -/
  generator_eq_modularHamiltonian :
    generator = toAlgebraEnd duality.modularHamiltonian

  /-- Additive modular flow generated by `generator`. -/
  modularFlow :
    InfoGeometry.Volume.ConnesCocycle.AdditiveModularFlow (H := H)

  /-- The modular flow is the exponential-conjugation flow generated by `generator`. -/
  modularFlow_eq_generated :
    modularFlow =
      InfoGeometry.Volume.ConnesCocycle.additiveModularFlowOfGenerator
        (H := H) generator

namespace ModularFlowOperatorDuality

variable {H Op : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (M : ModularFlowOperatorDuality H Op)

/-- The modular flow is generated by the mapped modular Hamiltonian. -/
theorem modularFlow_eq_generated_by_modularHamiltonian :
    M.modularFlow =
      InfoGeometry.Volume.ConnesCocycle.additiveModularFlowOfGenerator
        (H := H) (M.toAlgebraEnd M.duality.modularHamiltonian) := by
  rw [M.modularFlow_eq_generated, M.generator_eq_modularHamiltonian]

/-- The beta/K contact balance in the underlying operator duality. -/
theorem contact_balance :
    M.duality.massieu + M.duality.dualPotential =
      M.duality.frobenius.pairing
        M.duality.betaOperator M.duality.modularHamiltonian :=
  InfoGeometry.Canonical.OperatorModularTemperatureDuality.contact_balance M.duality

end ModularFlowOperatorDuality

end OperatorModularTemperatureDuality
