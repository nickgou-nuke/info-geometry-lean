import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative

/-!
# Operator Erlangen--Legendre principle

This file records the theorem-safe foundation layer:

* an observable algebra comes first;
* symmetries act by algebra automorphisms;
* states/weights supply physical readouts;
* modular/logarithmic data and Legendre/exponential-family readouts are
  downstream of a state choice;
* spectra, determinants, and diagonal coordinates are readouts, not primitive
  ontology.

The modular derivation, stabilizer predicate, and free-energy readout are
defined from the stored noncommutative data below; their compatibility laws
are derived theorems rather than supplied proof fields.  This file does not
construct a Tomita--Takesaki theory, prove a trace formula, or prove a
Hilbert--Polya operator for the Riemann zeroes.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorErlangenLegendre

universe uObs uSym uState uPol uH uD

/--
Operator Erlangen--Legendre packet.

The source object is an observable algebra with symmetry action.  A state or
weight then selects a sector/polarization and supplies expectation and
correlation readouts.  Modular and exponential/Legendre data are carried as
explicit laws, because the analytic operator-algebraic substrate is not proved
in this file.
-/
structure OperatorErlangenLegendrePacket
    (Obs : Type uObs)
    (Sym : Type uSym)
    (StateSpace : Type uState)
    [Ring Obs]
    [Group Sym] where
  /-- Symmetries act on observables by algebra automorphisms. -/
  symmetryAction :
    SymmetryAction Sym Obs

  /-- State/weight evaluation, the basic observable readout. -/
  eval :
    StateSpace → Obs → ℝ

  /-- Two-point correlation readout. -/
  correlation₂ :
    StateSpace → Obs → Obs → ℝ

  /-- Finite correlation readout. -/
  correlationList :
    StateSpace → List Obs → ℝ

  /-- Modular flow attached to a state/weight. -/
  modularFlow :
    StateSpace → ℝ → Obs → Obs

  /-- Logarithmic/modular generator attached to a state/weight. -/
  modularGenerator :
    StateSpace → Obs

  /-- A polarization/sector is chosen downstream of a state. -/
  Polarization :
    StateSpace → Type uPol

  /-- Exponential-family positive weight/readout shadow. -/
  exponentialWeight :
    StateSpace → Obs

  /--
  Guard: spectra and determinant counts are downstream readouts, not the
  foundation layer.
  -/
  noSpectraFirstGuardCarrier :
    Type

  /--
  Guard: finite diagonal/Cartan coordinates are representation shadows, not
  primitive observable-algebra data.
  -/
  noDiagonalPrimitiveGuardCarrier :
    Type

namespace OperatorErlangenLegendrePacket

variable
    {Obs : Type uObs}
    {Sym : Type uSym}
    {StateSpace : Type uState}
    [Ring Obs]
    [Group Sym]

variable (P : OperatorErlangenLegendrePacket Obs Sym StateSpace)

/-! These are derived from the observable algebra and its state readout.  The
packet therefore carries no proof-valued copies of these identities. -/

def modularDerivation
    (ω : StateSpace)
    (x : Obs) : Obs :=
  P.modularGenerator ω * x - x * P.modularGenerator ω

def stabilizer
    (ω : StateSpace)
    (g : Sym) : Prop :=
  ∀ x : Obs, P.eval ω ((P.symmetryAction.act g) x) = P.eval ω x

def freeEnergyReadout
    (ω : StateSpace) : ℝ :=
  P.eval ω (P.exponentialWeight ω)

/-- The modular derivation is the commutator with the supplied generator. -/
theorem modular_derivation_commutator
    (ω : StateSpace)
    (x : Obs) :
    P.modularDerivation ω x =
      P.modularGenerator ω * x - x * P.modularGenerator ω :=
  rfl

/-- Stabilizer membership is expectation invariance under the symmetry action. -/
theorem stabilizer_iff_eval_invariant
    (ω : StateSpace)
    (g : Sym) :
    P.stabilizer ω g ↔
      ∀ x : Obs, P.eval ω ((P.symmetryAction.act g) x) = P.eval ω x :=
  Iff.rfl

/-- The free-energy readout is evaluation of the supplied exponential weight. -/
theorem freeEnergyReadout_eq_eval_exponentialWeight
    (ω : StateSpace) :
    P.freeEnergyReadout ω = P.eval ω (P.exponentialWeight ω) :=
  rfl

/-- The state stabilizer as a set of symmetries. -/
def StateStabilizer
    (ω : StateSpace) :
    Set Sym :=
  {g | P.stabilizer ω g}

/-- Membership in the state stabilizer is exactly the supplied stabilizer predicate. -/
theorem mem_stateStabilizer_iff
    (ω : StateSpace)
    (g : Sym) :
    g ∈ P.StateStabilizer ω ↔ P.stabilizer ω g :=
  Iff.rfl

/-- Guard exposing that spectra are downstream readouts, not first principles here. -/
def spectraFirstGuard :
    Type :=
  P.noSpectraFirstGuardCarrier

@[simp] theorem spectraFirstGuard_eq :
    P.spectraFirstGuard = P.noSpectraFirstGuardCarrier :=
  rfl

/-- Guard exposing that diagonal data are not primitive owner data. -/
def diagonalPrimitiveGuard :
    Type :=
  P.noDiagonalPrimitiveGuardCarrier

@[simp] theorem diagonalPrimitiveGuard_eq :
    P.diagonalPrimitiveGuard = P.noDiagonalPrimitiveGuardCarrier :=
  rfl

end OperatorErlangenLegendrePacket

/-- Native operator Erlangen--Legendre readout theorem. -/
theorem operatorErlangenLegendre
    {Obs : Type uObs} {Sym : Type uSym} {StateSpace : Type uState}
    [Ring Obs] [Group Sym] :
    ∀ P : OperatorErlangenLegendrePacket.{uObs, uSym, uState, uPol} Obs Sym StateSpace,
      (∀ (ω : StateSpace) (x : Obs),
        P.modularDerivation ω x =
          P.modularGenerator ω * x - x * P.modularGenerator ω) ∧
      (∀ (ω : StateSpace) (g : Sym),
        P.stabilizer ω g ↔
          ∀ x : Obs, P.eval ω ((P.symmetryAction.act g) x) = P.eval ω x) ∧
      (∀ ω : StateSpace,
        P.freeEnergyReadout ω = P.eval ω (P.exponentialWeight ω)) := by
  intro P
  exact ⟨
    (fun ω x => P.modular_derivation_commutator ω x),
    (fun ω g => P.stabilizer_iff_eval_invariant ω g),
    (fun ω => P.freeEnergyReadout_eq_eval_exponentialWeight ω)⟩


end InfoGeometry.OperatorAlgebra.OperatorErlangenLegendre
