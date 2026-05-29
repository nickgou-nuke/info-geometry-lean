import Mathlib
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

It is intentionally a witness-gated owner surface.  It does not construct a
Tomita--Takesaki theory, prove a trace formula, or prove a Hilbert--Polya
operator for the Riemann zeroes.
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

  /-- Modular derivation readout. -/
  modularDerivation :
    StateSpace → Obs → Obs

  /-- Supplied law saying the modular derivation has the intended behavior. -/
  modularDerivation_law :
    Prop

  /-- Proof/witness of the modular derivation law. -/
  modularDerivation_valid :
    modularDerivation_law

  /-- A polarization/sector is chosen downstream of a state. -/
  Polarization :
    StateSpace → Type uPol

  /-- Stabilizer predicate for a state under the symmetry action. -/
  stabilizer :
    StateSpace → Sym → Prop

  /-- Supplied law governing the stabilizer/sector-selection interpretation. -/
  stabilizer_law :
    Prop

  /-- Proof/witness of the stabilizer law. -/
  stabilizer_valid :
    stabilizer_law

  /-- Exponential-family positive weight/readout shadow. -/
  exponentialWeight :
    StateSpace → Obs

  /-- Free-energy / Massieu / Legendre readout shadow. -/
  freeEnergyReadout :
    StateSpace → ℝ

  /-- Supplied law tying exponential weights to Legendre/free-energy readouts. -/
  exponentialLegendre_law :
    Prop

  /-- Proof/witness of the exponential/Legendre law. -/
  exponentialLegendre_valid :
    exponentialLegendre_law

  /--
  Guard: spectra and determinant counts are downstream readouts, not the
  foundation layer.
  -/
  noSpectraFirstWitness :
    Type

  /--
  Guard: finite diagonal/Cartan coordinates are representation shadows, not
  primitive observable-algebra data.
  -/
  noDiagonalPrimitiveWitness :
    Type

namespace OperatorErlangenLegendrePacket

variable
    {Obs : Type uObs}
    {Sym : Type uSym}
    {StateSpace : Type uState}
    [Ring Obs]
    [Group Sym]

variable (P : OperatorErlangenLegendrePacket Obs Sym StateSpace)

/-- The supplied modular-derivation law is available as a theorem. -/
theorem modular_derivation_law :
    P.modularDerivation_law :=
  P.modularDerivation_valid

/-- The supplied stabilizer/sector-selection law is available as a theorem. -/
theorem stabilizer_law_valid :
    P.stabilizer_law :=
  P.stabilizer_valid

/-- The supplied exponential/Legendre law is available as a theorem. -/
theorem exponential_legendre_law_valid :
    P.exponentialLegendre_law :=
  P.exponentialLegendre_valid

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
  P.noSpectraFirstWitness

@[simp] theorem spectraFirstGuard_eq :
    P.spectraFirstGuard = P.noSpectraFirstWitness :=
  rfl

/-- Guard exposing that diagonal data are not primitive owner data. -/
def diagonalPrimitiveGuard :
    Type :=
  P.noDiagonalPrimitiveWitness

@[simp] theorem diagonalPrimitiveGuard_eq :
    P.diagonalPrimitiveGuard = P.noDiagonalPrimitiveWitness :=
  rfl

end OperatorErlangenLegendrePacket

/-- Owner target for a supplied operator Erlangen--Legendre packet. -/
def OperatorErlangenLegendreTarget
    (Obs : Type uObs)
    (Sym : Type uSym)
    (StateSpace : Type uState)
    [Ring Obs]
    [Group Sym] : Prop :=
  Nonempty (OperatorErlangenLegendrePacket.{uObs, uSym, uState, uPol} Obs Sym StateSpace)

/-- Constructor for the operator Erlangen--Legendre owner target. -/
theorem constructOperatorErlangenLegendreTarget
    {Obs : Type uObs}
    {Sym : Type uSym}
    {StateSpace : Type uState}
    [Ring Obs]
    [Group Sym]
    (P : OperatorErlangenLegendrePacket.{uObs, uSym, uState, uPol} Obs Sym StateSpace) :
    OperatorErlangenLegendreTarget.{uObs, uSym, uState, uPol} Obs Sym StateSpace := by
  exact ⟨P⟩

/-! ## Conditional Hilbert--Polya socket -/

/--
Conditional Hilbert--Polya operator packet.

This is only a socket.  The zero/spectrum equivalence is a supplied field, not
a theorem proved here.  Therefore this file does not prove RH and does not
construct a self-adjoint Riemann-zero operator.
-/
structure HilbertPolyaOperatorPacket where
  /-- Underlying Hilbert/spectral carrier. -/
  SpectralCarrier :
    Type uH

  /-- Spectral generator datum. -/
  spectralGenerator :
    Type uD

  /-- Completed zeta/xi-style spectral determinant readout. -/
  completedZeta :
    ℂ → ℂ

  /-- Predicate that a real ordinate is a spectral value of the supplied generator. -/
  IsSpectralValue :
    ℝ → Prop

  /-- Supplied self-adjointness/symmetry witness. -/
  selfAdjointWitness :
    Prop

  /-- Proof/witness of self-adjointness/symmetry. -/
  selfAdjoint_valid :
    selfAdjointWitness

  /-- Supplied determinant/scattering/zeta witness. -/
  determinantWitness :
    Prop

  /-- Proof/witness of determinant/scattering/zeta compatibility. -/
  determinant_valid :
    determinantWitness

  /--
  Supplied equivalence between critical-line zeroes and spectral values.

  This is the nontrivial Hilbert--Polya content and remains explicitly
  hypothesis-bearing.
  -/
  zero_iff_spectral_value :
    ∀ γ : ℝ,
      completedZeta ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) = 0 ↔
        IsSpectralValue γ

  /-- Supplied functional-equation/reflection symmetry witness. -/
  functionalEquationSymmetry :
    Prop

  /-- Proof/witness of the functional-equation/reflection symmetry. -/
  functionalEquation_valid :
    functionalEquationSymmetry

namespace HilbertPolyaOperatorPacket

variable (P : HilbertPolyaOperatorPacket.{uH, uD})

/-- The supplied self-adjointness/symmetry witness is available. -/
theorem selfAdjoint_law :
    P.selfAdjointWitness :=
  P.selfAdjoint_valid

/-- The supplied determinant/scattering/zeta witness is available. -/
theorem determinant_law :
    P.determinantWitness :=
  P.determinant_valid

/--
If a Hilbert--Polya packet is supplied, its critical-line zeroes are exactly
the spectral values supplied by the packet.
-/
theorem criticalLine_zero_iff_spectral_value :
    ∀ γ : ℝ,
      P.completedZeta ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) = 0 ↔
        P.IsSpectralValue γ :=
  P.zero_iff_spectral_value

/-- The supplied functional-equation/reflection symmetry is available. -/
theorem functionalEquation_law :
    P.functionalEquationSymmetry :=
  P.functionalEquation_valid

end HilbertPolyaOperatorPacket

end InfoGeometry.OperatorAlgebra.OperatorErlangenLegendre

