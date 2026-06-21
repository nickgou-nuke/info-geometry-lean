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

  /--
  Concrete modular-derivation compatibility with the supplied modular
  generator.
  -/
  modularDerivation_eq_commutator :
    ∀ ω x,
      modularDerivation ω x =
        modularGenerator ω * x - x * modularGenerator ω

  /-- A polarization/sector is chosen downstream of a state. -/
  Polarization :
    StateSpace → Type uPol

  /-- Stabilizer predicate for a state under the symmetry action. -/
  stabilizer :
    StateSpace → Sym → Prop

  /--
  Concrete stabilizer criterion: a symmetry stabilizes a state precisely when
  it preserves all expectation readouts of that state.
  -/
  stabilizer_iff_eval_invariant :
    ∀ ω g,
      stabilizer ω g ↔
        ∀ x : Obs, eval ω ((symmetryAction.act g) x) = eval ω x

  /-- Exponential-family positive weight/readout shadow. -/
  exponentialWeight :
    StateSpace → Obs

  /-- Free-energy / Massieu / Legendre readout shadow. -/
  freeEnergyReadout :
    StateSpace → ℝ

  /--
  Concrete Legendre readout criterion used by this finite interface: the
  free-energy readout is the state evaluation of the supplied exponential
  weight.
  -/
  freeEnergyReadout_eq_eval_exponentialWeight :
    ∀ ω, freeEnergyReadout ω = eval ω (exponentialWeight ω)

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

/-- The modular derivation is the commutator with the supplied generator. -/
theorem modular_derivation_eq_commutator
    (ω : StateSpace)
    (x : Obs) :
    P.modularDerivation ω x =
      P.modularGenerator ω * x - x * P.modularGenerator ω :=
  P.modularDerivation_eq_commutator ω x

/-- Stabilizer membership is expectation invariance under the symmetry action. -/
theorem stabilizer_iff_eval_invariant_readback
    (ω : StateSpace)
    (g : Sym) :
    P.stabilizer ω g ↔
      ∀ x : Obs, P.eval ω ((P.symmetryAction.act g) x) = P.eval ω x :=
  P.stabilizer_iff_eval_invariant ω g

/-- The free-energy readout is evaluation of the supplied exponential weight. -/
theorem freeEnergyReadout_eq_eval_exponentialWeight_readback
    (ω : StateSpace) :
    P.freeEnergyReadout ω = P.eval ω (P.exponentialWeight ω) :=
  P.freeEnergyReadout_eq_eval_exponentialWeight ω

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

  /--
  Supplied equivalence between critical-line zeroes and spectral values.

  This is the nontrivial Hilbert--Polya content and remains explicitly
  hypothesis-bearing.
  -/
  zero_iff_spectral_value :
    ∀ γ : ℝ,
      completedZeta ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) = 0 ↔
        IsSpectralValue γ

namespace HilbertPolyaOperatorPacket

variable (P : HilbertPolyaOperatorPacket.{uH, uD})

/--
If a Hilbert--Polya packet is supplied, its critical-line zeroes are exactly
the spectral values supplied by the packet.
-/
theorem criticalLine_zero_iff_spectral_value :
    ∀ γ : ℝ,
      P.completedZeta ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) = 0 ↔
        P.IsSpectralValue γ :=
  P.zero_iff_spectral_value

end HilbertPolyaOperatorPacket

end InfoGeometry.OperatorAlgebra.OperatorErlangenLegendre
