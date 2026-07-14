import InfoGeometry.Canonical.TrifactorDecomposition
import InfoGeometry.Canonical.EvansHarmonicTrap
import InfoGeometry.Canonical.BostConnesSuperalgebraConstructive
import InfoGeometry.Canonical.CreationAnnihilationTomitaBridge
import InfoGeometry.Canonical.CelikErlangenBraidBridge

/-!
# Finite Phenomenology Readout

This module collects the finite algebraic readouts that may be used as a
dictionary for experimental or condensed-matter interpretations.

The words "superlocalization", "goldstino", "vortex pinning", and "fractional
Josephson" are used here only as labels for already-owned finite theorem
surfaces:

* `P_zero` is annihilated by a tripotent scale operator.
* `c - a` is odd under a Tomita swap, while `c + a` is even.
* parity-invariant states cancel parity-odd supertraces.
* the Evans three-site harmonic trap is pairwise fixed.
* the finite Z3 braid matrices satisfy the concrete Artin/Yang--Baxter readout.

No theorem in this file asserts an optical-lattice experiment, wavefunction
decay rate, Kibble--Zurek theorem, Josephson current spectrum, KMS phase
transition, C*-completion, zeta-zero theorem, or Riemann-hypothesis consequence.

#### BUCKET 1: CLOSED FINITE THEOREMS
Readbacks from the existing finite owners listed above.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The supertrace readouts depend on explicit parity/state/Cuntz witness data; the
Tomita odd/even readouts depend on an explicit `TomitaLadderPair`.

#### BUCKET 3: OPEN CLOSURE DEBT
Any continuum, topological, experimental, KMS/BEC, zeta, or RH interpretation.
-/

noncomputable section

namespace FinitePhenomenologyReadout

open InfoGeometry.Canonical.TrifactorDecomposition
open InfoGeometry.Canonical.EvansHarmonicTrap
open InfoGeometry.Canonical.BostConnesSuperalgebraConstructive
open InfoGeometry.Canonical.CreationAnnihilationTomitaBridge
open InfoGeometry.Canonical.CelikErlangenBraidBridge

/-! ## Trifactor null-sector readout -/

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

omit [Invertible (2 : R)] in
/--
Finite "superlocalization" readout: for a tripotent operator, the null
projector is annihilated by the operator.
-/
theorem superlocalization_null_projector_readout
    (T : R) (hT : T ^ 3 = T) :
    T * P_zero T = 0 :=
  T_on_P_zero T hT

/-- Finite sector partition readout for the three trifactor projectors. -/
theorem trifactor_sector_partition_readout (T : R) :
    P_zero T + P_plus T + P_minus T = 1 :=
  partition_of_unity T

/-! ## Evans harmonic-trap readout -/

/-- The left edge of the finite harmonic trap is locally fixed. -/
theorem trap_left_edge_readout :
    local_transition (LatticeCharge.coexact, LatticeCharge.harmonic) =
      (LatticeCharge.coexact, LatticeCharge.harmonic) :=
  harmonic_trap_invariant_left

/-- The right edge of the finite harmonic trap is locally fixed. -/
theorem trap_right_edge_readout :
    local_transition (LatticeCharge.harmonic, LatticeCharge.exact) =
      (LatticeCharge.harmonic, LatticeCharge.exact) :=
  harmonic_trap_invariant_right

/-- The three-site finite harmonic trap is fixed by both adjacent updates. -/
theorem harmonic_trap_readout :
    updateLeft harmonicTrap = harmonicTrap ∧
      updateRight harmonicTrap = harmonicTrap :=
  harmonic_trap_pairwise_invariant

/-! ## Tomita creation/annihilation readout -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Finite "goldstino" label: the imbalance `c - a` is Tomita-odd. -/
theorem goldstino_odd_density_readout (P : TomitaLadderPair V) :
    P.IsOddSector P.oddDensity :=
  P.oddDensity_mem_oddSector

/-- Finite Bose/Fermi pairing label: the Majorana sum `c + a` is Tomita-even. -/
theorem bose_fermi_pairing_even_readout (P : TomitaLadderPair V) :
    P.IsEvenSector P.evenMajorana :=
  P.evenMajorana_mem_evenSector

/-! ## Witten parity supertrace readout -/

variable {A : Type*} [Ring A] [StarRing A]

/--
Finite "vortex-pinning" label: a parity-invariant state has zero supertrace on
an explicitly parity-odd element.
-/
theorem parity_odd_supertrace_cancellation_readout
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityInvariant P φ) {x : A} (hx : ParityOdd P x) :
    supertrace P φ x = 0 :=
  supertrace_eq_zero_of_invariant_state_on_odd P φ hφ hx

/--
Cuntz/CAR specialization: the Cuntz-derived odd CAR generator has zero
supertrace for a parity-invariant state.
-/
theorem cuntz_car_supertrace_cancellation_readout
    (E : ParityEquivariantCuntzCarrier A)
    (φ : AlgebraicState A) (hφ : StateParityInvariant E.parity φ) :
    supertrace E.parity φ (InfoGeometry.Canonical.carFromCuntz E.cuntz) = 0 :=
  E.invariant_state_supertrace_carFromCuntz_eq_zero φ hφ

/-! ## Finite braid-gate readout -/

/--
Finite "fractional Josephson" label: the concrete Z3 braid matrices satisfy the
closed Artin/Yang--Baxter identity owned by the braid bridge.
-/
theorem finite_braid_gate_readout :
    ((InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix :
        Matrix (Fin 2) (Fin 2) ℝ) *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3RMatrix *
        InfoGeometry.Canonical.FibonacciParafermionAtoms.z3BMatrix) :=
  z3_artin_relation_via_atoms

end FinitePhenomenologyReadout

end noncomputable section
