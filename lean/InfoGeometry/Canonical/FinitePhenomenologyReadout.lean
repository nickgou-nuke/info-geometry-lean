import InfoGeometry.Canonical.TrifactorDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

namespace InfoGeometry.Canonical.FinitePhenomenologyReadout

open InfoGeometry.Canonical.TrifactorDecomposition
open InfoGeometry.Canonical.EvansHarmonicTrap
open InfoGeometry.Canonical.BostConnesSuperalgebraConstructive
open InfoGeometry.Canonical.CreationAnnihilationTomitaBridge
open InfoGeometry.Canonical.CelikErlangenBraidBridge

/-! ## Trifactor null-sector readout -/

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/--
Finite "superlocalization" readout: for a tripotent operator, the null
projector is annihilated by the operator.
-/
alias superlocalization_null_projector_readout := T_on_P_zero

/-- Finite sector partition readout for the three trifactor projectors. -/
alias trifactor_sector_partition_readout := partition_of_unity

/-! ## Evans harmonic-trap readout -/

/-- The left edge of the finite harmonic trap is locally fixed. -/
alias trap_left_edge_readout := harmonic_trap_invariant_left

/-- The right edge of the finite harmonic trap is locally fixed. -/
alias trap_right_edge_readout := harmonic_trap_invariant_right

/-- The three-site finite harmonic trap is fixed by both adjacent updates. -/
alias harmonic_trap_readout := harmonic_trap_pairwise_invariant

/-! ## Tomita creation/annihilation readout -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Finite "goldstino" label: the imbalance `c - a` is Tomita-odd. -/
alias goldstino_odd_density_readout := TomitaLadderPair.oddDensity_mem_oddSector

/-- Finite Bose/Fermi pairing label: the Majorana sum `c + a` is Tomita-even. -/
alias bose_fermi_pairing_even_readout := TomitaLadderPair.evenMajorana_mem_evenSector

/-! ## Witten parity supertrace readout -/

variable {A : Type*} [Ring A] [StarRing A]

/--
Finite "vortex-pinning" label: a parity-invariant state has zero supertrace on
an explicitly parity-odd element.
-/
alias parity_odd_supertrace_cancellation_readout := supertrace_eq_zero_of_invariant_state_on_odd

/--
Cuntz/CAR specialization: the Cuntz-derived odd CAR generator has zero
supertrace for a parity-invariant state.
-/
alias cuntz_car_supertrace_cancellation_readout :=
  ParityEquivariantCuntzCarrier.invariant_state_supertrace_carFromCuntz_eq_zero

/-! ## Finite braid-gate readout -/

/--
Finite "fractional Josephson" label: the concrete Z3 braid matrices satisfy the
closed Artin/Yang--Baxter identity owned by the braid bridge.
-/
alias finite_braid_gate_readout := z3_artin_relation_via_atoms

end InfoGeometry.Canonical.FinitePhenomenologyReadout

end noncomputable section
