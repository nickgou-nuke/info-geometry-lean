import InfoGeometry.Canonical.CompletionPathway
import InfoGeometry.Canonical.TomitaKreinNilpotentAtom
import InfoGeometry.External.Virasoro.Sugawara

open scoped InnerProductSpace

/-!
# Finite Clifford lattice and supplied current hierarchy

Boundary packet for the theorem-owned finite architecture:

1. finite doubled real `Cl(1,1)` nilpotent/idempotent atom;
2. the complete finite-level Cantor-Krein projection lattice and its adjacent-level Galois connection;
3. supplied source-side normal-ordered Heisenberg current law;
4. external Sugawara/Virasoro representation.

This module does not assert an unconstructed infinite or self-similar completion,
and deliberately does not claim that the finite complete lattice generates
Heisenberg, Kac-Moody, or Virasoro by itself.  The current/conformal layer is
available only after supplied `heiOper`, `heiTrunc`, and `hComm` data, i.e.
after the normal-ordered current construction and local truncation have been
provided.
-/

namespace InfoGeometry.Canonical.CliffordCompleteLatticeCurrentHierarchy

open InfoGeometry.Canonical.CompletionPathway
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom
open InfoGeometry.Krein
open Filter
open VirasoroProject

section Packet

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The theorem-level packet for the finite hierarchy.

The finite complete-lattice field is order-theoretic closure data.  The
`source_heisenberg_commutator` and `external_sugawara_central` fields are
available only from a supplied source-side current datum; this preserves the
boundary between sector completion and current construction.
-/
def FiniteLatticeCurrentHierarchyPacket
    (n : ℕ)
    (heiOper : ℤ → DoubledSpace E →ₗ[ℝ] DoubledSpace E)
    (heiTrunc : ∀ v : DoubledSpace E, ∀ᶠ k : ℤ in atTop, heiOper k v = 0)
    (hComm :
      ∀ m q : ℤ,
        (heiOper m).commutator (heiOper q) =
          if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0) :
    Prop :=
  (∀ T : Set (FiniteProjectionCompletion n), IsLUB T (sSup T) ∧ IsGLB T (sInf T)) ∧
  GaloisConnection (@refineProjectionAssignment n) (@coarseProjectionAssignment n) ∧
  ((concreteCARCreation (E := E)).comp (concreteCARCreation (E := E)) = 0
      ∧ (concreteCARAnnihilation (E := E)).comp
          (concreteCARAnnihilation (E := E)) = 0
      ∧ (concreteCARCreation (E := E)).comp (concreteCARAnnihilation (E := E))
          = spectralPlusProj (E := E)
      ∧ (concreteCARAnnihilation (E := E)).comp (concreteCARCreation (E := E))
          = spectralMinusProj (E := E)
      ∧ CCRBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARAnnihilation (E := E))
          = spectral_epsilon (E := E)) ∧
  (∀ m q : ℤ,
      (heiOper m).commutator (heiOper q) =
        if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0) ∧
  VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc hComm
      (VirasoroAlgebra.cgen ℝ) = 1

namespace FiniteLatticeCurrentHierarchyPacket

variable {n : ℕ}
variable {heiOper : ℤ → DoubledSpace E →ₗ[ℝ] DoubledSpace E}
variable {heiTrunc : ∀ v : DoubledSpace E, ∀ᶠ k : ℤ in atTop, heiOper k v = 0}
variable {hComm :
      ∀ m q : ℤ,
        (heiOper m).commutator (heiOper q) =
          if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0}

theorem finite_projection_complete
    (P : FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
    ∀ T : Set (FiniteProjectionCompletion n), IsLUB T (sSup T) ∧ IsGLB T (sInf T) :=
  P.1

theorem refinement_coarse_galois
    (P : FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
    GaloisConnection (@refineProjectionAssignment n) (@coarseProjectionAssignment n) :=
  P.2.1

theorem finite_split_null_atom
    (P : FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
    (concreteCARCreation (E := E)).comp (concreteCARCreation (E := E)) = 0
      ∧ (concreteCARAnnihilation (E := E)).comp
          (concreteCARAnnihilation (E := E)) = 0
      ∧ (concreteCARCreation (E := E)).comp (concreteCARAnnihilation (E := E))
          = spectralPlusProj (E := E)
      ∧ (concreteCARAnnihilation (E := E)).comp (concreteCARCreation (E := E))
          = spectralMinusProj (E := E)
      ∧ CCRBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARAnnihilation (E := E))
          = spectral_epsilon (E := E) :=
  P.2.2.1

theorem source_heisenberg_commutator
    (P : FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm)
    (m q : ℤ) :
    (heiOper m).commutator (heiOper q) =
      if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0 :=
  P.2.2.2.1 m q

theorem external_sugawara_central
    (P : FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
    VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc hComm
      (VirasoroAlgebra.cgen ℝ) = 1 :=
  P.2.2.2.2

end FiniteLatticeCurrentHierarchyPacket

/--
The corrected hierarchy is kernel-checked as a boundary packet:
finite-level complete projection closure, finite split-null atom, source Heisenberg current
law, and external Sugawara central action.

This is not a proof that the projection lattice alone derives the current
algebra.  The supplied `heiOper`, `heiTrunc`, and `hComm` arguments are exactly
the missing source-side normal-ordered current datum.
-/
@[rep_depth transport]
theorem finite_lattice_current_hierarchy_packet
    (n : ℕ)
    (heiOper : ℤ → DoubledSpace E →ₗ[ℝ] DoubledSpace E)
    (heiTrunc : ∀ v : DoubledSpace E, ∀ᶠ k : ℤ in atTop, heiOper k v = 0)
    (hComm :
      ∀ m q : ℤ,
        (heiOper m).commutator (heiOper q) =
          if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0) :
    FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm := by
  refine ⟨?_, projectionAssignment_galoisConnection n, ?_, hComm, ?_⟩
  · intro T
    refine ⟨?_, ?_⟩
    · exact finiteProjectionCompletion_sSup_isLUB n T
    · exact finiteProjectionCompletion_sInf_isGLB n T
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact concrete_creation_square_zero (E := E)
    · exact concrete_annihilation_square_zero (E := E)
    · exact concrete_creation_comp_annihilation_eq_spectralPlusProj (E := E)
    · exact concrete_annihilation_comp_creation_eq_spectralMinusProj (E := E)
    · exact concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon (E := E)
  · exact VirasoroProject.sugawaraRepresentation_cgen (heiOper := heiOper) heiTrunc hComm

/--
Readback: the complete-lattice part of the packet is strictly order-theoretic.
-/
@[rep_depth transport]
theorem packet_refinement_coarse_galois
    {n : ℕ} {heiOper : ℤ → DoubledSpace E →ₗ[ℝ] DoubledSpace E}
    {heiTrunc : ∀ v : DoubledSpace E, ∀ᶠ k : ℤ in atTop, heiOper k v = 0}
    {hComm :
      ∀ m q : ℤ,
        (heiOper m).commutator (heiOper q) =
          if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0}
    (P : FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
    GaloisConnection (@refineProjectionAssignment n) (@coarseProjectionAssignment n) :=
  P.refinement_coarse_galois

/--
Readback: the finite base of the packet is the split-null
nilpotent/idempotent `Cl(1,1)` atom.
-/
@[rep_depth transport]
theorem packet_finite_split_null_atom
    {n : ℕ} {heiOper : ℤ → DoubledSpace E →ₗ[ℝ] DoubledSpace E}
    {heiTrunc : ∀ v : DoubledSpace E, ∀ᶠ k : ℤ in atTop, heiOper k v = 0}
    {hComm :
      ∀ m q : ℤ,
        (heiOper m).commutator (heiOper q) =
          if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0}
    (P : FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
    (concreteCARCreation (E := E)).comp (concreteCARCreation (E := E)) = 0
      ∧ (concreteCARAnnihilation (E := E)).comp
          (concreteCARAnnihilation (E := E)) = 0
      ∧ (concreteCARCreation (E := E)).comp (concreteCARAnnihilation (E := E))
          = spectralPlusProj (E := E)
      ∧ (concreteCARAnnihilation (E := E)).comp (concreteCARCreation (E := E))
          = spectralMinusProj (E := E)
      ∧ CCRBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARAnnihilation (E := E))
          = spectral_epsilon (E := E) :=
  P.finite_split_null_atom

/--
Readback: the source Heisenberg law is part of the supplied mode-current data,
not a consequence of the complete-lattice layer alone.
-/
@[rep_depth transport]
theorem packet_source_heisenberg_commutator
    {n : ℕ} {heiOper : ℤ → DoubledSpace E →ₗ[ℝ] DoubledSpace E}
    {heiTrunc : ∀ v : DoubledSpace E, ∀ᶠ k : ℤ in atTop, heiOper k v = 0}
    {hComm :
      ∀ m q : ℤ,
        (heiOper m).commutator (heiOper q) =
          if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0}
    (P : FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm)
    (m q : ℤ) :
    (heiOper m).commutator (heiOper q) =
      if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0 :=
  P.source_heisenberg_commutator m q

/--
Readback: the current/conformal part of the packet is supplied by the
source-side Heisenberg datum and consumed by the external Sugawara construction.
-/
@[rep_depth transport]
theorem packet_external_sugawara_central
    {n : ℕ} {heiOper : ℤ → DoubledSpace E →ₗ[ℝ] DoubledSpace E}
    {heiTrunc : ∀ v : DoubledSpace E, ∀ᶠ k : ℤ in atTop, heiOper k v = 0}
    {hComm :
      ∀ m q : ℤ,
        (heiOper m).commutator (heiOper q) =
          if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0}
    (P : FiniteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
    VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc hComm
      (VirasoroAlgebra.cgen ℝ) = 1 :=
  P.external_sugawara_central

end Packet

end InfoGeometry.Canonical.CliffordCompleteLatticeCurrentHierarchy
