import InfoGeometry.Canonical.CompletionPathway
import InfoGeometry.Canonical.TomitaKreinNilpotentAtom
import InfoGeometry.External.Virasoro.Sugawara

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CliffordCompleteLatticeCurrentHierarchy

Boundary packet for the full four-tier architecture:

1. finite doubled real `Cl(1,1)` nilpotent/idempotent atom;
2. complete Cantor-Krein projection lattice and self-similar fixed-point layer;
3. supplied source-side normal-ordered Heisenberg current law;
4. external Sugawara/Virasoro representation.

This module deliberately does not claim that the complete lattice generates
Heisenberg, Kac-Moody, or Virasoro by itself.  The current/conformal layer is
available only after supplied `heiOper`, `heiTrunc`, and `hComm` data, i.e.
after the normal-ordered current construction and local truncation have been
provided.
-/

namespace InfoGeometry.Canonical.CliffordCompleteLatticeCurrentHierarchy

open InfoGeometry.Canonical.CompletionPathway
open InfoGeometry.Canonical.SectorLattice
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom
open InfoGeometry.Krein
open Filter
open VirasoroProject

section Packet

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The theorem-level packet for the corrected hierarchy.

The complete-lattice fields are order-theoretic closure data.  The
`source_heisenberg_commutator` and `external_sugawara_central` fields are
available only from a supplied source-side current datum; this preserves the
boundary between sector completion and current construction.
-/
structure CompleteLatticeCurrentHierarchyPacket
    (n : ℕ)
    (heiOper : ℤ → DoubledSpace E →ₗ[ℝ] DoubledSpace E)
    (heiTrunc : ∀ v : DoubledSpace E, ∀ᶠ k : ℤ in atTop, heiOper k v = 0)
    (hComm :
      ∀ m q : ℤ,
        (heiOper m).commutator (heiOper q) =
          if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0) :
    Prop where
  finite_projection_complete :
    ∀ T : Set (FiniteProjectionCompletion n), IsLUB T (sSup T) ∧ IsGLB T (sInf T)
  infinite_projection_complete :
    ∀ T : Set InfiniteProjectionCompletion, IsLUB T (sSup T) ∧ IsGLB T (sInf T)
  self_similar_projection_complete :
    ∀ T : Set SelfSimilarProjectionCompletion, IsLUB T (sSup T) ∧ IsGLB T (sInf T)
  refinement_coarse_galois :
    GaloisConnection (@refineProjectionAssignment n) (@coarseProjectionAssignment n)
  finite_split_null_atom :
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
          = spectral_epsilon (E := E)
  source_heisenberg_commutator :
    ∀ m q : ℤ,
      (heiOper m).commutator (heiOper q) =
        if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0
  external_sugawara_central :
    VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc hComm
      (VirasoroAlgebra.cgen ℝ) = 1

/--
The corrected hierarchy is kernel-checked as a boundary packet:
complete projection closure, finite split-null atom, source Heisenberg current
law, and external Sugawara central action.

This is not a proof that the projection lattice alone derives the current
algebra.  The supplied `heiOper`, `heiTrunc`, and `hComm` arguments are exactly
the missing source-side normal-ordered current datum.
-/
@[rep_depth transport]
theorem complete_lattice_current_hierarchy_packet
    (n : ℕ)
    (heiOper : ℤ → DoubledSpace E →ₗ[ℝ] DoubledSpace E)
    (heiTrunc : ∀ v : DoubledSpace E, ∀ᶠ k : ℤ in atTop, heiOper k v = 0)
    (hComm :
      ∀ m q : ℤ,
        (heiOper m).commutator (heiOper q) =
          if m + q = 0 then (m : ℝ) • (1 : DoubledSpace E →ₗ[ℝ] DoubledSpace E) else 0) :
    CompleteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm := by
  rcases completeLatticeProjectionArchitecture n with
    ⟨hfinite, hinfinite, hself, hrefine⟩
  refine
    { finite_projection_complete := hfinite
      infinite_projection_complete := hinfinite
      self_similar_projection_complete := hself
      refinement_coarse_galois := hrefine
      finite_split_null_atom := by
        exact ⟨concrete_creation_square_zero (E := E),
          concrete_annihilation_square_zero (E := E),
          concrete_creation_comp_annihilation_eq_spectralPlusProj (E := E),
          concrete_annihilation_comp_creation_eq_spectralMinusProj (E := E),
          concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon (E := E)⟩
      source_heisenberg_commutator := hComm
      external_sugawara_central := by
        exact VirasoroProject.sugawaraRepresentation_cgen (heiOper := heiOper) heiTrunc hComm }

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
    (P : CompleteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
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
    (P : CompleteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
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
    (P : CompleteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm)
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
    (P : CompleteLatticeCurrentHierarchyPacket n heiOper heiTrunc hComm) :
    VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc hComm
      (VirasoroAlgebra.cgen ℝ) = 1 :=
  P.external_sugawara_central

end Packet

end InfoGeometry.Canonical.CliffordCompleteLatticeCurrentHierarchy
