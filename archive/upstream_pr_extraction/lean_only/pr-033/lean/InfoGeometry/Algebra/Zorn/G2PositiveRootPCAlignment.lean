import InfoGeometry.Algebra.Zorn.G2SteinbergPositiveRoots
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-!
# Positive-root packet versus PC generators

The current `positiveRootPacket` consists entirely of involutions.  The current
polycyclic generator packet `pcGenerator`, however, contains two elements of
order four: `pc2Aut` and `pc3Aut`, whose squares are the nontrivial involution
`pc6Aut`.

Consequently there is no index-preserving identification, and in fact no
reindexing by an equivalence `Fin 6 ≃ Fin 6`, between the two packets.

This is a structural guard theorem.  It prevents the Bruhat residual layer from
identifying Chevalley root coordinates with the chosen PC generator coordinates
without first constructing a genuine root-to-PC-word bridge.

/-!
# Separation of root-group and PC-generator carriers

The six elements in `positiveRootPacket` are involutions, as required for
the nontrivial elements of root groups over `𝔽₂`.  The ordered PC basis is a
polycyclic normal-form basis and is not a root-group basis: two of its
coordinates have order four.  Consequently no reindexing can identify the
two families.
-/

namespace InfoGeometry.Algebra.Zorn.G2PositiveRootPCAlignment

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2SteinbergRoots
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-- Every member of the current positive-root packet is an involution. -/
theorem positiveRootPacket_all_involutions (i : Fin 6) :
    positiveRootPacket i * positiveRootPacket i = 1 :=
  positiveRootPacket_sq i

/-- `pcGenerator 1 = pc2Aut` is not an involution. -/
theorem pcGenerator_one_not_involution :
    pcGenerator 1 * pcGenerator 1 ≠ (1 : SplitOctF2Aut) := by
  change pc2Aut * pc2Aut ≠ (1 : SplitOctF2Aut)
  rw [pc2Aut_sq_eq_pc6Aut]
  exact pc6Aut_ne_one

/-- `pcGenerator 2 = pc3Aut` is not an involution. -/
theorem pcGenerator_two_not_involution :
    pcGenerator 2 * pcGenerator 2 ≠ (1 : SplitOctF2Aut) := by
  change pc3Aut * pc3Aut ≠ (1 : SplitOctF2Aut)
  rw [pc3Aut_sq_eq_pc6Aut]
  exact pc6Aut_ne_one

/-- The two six-element packets do not even have the same range. -/
theorem positiveRootPacket_range_ne_pcGenerator_range :
    Set.range positiveRootPacket ≠ Set.range pcGenerator := by
  intro hRange
  have hmem : pcGenerator 1 ∈ Set.range positiveRootPacket := by
    rw [hRange]
    exact ⟨1, rfl⟩
  rcases hmem with ⟨i, hi⟩
  have hsquare := positiveRootPacket_sq i
  rw [hi] at hsquare
  exact pcGenerator_one_not_involution hsquare

/-- There is no equivalence of indices aligning the current root packet with
    the current PC generators pointwise. -/
theorem no_positiveRootPacket_pcGenerator_reindex
    (σ : Fin 6 ≃ Fin 6) :
    ¬ ∀ i : Fin 6, positiveRootPacket i = pcGenerator (σ i) := by
  intro h
  let i : Fin 6 := σ.symm 1
  have hi : σ i = 1 := σ.apply_symm_apply 1
  have hsquare : pcGenerator (σ i) * pcGenerator (σ i) =
      (1 : SplitOctF2Aut) := by
    rw [← h i]
    exact positiveRootPacket_sq i
  rw [hi] at hsquare
  exact pcGenerator_one_not_involution hsquare

/-- In particular, the identity indexing is impossible. -/
theorem positiveRootPacket_not_pointwise_pcGenerator :
    ¬ ∀ i : Fin 6, positiveRootPacket i = pcGenerator i := by
  intro h
  have hsquare := positiveRootPacket_sq (1 : Fin 6)
  rw [h 1] at hsquare
  exact pcGenerator_one_not_involution hsquare

/-- The correct alignment interface is through complete PC normal-form words,
    not through the six PC generators individually.  This definition is only
    an interface: no alignment theorem is asserted for the current packet. -/
theorem pcGenerator_one_not_involution :
    ¬ (pcGenerator 1 * pcGenerator 1 = (1 : SplitOctF2Aut)) := by
  rw [pcGenerator.eq_def, pc2Aut_sq_eq_pc6Aut]
  exact pc6Aut_ne_one

theorem pcGenerator_two_not_involution :
    ¬ (pcGenerator 2 * pcGenerator 2 = (1 : SplitOctF2Aut)) := by
  rw [pcGenerator.eq_def, pc3Aut_sq_eq_pc6Aut]
  exact pc6Aut_ne_one

theorem no_positiveRootPacket_pcGenerator_reindex
    (σ : Fin 6 ≃ Fin 6) :
    ¬ ∀ i : Fin 6,
      positiveRootPacket i = pcGenerator (σ i) := by
  intro h
  let i : Fin 6 := σ.symm 1
  have hi : σ i = 1 := by
    dsimp [i]
    exact σ.apply_symm_apply 1
  have hsq := positiveRootPacket_sq i
  rw [h i, hi] at hsq
  exact pcGenerator_one_not_involution hsq

def PacketPCWordAligned
    (packet : Fin 6 → SplitOctF2Aut)
    (word : (Fin 6 → Bool) → SplitOctF2Aut) : Prop :=
  ∀ i : Fin 6, ∃ e : Fin 6 → Bool, packet i = word e

end InfoGeometry.Algebra.Zorn.G2PositiveRootPCAlignment
