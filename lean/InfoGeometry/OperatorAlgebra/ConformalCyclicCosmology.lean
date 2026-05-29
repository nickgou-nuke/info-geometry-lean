/-
InfoGeometry/OperatorAlgebra/ConformalCyclicCosmology.lean

Conformal cyclic crossover as a projective null-lightcone bridge.

This file does not formalize Penrose CCC as a physical cosmology.  It records
the operator-Erlangen boundary:

* affine metric scale, clocks, and one-aeon chart representatives are not
  transported by default;
* projective null/conformal data survives only through an explicit crossover
  bridge;
* hidden memory survives only when a separate recovery/residue witness is
  supplied.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ClosureInvolution

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ConformalCyclicCosmology

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ClosureInvolution
open InfoGeometry.OperatorAlgebra.HorizonEschaton

/-! ## 1. Aeonic conformal crossover -/

/--
Conformal crossover between two aeon ledgers.

`Old` and `New` are not assumed to share an affine chart or a metric scale.
They are related only through ambient conformal representatives in `W`.

The key law says that a crossover pair is projectively identified after
Möbius inversion of the old representative.
-/
structure AeonConformalCrossover
    (Old New W : Type*) [AddCommGroup W] [Module ℝ W] where
  /-- Ambient Möbius/chart-swap inversion. -/
  inversion :
    MobiusInversionDatum W

  /-- Old-aeon conformal representative. -/
  oldCarrier :
    Old → W

  /-- New-aeon conformal representative. -/
  newCarrier :
    New → W

  /-- Old representatives lie on the ambient null cone. -/
  old_null :
    ∀ o : Old, oldCarrier o ∈ inversion.nullCone

  /-- New representatives lie on the ambient null cone. -/
  new_null :
    ∀ n : New, newCarrier n ∈ inversion.nullCone

  /-- Crossover relation between old and new aeon labels. -/
  crossoverRel :
    Old → New → Prop

  /--
  Crossover identifies the new representative with the inverted old
  representative projectively, not affinely.
  -/
  crossover_projective :
    ∀ o : Old, ∀ n : New,
      crossoverRel o n →
        ∃ c : ℝ, c ≠ 0 ∧ newCarrier n = c • inversion.inv (oldCarrier o)

namespace AeonConformalCrossover

variable
    {Old New W : Type*} [AddCommGroup W] [Module ℝ W]
    (C : AeonConformalCrossover Old New W)

/-- The inverted old representative remains on the conformal null cone. -/
theorem inverted_old_null
    (o : Old) :
    C.inversion.inv (C.oldCarrier o) ∈ C.inversion.nullCone :=
  C.inversion.preserves_null (C.oldCarrier o) (C.old_null o)

/--
A crossover pair is projectively represented by the inverted old aeon carrier.
-/
theorem newCarrier_sameRay_inverted_old
    {o : Old}
    {n : New}
    (hcross : C.crossoverRel o n) :
    ∃ c : ℝ, c ≠ 0 ∧
      C.newCarrier n = c • C.inversion.inv (C.oldCarrier o) :=
  C.crossover_projective o n hcross

/-- Self-dual crossover representatives are projectively fixed by inversion. -/
def IsSelfDualCrossoverState
    (x : W) : Prop :=
  C.inversion.IsProjectiveFixed x

/--
A nonzero self-dual crossover representative is fixed or anti-fixed under the
Möbius involution.
-/
theorem selfDual_fixed_or_antiFixed
    [NoZeroSMulDivisors ℝ W]
    {x : W}
    (hx : C.IsSelfDualCrossoverState x) :
    C.inversion.IsFixedVector x ∨ C.inversion.IsAntiFixedVector x :=
  C.inversion.projectiveFixed_fixed_or_antiFixed hx

end AeonConformalCrossover

/-! ## 2. Surviving conformal readouts -/

/--
A conformal readout that survives the crossover inversion.

This is the formal replacement for saying that a cross-ratio/null-incidence
type observable survives: the readout is invariant on the null cone under the
Möbius chart swap.
-/
structure SurvivingConformalReadout
    {Old New W : Type*} [AddCommGroup W] [Module ℝ W]
    (C : AeonConformalCrossover Old New W)
    (Readout : Type*) where
  /-- Ambient conformal readout. -/
  read :
    W → Readout

  /-- The readout is invariant under the crossover inversion on null data. -/
  read_invariant :
    C.inversion.IsMobiusInvariantReadout read

namespace SurvivingConformalReadout

variable
    {Old New W Readout : Type*} [AddCommGroup W] [Module ℝ W]
    {C : AeonConformalCrossover Old New W}
    (R : SurvivingConformalReadout C Readout)

/-- The readout of an old representative agrees with its inverted representative. -/
theorem old_read_eq_inverted_old_read
    (o : Old) :
    R.read (C.inversion.inv (C.oldCarrier o)) =
      R.read (C.oldCarrier o) :=
  C.inversion.invariantReadout_inv_eq R.read_invariant (C.old_null o)

/--
The symmetrized old readout is chart-swap stable up to swapping its two entries.
-/
theorem old_symmetrized_readout_swaps
    (o : Old) :
    C.inversion.symmetrizedReadout R.read
        (C.inversion.inv (C.oldCarrier o)) =
      (R.read (C.inversion.inv (C.oldCarrier o)), R.read (C.oldCarrier o)) :=
  C.inversion.symmetrizedReadout_inv R.read (C.oldCarrier o)

end SurvivingConformalReadout

/-! ## 3. Lightlike grammar and boundary memory -/

/--
Lightlike grammar surviving a conformal crossover.

The readout is projective, so it ignores nonzero scalar rescaling, and it is
Möbius-invariant on the null cone.  This is the formal content of “light
survives as conformal null grammar, not as old metric substance.”
-/
structure CrossoverLightlikeGrammar
    {Old New W : Type*} [AddCommGroup W] [Module ℝ W]
    (C : AeonConformalCrossover Old New W)
    (Grammar : Type*) where
  /-- Grammar/readout of a projective null representative. -/
  grammar :
    W → Grammar

  /-- The grammar ignores nonzero scalar rescaling. -/
  projective :
    MobiusInversionDatum.IsProjectiveReadout grammar

  /-- The grammar is invariant under the crossover inversion on null data. -/
  inversion_invariant :
    C.inversion.IsMobiusInvariantReadout grammar

namespace CrossoverLightlikeGrammar

variable
    {Old New W Grammar : Type*} [AddCommGroup W] [Module ℝ W]
    {C : AeonConformalCrossover Old New W}
    (G : CrossoverLightlikeGrammar C Grammar)

/--
Across a crossover pair, the new carrier has the same lightlike grammar as the
old carrier.
-/
theorem grammar_eq_on_crossover
    {o : Old}
    {n : New}
    (hcross : C.crossoverRel o n) :
    G.grammar (C.newCarrier n) =
      G.grammar (C.oldCarrier o) := by
  rcases C.crossover_projective o n hcross with ⟨c, hc, hnew⟩
  calc
    G.grammar (C.newCarrier n)
        = G.grammar (c • C.inversion.inv (C.oldCarrier o)) := by
            rw [hnew]
    _ = G.grammar (C.inversion.inv (C.oldCarrier o)) := by
            exact G.projective c (C.inversion.inv (C.oldCarrier o)) hc
    _ = G.grammar (C.oldCarrier o) := by
            exact C.inversion.invariantReadout_inv_eq
              G.inversion_invariant
              (C.old_null o)

end CrossoverLightlikeGrammar

/--
Kitaev-like boundary memory bridge.

This does not assert that the universe is literally a Kitaev chain.  It
records the algebraic archetype: a boundary/edge memory is encoded as
projective lightlike grammar that can pass through a conformal crossover.
-/
structure KitaevLikeBoundaryMemoryBridge
    {Old New W : Type*} [AddCommGroup W] [Module ℝ W]
    (C : AeonConformalCrossover Old New W)
    (Memory Grammar : Type*) where
  /-- Lightlike grammar transported by the crossover. -/
  lightlikeGrammar :
    CrossoverLightlikeGrammar C Grammar

  /-- Old-aeon boundary/edge memory. -/
  edgeMemory :
    Old → Memory

  /-- Encoding of boundary memory into lightlike grammar. -/
  encode :
    Memory → Grammar

  /-- Boundary memory is represented by the old conformal grammar. -/
  edge_memory_encodes_as_grammar :
    ∀ o : Old,
      encode (edgeMemory o) =
        lightlikeGrammar.grammar (C.oldCarrier o)

namespace KitaevLikeBoundaryMemoryBridge

variable
    {Old New W Memory Grammar : Type*} [AddCommGroup W] [Module ℝ W]
    {C : AeonConformalCrossover Old New W}
    (B : KitaevLikeBoundaryMemoryBridge C Memory Grammar)

/--
For crossover-related states, the old edge memory is encoded by the new
lightlike grammar.
-/
theorem edge_memory_matches_new_grammar
    {o : Old}
    {n : New}
    (hcross : C.crossoverRel o n) :
    B.encode (B.edgeMemory o) =
      B.lightlikeGrammar.grammar (C.newCarrier n) := by
  rw [B.edge_memory_encodes_as_grammar o]
  exact (B.lightlikeGrammar.grammar_eq_on_crossover hcross).symm

end KitaevLikeBoundaryMemoryBridge

/--
Genesis re-entanglement bridge.

A surviving lightlike grammar becomes physically meaningful in the new aeon
only after a new Genesis split/ledger supplies a latent context and an
entanglement relation.
-/
structure GenesisReentanglementBridge
    {Old New W : Type*} [AddCommGroup W] [Module ℝ W]
    (C : AeonConformalCrossover Old New W)
    (Latent Observable Hidden Boundary Grammar : Type*) where
  /-- Surviving lightlike grammar. -/
  lightlikeGrammar :
    CrossoverLightlikeGrammar C Grammar

  /-- New-aeon latent state associated to a new label. -/
  latentOfNew :
    New → Latent

  /-- New Genesis split giving the fresh observable/hidden/boundary context. -/
  genesis :
    GenesisSplitDatum Latent Observable Hidden Boundary

  /-- Relation saying the bare grammar has entered the new ledger context. -/
  reentangles :
    Grammar → Latent → Prop

  /-- The new carrier grammar is re-entangled into the new latent context. -/
  reentanglement_law :
    ∀ o : Old, ∀ n : New,
      C.crossoverRel o n →
        reentangles
          (lightlikeGrammar.grammar (C.newCarrier n))
          (latentOfNew n)

namespace GenesisReentanglementBridge

variable
    {Old New W Latent Observable Hidden Boundary Grammar : Type*}
    [AddCommGroup W] [Module ℝ W]
    {C : AeonConformalCrossover Old New W}
    (B :
      GenesisReentanglementBridge
        C Latent Observable Hidden Boundary Grammar)

/--
The old lightlike grammar re-entangles into the new Genesis context whenever
the old and new states are related by crossover.
-/
theorem old_grammar_reentangles
    {o : Old}
    {n : New}
    (hcross : C.crossoverRel o n) :
    B.reentangles
      (B.lightlikeGrammar.grammar (C.oldCarrier o))
      (B.latentOfNew n) := by
  have hnew := B.reentanglement_law o n hcross
  have hgrammar :
      B.lightlikeGrammar.grammar (C.newCarrier n) =
        B.lightlikeGrammar.grammar (C.oldCarrier o) :=
    B.lightlikeGrammar.grammar_eq_on_crossover hcross
  rwa [hgrammar] at hnew


end GenesisReentanglementBridge

/-! ## 4. Optional memory residue / Revelation bridge -/

/--
Optional residue bridge across a conformal crossover.

This is deliberately separate from `AeonConformalCrossover`: conformal
identification does not by itself prove that old hidden memory is recoverable
in the new aeon.  Recovery requires this extra witness.
-/
structure CrossoverMemoryRecoveryBridge
    {Old New W : Type*} [AddCommGroup W] [Module ℝ W]
    (C : AeonConformalCrossover Old New W)
    (Memory Residue : Type*) where
  /-- Hidden old-aeon memory readout. -/
  oldMemory :
    Old → Memory

  /-- New-aeon residue, such as a Hawking-point-like conformal trace. -/
  newResidue :
    New → Residue

  /-- Decoder from conformal residue to old memory. -/
  decode :
    Residue → Memory

  /-- Faithful recovery law for crossover-related states. -/
  recovery_law :
    ∀ o : Old, ∀ n : New,
      C.crossoverRel o n →
        decode (newResidue n) = oldMemory o

namespace CrossoverMemoryRecoveryBridge

variable
    {Old New W Memory Residue : Type*} [AddCommGroup W] [Module ℝ W]
    {C : AeonConformalCrossover Old New W}
    (B : CrossoverMemoryRecoveryBridge C Memory Residue)

/--
If a memory bridge is supplied, the new-aeon residue decodes the old hidden
memory for crossover-related states.
-/
theorem residue_recovers_old_memory
    {o : Old}
    {n : New}
    (hcross : C.crossoverRel o n) :
    B.decode (B.newResidue n) = B.oldMemory o :=
  B.recovery_law o n hcross

end CrossoverMemoryRecoveryBridge

/-! ## 5. Linear closure survivor packet -/

/--
A linearized aeon-reset packet.

This packages the statement that what survives a closure/reset involution is
the fixed equalizer, while the anti-diagonal records orientation/scale-sensitive
data.
-/
structure LinearAeonReset
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  closure :
    LinearClosureInvolution V

namespace LinearAeonReset

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : LinearAeonReset V)

/-- The survivor sector of the linearized aeon reset. -/
abbrev Survivor : Submodule ℝ V :=
  A.closure.Fixed

/-- The orientation/scale-sensitive anti-survivor sector. -/
abbrev AntiSurvivor : Submodule ℝ V :=
  A.closure.AntiFixed

/-- The diagonal part of any vector survives the reset involution. -/
theorem diagonal_survives
    (v : V) :
    v + A.closure.theta v ∈ A.Survivor :=
  A.closure.diagonal_with_image_fixed v

/-- The anti-diagonal part is anti-fixed under the reset involution. -/
theorem anti_diagonal_is_antiSurvivor
    (v : V) :
    v - A.closure.theta v ∈ A.AntiSurvivor :=
  A.closure.anti_diagonal_with_image v

end LinearAeonReset

end InfoGeometry.OperatorAlgebra.ConformalCyclicCosmology
