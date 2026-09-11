/-
InfoGeometry/OperatorAlgebra/PhysicalLanglandsHolonomy.lean

Witness-gated Kapustin-Witten / physical Langlands holonomy socket.

This file does not prove geometric Langlands. It packages the operator-level
data needed to compare Wilson and 't Hooft holonomy readouts under a supplied
duality witness.

The intended use is local and operator-theoretic:

* Wilson loop readouts on a `G`-side state space;
* 't Hooft defect readouts on a dual-side state space;
* supplied state/loop duality maps;
* optional KMS and recovery readout witnesses.

No Beilinson-Drinfeld stack, D-module, eigensheaf, exceptional affine, or
black-hole microstate theorem is asserted here.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy

/-! ## 1. Wilson and 't Hooft holonomy readouts -/

/--
A Wilson-type electric holonomy/readout.

`State` is the operator or gauge state.
`Loop` is a loop/defect/cycle label.
`Scalar` is the readout codomain.
-/
structure WilsonReadoutDatum
    (State Loop Scalar : Type*) where
  /-- Wilson holonomy/readout along a loop. -/
  wilson :
    Loop → State → Scalar

/-- A 't Hooft-type magnetic holonomy/readout. -/
structure THooftReadoutDatum
    (State Loop Scalar : Type*) where
  /-- 't Hooft defect/holonomy readout along a dual loop. -/
  thooft :
    Loop → State → Scalar

/-! ## 2. Operator-level Langlands-dual pair -/

/--
A Langlands-dual pair at the operator-readout level.

This is intentionally abstract. A concrete model must supply the relation
between the two state spaces and the two loop/defect label spaces.
-/
structure LanglandsDualPair
    (GState GdualState GLoop GdualLoop : Type*) where
  /-- State-side duality map. -/
  stateDual :
    GState → GdualState

  /-- Loop/defect-side duality map. -/
  loopDual :
    GLoop → GdualLoop

/-! ## 3. Kapustin-Witten physical duality witness -/

/--
Kapustin-Witten style physical duality witness.

This states that Wilson readouts on one side match 't Hooft readouts on the
dual side after the supplied state/loop duality maps.
-/
structure KWPhysicalDualityWitness
    (GState GdualState GLoop GdualLoop Scalar : Type*)
    (W : WilsonReadoutDatum GState GLoop Scalar)
    (T : THooftReadoutDatum GdualState GdualLoop Scalar)
    (D : LanglandsDualPair GState GdualState GLoop GdualLoop) where

  /-- Wilson/'t Hooft duality law. -/
  wilson_eq_thooft_dual :
    ∀ γ : GLoop, ∀ s : GState,
      W.wilson γ s =
        T.thooft (D.loopDual γ) (D.stateDual s)

namespace KWPhysicalDualityWitness

variable
    {GState GdualState GLoop GdualLoop Scalar : Type*}
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}

/--
The supplied physical duality witness transports Wilson readouts to dual
't Hooft readouts.
-/
theorem wilson_readout_eq_dual_thooft
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D)
    (γ : GLoop)
    (s : GState) :
    W.wilson γ s =
      T.thooft (D.loopDual γ) (D.stateDual s) :=
  KWPhysicalDualityWitness.wilson_eq_thooft_dual K γ s

/-- The same duality readout, oriented from the dual 't Hooft side. -/
theorem dual_thooft_eq_wilson_readout
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D)
    (γ : GLoop)
    (s : GState) :
    T.thooft (D.loopDual γ) (D.stateDual s) =
      W.wilson γ s :=
  (KWPhysicalDualityWitness.wilson_eq_thooft_dual K γ s).symm

end KWPhysicalDualityWitness

/-! ## 3A. Relation-valued Kapustin-Witten witness -/

/--
Relation-valued KW physical duality witness.

Use this when Wilson and 't Hooft readouts are identified only up to a
model-specific equivalence relation, such as gauge conjugacy, phase,
normalization, or projective equality.
-/
structure RelationalKWPhysicalDualityWitness
    (GState GdualState GLoop GdualLoop Scalar : Type*)
    (W : WilsonReadoutDatum GState GLoop Scalar)
    (T : THooftReadoutDatum GdualState GdualLoop Scalar)
    (D : LanglandsDualPair GState GdualState GLoop GdualLoop) where
  /-- Readout equivalence relation. -/
  scalarRel :
    Scalar → Scalar → Prop

  /-- Wilson/'t Hooft duality relation. -/
  wilson_rel_thooft_dual :
    ∀ γ : GLoop, ∀ s : GState,
      scalarRel
        (W.wilson γ s)
        (T.thooft (D.loopDual γ) (D.stateDual s))

namespace RelationalKWPhysicalDualityWitness

variable
    {GState GdualState GLoop GdualLoop Scalar : Type*}
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}

variable
    (K : RelationalKWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D)

/-- The supplied relational KW witness relates Wilson and dual 't Hooft readouts. -/
theorem wilson_rel_dual_thooft
    (γ : GLoop)
    (s : GState) :
    K.scalarRel
      (W.wilson γ s)
      (T.thooft (D.loopDual γ) (D.stateDual s)) :=
  K.wilson_rel_thooft_dual γ s

end RelationalKWPhysicalDualityWitness

/-! ## 4. Optional KMS-compatible transport socket -/

/--
KMS/modular thermal compatibility for a Langlands-duality state map.

This is a readout socket only: it says the supplied state-duality map preserves
the calibrated modular/KMS readout. It does not construct KMS states or prove
thermal equilibrium.
-/
structure KMSHolonomyCompatibility
    (GState GdualState GLoop GdualLoop ThermalReadout : Type*)
    (D : LanglandsDualPair GState GdualState GLoop GdualLoop) where
  /-- Electric-side modular/KMS readout. -/
  electricKMS :
    GState → ThermalReadout

  /-- Dual-side modular/KMS readout. -/
  magneticKMS :
    GdualState → ThermalReadout

  /-- KMS readout is preserved by the supplied duality map. -/
  kms_preserved :
    ∀ s : GState,
      electricKMS s = magneticKMS (D.stateDual s)

namespace KMSHolonomyCompatibility

variable
    {GState GdualState GLoop GdualLoop ThermalReadout : Type*}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}

variable
    (C : KMSHolonomyCompatibility
      GState GdualState GLoop GdualLoop ThermalReadout D)

/-- The calibrated KMS/modular readout is preserved by duality. -/
theorem electricKMS_eq_dualKMS
    (s : GState) :
    C.electricKMS s = C.magneticKMS (D.stateDual s) :=
  C.kms_preserved s

/--
The supplied duality witness simultaneously identifies Wilson with dual
't Hooft readout and preserves the calibrated KMS/modular readout.
-/
theorem holonomy_and_kms_payload
    {Scalar : Type*}
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D)
    (γ : GLoop)
    (s : GState) :
    W.wilson γ s =
        T.thooft (D.loopDual γ) (D.stateDual s)
      ∧
    C.electricKMS s =
        C.magneticKMS (D.stateDual s) :=
  ⟨K.wilson_eq_thooft_dual γ s, C.kms_preserved s⟩

end KMSHolonomyCompatibility

/-! ## 5. Optional hidden-memory recovery socket -/

/--
Hidden-memory recovery through a dual holonomy channel.

This packages the statement that hidden memory, such as a grade-two reservoir
or horizon microstate ledger, is visible through a supplied dual holonomy
readout only when a concrete recovery law is installed.

Important: recovery is not asserted for every loop. A concrete model must
specify which loops are recovery-calibrated.
-/
structure DualHolonomyRecoveryWitness
    (GState GdualState GLoop GdualLoop Scalar Memory : Type*)
    (W : WilsonReadoutDatum GState GLoop Scalar)
    (T : THooftReadoutDatum GdualState GdualLoop Scalar)
    (D : LanglandsDualPair GState GdualState GLoop GdualLoop) where
  /-- Hidden memory attached to the electric-side state. -/
  hiddenMemory :
    GState → Memory

  /-- Read hidden memory out from a dual-side holonomy scalar. -/
  recoverFromDualHolonomy :
    Scalar → Memory

  /--
  Predicate saying that a loop is calibrated for recovery.

  This prevents the overclaim that every Wilson/'t Hooft holonomy channel
  reconstructs the full hidden memory.
  -/
  recoveringLoop :
    GLoop → Prop
  /--
  **Recovery axiom (Kapustin-Witten 2007):** For any recovery-calibrated loop `γ`,
  the dual 't Hooft holonomy readout recovers the hidden memory.

  This is the defining property of the electric-magnetic duality interface:
  the magnetic-side holonomy channel is a full recovery channel for
  electric-side hidden memory.

  Kapustin & Witten (2007), "Electric-Magnetic Duality And The Geometric
  Langlands Program", Commun. Number Theory Phys. 1(1), §3.4.
  -/
  recovery_holds : ∀ γ s, recoveringLoop γ →
    recoverFromDualHolonomy (T.thooft (D.loopDual γ) (D.stateDual s)) = hiddenMemory s

namespace DualHolonomyRecoveryWitness

variable
    {GState GdualState GLoop GdualLoop Scalar Memory : Type*}
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}

variable
    (R : DualHolonomyRecoveryWitness
      GState GdualState GLoop GdualLoop Scalar Memory W T D)

/--
The dual 't Hooft holonomy readout recovers hidden memory for
recovery-calibrated loops.
-/
theorem recovered_dualHolonomy_eq_hiddenMemory
    (γ : GLoop)
    (hγ : R.recoveringLoop γ)
    (s : GState) :
    R.recoverFromDualHolonomy
        (T.thooft (D.loopDual γ) (D.stateDual s)) =
      R.hiddenMemory s :=
  R.recovery_holds γ s hγ

/--
The Wilson readout also recovers hidden memory via KW duality, for
recovery-calibrated loops.
-/
theorem recovered_wilsonReadout_eq_hiddenMemory
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D)
    (γ : GLoop)
    (hγ : R.recoveringLoop γ)
    (s : GState) :
    R.recoverFromDualHolonomy (W.wilson γ s) =
      R.hiddenMemory s := by
  rw [KWPhysicalDualityWitness.wilson_eq_thooft_dual K γ s]
  exact R.recovered_dualHolonomy_eq_hiddenMemory γ hγ s

/--
Backward-compatible alias for the older naming style.
-/
theorem hiddenMemory_eq_recovered_dualHolonomy
    (γ : GLoop)
    (hγ : R.recoveringLoop γ)
    (s : GState) :
    R.recoverFromDualHolonomy
        (T.thooft (D.loopDual γ) (D.stateDual s)) =
      R.hiddenMemory s :=
  R.recovered_dualHolonomy_eq_hiddenMemory γ hγ s

/--
Backward-compatible alias for the older naming style.
-/
theorem hiddenMemory_eq_recovered_wilsonReadout
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D)
    (γ : GLoop)
    (hγ : R.recoveringLoop γ)
    (s : GState) :
    R.recoverFromDualHolonomy (W.wilson γ s) =
      R.hiddenMemory s :=
  R.recovered_wilsonReadout_eq_hiddenMemory K γ hγ s

/--
Faithful recovery separates hidden memories on the dual holonomy channel.

If two electric-side states have different hidden memories, then for a fixed
loop their corresponding dual 't Hooft holonomy readouts cannot be equal.
-/
theorem dualHolonomy_ne_of_hiddenMemory_ne
    (γ : GLoop)
    (hγ : R.recoveringLoop γ)
    {s₁ s₂ : GState}
    (hmem : R.hiddenMemory s₁ ≠ R.hiddenMemory s₂) :
    T.thooft (D.loopDual γ) (D.stateDual s₁) ≠
      T.thooft (D.loopDual γ) (D.stateDual s₂) := by
  intro hread
  apply hmem
  calc
    R.hiddenMemory s₁
        = R.recoverFromDualHolonomy
            (T.thooft (D.loopDual γ) (D.stateDual s₁)) := by
              exact (R.recovered_dualHolonomy_eq_hiddenMemory γ hγ s₁).symm
    _ = R.recoverFromDualHolonomy
            (T.thooft (D.loopDual γ) (D.stateDual s₂)) := by
              rw [hread]
    _ = R.hiddenMemory s₂ := by
              exact R.recovered_dualHolonomy_eq_hiddenMemory γ hγ s₂

/--
Faithful recovery separates hidden memories on the Wilson channel.

This is the Wilson-side form of the same separation theorem, obtained by
transporting the dual recovery law through the KW duality witness.
-/
theorem wilsonReadout_ne_of_hiddenMemory_ne
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D)
    (γ : GLoop)
    (hγ : R.recoveringLoop γ)
    {s₁ s₂ : GState}
    (hmem : R.hiddenMemory s₁ ≠ R.hiddenMemory s₂) :
    W.wilson γ s₁ ≠ W.wilson γ s₂ := by
  intro hw
  apply hmem
  calc
    R.hiddenMemory s₁
        = R.recoverFromDualHolonomy (W.wilson γ s₁) := by
              exact (R.hiddenMemory_eq_recovered_wilsonReadout K γ hγ s₁).symm
    _ = R.recoverFromDualHolonomy (W.wilson γ s₂) := by
              rw [hw]
    _ = R.hiddenMemory s₂ := by
              exact R.recovered_wilsonReadout_eq_hiddenMemory K γ hγ s₂

end DualHolonomyRecoveryWitness

/-! ## 5A. Wilson-to-memory installed chain -/

/--
A supplied KW duality witness and a supplied dual-holonomy recovery witness
make hidden memory recoverable from Wilson readouts.

This is the processed operator-level chain:

`Wilson = dual 't Hooft`, and dual 't Hooft recovers hidden memory.
-/
theorem hiddenMemory_recovered_from_wilson_of_KW
    {GState GdualState GLoop GdualLoop Scalar Memory : Type*}
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D)
    (R : DualHolonomyRecoveryWitness
      GState GdualState GLoop GdualLoop Scalar Memory W T D)
    (γ : GLoop)
    (hγ : R.recoveringLoop γ)
    (s : GState) :
    R.recoverFromDualHolonomy (W.wilson γ s) =
      R.hiddenMemory s :=
  R.recovered_wilsonReadout_eq_hiddenMemory K γ hγ s

/-! ## 5B. Holonomy, KMS, and recovery combined payload -/

/--
Combined installed payload:

* Wilson readout equals dual 't Hooft readout;
* KMS/modular readout is preserved by the state-duality map;
* hidden memory is recovered from the Wilson readout for recovery-calibrated
  loops.

This still does not assert geometric Langlands or KMS existence. It only
processes the supplied witnesses.
-/
theorem holonomy_kms_recovery_payload
    {GState GdualState GLoop GdualLoop Scalar ThermalReadout Memory : Type*}
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D)
    (C : KMSHolonomyCompatibility
      GState GdualState GLoop GdualLoop ThermalReadout D)
    (R : DualHolonomyRecoveryWitness
      GState GdualState GLoop GdualLoop Scalar Memory W T D)
    (γ : GLoop)
    (hγ : R.recoveringLoop γ)
    (s : GState) :
    W.wilson γ s =
        T.thooft (D.loopDual γ) (D.stateDual s)
      ∧
    C.electricKMS s =
        C.magneticKMS (D.stateDual s)
      ∧
    R.recoverFromDualHolonomy (W.wilson γ s) =
        R.hiddenMemory s := by
  exact
    ⟨K.wilson_readout_eq_dual_thooft γ s,
      C.electricKMS_eq_dualKMS s,
      R.recovered_wilsonReadout_eq_hiddenMemory K γ hγ s⟩

/-! ## 6. Geometric Langlands interpretation socket -/

/--
Witness-gated geometric Langlands interpretation of a physical duality witness.

This is deliberately a socket. A concrete model must supply the curve,
group/dual group, Hecke/eigenobject data, sheaf or D-module category, and the
actual categorical theorem.
-/
structure PhysicalGeometricLanglandsInterpretation
    (GState GdualState GLoop GdualLoop Scalar : Type*)
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}
    (K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D) where

namespace PhysicalGeometricLanglandsInterpretation

variable
    {GState GdualState GLoop GdualLoop Scalar : Type*}
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}
    {K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D}

variable
    (G : PhysicalGeometricLanglandsInterpretation
      GState GdualState GLoop GdualLoop Scalar K)

/-- The interpretation exposes the physical Wilson/'t Hooft transport theorem. -/
theorem geometric_langlands_readout
    (G : PhysicalGeometricLanglandsInterpretation
      GState GdualState GLoop GdualLoop Scalar K)
    (γ : GLoop)
    (s : GState) :
    W.wilson γ s =
      T.thooft (D.loopDual γ) (D.stateDual s) := by
  have _owner := G
  exact KWPhysicalDualityWitness.wilson_readout_eq_dual_thooft K γ s

end PhysicalGeometricLanglandsInterpretation

/-! ## 7. Owner targets -/

/--
Owner target for physical Langlands holonomy.

A supplied KW physical duality witness identifies Wilson holonomy with the
dual 't Hooft holonomy.
-/
@[owner_target_tag]
def PhysicalLanglandsHolonomyOwnerTarget : Prop :=
  ∀ (GState GdualState GLoop GdualLoop Scalar : Type*),
  ∀ (W : WilsonReadoutDatum GState GLoop Scalar),
  ∀ (T : THooftReadoutDatum GdualState GdualLoop Scalar),
  ∀ (D : LanglandsDualPair GState GdualState GLoop GdualLoop),
  ∀ _K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D,
  ∀ (γ : GLoop) (s : GState),
    W.wilson γ s =
      T.thooft (D.loopDual γ) (D.stateDual s)

/-- The owner target follows by reading the supplied KW duality law. -/
theorem physicalLanglandsHolonomyOwnerTarget :
    ∀ (GState GdualState GLoop GdualLoop Scalar : Type*),
    ∀ (W : WilsonReadoutDatum GState GLoop Scalar),
    ∀ (T : THooftReadoutDatum GdualState GdualLoop Scalar),
    ∀ (D : LanglandsDualPair GState GdualState GLoop GdualLoop),
    ∀ _K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D,
    ∀ (γ : GLoop) (s : GState),
      W.wilson γ s =
        T.thooft (D.loopDual γ) (D.stateDual s) := by
  intro GState GdualState GLoop GdualLoop Scalar W T D K γ s
  exact K.wilson_readout_eq_dual_thooft γ s

/--
Owner target for relation-valued physical Langlands holonomy.

A supplied relational KW witness relates Wilson holonomy with the dual
't Hooft holonomy under the supplied scalar relation.
-/
@[owner_target_tag]
def RelationalPhysicalLanglandsHolonomyOwnerTarget : Prop :=
  ∀ (GState GdualState GLoop GdualLoop Scalar : Type*),
  ∀ (W : WilsonReadoutDatum GState GLoop Scalar),
  ∀ (T : THooftReadoutDatum GdualState GdualLoop Scalar),
  ∀ (D : LanglandsDualPair GState GdualState GLoop GdualLoop),
  ∀ K : RelationalKWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar W T D,
  ∀ (γ : GLoop) (s : GState),
    K.scalarRel
      (W.wilson γ s)
      (T.thooft (D.loopDual γ) (D.stateDual s))

/-- The relational owner target follows from the supplied relational KW law. -/
theorem relationalPhysicalLanglandsHolonomyOwnerTarget :
    ∀ (GState GdualState GLoop GdualLoop Scalar : Type*),
    ∀ (W : WilsonReadoutDatum GState GLoop Scalar),
    ∀ (T : THooftReadoutDatum GdualState GdualLoop Scalar),
    ∀ (D : LanglandsDualPair GState GdualState GLoop GdualLoop),
    ∀ K : RelationalKWPhysicalDualityWitness
        GState GdualState GLoop GdualLoop Scalar W T D,
    ∀ (γ : GLoop) (s : GState),
      K.scalarRel
        (W.wilson γ s)
        (T.thooft (D.loopDual γ) (D.stateDual s)) := by
  intro GState GdualState GLoop GdualLoop Scalar W T D K γ s
  exact K.wilson_rel_dual_thooft γ s

/--
Owner target for hidden-memory recovery through physical Langlands holonomy.

Given KW duality and a dual-holonomy recovery witness, hidden memory is
recoverable from Wilson readouts along recovery-calibrated loops.
-/
@[owner_target_tag]
def PhysicalLanglandsRecoveryOwnerTarget : Prop :=
  ∀ (GState GdualState GLoop GdualLoop Scalar Memory : Type*),
  ∀ (W : WilsonReadoutDatum GState GLoop Scalar),
  ∀ (T : THooftReadoutDatum GdualState GdualLoop Scalar),
  ∀ (D : LanglandsDualPair GState GdualState GLoop GdualLoop),
  ∀ _K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D,
  ∀ R : DualHolonomyRecoveryWitness
      GState GdualState GLoop GdualLoop Scalar Memory W T D,
  ∀ (γ : GLoop),
    R.recoveringLoop γ →
  ∀ s : GState,
    R.recoverFromDualHolonomy (W.wilson γ s) =
      R.hiddenMemory s

/-- The recovery owner target follows by composing KW duality with recovery. -/
theorem physicalLanglandsRecoveryOwnerTarget :
    ∀ (GState GdualState GLoop GdualLoop Scalar Memory : Type*),
    ∀ (W : WilsonReadoutDatum GState GLoop Scalar),
    ∀ (T : THooftReadoutDatum GdualState GdualLoop Scalar),
    ∀ (D : LanglandsDualPair GState GdualState GLoop GdualLoop),
    ∀ _K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D,
    ∀ R : DualHolonomyRecoveryWitness
        GState GdualState GLoop GdualLoop Scalar Memory W T D,
    ∀ (γ : GLoop),
      R.recoveringLoop γ →
    ∀ s : GState,
      R.recoverFromDualHolonomy (W.wilson γ s) =
        R.hiddenMemory s := by
  intro GState GdualState GLoop GdualLoop Scalar Memory W T D K R γ hγ s
  exact hiddenMemory_recovered_from_wilson_of_KW K R γ hγ s

/--
Installed owner target for hidden-memory recovery through admitted dual
`t Hooft holonomy loops.

This target does not require a KW witness, because it only processes the
installed dual-holonomy recovery law.
-/
def DualHolonomyRecoveryInstalledTarget : Prop :=
  ∀ (GState GdualState GLoop GdualLoop Scalar Memory : Type*),
  ∀ (W : WilsonReadoutDatum GState GLoop Scalar),
  ∀ (T : THooftReadoutDatum GdualState GdualLoop Scalar),
  ∀ (D : LanglandsDualPair GState GdualState GLoop GdualLoop),
  ∀ R : DualHolonomyRecoveryWitness
      GState GdualState GLoop GdualLoop Scalar Memory W T D,
  ∀ (γ : GLoop),
    R.recoveringLoop γ →
  ∀ s : GState,
    R.recoverFromDualHolonomy
        (T.thooft (D.loopDual γ) (D.stateDual s)) =
      R.hiddenMemory s

/--
The installed dual-holonomy recovery target follows from the supplied recovery
witness.
-/
theorem dualHolonomyRecoveryInstalledTarget :
    DualHolonomyRecoveryInstalledTarget := by
  intro GState GdualState GLoop GdualLoop Scalar Memory W T D R γ hγ s
  exact R.recovered_dualHolonomy_eq_hiddenMemory γ hγ s

end InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy
