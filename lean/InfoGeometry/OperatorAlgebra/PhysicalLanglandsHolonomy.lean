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

import Mathlib

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

/-! ## 4. Optional KMS-compatible transport socket -/

/--
KMS/modular thermal compatibility for a physical Langlands holonomy witness.

This is a readout socket only: it says the supplied state-duality map preserves
the calibrated modular/KMS readout. It does not construct KMS states or prove
thermal equilibrium.
-/
structure KMSHolonomyCompatibility
    (GState GdualState GLoop GdualLoop Scalar ThermalReadout : Type*)
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}
    (K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D) where
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
    {GState GdualState GLoop GdualLoop Scalar ThermalReadout : Type*}
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}
    {K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D}

variable
    (C : KMSHolonomyCompatibility
      GState GdualState GLoop GdualLoop Scalar ThermalReadout K)

/-- The calibrated KMS/modular readout is preserved by duality. -/
theorem electricKMS_eq_dualKMS
    (s : GState) :
    C.electricKMS s = C.magneticKMS (D.stateDual s) :=
  C.kms_preserved s

end KMSHolonomyCompatibility

/-! ## 5. Optional hidden-memory recovery socket -/

/--
Hidden-memory recovery through a dual holonomy channel.

This packages the statement that hidden memory, such as a grade-two reservoir
or horizon microstate ledger, is visible through a supplied dual holonomy
readout only when a concrete recovery law is installed.
-/
structure DualHolonomyRecoveryWitness
    (GState GdualState GLoop GdualLoop Scalar Memory : Type*)
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}
    (K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D) where
  /-- Hidden memory attached to the electric-side state. -/
  hiddenMemory :
    GState → Memory

  /-- Read hidden memory out from a dual-side holonomy scalar. -/
  recoverFromDualHolonomy :
    Scalar → Memory

  /--
  Recovery law: hidden memory is decoded by the dual 't Hooft readout for the
  supplied loop.
  -/
  recovery_law :
    ∀ γ : GLoop, ∀ s : GState,
      recoverFromDualHolonomy
          (T.thooft (D.loopDual γ) (D.stateDual s)) =
        hiddenMemory s

namespace DualHolonomyRecoveryWitness

variable
    {GState GdualState GLoop GdualLoop Scalar Memory : Type*}
    {W : WilsonReadoutDatum GState GLoop Scalar}
    {T : THooftReadoutDatum GdualState GdualLoop Scalar}
    {D : LanglandsDualPair GState GdualState GLoop GdualLoop}
    {K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar W T D}

variable
    (R : DualHolonomyRecoveryWitness
      GState GdualState GLoop GdualLoop Scalar Memory K)

/-- Hidden memory is recovered from the dual 't Hooft holonomy readout. -/
theorem hiddenMemory_eq_recovered_dualHolonomy
    (γ : GLoop)
    (s : GState) :
    R.recoverFromDualHolonomy
        (T.thooft (D.loopDual γ) (D.stateDual s)) =
      R.hiddenMemory s :=
  R.recovery_law γ s

/-- Hidden memory is also recovered from the Wilson readout via KW duality. -/
theorem hiddenMemory_eq_recovered_wilsonReadout
    (γ : GLoop)
    (s : GState) :
    R.recoverFromDualHolonomy (W.wilson γ s) =
      R.hiddenMemory s := by
  rw [KWPhysicalDualityWitness.wilson_eq_thooft_dual K γ s]
  exact R.hiddenMemory_eq_recovered_dualHolonomy γ s

/--
Faithful recovery separates hidden memories on the dual holonomy channel.

If two electric-side states have different hidden memories, then for a fixed
loop their corresponding dual 't Hooft holonomy readouts cannot be equal.
-/
theorem dualHolonomy_ne_of_hiddenMemory_ne
    (γ : GLoop)
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
              exact (R.recovery_law γ s₁).symm
    _ = R.recoverFromDualHolonomy
            (T.thooft (D.loopDual γ) (D.stateDual s₂)) := by
              rw [hread]
    _ = R.hiddenMemory s₂ := by
              exact R.recovery_law γ s₂

/--
Faithful recovery separates hidden memories on the Wilson channel.

This is the Wilson-side form of the same separation theorem, obtained by
transporting the dual recovery law through the KW duality witness.
-/
theorem wilsonReadout_ne_of_hiddenMemory_ne
    (γ : GLoop)
    {s₁ s₂ : GState}
    (hmem : R.hiddenMemory s₁ ≠ R.hiddenMemory s₂) :
    W.wilson γ s₁ ≠ W.wilson γ s₂ := by
  intro hw
  apply hmem
  calc
    R.hiddenMemory s₁
        = R.recoverFromDualHolonomy (W.wilson γ s₁) := by
              exact (R.hiddenMemory_eq_recovered_wilsonReadout γ s₁).symm
    _ = R.recoverFromDualHolonomy (W.wilson γ s₂) := by
              rw [hw]
    _ = R.hiddenMemory s₂ := by
              exact R.hiddenMemory_eq_recovered_wilsonReadout γ s₂

end DualHolonomyRecoveryWitness

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
  /-- Model-specific geometric Langlands statement. -/
  geometric_langlands_law :
    Prop

  /-- Certificate for the model-specific statement. -/
  geometric_langlands_certificate :
    geometric_langlands_law

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

/-- The supplied geometric Langlands interpretation certificate is available. -/
theorem geometric_langlands_valid :
    G.geometric_langlands_law :=
  G.geometric_langlands_certificate

end PhysicalGeometricLanglandsInterpretation

/-! ## 7. Owner target -/

/--
Owner target for physical Langlands holonomy.

A supplied KW physical duality witness identifies Wilson holonomy with the
dual 't Hooft holonomy.
-/
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
    PhysicalLanglandsHolonomyOwnerTarget := by
  intro GState GdualState GLoop GdualLoop Scalar W T D K γ s
  exact KWPhysicalDualityWitness.wilson_eq_thooft_dual K γ s

end InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy
