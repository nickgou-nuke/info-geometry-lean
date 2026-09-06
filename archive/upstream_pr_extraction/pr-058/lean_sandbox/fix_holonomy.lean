import Mathlib

structure WilsonReadoutDatum (GState GLoop Scalar : Type*) where
  wilson : GLoop → GState → Scalar

structure THooftReadoutDatum (GdualState GdualLoop Scalar : Type*) where
  thooft : GdualLoop → GdualState → Scalar

structure LanglandsDualPair (GState GdualState GLoop GdualLoop : Type*) where
  loopDual : GLoop → GdualLoop
  stateDual : GState → GdualState

structure DualHolonomyRecoveryWitness
    (GState GdualState GLoop GdualLoop Scalar Memory : Type*)
    (W : WilsonReadoutDatum GState GLoop Scalar)
    (T : THooftReadoutDatum GdualState GdualLoop Scalar)
    (D : LanglandsDualPair GState GdualState GLoop GdualLoop) where
  hiddenMemory : GState → Memory
  recoverFromDualHolonomy : Scalar → Memory
  recoveringLoop : GLoop → Prop
  recovery_holds :
    ∀ γ s, recoveringLoop γ →
      recoverFromDualHolonomy (T.thooft (D.loopDual γ) (D.stateDual s)) = hiddenMemory s

namespace DualHolonomyRecoveryWitness
variable {GState GdualState GLoop GdualLoop Scalar Memory : Type*}
  {W : WilsonReadoutDatum GState GLoop Scalar}
  {T : THooftReadoutDatum GdualState GdualLoop Scalar}
  {D : LanglandsDualPair GState GdualState GLoop GdualLoop}

theorem dual_holonomy_recovery (R : DualHolonomyRecoveryWitness GState GdualState GLoop GdualLoop Scalar Memory W T D)
    (γ : GLoop) (hγ : R.recoveringLoop γ) (s : GState) :
    R.recoverFromDualHolonomy (T.thooft (D.loopDual γ) (D.stateDual s)) = R.hiddenMemory s :=
  R.recovery_holds γ s hγ

end DualHolonomyRecoveryWitness