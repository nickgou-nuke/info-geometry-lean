import InfoGeometry.Lie.SplitRealNullTetradZornProjectiveBridge

/-!
# Signed representatives above the projective tetrad rays

Real projectivization forgets every nonzero scalar, in particular the sign.
This owner records the elementary representative-level sign involution and
its compatibility with the already-proved tetrad flow.  It deliberately does
not call the representative carrier a spin double cover: all nonzero scalar
rescalings are still present.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitRealNullTetradProjectiveSignLift

open InfoGeometry.Clifford.SplitRealNullTetrad
open InfoGeometry.Lie.SplitRealNullTetradZornBridge.Tetrad
open InfoGeometry.Lie.SplitRealNullTetradZornProjectiveBridge

abbrev TetradNonzero := {X : Carrier // X ≠ 0}

def projectiveRay (X : TetradNonzero) : TetradProjective :=
  Projectivization.mk ℝ X.1 X.2

def negRepresentative (X : TetradNonzero) : TetradNonzero :=
  ⟨-X.1, by simpa using X.2⟩

@[simp] theorem projectiveRay_neg (X : TetradNonzero) :
    projectiveRay (negRepresentative X) = projectiveRay X := by
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨Units.mk0 (-1 : ℝ) (by norm_num), ?_⟩
  simp [negRepresentative]

@[simp] theorem negRepresentative_involution (X : TetradNonzero) :
    negRepresentative (negRepresentative X) = X := by
  apply Subtype.ext
  simp [negRepresentative]

def doubleWittBoostNonzero (t : ℝ) (X : TetradNonzero) : TetradNonzero :=
  ⟨doubleWittBoost t X.1, by
    intro h
    apply X.2
    have h' := congrArg (doubleWittBoost (-t)) h
    simpa [doubleWittBoost_neg_apply] using h'⟩

theorem projectiveRay_doubleWittBoostNonzero (t : ℝ) (X : TetradNonzero) :
    projectiveRay (doubleWittBoostNonzero t X) =
      doubleWittBoostProjectiveMap t (projectiveRay X) := by
  change Projectivization.mk ℝ (doubleWittBoost t X.1) _ =
    doubleWittBoostProjectiveMap t (Projectivization.mk ℝ X.1 X.2)
  rw [doubleWittBoostProjectiveMap_mk]

theorem projectiveRay_neg_doubleWittBoostNonzero (t : ℝ) (X : TetradNonzero) :
    projectiveRay (negRepresentative (doubleWittBoostNonzero t X)) =
      projectiveRay (doubleWittBoostNonzero t X) := by
  exact projectiveRay_neg _

end InfoGeometry.Lie.SplitRealNullTetradProjectiveSignLift
