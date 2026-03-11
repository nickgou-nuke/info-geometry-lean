module InfoGeometry.Krein.NoetherSandbox

import InfoGeometry.Krein.DoubledAdjoint
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.KreinSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Krein equivalence from the reduced diagonal model to the neutral model via Hilbert doubled. -/
noncomputable def doubledToNeutralKreinEquiv : KreinEquiv (DoubledSpace E) (NeutralSpace E) where
  toContinuousLinearEquiv :=
    (rotation45KreinEquiv (E := E)).symm.toContinuousLinearEquiv.trans
      (doubledToHilbert (E := E)).toLinearEquiv.toContinuousLinearEquiv
  isometric := fun u v => by
    have h₁ : KreinSpace.kreinInner ((doubledToHilbert (E := E)) u) ((doubledToHilbert (E := E)) v) =
      KreinSpace.kreinInner u v := by simp [doubledToHilbert]
    have h₂ : KreinSpace.kreinInner (rotation45 (E := E)).symm.toLinearEquiv u' v' =
        KreinSpace.kreinInner u' v' := by
      simp [rotation45KreinEquiv]
    simp [h₁, h₂]

/-- Neutral lift via conjugation by the Krein equivalence. -/
noncomputable def neutralLift (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    NeutralSpace E →L[ℝ] NeutralSpace E :=
  (doubledToNeutralKreinEquiv (E := E)).conjContinuousLinearEquiv A

/-- Neutral lift carries the Krein adjoint. -/
lemma neutralLift_kreinAdjoint (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    neutralLift (Krein.doubledKreinAdjoint A) = KreinSpace.kreinAdjoint (neutralLift A) := by
  simp [neutralLift]
  have h := (doubledToNeutralKreinEquiv (E := E)).conjKreinEquiv
  simp [h]

end InfoGeometry.Krein.NoetherSandbox
