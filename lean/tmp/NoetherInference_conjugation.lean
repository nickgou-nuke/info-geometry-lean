import InfoGeometry.Krein.DoubledAdjoint
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.Automorphisms
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace InfoGeometry.Krein.NoetherSandbox

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Placeholder for the missing definition to allow compilation
-- In a real implementation, this would be defined in HilbertBridge.lean
-- and proved to be a KreinEquiv between the diagonal and off-diagonal models.
noncomputable def rotation45KreinEquiv (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (∀ u v : DoubledSpace E,
      KreinSpace.kreinInner ((NeutralSpace.rotation45 (E := E)) u)
        ((NeutralSpace.rotation45 (E := E)) v) =
      KreinSpace.kreinInner u v) →
    KreinEquiv (DoubledSpace E) (NeutralSpace E) :=
  fun hIso =>
  { (NeutralSpace.rotation45 (E := E)).toContinuousLinearEquiv with
    isometric := hIso }

/-- Krein equivalence from the reduced diagonal model to the neutral model. -/
noncomputable def doubledToNeutralKreinEquiv
    (hIso : ∀ u v : DoubledSpace E,
      KreinSpace.kreinInner ((NeutralSpace.rotation45 (E := E)) u)
        ((NeutralSpace.rotation45 (E := E)) v) =
      KreinSpace.kreinInner u v) :
    KreinEquiv (DoubledSpace E) (NeutralSpace E) :=
  rotation45KreinEquiv E hIso

/-- Neutral lift via conjugation by the Krein equivalence. -/
noncomputable def neutralLift
    (hIso : ∀ u v : DoubledSpace E,
      KreinSpace.kreinInner ((NeutralSpace.rotation45 (E := E)) u)
        ((NeutralSpace.rotation45 (E := E)) v) =
      KreinSpace.kreinInner u v)
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    NeutralSpace E →L[ℝ] NeutralSpace E :=
  conjKreinEquiv (doubledToNeutralKreinEquiv (E := E) hIso) A

/-- Neutral-lift/adjoint compatibility as an explicit transport hypothesis. -/
lemma neutralLift_kreinAdjoint
    (hIso : ∀ u v : DoubledSpace E,
      KreinSpace.kreinInner ((NeutralSpace.rotation45 (E := E)) u)
        ((NeutralSpace.rotation45 (E := E)) v) =
      KreinSpace.kreinInner u v)
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hCompat :
      neutralLift (E := E) hIso (Krein.doubledKreinAdjoint A) =
        KreinSpace.kreinAdjoint (neutralLift (E := E) hIso A)) :
    neutralLift (E := E) hIso (Krein.doubledKreinAdjoint A) =
      KreinSpace.kreinAdjoint (neutralLift (E := E) hIso A) :=
  hCompat

end InfoGeometry.Krein.NoetherSandbox
