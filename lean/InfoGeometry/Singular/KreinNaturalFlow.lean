import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.Algebra.Module.StrongTopology
import InfoGeometry.Singular.MoorePenroseAdjoint
import InfoGeometry.Singular.DrazinAdjoint
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Core.Involution

/-!
# Singular Natural Gradient Flow on Krein Spaces

This module wires singular-flow structures to the canonical Mathlib-based Krein stack.
It keeps the API used by downstream singular-bridge modules.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Singular.Architecture

open InfoGeometry.Singular.MoorePenroseAdjoint
open InfoGeometry.Singular.DrazinAdjoint
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Commutator on doubled endomorphisms. -/
def clmComm
    (A B : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E :=
  A * B - B * A

/-- Hilbert-side Krein adjoint alias used by the singular boundary stack. -/
noncomputable abbrev kreinAdjointH
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  KreinSpace.kreinAdjoint (H := HilbertDoubled E) A

@[simp] lemma kreinAdjointH_involutive
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    kreinAdjointH (E := E) (kreinAdjointH (E := E) A) = A := by
  unfold kreinAdjointH
  exact KreinSpace.kreinAdjoint_involutive (H := HilbertDoubled E) A

@[simp] lemma kreinAdjointH_comp
    (A B : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    kreinAdjointH (E := E) (A * B) =
      kreinAdjointH (E := E) B * kreinAdjointH (E := E) A := by
  unfold kreinAdjointH
  exact KreinSpace.kreinAdjoint_mul (H := HilbertDoubled E) A B

@[simp] lemma kreinAdjointH_add
    (A B : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    kreinAdjointH (E := E) (A + B) =
      kreinAdjointH (E := E) A + kreinAdjointH (E := E) B := by
  unfold kreinAdjointH
  exact KreinSpace.kreinAdjoint_add (H := HilbertDoubled E) A B

/-- Hilbert-carrier skew-adjointness predicate used by singular bridge files. -/
abbrev IsKreinSkewAdjointH
    (X : HilbertDoubled E →L[ℝ] HilbertDoubled E) : Prop :=
  X† = -X

/--
Natural gradient operator on the singular boundary:
`G⁺ grad_f` relative to a Moore-Penrose witness.
-/
noncomputable def OperatorNaturalGradient
    (G G_pinv grad_f : HilbertDoubled E →L[ℝ] HilbertDoubled E)
    (_hMP : IsMoorePenroseInverse G G_pinv) :
    HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  G_pinv * grad_f

/-- Infinitesimal-isometry predicate on doubled coordinates:
    `A` is Krein-skew-adjoint, i.e. `J A J = -A` for the fundamental symmetry `J`. -/
def IsInfinitesimalIsometry
    (A : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) : Prop :=
  KreinSpace.IsKreinSkewAdjoint (H := Krein.DoubledSpace E) A

/--
Singular Natural Gradient Flow package.
-/
structure SingularNaturalGradientFlow (G grad_f : HilbertDoubled E →L[ℝ] HilbertDoubled E) where
  G_pinv : HilbertDoubled E →L[ℝ] HilbertDoubled E
  is_mp : IsMoorePenroseInverse G G_pinv
  generator : HilbertDoubled E →L[ℝ] HilbertDoubled E
  gen_def : generator = OperatorNaturalGradient G G_pinv grad_f is_mp
  D_inv : HilbertDoubled E →L[ℝ] HilbertDoubled E
  k_index : ℕ
  is_drazin : IsDrazinInverse G D_inv k_index
  transport_generator : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  isometry : IsInfinitesimalIsometry (E := E) transport_generator

/--
Extract the chiral anomaly associated to a singular flow package.
-/
noncomputable def extractFlowAnomaly
    {G grad_f : HilbertDoubled E →L[ℝ] HilbertDoubled E}
    (flow : SingularNaturalGradientFlow G grad_f) :
    HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  ChiralAnomaly G flow.G_pinv flow.D_inv flow.k_index flow.is_mp flow.is_drazin

/-!
The transport/cartan bridge formerly implemented in this file has moved to
dedicated modules. This singular-flow API intentionally keeps the anomaly
packaging surface above.
-/

end InfoGeometry.Singular.Architecture
