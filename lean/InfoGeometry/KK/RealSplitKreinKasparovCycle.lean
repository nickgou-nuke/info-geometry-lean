import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Krein.Superalgebra
import Mathlib.Analysis.Normed.Operator.Compact

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-- Endomorphism algebra on a real Krein-graded Hilbert carrier. -/
abbrev EndH (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] := H →L[ℝ] H

/-- Concrete compact-operator predicate on bounded real endomorphisms. -/
abbrev IsCompactEnd (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : EndH H) : Prop :=
  IsCompactOperator (A : H → H)

/-!
Primitive bounded real split-Krein cycle.

Policy note: any surviving `complex_i` terminology elsewhere in the repository
is legacy compatibility language only. The canonical internal square-minus-one
axis is `K := J.comp eps`, derived from the split `Cl(1,1)` atom.

This is a primitive bounded real split-Krein Fredholm-like carrier. It is not
yet a final Kasparov-product-ready `B`-module object; the current `ρ` field is
still a second even algebra representation rather than a genuine right module
structure.
-/

/--
Primitive bounded real split-Krein cycle.

This first-pass bounded object contains only carrier data, grading, the split
Clifford atom, the bounded odd phase, parity bookkeeping for the algebra
representations, and compactness conditions against algebra and generator data.
-/
structure RealSplitKreinKasparovCycle
    (A B H : Type*)
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] where
  cl11 : InfoGeometry.Quantum.RealSplitCl11Action H
  π : A →ₐ[ℝ] EndH H
  ρ : B →ₐ[ℝ] EndH H
  π_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (π a)
  ρ_even : ∀ b : B, KreinGradedModule.IsEven (H := H) (ρ b)
  F : EndH H
  F_odd : KreinGradedModule.IsOdd (H := H) F
  F_skewAdj : KreinSpace.IsKreinSkewAdjoint (H := H) F
  F_sq_one_compact : IsCompactEnd H (F * F - (1 : EndH H))
  comm_compact : ∀ a : A, IsCompactEnd H (F * (π a) - (π a) * F)
  superComm_eps_compact :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) F cl11.eps)
  superComm_J_compact :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) F cl11.J)

namespace RealSplitKreinKasparovCycle

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- The derived internal square-minus-one axis carried by the split atom. -/
noncomputable def K (X : RealSplitKreinKasparovCycle A B H) : EndH H :=
  X.cl11.K

/-- The `A`-action is grading-even by primitive hypothesis. -/
lemma π_even_apply (X : RealSplitKreinKasparovCycle A B H) (a : A) :
    KreinGradedModule.IsEven (H := H) (X.π a) :=
  X.π_even a

/-- The `B`-action is grading-even by primitive hypothesis. -/
lemma ρ_even_apply (X : RealSplitKreinKasparovCycle A B H) (b : B) :
    KreinGradedModule.IsEven (H := H) (X.ρ b) :=
  X.ρ_even b

/-- The super-commutator with the even `A`-action reduces to the ordinary commutator. -/
lemma superComm_pi_compact
    (X : RealSplitKreinKasparovCycle A B H) (a : A) :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) X.F (X.π a)) := by
  have hsuper :
      KreinGradedModule.superComm (H := H) X.F (X.π a)
        = KreinGradedModule.comm (H := H) X.F (X.π a) :=
    KreinGradedModule.superComm_odd_even (H := H) X.F_odd (X.π_even a)
  rw [hsuper]
  simpa [KreinGradedModule.comm] using X.comm_compact a

end RealSplitKreinKasparovCycle

end InfoGeometry.KK
