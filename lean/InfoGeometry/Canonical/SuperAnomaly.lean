import InfoGeometry.Krein.Clifford
import InfoGeometry.Krein.HilbertBridge

open scoped InnerProductSpace

namespace SuperAnomaly

open InfoGeometry.Krein
open KreinGradedModule

/-- Endomorphism algebra on the graded Krein carrier. -/
abbrev EndH (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] := H →L[ℝ] H

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- `Z/2` parity tags used for graded brackets. -/
inductive SuperParity where
  | even
  | odd
deriving DecidableEq, Repr

/-- Sign factor `(-1)^{|p||q|}` specialized to `{even, odd}`. -/
def paritySign : SuperParity → SuperParity → ℝ
  | .odd, .odd => -1
  | _, _ => 1

/-- Compatibility predicate tying a parity label to the grading involution. -/
def IsParity (p : SuperParity) (A : EndH H) : Prop :=
  match p with
  | .even => KreinGradedModule.IsEven (H := H) A
  | .odd => KreinGradedModule.IsOdd (H := H) A

/-- Graded commutator `[A, B}` on endomorphisms. -/
noncomputable def superComm (p q : SuperParity) (A B : EndH H) : EndH H :=
  A.comp B - paritySign p q • (B.comp A)

/-- Even-even channel (ordinary commutator). -/
noncomputable abbrev commutator (A B : EndH H) : EndH H :=
  superComm (H := H) SuperParity.even SuperParity.even A B

/-- Odd-odd channel (ordinary anticommutator). -/
noncomputable abbrev anticommutator (A B : EndH H) : EndH H :=
  superComm (H := H) SuperParity.odd SuperParity.odd A B

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
@[simp] lemma superComm_even_left (q : SuperParity) (A B : EndH H) :
    superComm (H := H) SuperParity.even q A B = A.comp B - B.comp A := by
  simp [superComm, paritySign]

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
@[simp] lemma superComm_odd_odd (A B : EndH H) :
    superComm (H := H) SuperParity.odd SuperParity.odd A B = A.comp B + B.comp A := by
  simp [superComm, paritySign, sub_eq_add_neg]

/--
Superweight-like anomaly functional: a linear functional vanishing on graded
commutators of homogeneous elements.
-/
structure SuperWeightLike where
  τ : EndH H →ₗ[ℝ] ℝ
  graded_weight :
    ∀ {p q : SuperParity} {A B : EndH H},
      IsParity (H := H) p A →
      IsParity (H := H) q B →
      τ (superComm (H := H) p q A B) = 0

namespace SuperWeightLike

variable (S : SuperWeightLike (H := H))

/-- Lemma `graded_weight_commutator`. -/
lemma graded_weight_commutator {A B : EndH H}
    (hA : IsParity (H := H) SuperParity.even A)
    (hB : IsParity (H := H) SuperParity.even B) :
    S.τ (commutator (H := H) A B) = 0 :=
  S.graded_weight hA hB

/-- Lemma `graded_weight_anticommutator`. -/
lemma graded_weight_anticommutator {A B : EndH H}
    (hA : IsParity (H := H) SuperParity.odd A)
    (hB : IsParity (H := H) SuperParity.odd B) :
    S.τ (anticommutator (H := H) A B) = 0 := by
  simpa [anticommutator] using
    (S.graded_weight (p := SuperParity.odd) (q := SuperParity.odd) hA hB)

end SuperWeightLike

end SuperAnomaly
