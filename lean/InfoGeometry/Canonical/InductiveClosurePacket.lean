import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents
import InfoGeometry.OperatorAlgebra.SupergradedClosure
import InfoGeometry.OperatorAlgebra.RecursiveSupercharge
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

noncomputable section

namespace InfoGeometry.Canonical.InductiveClosurePacket

open InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents
open InfoGeometry.OperatorAlgebra.SupergradedClosure
open InfoGeometry.OperatorAlgebra.RecursiveSupercharge

/--
The inductive chain representing the local-to-global hierarchy.
$A_0 \to A_1 \to A_2 \to \dots$
-/
structure InductiveOperatorChain where
  Stage : ℕ → Type*
  stageRing : ∀ n, Ring (Stage n)
  Bonding : ∀ n, Stage n →+* Stage (n + 1)

attribute [instance] InductiveOperatorChain.stageRing

namespace InductiveOperatorChain

variable (C : InductiveOperatorChain)

/-- Iterated embedding from stage 0 to stage n. -/
def iterMap : ∀ n, C.Stage 0 → C.Stage n
  | 0 => fun x => x
  | n + 1 => fun x => C.Bonding n (iterMap n x)

/-- Iterated embeddings preserve addition. -/
@[simp]
theorem iterMap_add (n : ℕ) (x y : C.Stage 0) :
    C.iterMap n (x + y) = C.iterMap n x + C.iterMap n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [iterMap]
      rw [ih]
      exact map_add (C.Bonding n) _ _

/-- Iterated embeddings preserve multiplication. -/
@[simp]
theorem iterMap_mul (n : ℕ) (x y : C.Stage 0) :
    C.iterMap n (x * y) = C.iterMap n x * C.iterMap n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [iterMap]
      rw [ih]
      exact map_mul (C.Bonding n) _ _

/--
Inductive lemma schema: if map n→n+1 preserves the generators, then
SupergradedClosureAt is perfectly stable along the chain.
-/
@[rep_depth transport]
theorem supergradedClosureAt_stable_along_chain
    {Q0 Qsharp0 : C.Stage 0}
    (hClosure0 : SupergradedClosureAt (R := C.Stage 0) Q0 Qsharp0) :
    ∀ n, SupergradedClosureAt (R := C.Stage n) (C.iterMap n Q0) (C.iterMap n Qsharp0) := by
  intro n
  rcases hClosure0 with ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1' := congrArg (C.iterMap n) h1
    simpa [iterMap_add, iterMap_mul] using h1'
  · have h2' := congrArg (C.iterMap n) h2
    simpa [iterMap_add, iterMap_mul] using h2'
  · have h3' := congrArg (C.iterMap n) h3
    simpa [iterMap_add, iterMap_mul] using h3'
  · have h4' := congrArg (C.iterMap n) h4
    simpa [iterMap_add, iterMap_mul] using h4'

/-- Functorial transport: intertwiners preserve odd-odd brackets. -/
@[rep_depth transport]
theorem iterMap_preserves_oddAnticomm
    (n : ℕ) (Q R : C.Stage 0) :
    C.iterMap n (oddAnticomm Q R) = oddAnticomm (C.iterMap n Q) (C.iterMap n R) := by
  simp [oddAnticomm, iterMap_add, iterMap_mul]

/-- Functorial transport: central term is natural under embeddings. -/
@[rep_depth transport]
theorem iterMap_preserves_centrality
    (n : ℕ) (Z : C.Stage 0)
    (hCentral : ∀ X : C.Stage 0, Z * X = X * Z)
    (hSurj : Function.Surjective (C.iterMap n)) :
    ∀ Y : C.Stage n, C.iterMap n Z * Y = Y * C.iterMap n Z := by
  intro Y
  rcases hSurj Y with ⟨X, rfl⟩
  have h := congrArg (C.iterMap n) (hCentral X)
  simpa [iterMap_mul] using h

end InductiveOperatorChain

/-- Duality maps preserve the full supergraded closure identities. -/
@[rep_depth transport]
theorem duality_transport_supergradedClosureAt
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A ≃+* B)
    {Q Qsharp : A}
    (hClosure : SupergradedClosureAt (R := A) Q Qsharp) :
    SupergradedClosureAt (R := B) (Dual Q) (Dual Qsharp) := by
  rcases hClosure with ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1' := congrArg Dual h1
    simpa [map_add, map_mul] using h1'
  · have h2' := congrArg Dual h2
    simpa [map_add, map_mul] using h2'
  · have h3' := congrArg Dual h3
    simpa [map_add, map_mul] using h3'
  · have h4' := congrArg Dual h4
    simpa [map_add, map_mul] using h4'

/-! ## 5. Concrete algebraic direct-limit passage -/

/-- The canonical algebraic direct limit of an inductive operator chain. -/
abbrev LimitStage (C : InductiveOperatorChain) :=
  InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.DirectLimitSuperClosure C.Bonding

/-- The canonical stage injection into the direct limit. -/
abbrev limitEmbed (C : InductiveOperatorChain) (n : ℕ) :
    C.Stage n →+* LimitStage C :=
  InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf C.Bonding n

/-!
The remaining closure obligation is stated over the canonical direct-limit
carrier. The carrier, ring structure, injections, and transition law are
derived from Mathlib's quotient direct limit rather than supplied as fields.
-/
def limitPassage (C : InductiveOperatorChain) : Prop :=
  ∀ (Q0 Qsharp0 : C.Stage 0),
    (∀ n, SupergradedClosureAt (R := C.Stage n)
      (C.iterMap n Q0) (C.iterMap n Qsharp0)) →
      SupergradedClosureAt (R := LimitStage C)
      (limitEmbed C 0 Q0) (limitEmbed C 0 Qsharp0)

/-!
The direct-limit passage is already forced by the stage-zero closure.

`SupergradedClosureAt` is a finite conjunction of ring identities, and
`limitEmbed C 0` is a ring homomorphism.  Thus no additional colimit interface
is needed for this algebraic closure: the universal direct-limit carrier
preserves the four identities coefficientwise.
-/
theorem limitPassage_of_stage_zero
    (C : InductiveOperatorChain) :
    limitPassage C := by
  intro Q0 Qsharp0 hStages
  rcases hStages 0 with ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (limitEmbed C 0) h1
    simpa [InductiveOperatorChain.iterMap, map_add, map_mul] using h
  · have h := congrArg (limitEmbed C 0) h2
    simpa [InductiveOperatorChain.iterMap, map_add, map_mul] using h
  · have h := congrArg (limitEmbed C 0) h3
    simpa [InductiveOperatorChain.iterMap, map_add, map_mul] using h
  · have h := congrArg (limitEmbed C 0) h4
    simpa [InductiveOperatorChain.iterMap, map_add, map_mul] using h

namespace LimitPassage

variable {C : InductiveOperatorChain}

theorem limit_closure_stable (h : limitPassage C)
    (Q0 Qsharp0 : C.Stage 0)
    (hStages : ∀ n, SupergradedClosureAt (R := C.Stage n)
      (C.iterMap n Q0) (C.iterMap n Qsharp0)) :
    SupergradedClosureAt (R := LimitStage C)
      (limitEmbed C 0 Q0) (limitEmbed C 0 Qsharp0) :=
  h Q0 Qsharp0 hStages

theorem limit_closure_stable_of_stage_zero
    (Q0 Qsharp0 : C.Stage 0)
    (hStages : ∀ n, SupergradedClosureAt (R := C.Stage n)
      (C.iterMap n Q0) (C.iterMap n Qsharp0)) :
    SupergradedClosureAt (R := LimitStage C)
      (limitEmbed C 0 Q0) (limitEmbed C 0 Qsharp0) :=
  limit_closure_stable (limitPassage_of_stage_zero C) Q0 Qsharp0 hStages

instance : Ring (LimitStage C) := inferInstance

def embed_hom (n : ℕ) : C.Stage n →+* LimitStage C :=
  limitEmbed C n

theorem embed_compatible (n : ℕ) (x : C.Stage n) :
    limitEmbed C (n + 1) (C.Bonding n x) = limitEmbed C n x := by
  exact InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_bond
    C.Bonding n x

end LimitPassage

end InfoGeometry.Canonical.InductiveClosurePacket
