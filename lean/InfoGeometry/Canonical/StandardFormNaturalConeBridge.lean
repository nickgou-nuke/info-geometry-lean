import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

set_option linter.unusedSectionVars false

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.StandardFormNaturalConeBridge

Theorem-safe standard-form natural cone interface.

This file records the Type III replacement of density matrices and traces:

`M_*^+ ≃ P`

where `P` is the standard-form natural positive cone. A normal positive
functional is represented by a unique cone vector:

`ω(A) = ⟪A ξ_ω, ξ_ω⟫`.

The file does not construct a full von Neumann algebra standard form in Mathlib.
It records the standard-form carrier data together with the three standard-form
facts required to instantiate this interface.  The readback theorems below are
therefore projections from explicit model data, not hidden global proofs.
Self-duality of the cone and Cantor/cylinder face readouts remain separate
owner statements.

The natural cone is not identified with the Krein causal cone
`{ξ | [ξ,ξ]_J ≥ 0}` unless a separate specialization theorem supplies that
identification.
-/

namespace InfoGeometry.Canonical.StandardFormNaturalConeBridge

/-! ## Doubled Tomita--Cartan carrier -/

/--
Carrier for a doubled real Tomita--Cartan split.

The intended model is `M_sa ⊕ M'_sa` with
`Θ(A,B) = (J B J, J A J)`, but this structure only records the doubled carrier
map.  The involution law is an external predicate.
-/
@[rep_depth operator]
structure DoubledTomitaCartanCarrier
    (Left Right : Type*) where
  /-- Tomita/Cartan reflection on the doubled left/right carrier. -/
  theta : Left × Right → Left × Right

/-- Predicate asserting that the supplied Tomita/Cartan reflection squares to identity. -/
@[rep_depth operator]
def IsTomitaCartanInvolution {Left Right : Type*}
    (C : DoubledTomitaCartanCarrier Left Right) : Prop :=
  ∀ x : Left × Right, C.theta (C.theta x) = x

/-- Self-dual doubled sector: `Θx = x`. -/
@[rep_depth operator]
def IsTomitaCartanSelfDual {Left Right : Type*}
    (C : DoubledTomitaCartanCarrier Left Right)
    (x : Left × Right) : Prop :=
  C.theta x = x

/-- Anti-self-dual doubled sector: `Θx = -x`. -/
@[rep_depth operator]
def IsTomitaCartanAntiSelfDual {Left Right : Type*}
    [Neg Left] [Neg Right]
    (C : DoubledTomitaCartanCarrier Left Right)
    (x : Left × Right) : Prop :=
  C.theta x = -x

/-- Self-dual sector as a set. -/
@[rep_depth operator]
def tomitaCartanSelfDualSector {Left Right : Type*}
    (C : DoubledTomitaCartanCarrier Left Right) : Set (Left × Right) :=
  {x | IsTomitaCartanSelfDual C x}

/-- Anti-self-dual sector as a set. -/
@[rep_depth operator]
def tomitaCartanAntiSelfDualSector {Left Right : Type*}
    [Neg Left] [Neg Right]
    (C : DoubledTomitaCartanCarrier Left Right) : Set (Left × Right) :=
  {x | IsTomitaCartanAntiSelfDual C x}

namespace DoubledTomitaCartanCarrier

variable {Left Right : Type*}
variable (C : DoubledTomitaCartanCarrier Left Right)

/-- Readback of the externally supplied involution law. -/
@[rep_depth operator]
theorem theta_sq_of_isTomitaCartanInvolution
    (hC : IsTomitaCartanInvolution C)
    (x : Left × Right) :
    C.theta (C.theta x) = x :=
  hC x

/-- Membership in the self-dual sector is exactly the fixed-point law. -/
@[rep_depth operator]
theorem mem_selfDualSector_iff
    (x : Left × Right) :
    x ∈ tomitaCartanSelfDualSector C ↔ C.theta x = x :=
  Iff.rfl

/-- Membership in the anti-self-dual sector is exactly the negated fixed-point law. -/
@[rep_depth operator]
theorem mem_antiSelfDualSector_iff
    [Neg Left] [Neg Right]
    (x : Left × Right) :
    x ∈ tomitaCartanAntiSelfDualSector C ↔ C.theta x = -x :=
  Iff.rfl

end DoubledTomitaCartanCarrier

/-! ## Natural-cone standard-form carrier -/

/--
Standard-form representation interface for normal positive functionals.

The intended interpretation is `M_*^+ ↔ P`, with
`ω(A) = ⟪A ξ_ω, ξ_ω⟫`.  Since these identities are not derivable from arbitrary
carrier maps, they are explicit obligations of any concrete standard-form
model.
-/
@[rep_depth operator]
structure NaturalConeStandardFormInterface
    (Alg Hilb NormalPositive : Type*) where
  /-- Algebra action on the standard-form Hilbert carrier. -/
  act : Alg → Hilb → Hilb

  /-- Modular conjugation / Tomita reflection. -/
  J : Hilb → Hilb

  /-- Natural positive cone. -/
  cone : Set Hilb

  /-- Predicate selecting normal positive functionals. -/
  isNormalPositive : NormalPositive → Prop

  /-- Standard-form vector representative of a normal positive functional. -/
  coneVector : NormalPositive → Hilb

  /-- Functional evaluation. -/
  eval : NormalPositive → Alg → ℝ

  /-- Real inner-product/readout channel on the Hilbert carrier. -/
  innerReadout : Hilb → Hilb → ℝ

  /-- Cone-vector representatives of normal positive functionals lie in the natural cone. -/
  coneVector_mem :
    ∀ ω : NormalPositive, isNormalPositive ω → coneVector ω ∈ cone

  /-- Functional evaluation agrees with the standard-form vector readout. -/
  eval_eq_vector_readout :
    ∀ (ω : NormalPositive) (A : Alg), isNormalPositive ω →
      eval ω A = innerReadout (act A (coneVector ω)) (coneVector ω)

  /-- The modular reflection fixes every element of the natural cone. -/
  J_fixes_cone :
    ∀ ξ : Hilb, ξ ∈ cone → J ξ = ξ



namespace NaturalConeStandardFormInterface

variable {Alg Hilb NormalPositive : Type*}
variable (S : NaturalConeStandardFormInterface Alg Hilb NormalPositive)

/-- Theorem owner: a normal positive functional has a cone-vector representative. -/
@[rep_depth operator]
theorem coneVector_mem_thm
    (ω : NormalPositive)
    (hω : S.isNormalPositive ω) :
    S.coneVector ω ∈ S.cone :=
  S.coneVector_mem ω hω

/-- Readback: a normal positive functional has a cone-vector representative. -/
@[rep_depth operator]
theorem coneVector_mem_of_normal
    (ω : NormalPositive)
    (hω : S.isNormalPositive ω) :
    S.coneVector ω ∈ S.cone := by
  exact S.coneVector_mem_thm ω hω

/-- Theorem owner: functional evaluation is the standard-form vector readout. -/
@[rep_depth operator]
theorem eval_eq_vector_readout_thm
    (ω : NormalPositive)
    (A : Alg)
    (hω : S.isNormalPositive ω) :
    S.eval ω A = S.innerReadout (S.act A (S.coneVector ω)) (S.coneVector ω) :=
  S.eval_eq_vector_readout ω A hω

/-- Readback: functional evaluation is the standard-form vector readout. -/
@[rep_depth operator]
theorem eval_eq_vector_readout_of_normal
    (ω : NormalPositive)
    (A : Alg)
    (hω : S.isNormalPositive ω) :
    S.eval ω A = S.innerReadout (S.act A (S.coneVector ω)) (S.coneVector ω) := by
  exact S.eval_eq_vector_readout_thm ω A hω

/-- Theorem owner: cone elements are fixed pointwise by the modular reflection. -/
@[rep_depth operator]
theorem J_fixes_cone_thm
    (ξ : Hilb)
    (hξ : ξ ∈ S.cone) :
    S.J ξ = ξ :=
  S.J_fixes_cone ξ hξ

/-- Readback: cone elements are fixed pointwise by the modular reflection. -/
@[rep_depth operator]
theorem J_fixes_cone_of_mem
    (ξ : Hilb)
    (hξ : ξ ∈ S.cone) :
    S.J ξ = ξ := by
  exact S.J_fixes_cone_thm ξ hξ

/-- Readback: `J` fixes the cone vector of a normal positive functional. -/
@[rep_depth operator]
theorem J_fixes_coneVector
    (ω : NormalPositive)
    (hω : S.isNormalPositive ω) :
    S.J (S.coneVector ω) = S.coneVector ω :=
  S.J_fixes_cone_of_mem (S.coneVector ω) (S.coneVector_mem_of_normal ω hω)

end NaturalConeStandardFormInterface

/-! ## Cantor/cylinder natural-cone face readouts -/

/--
Cantor/cylinder localization of the standard-form natural cone.

This is a theorem-safe carrier for the face/readout layer.  The intended
identity is `P_w = p_w J p_w J P`, but this file does not construct the full
Tomita--Takesaki standard form; the face law and cylinder weights are explicit
local data at this layer.
-/
@[rep_depth projective]
structure NaturalConeCantorFaceSystem
    (Alg Hilb NormalPositive : Type*) where
  /-- Standard-form natural-cone interface. -/
  standard :
    NaturalConeStandardFormInterface Alg Hilb NormalPositive

  /-- Cylinder projection associated to a finite binary word. -/
  cylinderProjection :
    TypeIIIModularCantorSystem.BinaryWord → Alg

  /-- Localized face of the natural cone. -/
  face :
    TypeIIIModularCantorSystem.BinaryWord → Set Hilb

  /-- Cylinder weight/readout, replacing trace-size. -/
  cylinderWeight :
    TypeIIIModularCantorSystem.BinaryWord → ℝ

  /-- Positivity of cylinder weights. -/
  cylinderWeight_pos :
    ∀ w : TypeIIIModularCantorSystem.BinaryWord, 0 < cylinderWeight w

namespace NaturalConeCantorFaceSystem

variable {Alg Hilb NormalPositive : Type*}
variable (C : NaturalConeCantorFaceSystem Alg Hilb NormalPositive)

/-- Negative logarithmic cylinder potential. -/
@[rep_depth thermo]
noncomputable def cylinderPotential
    (w : TypeIIIModularCantorSystem.BinaryWord) : ℝ :=
  TypeIIIModularCantorSystem.cylinderPotential C.cylinderWeight w

/-- Local branch information increment. -/
@[rep_depth thermo]
noncomputable def branchIncrement
    (w : TypeIIIModularCantorSystem.BinaryWord) (b : Bool) : ℝ :=
  TypeIIIModularCantorSystem.branchIncrement C.cylinderWeight w b

/-- Logarithmic chain rule for cylinder potentials. -/
@[rep_depth thermo]
theorem cylinderPotential_child
    (w : TypeIIIModularCantorSystem.BinaryWord) (b : Bool) :
    C.cylinderPotential (TypeIIIModularCantorSystem.BinaryWord.child w b) =
      C.cylinderPotential w + C.branchIncrement w b := by
  exact
    TypeIIIModularCantorSystem.cylinderPotential_child
      C.cylinderWeight C.cylinderWeight_pos w b

end NaturalConeCantorFaceSystem

/-! ## Concrete finite binary levels -/

namespace BinaryLevel

open TypeIIIModularCantorSystem

/-- Concrete list of all binary words at level `n`. -/
@[rep_depth projective]
def wordsList : ℕ → List BinaryWord
  | 0 => [[]]
  | n + 1 =>
      (wordsList n).flatMap
        (fun w => [BinaryWord.child w false, BinaryWord.child w true])

/--
Concrete finite set of binary words at level `n`.

This is the canonical finite level index set used by partition backends.  The
underlying list is recursive; `toFinset` removes any duplicates, while concrete
partition theorems below use the list directly to avoid hiding multiplicity
assumptions in `Finset` coercions.
-/
@[rep_depth projective]
def words (n : ℕ) : Finset BinaryWord :=
  (wordsList n).toFinset

@[simp] theorem wordsList_zero :
    wordsList 0 = ([[]] : List BinaryWord) :=
  rfl

@[simp] theorem wordsList_succ (n : ℕ) :
    wordsList (n + 1) =
      (wordsList n).flatMap
        (fun w => [BinaryWord.child w false, BinaryWord.child w true]) :=
  rfl

@[simp] theorem words_zero :
    words 0 = ({[]} : Finset BinaryWord) :=
  rfl

section Partition

variable {Alg : Type*} [AddCommMonoid Alg]

/-- Sum of a projection family over the concrete binary level list. -/
@[rep_depth projective]
def levelSum (projectionOf : BinaryWord → Alg) (n : ℕ) : Alg :=
  ((wordsList n).map projectionOf).sum

@[simp] theorem levelSum_zero
    (projectionOf : BinaryWord → Alg) :
    levelSum projectionOf 0 = projectionOf [] := by
  simp [levelSum]

@[simp] theorem levelSum_succ
    (projectionOf : BinaryWord → Alg) (n : ℕ) :
    levelSum projectionOf (n + 1) =
      ((wordsList n).flatMap
        (fun w =>
          [projectionOf (BinaryWord.child w false),
            projectionOf (BinaryWord.child w true)])).sum := by
  unfold levelSum
  rw [wordsList_succ]
  simp [List.map_flatMap]

/--
Concrete recursive binary partition theorem.

If every parent projection splits as the sum of its two child projections, then
the total projection over every concrete binary level equals the root
projection.
-/
@[rep_depth projective]
theorem levelSum_eq_root_of_binary_split
    (projectionOf : BinaryWord → Alg)
    (hSplit :
      ∀ w : BinaryWord,
        projectionOf w =
          projectionOf (BinaryWord.child w false) +
            projectionOf (BinaryWord.child w true))
    (n : ℕ) :
    levelSum projectionOf n = projectionOf [] := by
  induction n with
  | zero =>
      simp [levelSum]
  | succ n ih =>
      have hmap :
          ((wordsList n).flatMap
            (fun w =>
              [projectionOf (BinaryWord.child w false),
                projectionOf (BinaryWord.child w true)])).sum =
            ((wordsList n).map projectionOf).sum := by
        induction wordsList n with
        | nil =>
            simp
        | cons w ws ihws =>
            simp [hSplit w, ihws, add_assoc]
      calc
        levelSum projectionOf (n + 1)
            =
          ((wordsList n).flatMap
            (fun w =>
              [projectionOf (BinaryWord.child w false),
                projectionOf (BinaryWord.child w true)])).sum := by
              rw [levelSum_succ]
        _ = ((wordsList n).map projectionOf).sum := hmap
        _ = projectionOf [] := ih

end Partition

section Expectation

variable {Alg State : Type*}
variable [AddCommMonoid Alg]

/-- Predicate: an evaluation readout preserves concrete binary-level list sums. -/
@[rep_depth projective]
def EvalPreservesBinaryLevelListSums
    (eval : State → Alg → ℝ) : Prop :=
  ∀ (ω : State) (n : ℕ) (projectionOf : BinaryWord → Alg),
    eval ω (levelSum projectionOf n) =
      ((wordsList n).map (fun w => eval ω (projectionOf w))).sum

/--
Concrete binary-level expectation partition theorem.

The only algebraic input is the supplied binary split law for projectors and
finite additivity of the chosen readout over the concrete level lists.
-/
@[rep_depth projective]
theorem expectation_level_sum_eq_root_of_binary_split
    (eval : State → Alg → ℝ)
    (projectionOf : BinaryWord → Alg)
    (ω : State)
    (hSplit :
      ∀ w : BinaryWord,
        projectionOf w =
          projectionOf (BinaryWord.child w false) +
            projectionOf (BinaryWord.child w true))
    (hEval : EvalPreservesBinaryLevelListSums eval)
    (n : ℕ) :
    ((wordsList n).map (fun w => eval ω (projectionOf w))).sum =
      eval ω (projectionOf []) := by
  calc
    ((wordsList n).map (fun w => eval ω (projectionOf w))).sum
        = eval ω (levelSum projectionOf n) := by
            exact (hEval ω n projectionOf).symm
    _ = eval ω (projectionOf []) := by
            rw [levelSum_eq_root_of_binary_split projectionOf hSplit n]

end Expectation

end BinaryLevel

/--
Predicate: a finite family of cylinder projections sums to the distinguished
unit/total observable.

This is intentionally abstract over the projection carrier and the operator
carrier.
-/
@[rep_depth projective]
def IsFinitePartitionOfUnity
    {Proj End : Type*} [AddCommMonoid End] [One End]
    (words : Finset TypeIIIModularCantorSystem.BinaryWord)
    (projectionOf : TypeIIIModularCantorSystem.BinaryWord → Proj)
    (toOperator : Proj → End) : Prop :=
  Finset.sum words (fun w => toOperator (projectionOf w)) = 1

/--
Predicate: an evaluation functional preserves finite binary-word indexed sums.

This avoids any injectivity/deduplication property on the map from cylinder
words to concrete operators, while staying at the actual Cantor index type used
by this bridge.
-/
@[rep_depth projective]
def EvalPreservesFiniteIndexedSums
    {State End : Type*} [AddCommMonoid End]
    (eval : State → End → ℝ) : Prop :=
  ∀ (ω : State) (s : Finset TypeIIIModularCantorSystem.BinaryWord)
    (f : TypeIIIModularCantorSystem.BinaryWord → End),
    eval ω (Finset.sum s f) = Finset.sum s (fun i => eval ω (f i))

/--
Conditional finite-level expectation partition theorem.

If a finite cylinder family partitions unity and the readout preserves finite
indexed sums, then the sum of cylinder expectations is the expectation of the
total observable.
-/
@[rep_depth projective]
theorem expectation_sum_eq_total_of_partition
    {Alg Hilb NormalPositive Proj : Type*}
    [AddCommMonoid Alg] [One Alg]
    (S : NaturalConeStandardFormInterface Alg Hilb NormalPositive)
    (words : Finset TypeIIIModularCantorSystem.BinaryWord)
    (projectionOf : TypeIIIModularCantorSystem.BinaryWord → Proj)
    (toOperator : Proj → Alg)
    (ω : NormalPositive)
    (hPartition : IsFinitePartitionOfUnity words projectionOf toOperator)
    (hEval : EvalPreservesFiniteIndexedSums S.eval) :
    Finset.sum words (fun w => S.eval ω (toOperator (projectionOf w))) =
      S.eval ω (1 : Alg) := by
  have hEvalWords :
      S.eval ω (Finset.sum words (fun w => toOperator (projectionOf w))) =
        Finset.sum words (fun w => S.eval ω (toOperator (projectionOf w))) :=
    hEval ω words (fun w => toOperator (projectionOf w))
  calc
    Finset.sum words (fun w => S.eval ω (toOperator (projectionOf w)))
        = S.eval ω (Finset.sum words (fun w => toOperator (projectionOf w))) :=
            hEvalWords.symm
    _ = S.eval ω (1 : Alg) := by
            rw [hPartition]

/--
Finite-level cylinder partition readout.

This carrier records only the finite cylinder system and distinguished state.
The partition/readout law is proved below from explicit finite-partition and
finite-additivity premises.
-/
@[rep_depth projective]
structure FiniteCylinderExpectationPartition
    (Alg Hilb NormalPositive : Type*) where
  /-- Cantor/cylinder natural-cone face system. -/
  faces :
    NaturalConeCantorFaceSystem Alg Hilb NormalPositive

  /-- Distinguished identity/total observable used for normalization. -/
  one : Alg

  /-- Finite set of active words at level `n`. -/
  levelWords :
    ℕ → Finset TypeIIIModularCantorSystem.BinaryWord

  /-- Distinguished normal positive functional, e.g. vacuum/KMS state. -/
  omega :
    NormalPositive

  /-- `omega` is a normal positive functional in the standard-form interface. -/
  omega_mem :
    faces.standard.isNormalPositive omega

namespace FiniteCylinderExpectationPartition

variable {Alg Hilb NormalPositive : Type*}
variable (P : FiniteCylinderExpectationPartition Alg Hilb NormalPositive)

/-- Readback: the distinguished functional is normal positive. -/
@[rep_depth projective]
theorem omega_isNormalPositive :
    P.faces.standard.isNormalPositive P.omega :=
  P.omega_mem

/-- Readback: finite level expectation recovers total expectation. -/
@[rep_depth projective]
theorem level_expectation_sum_eq_total
    [AddCommMonoid Alg]
    (hEval : EvalPreservesFiniteIndexedSums P.faces.standard.eval)
    (n : ℕ) :
    Finset.sum (P.levelWords n) (fun w => P.faces.cylinderProjection w) = P.one →
    Finset.sum (P.levelWords n)
      (fun w => P.faces.standard.eval P.omega (P.faces.cylinderProjection w)) =
    P.faces.standard.eval P.omega P.one := by
  intro hPartition
  have hEvalWords :
      P.faces.standard.eval P.omega
          (Finset.sum (P.levelWords n) (fun w => P.faces.cylinderProjection w)) =
        Finset.sum (P.levelWords n)
          (fun w => P.faces.standard.eval P.omega (P.faces.cylinderProjection w)) :=
    hEval P.omega (P.levelWords n) (fun w => P.faces.cylinderProjection w)
  calc
    Finset.sum (P.levelWords n)
        (fun w => P.faces.standard.eval P.omega (P.faces.cylinderProjection w))
        = P.faces.standard.eval P.omega
            (Finset.sum (P.levelWords n) (fun w => P.faces.cylinderProjection w)) :=
            hEvalWords.symm
    _ = P.faces.standard.eval P.omega P.one := by rw [hPartition]

/-- If the distinguished functional is normalized, every finite level sums to one. -/
@[rep_depth projective]
theorem level_expectation_sum_eq_one
    [AddCommMonoid Alg]
    (hEval : EvalPreservesFiniteIndexedSums P.faces.standard.eval)
    (hΩ : P.faces.standard.eval P.omega P.one = 1)
    (n : ℕ) :
    Finset.sum (P.levelWords n) (fun w => P.faces.cylinderProjection w) = P.one →
    Finset.sum (P.levelWords n)
      (fun w => P.faces.standard.eval P.omega (P.faces.cylinderProjection w)) = 1 := by
  intro hPartition
  rw [P.level_expectation_sum_eq_total hEval n hPartition, hΩ]

/-- Readback of the standard-form vector law on a cylinder projection. -/
@[rep_depth projective]
theorem cylinderExpectation_eq_vector_readout
    (w : TypeIIIModularCantorSystem.BinaryWord) :
    P.faces.standard.eval P.omega (P.faces.cylinderProjection w) =
      P.faces.standard.innerReadout
        (P.faces.standard.act (P.faces.cylinderProjection w)
          (P.faces.standard.coneVector P.omega))
        (P.faces.standard.coneVector P.omega) :=
  P.faces.standard.eval_eq_vector_readout_of_normal
    P.omega (P.faces.cylinderProjection w) P.omega_mem

/-- Readback of the standard-form vector law on the total observable. -/
@[rep_depth projective]
theorem totalExpectation_eq_vector_readout :
    P.faces.standard.eval P.omega P.one =
      P.faces.standard.innerReadout
        (P.faces.standard.act P.one (P.faces.standard.coneVector P.omega))
        (P.faces.standard.coneVector P.omega) :=
  P.faces.standard.eval_eq_vector_readout_of_normal P.omega P.one P.omega_mem

end FiniteCylinderExpectationPartition

/-! ## Modular natural-cone face carrier -/

section ModularFaces

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace H
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance modularFaceNormedRing : NormedRing EndH := inferInstance
noncomputable local instance modularFaceNormedAlgebra : NormedAlgebra ℝ EndH := inferInstance
local instance modularFaceTopologicalRing : IsTopologicalRing EndH := inferInstance
local instance modularFaceCompleteSpace : CompleteSpace EndH := inferInstance
local instance modularFaceSMulCommClass : SMulCommClass ℝ EndH EndH := inferInstance
local instance modularFaceIsScalarTower : IsScalarTower ℝ EndH EndH := inferInstance

/--
Theorem-safe modular face carrier for natural-cone localization.

The intended analytic model is `L_w = p_w J p_w J`, but this carrier does not
construct Tomita--Takesaki standard form.  It records bounded cylinder
projectors and their modular mirrors as supplied data, and defines the
localizer as their product.
-/
@[rep_depth operator]
structure ModularNaturalConeFaceBridge (Word : Type*) where
  /-- Natural-cone shadow on the doubled standard-form carrier. -/
  naturalCone : Set H₂

  /-- Cylinder/Wigner--Jones projector for a word or atom. -/
  cylinderProjector : Word → EndH

  /-- Modular mirror of the cylinder projector, morally `J p_w J`. -/
  modularMirrorProjector : Word → EndH

  /-- Supplied preservation law for cylinder projectors. -/
  cylinderProjector_preserves_naturalCone :
    ∀ w : Word, ∀ ξ : H₂, ξ ∈ naturalCone → cylinderProjector w ξ ∈ naturalCone

  /-- Supplied preservation law for mirrored cylinder projectors. -/
  modularMirrorProjector_preserves_naturalCone :
    ∀ w : Word, ∀ ξ : H₂, ξ ∈ naturalCone → modularMirrorProjector w ξ ∈ naturalCone

namespace ModularNaturalConeFaceBridge

variable {Word : Type*}
variable (B : ModularNaturalConeFaceBridge (H := H) Word)

/-- Localized modular face operator, morally `L_w = p_w J p_w J`. -/
@[rep_depth operator]
noncomputable def localizationOp (w : Word) : EndH :=
  B.cylinderProjector w * B.modularMirrorProjector w

/-- Readback: cylinder projectors preserve the supplied natural-cone shadow. -/
@[rep_depth operator]
theorem cylinderProjector_mem_naturalCone
    (w : Word) {ξ : H₂} (hξ : ξ ∈ B.naturalCone) :
    B.cylinderProjector w ξ ∈ B.naturalCone :=
  B.cylinderProjector_preserves_naturalCone w ξ hξ

/-- Readback: mirrored cylinder projectors preserve the supplied natural-cone shadow. -/
@[rep_depth operator]
theorem modularMirrorProjector_mem_naturalCone
    (w : Word) {ξ : H₂} (hξ : ξ ∈ B.naturalCone) :
    B.modularMirrorProjector w ξ ∈ B.naturalCone :=
  B.modularMirrorProjector_preserves_naturalCone w ξ hξ

/--
The localizer preserves the supplied natural-cone shadow.

This is the theorem-safe form of the face-localization statement: preservation
is obtained from the two supplied preservation laws, not from an unimplemented
global standard-form theorem.
-/
@[rep_depth operator]
theorem localizationOp_mem_naturalCone
    (w : Word) {ξ : H₂} (hξ : ξ ∈ B.naturalCone) :
    ModularNaturalConeFaceBridge.localizationOp B w ξ ∈ B.naturalCone := by
  unfold localizationOp
  exact B.cylinderProjector_preserves_naturalCone w
    (B.modularMirrorProjector w ξ)
    (B.modularMirrorProjector_preserves_naturalCone w ξ hξ)

/--
Localized modular cone face for a word.

This is the theorem-safe form of `P_w`: a vector is in the localized face when
it lies in the supplied natural-cone shadow and is fixed by the localizer
`L_w = p_w Jp_wJ`.
-/
@[rep_depth operator]
noncomputable def modularConeFace (w : Word) : Set H₂ :=
  {ξ | ξ ∈ B.naturalCone ∧ ModularNaturalConeFaceBridge.localizationOp B w ξ = ξ}

/-- Membership in the localized modular cone face is exactly cone membership plus fixedness. -/
@[rep_depth operator]
theorem mem_modularConeFace_iff
    (w : Word) (ξ : H₂) :
    ξ ∈ ModularNaturalConeFaceBridge.modularConeFace B w ↔
      ξ ∈ B.naturalCone ∧ ModularNaturalConeFaceBridge.localizationOp B w ξ = ξ :=
  Iff.rfl

/-- The localized modular cone face is a subset of the supplied natural cone. -/
@[rep_depth operator]
theorem modularConeFace_subset_naturalCone
    (w : Word) {ξ : H₂}
    (hξ : ξ ∈ ModularNaturalConeFaceBridge.modularConeFace B w) :
    ξ ∈ B.naturalCone :=
  hξ.1

/-- Vectors in a localized modular cone face are fixed by the localizer. -/
@[rep_depth operator]
theorem localizationOp_fixes_of_mem_modularConeFace
    (w : Word) {ξ : H₂}
    (hξ : ξ ∈ ModularNaturalConeFaceBridge.modularConeFace B w) :
    ModularNaturalConeFaceBridge.localizationOp B w ξ = ξ :=
  hξ.2

end ModularNaturalConeFaceBridge

/--
Binary-word specialization of the modular natural-cone face bridge.

This is the theorem-safe version of the proposed `ModularFaceBridge`: it uses
the repo-owned `TypeIIIModularCantorSystem.BinaryWord` and the bounded doubled
carrier, while keeping all natural-cone preservation laws explicit.
-/
@[rep_depth operator]
abbrev BinaryWordModularFaceBridge :=
  ModularNaturalConeFaceBridge (H := H) TypeIIIModularCantorSystem.BinaryWord

namespace BinaryWordModularFaceBridge

variable (B : BinaryWordModularFaceBridge (H := H))

/-- Binary-word localized modular face operator, morally `L_w = p_w J p_w J`. -/
@[rep_depth operator]
noncomputable def localizationOp
    (w : TypeIIIModularCantorSystem.BinaryWord) : EndH :=
  ModularNaturalConeFaceBridge.localizationOp B w

/--
Binary-word face-localization readback: the localizer preserves the supplied
natural-cone shadow.
-/
@[rep_depth operator]
theorem cone_face_localization
    (w : TypeIIIModularCantorSystem.BinaryWord)
    {ξ : H₂} (hξ : ξ ∈ B.naturalCone) :
    BinaryWordModularFaceBridge.localizationOp B w ξ ∈ B.naturalCone :=
  ModularNaturalConeFaceBridge.localizationOp_mem_naturalCone B w hξ

/-- Binary-word localized modular cone face. -/
@[rep_depth operator]
noncomputable def modularConeFace
    (w : TypeIIIModularCantorSystem.BinaryWord) : Set H₂ :=
  ModularNaturalConeFaceBridge.modularConeFace B w

/-- Membership in a binary-word face is cone membership plus localizer fixedness. -/
@[rep_depth operator]
theorem mem_modularConeFace_iff
    (w : TypeIIIModularCantorSystem.BinaryWord) (ξ : H₂) :
    ξ ∈ BinaryWordModularFaceBridge.modularConeFace B w ↔
      ξ ∈ B.naturalCone ∧ BinaryWordModularFaceBridge.localizationOp B w ξ = ξ :=
  Iff.rfl

/-- Binary-word localized modular cone faces sit inside the supplied natural cone. -/
@[rep_depth operator]
theorem modularConeFace_subset_naturalCone
    (w : TypeIIIModularCantorSystem.BinaryWord)
    {ξ : H₂} (hξ : ξ ∈ BinaryWordModularFaceBridge.modularConeFace B w) :
    ξ ∈ B.naturalCone :=
  ModularNaturalConeFaceBridge.modularConeFace_subset_naturalCone B w hξ

/-- Binary-word face vectors are fixed by the binary-word localizer. -/
@[rep_depth operator]
theorem localizationOp_fixes_of_mem_modularConeFace
    (w : TypeIIIModularCantorSystem.BinaryWord)
    {ξ : H₂} (hξ : ξ ∈ BinaryWordModularFaceBridge.modularConeFace B w) :
    BinaryWordModularFaceBridge.localizationOp B w ξ = ξ :=
  ModularNaturalConeFaceBridge.localizationOp_fixes_of_mem_modularConeFace B w hξ

end BinaryWordModularFaceBridge

end ModularFaces

end InfoGeometry.Canonical.StandardFormNaturalConeBridge
