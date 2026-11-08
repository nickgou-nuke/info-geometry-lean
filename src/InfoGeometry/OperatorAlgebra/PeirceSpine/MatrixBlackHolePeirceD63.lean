/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceChiralGeometry
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformationPeirce
import InfoGeometry.Quantum.KrausAmplificationCP
import InfoGeometry.Meta.ArchetypePipeline

/-!
# D₆₃: positive matrix sheets and reversible Peirce shear

For an arbitrary star projection in a finite matrix algebra, choosing the
backward amplitude as the adjoint of the forward amplitude makes the two
Peirce sheets Gram operators. Their positivity, cyclic trace balance, and
trace-kernel criterion are matrix facts. The separate shear result is
not specialized here; the generic Peirce owner proves its two-sided
invertibility without identifying it as a unitary.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation
open InfoGeometry.MetaCompiler
open scoped ComplexOrder

/-! ## Star-preserving similarity requires the adjoint inverse -/

/-- If an invertible operator has its adjoint as its two-sided inverse, then
similarity by that operator preserves the involution. This is the algebraic
condition needed for conjugation to preserve self-adjoint operators. -/
theorem d63_similarity_preserves_star_of_unitary
    {B : Type*} [Ring B] [StarRing B] (S Sinv X : B)
    (hLeft : S * Sinv = 1) (hRight : Sinv * S = 1)
    (hAdjoint : star S = Sinv) :
    star (S * X * Sinv) = S * star X * Sinv ∧
      S * Sinv = 1 ∧ Sinv * S = 1 := by
  have hStar : star (S * X * Sinv) = S * star X * Sinv := by
    calc
      star (S * X * Sinv) = star Sinv * star X * star S := by
        rw [star_mul, star_mul]
        simp only [mul_assoc]
      _ = S * star X * Sinv := by
        rw [← hAdjoint, star_star, hAdjoint]
  exact ⟨hStar, hLeft, hRight⟩

/-- For an invertible similarity, preservation of the involution on every
operator is equivalent to centrality of the Gram element `S⋆ * S`. This is
the exact noncommutative condition; unitarity is the special case where that
central element is `1`. -/
theorem d63_similarity_star_iff_gram_central
    {B : Type*} [Ring B] [StarRing B] (S Sinv : B)
    (hLeft : S * Sinv = 1) (hRight : Sinv * S = 1) :
    (∀ X : B, star (S * X * Sinv) = S * star X * Sinv) ↔
      ∀ Y : B, (Y * star S) * S = (star S * S) * Y := by
  have hAdjLeft : star Sinv * star S = 1 := by
    have h := congrArg star hLeft
    simpa only [star_mul, star_one] using h
  have hAdjRight : star S * star Sinv = 1 := by
    have h := congrArg star hRight
    simpa only [star_mul, star_one] using h
  constructor
  · intro hPreserves Y
    have hConj : star Sinv * Y * star S = S * Y * Sinv := by
      simpa only [star_mul, star_star, mul_assoc] using hPreserves (star Y)
    calc
      Y * star S * S = (star S * star Sinv) * Y * star S * S := by
        rw [hAdjRight]
        noncomm_ring
      _ = star S * (star Sinv * Y * star S) * S := by noncomm_ring
      _ = star S * (S * Y * Sinv) * S := by rw [hConj]
      _ = star S * S * Y := by noncomm_ring [hRight]
  · intro hCentral X
    have hGram := hCentral (star X)
    have hConj : star Sinv * star X * star S = S * star X * Sinv := by
      calc
        star Sinv * star X * star S =
            star Sinv * star X * star S * S * Sinv := by
              noncomm_ring [hLeft]
        _ = star Sinv * star S * S * star X * Sinv := by
              noncomm_ring [hGram]
        _ = S * star X * Sinv := by noncomm_ring [hAdjLeft]
    calc
      star (S * X * Sinv) = star Sinv * star X * star S := by
        rw [star_mul, star_mul]
        simp only [mul_assoc]
      _ = S * star X * Sinv := hConj

/-! ## Matrix specialization -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two-sided unitary condition for a square complex matrix. -/
def d63MatrixUnitary (U : Matrix n n ℂ) : Prop :=
  star U * U = 1 ∧ U * star U = 1

/-- Unitary conjugation preserves positivity and the ordinary matrix trace.
The positivity statement is the matrix congruence law; trace invariance uses
cyclicity together with the left unitary identity. -/
theorem d63_matrix_unitary_conjugation_preserves_positive_and_trace
    (U X : Matrix n n ℂ) (hU : d63MatrixUnitary U)
    (hX : X.PosSemidef) :
    (U * X * star U).PosSemidef ∧
      Matrix.trace (U * X * star U) = Matrix.trace X := by
  constructor
  · exact Matrix.PosSemidef.mul_mul_conjTranspose_same hX U
  · calc
      Matrix.trace (U * X * star U) = Matrix.trace (star U * (U * X)) := by
        exact Matrix.trace_mul_comm (U * X) (star U)
      _ = Matrix.trace ((star U * U) * X) := by
        congr 1
        rw [← mul_assoc]
      _ = Matrix.trace X := by rw [hU.1, one_mul]

/-- With adjoint-related amplitudes, the two Peirce sheets are the two Gram
operators associated with the forward cone. -/
theorem d63_matrix_sheet_gram_forms {p A : Matrix n n ℂ}
    (hp : IsStarProjection p) :
    qgtPlus p A (star A) = conePlus p A * star (conePlus p A) ∧
    qgtMinus p A (star A) = star (conePlus p A) * conePlus p A := by
  have hStar : star (conePlus p A) = coneMinus p (star A) :=
    star_conePlus hp.isSelfAdjoint A
  constructor <;> simp [qgtPlus, qgtMinus, hStar]

/-- Both adjoint-related sheets are positive semidefinite, and the ordinary
matrix trace assigns them the same value by cyclicity. -/
theorem d63_matrix_sheet_positivity_and_trace_balance {p A : Matrix n n ℂ}
    (hp : IsStarProjection p) :
    (qgtPlus p A (star A)).PosSemidef ∧
    (qgtMinus p A (star A)).PosSemidef ∧
    Matrix.trace (qgtPlus p A (star A)) =
      Matrix.trace (qgtMinus p A (star A)) := by
  rcases d63_matrix_sheet_gram_forms hp with ⟨hPlus, hMinus⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hPlus]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  · rw [hMinus]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [hPlus, hMinus]
    exact Matrix.trace_mul_comm _ _

/-- The Peirce Page-state identities specialize to the genuine finite complex
matrix carrier. This identifies the density with the logistic Peirce state,
computes its impurity as the negative metric idempotency defect, and
characterizes purity by vanishing of that defect. It is an algebraic matrix
statement, without an entropy or time-evolution interpretation. -/
theorem d63_matrix_page_state_and_defect {p A : Matrix n n ℂ}
    (hp : IsStarProjection p) :
    pageDensityOp p A (star A) = peirceLogisticPlus p A (star A) ∧
    pageImpurity p A (star A) =
      -(genV p A (star A) * genV p A (star A) - genV p A (star A)) ∧
    (pageDensityOp p A (star A) * pageDensityOp p A (star A) =
        pageDensityOp p A (star A) ↔
      genV p A (star A) * genV p A (star A) - genV p A (star A) = 0) := by
  have hP : p * p = p := hp.isIdempotentElem
  have hDensity : pageDensityOp p A (star A) = peirceLogisticPlus p A (star A) := by
    rw [page_density_eq_cut_sub_curvature hP A (star A),
      peirce_logistic_state_eq_cut_sub_curvature hP A (star A)]
  exact ⟨hDensity,
    page_impurity_eq_negative_metric_defect hP A (star A),
    (page_purity_iff_metric_idempotency_defect hP A (star A)).1⟩

/-- Input for the finite-matrix Page-state defect archetype. -/
structure D63MatrixPageInput (n : Type*) [Fintype n] [DecidableEq n] where
  projection : Matrix n n ℂ
  amplitude : Matrix n n ℂ
  projectionStar : IsStarProjection projection

/-- Matrix Page-state density, impurity, and purity criterion, discharged from
the noncommutative Peirce owner theorem. -/
def d63MatrixPageDefectArchetype :
    TypedArchetype (D63MatrixPageInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixPageDefectArchetype
  phase := 63
  claim := fun input =>
    pageDensityOp input.projection input.amplitude (star input.amplitude) =
        peirceLogisticPlus input.projection input.amplitude (star input.amplitude) ∧
      pageImpurity input.projection input.amplitude (star input.amplitude) =
        -(genV input.projection input.amplitude (star input.amplitude) *
          genV input.projection input.amplitude (star input.amplitude) -
          genV input.projection input.amplitude (star input.amplitude)) ∧
      (pageDensityOp input.projection input.amplitude (star input.amplitude) *
          pageDensityOp input.projection input.amplitude (star input.amplitude) =
            pageDensityOp input.projection input.amplitude (star input.amplitude) ↔
        genV input.projection input.amplitude (star input.amplitude) *
            genV input.projection input.amplitude (star input.amplitude) -
          genV input.projection input.amplitude (star input.amplitude) = 0)
  evidence := fun input => d63_matrix_page_state_and_defect input.projectionStar

/-- Matrix input for the two-sided sheet Gram archetype. -/
structure D63MatrixSheetInput (n : Type*) [Fintype n] [DecidableEq n] where
  projection : Matrix n n ℂ
  amplitude : Matrix n n ℂ
  projectionStar : IsStarProjection projection

/-- Opposite Peirce sheets are positive Gram operators and have equal trace
for every finite matrix size and arbitrary star projection. -/
def d63MatrixSheetArchetype :
    TypedArchetype (D63MatrixSheetInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixSheetArchetype
  phase := 63
  claim := fun input =>
    (qgtPlus input.projection input.amplitude (star input.amplitude)).PosSemidef ∧
      (qgtMinus input.projection input.amplitude (star input.amplitude)).PosSemidef ∧
      Matrix.trace (qgtPlus input.projection input.amplitude (star input.amplitude)) =
        Matrix.trace (qgtMinus input.projection input.amplitude (star input.amplitude))
  evidence := fun input => d63_matrix_sheet_positivity_and_trace_balance
    input.projectionStar

/-- Trace faithfulness on the Gram sheet: vanishing trace is equivalent to
vanishing of the forward off-diagonal cone. -/
theorem d63_matrix_sheet_trace_zero_iff_cone_zero {p A : Matrix n n ℂ}
    (hp : IsStarProjection p) :
    Matrix.trace (qgtPlus p A (star A)) = 0 ↔ conePlus p A = 0 := by
  rw [(d63_matrix_sheet_gram_forms hp).1]
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff

/-- The adjoint-corrected Peirce mirror is a two-Kraus map. Unlike the raw
quadratic expression, each summand is a congruence and hence preserves
positive semidefiniteness. This is a finite-matrix positivity statement; it
does not assert a physical decoding or time-evolution interpretation. -/
def d63PositivePeirceMirror (p A C X : Matrix n n ℂ) : Matrix n n ℂ :=
  conePlus p A * X * star (conePlus p A) +
    coneMinus p C * X * star (coneMinus p C)

/-- Positivity of the corrected two-Kraus Peirce mirror. -/
theorem d63_positive_peirce_mirror_preserves_posSemidef
    (p A C X : Matrix n n ℂ) (hX : X.PosSemidef) :
    (d63PositivePeirceMirror p A C X).PosSemidef := by
  unfold d63PositivePeirceMirror
  exact Matrix.PosSemidef.add
    (Matrix.PosSemidef.mul_mul_conjTranspose_same hX (conePlus p A))
    (Matrix.PosSemidef.mul_mul_conjTranspose_same hX (coneMinus p C))

/-- Kraus operators for the corrected Peirce mirror. -/
def d63PeirceMirrorKraus (p A C : Matrix n n ℂ) : Fin 2 → Matrix n n ℂ :=
  fun i => if i = 0 then conePlus p A else coneMinus p C

/-- The corrected Peirce mirror is exactly the finite Kraus channel with the
two off-diagonal Peirce cones as its Kraus operators. -/
theorem d63_positive_peirce_mirror_eq_krausChannel
    (p A C X : Matrix n n ℂ) :
    d63PositivePeirceMirror p A C X =
      InfoGeometry.Modular.Choi.krausChannel (d63PeirceMirrorKraus p A C) X := by
  simp [d63PositivePeirceMirror, d63PeirceMirrorKraus,
    InfoGeometry.Modular.Choi.krausChannel,
    InfoGeometry.Quantum.Choi.krausMap, Fin.sum_univ_two]

/-- Complete positivity of the corrected Peirce mirror: every finite matrix
amplification preserves positive semidefiniteness. This uses the repository's
block-amplification theorem for finite Kraus channels. -/
theorem d63_positive_peirce_mirror_completely_positive
    {r : Type*} [Fintype r] [DecidableEq r]
    (p A C : Matrix n n ℂ) (X : Matrix (r × n) (r × n) ℂ)
    (hX : X.PosSemidef) :
    (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
      (InfoGeometry.Modular.Choi.krausChannel (d63PeirceMirrorKraus p A C)) X).PosSemidef := by
  exact InfoGeometry.Quantum.KrausAmplification.amplification_krausChannel_posSemidef
    (d63PeirceMirrorKraus p A C) X hX

/-- Input for a finite amplification of the corrected Peirce mirror. -/
structure D63MatrixMirrorCPInput
    (r n : Type*) [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] where
  projectionParameter : Matrix n n ℂ
  forwardParameter : Matrix n n ℂ
  backwardParameter : Matrix n n ℂ
  baseInput : Matrix n n ℂ
  amplifiedInput : Matrix (r × n) (r × n) ℂ
  inputPositive : amplifiedInput.PosSemidef

/-- The corrected Peirce mirror has its stated Kraus form, and every finite
amplification of that map preserves positive semidefiniteness. -/
def d63MatrixMirrorCPArchetype {r : Type*} [Fintype r] [DecidableEq r] :
    TypedArchetype (D63MatrixMirrorCPInput r n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixMirrorCPArchetype
  phase := 63
  claim := fun input =>
    d63PositivePeirceMirror input.projectionParameter input.forwardParameter
        input.backwardParameter input.baseInput =
      InfoGeometry.Modular.Choi.krausChannel
        (d63PeirceMirrorKraus input.projectionParameter input.forwardParameter
          input.backwardParameter) input.baseInput ∧
    (InfoGeometry.Quantum.KrausAmplification.amplification
      (r := r) (InfoGeometry.Modular.Choi.krausChannel
        (d63PeirceMirrorKraus input.projectionParameter input.forwardParameter
          input.backwardParameter)) input.amplifiedInput).PosSemidef
  evidence := fun input =>
    ⟨d63_positive_peirce_mirror_eq_krausChannel input.projectionParameter
      input.forwardParameter input.backwardParameter input.baseInput,
     d63_positive_peirce_mirror_completely_positive input.projectionParameter
       input.forwardParameter input.backwardParameter input.amplifiedInput
       input.inputPositive⟩

/-- Input data for the kernel statement of the finite Peirce mirror. -/
structure D63MatrixKernelInput where
  projection : Matrix n n ℂ
  forwardParameter : Matrix n n ℂ
  backwardParameter : Matrix n n ℂ
  input : Matrix n n ℂ
  projectionIdempotent : projection * projection = projection
  projectionSelfAdjoint : star projection = projection
  inputInUpperCorner : projection * input * (1 - projection) = input

/-- Input data for trace preservation of the finite Peirce mirror, including
the independent Kraus completeness equation required by the theorem. -/
structure D63MatrixTracePreservationInput where
  projection : Matrix n n ℂ
  forwardParameter : Matrix n n ℂ
  backwardParameter : Matrix n n ℂ
  input : Matrix n n ℂ
  krausComplete : (∑ i : Fin 2,
    star (d63PeirceMirrorKraus projection forwardParameter backwardParameter i) *
      d63PeirceMirrorKraus projection forwardParameter backwardParameter i) = 1

/-- The adjoint-corrected two-Kraus Peirce mirror annihilates every input
supported in the upper off-diagonal corner. This records a genuine kernel of
the channel, rather than inferring recoverability from its Kraus form. -/
theorem d63_positive_peirce_mirror_annihilates_upper_corner
    (p A C X : Matrix n n ℂ) (hp : p * p = p) (hps : star p = p)
    (hX : p * X * (1 - p) = X) :
    d63PositivePeirceMirror p A C X = 0 := by
  have hLowerP : (1 - p) * p = 0 := by noncomm_ring [hp]
  have hLowerX : (1 - p) * X = 0 := by
    calc
      (1 - p) * X = (1 - p) * (p * X * (1 - p)) := by rw [hX]
      _ = ((1 - p) * p) * X * (1 - p) := by noncomm_ring
      _ = 0 := by rw [hLowerP]; simp
  have hXP : X * p = 0 := by
    calc
      X * p = (p * X * (1 - p)) * p := by rw [hX]
      _ = p * X * ((1 - p) * p) := by noncomm_ring
      _ = 0 := by rw [hLowerP]; simp
  have hPlus : conePlus p A * X * star (conePlus p A) = 0 := by
    unfold conePlus
    calc
      (p * A * (1 - p)) * X * star (p * A * (1 - p)) =
          (p * A) * ((1 - p) * X) * star (p * A * (1 - p)) := by
            noncomm_ring
      _ = 0 := by rw [hLowerX]; simp
  have hStarLower : star (coneMinus p C) = p * star C * (1 - p) := by
    unfold coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hps]
    noncomm_ring
  have hMinus : coneMinus p C * X * star (coneMinus p C) = 0 := by
    rw [hStarLower]
    unfold coneMinus
    calc
      ((1 - p) * C * p) * X * (p * star C * (1 - p)) =
          ((1 - p) * C) * (p * X * p) * (star C * (1 - p)) := by
            noncomm_ring
      _ = 0 := by noncomm_ring [hXP]
  unfold d63PositivePeirceMirror
  rw [hPlus, hMinus, add_zero]

/-- Whenever a nonzero upper off-diagonal input exists, the corrected Peirce
mirror is not injective: it maps that input and zero to the same output. -/
theorem d63_positive_peirce_mirror_not_injective_of_upper_corner
    (p A C : Matrix n n ℂ) (hp : p * p = p) (hps : star p = p)
    (hWitness : ∃ X : Matrix n n ℂ, p * X * (1 - p) = X ∧ X ≠ 0) :
    ¬ Function.Injective (d63PositivePeirceMirror p A C) := by
  rintro hinj
  obtain ⟨X, hX, hXne⟩ := hWitness
  have hKernel := d63_positive_peirce_mirror_annihilates_upper_corner
    p A C X hp hps hX
  have hZero : d63PositivePeirceMirror p A C 0 = 0 := by
    simp [d63PositivePeirceMirror]
  have hEq : X = 0 := hinj (by rw [hKernel, hZero])
  exact hXne hEq

/-- Trace preservation needs the separate Kraus completeness condition; it
does not follow from complete positivity alone. -/
theorem d63_positive_peirce_mirror_trace_preserving_of_completeness
    (p A C X : Matrix n n ℂ)
    (hComplete : (∑ i : Fin 2,
      star (d63PeirceMirrorKraus p A C i) * d63PeirceMirrorKraus p A C i) = 1) :
    Matrix.trace (d63PositivePeirceMirror p A C X) = Matrix.trace X := by
  rw [d63_positive_peirce_mirror_eq_krausChannel]
  exact InfoGeometry.Quantum.Choi.trace_krausMap_of_completeness
    (d63PeirceMirrorKraus p A C) hComplete X

/-- An upper-corner input lies in the kernel of the adjoint-corrected Peirce
mirror. This archetype records the proved kernel statement, rather than
assuming it as a causal edge. -/
def d63MatrixMirrorKernelArchetype :
    TypedArchetype (D63MatrixKernelInput (n := n)) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixMirrorKernelArchetype
  phase := 63
  claim := fun input =>
    d63PositivePeirceMirror input.projection input.forwardParameter
      input.backwardParameter input.input = 0
  evidence := fun input => d63_positive_peirce_mirror_annihilates_upper_corner
    input.projection input.forwardParameter input.backwardParameter input.input
    input.projectionIdempotent input.projectionSelfAdjoint input.inputInUpperCorner

/-- Trace preservation is proved under the actual Kraus completeness
condition; complete positivity alone is not substituted for that condition. -/
def d63MatrixMirrorTracePreservationArchetype :
    TypedArchetype (D63MatrixTracePreservationInput (n := n)) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixMirrorTracePreservationArchetype
  phase := 63
  claim := fun input =>
    Matrix.trace (d63PositivePeirceMirror input.projection input.forwardParameter
      input.backwardParameter input.input) = Matrix.trace input.input
  evidence := fun input => d63_positive_peirce_mirror_trace_preserving_of_completeness
    input.projection input.forwardParameter input.backwardParameter input.input
    input.krausComplete

/-! ## Causal order for the finite-matrix mirror claims

The Kraus formula supports two distinct conclusions: amplification positivity
and, when the completeness equation is supplied, trace preservation. The
dependency order keeps the latter condition visible instead of deriving it
from complete positivity.
-/

inductive D63MirrorStage where
  | operatorData
  | starProjection
  | amplitude
  | krausRepresentation
  | completePositivity
  | traceCompleteness
  | tracePreservation
  | upperCornerWitness
  | kernelAnnihilation
  | nonInjectivity
  deriving DecidableEq, Repr

/- The edge propositions are the concrete operator statements proved by the
owner theorems below. Input labels without a proved dependency do not create
edges. -/
def D63MirrorStage.edge : D63MirrorStage → D63MirrorStage → Prop
  | .operatorData, .krausRepresentation =>
      ∀ p A C X : Matrix (Fin 2) (Fin 2) ℂ,
        d63PositivePeirceMirror p A C X =
          InfoGeometry.Modular.Choi.krausChannel (d63PeirceMirrorKraus p A C) X
  | .upperCornerWitness, .kernelAnnihilation =>
      ∀ p A C X : Matrix (Fin 2) (Fin 2) ℂ, p * p = p → star p = p →
        p * X * (1 - p) = X → d63PositivePeirceMirror p A C X = 0
  | .kernelAnnihilation, .nonInjectivity =>
      ∀ p A C : Matrix (Fin 2) (Fin 2) ℂ, p * p = p → star p = p →
        (∃ X : Matrix (Fin 2) (Fin 2) ℂ, p * X * (1 - p) = X ∧ X ≠ 0) →
        ¬ Function.Injective (d63PositivePeirceMirror p A C)
  | .krausRepresentation, .completePositivity =>
      ∀ (p A C : Matrix (Fin 2) (Fin 2) ℂ)
        (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), X.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := Fin 2)
          (InfoGeometry.Modular.Choi.krausChannel (d63PeirceMirrorKraus p A C)) X).PosSemidef
  | .traceCompleteness, .tracePreservation =>
      ∀ p A C X : Matrix (Fin 2) (Fin 2) ℂ,
        (∑ i : Fin 2, star (d63PeirceMirrorKraus p A C i) *
          d63PeirceMirrorKraus p A C i) = 1 →
        Matrix.trace (d63PositivePeirceMirror p A C X) = Matrix.trace X
  | _, _ => False

def D63MirrorStage.rank : D63MirrorStage → Nat
  | .operatorData => 0
  | .starProjection => 1
  | .amplitude => 1
  | .krausRepresentation => 1
  | .upperCornerWitness => 2
  | .traceCompleteness => 2
  | .kernelAnnihilation => 3
  | .tracePreservation => 3
  | .nonInjectivity => 4
  | .completePositivity => 5

inductive D63MirrorStage.Reachable : D63MirrorStage → D63MirrorStage → Prop where
  | refl (a : D63MirrorStage) : Reachable a a
  | edge {a b : D63MirrorStage} : a.edge b → Reachable a b
  | trans {a b c : D63MirrorStage} : Reachable a b → Reachable b c → Reachable a c

/-- Causal order generated by the direct finite-matrix dependency edges. -/
def D63MirrorStage.dependencyLE : D63MirrorStage → D63MirrorStage → Prop := Reachable

theorem D63MirrorStage.edge_rank_strict {a b : D63MirrorStage} (h : a.edge b) :
    a.rank < b.rank := by
  cases a <;> cases b <;> simp_all [D63MirrorStage.edge, D63MirrorStage.rank]

theorem D63MirrorStage.reachable_rank_strict_of_ne {a b : D63MirrorStage}
    (h : a.Reachable b) (hne : a ≠ b) : a.rank < b.rank := by
  induction h with
  | @refl x => exact (hne rfl).elim
  | edge h => exact edge_rank_strict h
  | @trans x y z hxy hyz ihxy ihyz =>
      by_cases hxyEq : x = y
      · subst y
        exact ihyz hne
      · by_cases hyzEq : y = z
        · subst z
          exact ihxy hne
        · exact lt_trans (ihxy hxyEq) (ihyz hyzEq)

theorem D63MirrorStage.dependencyLE_refl (a : D63MirrorStage) :
    a.dependencyLE a := Reachable.refl a

theorem D63MirrorStage.dependencyLE_trans {a b c : D63MirrorStage}
    (hab : a.dependencyLE b) (hbc : b.dependencyLE c) :
    a.dependencyLE c := Reachable.trans hab hbc

theorem D63MirrorStage.dependencyLE_antisymm {a b : D63MirrorStage}
    (hab : a.dependencyLE b) (hba : b.dependencyLE a) : a = b := by
  by_cases hEq : a = b
  · exact hEq
  · exact (lt_asymm (reachable_rank_strict_of_ne hab hEq)
      (reachable_rank_strict_of_ne hba (Ne.symm hEq))).elim

instance : PartialOrder D63MirrorStage where
  le := D63MirrorStage.dependencyLE
  le_refl := D63MirrorStage.dependencyLE_refl
  le_trans := fun _ _ _ hab hbc => D63MirrorStage.dependencyLE_trans hab hbc
  le_antisymm := fun _ _ hab hba => D63MirrorStage.dependencyLE_antisymm hab hba

theorem D63MirrorStage.edge_dependencyLE {a b : D63MirrorStage} (h : a.edge b) :
    a.dependencyLE b := Reachable.edge h

/-- Complete positivity and trace preservation are separate branches after
the Kraus representation; only trace completeness implies trace preservation. -/
theorem d63_mirror_causal_dependencies :
    D63MirrorStage.krausRepresentation ≤ D63MirrorStage.completePositivity ∧
    D63MirrorStage.traceCompleteness ≤ D63MirrorStage.tracePreservation ∧
    ¬ D63MirrorStage.completePositivity ≤ D63MirrorStage.tracePreservation := by
  refine ⟨?_, ?_, ?_⟩
  · apply D63MirrorStage.edge_dependencyLE
    intro p A C X hX
    exact d63_positive_peirce_mirror_completely_positive p A C X hX
  · apply D63MirrorStage.edge_dependencyLE
    intro p A C X hComplete
    exact d63_positive_peirce_mirror_trace_preserving_of_completeness p A C X hComplete
  intro h
  have hlt := D63MirrorStage.reachable_rank_strict_of_ne h (by decide)
  norm_num [D63MirrorStage.rank] at hlt

/-- The matrix kernel branch is distinct from the positivity/trace branch:
the proved off-diagonal witness feeds the kernel theorem, which feeds
non-injectivity. -/
theorem d63_mirror_kernel_causal_dependencies :
    D63MirrorStage.upperCornerWitness ≤ D63MirrorStage.kernelAnnihilation ∧
    D63MirrorStage.kernelAnnihilation ≤ D63MirrorStage.nonInjectivity ∧
    ¬ D63MirrorStage.completePositivity ≤ D63MirrorStage.nonInjectivity := by
  refine ⟨?_, ?_, ?_⟩
  · apply D63MirrorStage.edge_dependencyLE
    intro p A C X hp hps hX
    exact d63_positive_peirce_mirror_annihilates_upper_corner p A C X hp hps hX
  · apply D63MirrorStage.edge_dependencyLE
    intro p A C hp hps hWitness
    exact d63_positive_peirce_mirror_not_injective_of_upper_corner
      p A C hp hps hWitness
  intro h
  have hlt := D63MirrorStage.reachable_rank_strict_of_ne h (by decide)
  norm_num [D63MirrorStage.rank] at hlt

/-- For adjoint-related amplitudes, the real matrix trace of the metric is
twice the nonnegative trace of one Gram sheet. It vanishes exactly when the
boundary cone vanishes. -/
theorem d63_matrix_metric_trace_is_twice_positive_boundary_gram
    {p A : Matrix n n ℂ} (hp : IsStarProjection p) :
    (Matrix.trace (genV p A (star A))).re =
      2 * (Matrix.trace (qgtPlus p A (star A))).re ∧
    0 ≤ (Matrix.trace (genV p A (star A))).re ∧
    ((Matrix.trace (genV p A (star A))).re = 0 ↔ conePlus p A = 0) := by
  have hTraceSheets :=
    (d63_matrix_sheet_positivity_and_trace_balance (p := p) (A := A) hp).2.2
  have hPlus : qgtPlus p A (star A) = conePlus p A * star (conePlus p A) :=
    (d63_matrix_sheet_gram_forms hp).1
  have hMetricTrace : Matrix.trace (genV p A (star A)) =
      Matrix.trace (qgtPlus p A (star A)) +
        Matrix.trace (qgtMinus p A (star A)) := by
    simp [genV, anticomm, qgtPlus, qgtMinus]
  have hRealTrace : (Matrix.trace (genV p A (star A))).re =
      2 * (Matrix.trace (qgtPlus p A (star A))).re := by
    rw [hMetricTrace, Complex.add_re, hTraceSheets]
    ring
  have hPos : 0 ≤ (Matrix.trace (qgtPlus p A (star A))).re := by
    rw [hPlus]
    exact (Complex.nonneg_iff.mp
      (Matrix.posSemidef_self_mul_conjTranspose (conePlus p A)).trace_nonneg).1
  refine ⟨hRealTrace, ?_, ?_⟩
  · rw [hRealTrace]
    positivity
  · rw [hRealTrace]
    constructor
    · intro hzero
      have hzero' : (Matrix.trace (qgtPlus p A (star A))).re = 0 := by
        nlinarith
      have hTraceZero : Matrix.trace (qgtPlus p A (star A)) = 0 := by
        apply Complex.ext
        · exact hzero'
        · have hImZero : (Matrix.trace (qgtPlus p A (star A))).im = 0 := by
            have hSelf : star (qgtPlus p A (star A)) = qgtPlus p A (star A) := by
              rw [hPlus]
              simp
            have hTraceSelf : Matrix.trace (qgtPlus p A (star A)) =
                star (Matrix.trace (qgtPlus p A (star A))) := by
              have hConj := Matrix.trace_conjTranspose (qgtPlus p A (star A))
              change Matrix.trace (star (qgtPlus p A (star A))) = _ at hConj
              rw [hSelf] at hConj
              exact hConj
            have hIm := congrArg Complex.im hTraceSelf
            have hImNeg : (Matrix.trace (qgtPlus p A (star A))).im =
                -(Matrix.trace (qgtPlus p A (star A))).im := by
              simpa using hIm
            linarith
          exact hImZero
      exact (d63_matrix_sheet_trace_zero_iff_cone_zero hp).mp hTraceZero
    · intro hzero
      rw [hPlus, hzero]
      simp

/-! ## Invertibility does not imply unitarity -/

abbrev D63Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- A non-diagonal orthogonal projection on `ℂ²`. -/
noncomputable def d63TiltedProjection : D63Mat2 := !![(1 / 2 : ℂ), (1 / 2 : ℂ); (1 / 2 : ℂ), (1 / 2 : ℂ)]

/-- A self-adjoint, non-diagonal amplitude whose forward Peirce corner is
nonzero and not skew-adjoint. -/
def d63TiltedAmplitude : D63Mat2 := !![(1 : ℂ), 1; 1, -1]

/-- Concrete noncommutativity witness in the finite matrix carrier. -/
theorem d63_tilted_cut_amplitude_noncommute :
    d63TiltedProjection * d63TiltedAmplitude ≠
      d63TiltedAmplitude * d63TiltedProjection := by
  intro h
  have hEntry := congrArg (fun M : D63Mat2 => M 0 1) h
  norm_num [d63TiltedProjection, d63TiltedAmplitude, Matrix.mul_apply,
    Fin.sum_univ_two] at hEntry

theorem d63_tilted_amplitude_is_selfAdjoint :
    star d63TiltedAmplitude = d63TiltedAmplitude := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [d63TiltedAmplitude, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]

theorem d63_tilted_projection_is_star_projection :
    IsStarProjection d63TiltedProjection := by
  apply (isStarProjection_iff').2
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d63TiltedProjection, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d63TiltedProjection, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]

/-- The tilted star projection has a concrete nonzero upper Peirce corner.
This is the witness archetype used by the mirror-kernel result below. -/
theorem d63_tilted_upper_corner_witness :
    ∃ X : D63Mat2,
      d63TiltedProjection * X * (1 - d63TiltedProjection) = X ∧ X ≠ 0 := by
  let X := conePlus d63TiltedProjection d63TiltedAmplitude
  have hP : d63TiltedProjection * d63TiltedProjection =
      d63TiltedProjection :=
    d63_tilted_projection_is_star_projection.isIdempotentElem.eq
  have hCorner : d63TiltedProjection * X * (1 - d63TiltedProjection) = X := by
    dsimp [X, conePlus]
    peirce_nf hP
  have hValue : X =
      !![(1 / 2 : ℂ), -(1 / 2 : ℂ); (1 / 2 : ℂ), -(1 / 2 : ℂ)] := by
    dsimp [X]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [conePlus, d63TiltedProjection, d63TiltedAmplitude,
        Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨X, hCorner, ?_⟩
  rw [hValue]
  intro hzero
  have hEntry := congrArg (fun M : D63Mat2 => M 0 0) hzero
  norm_num at hEntry

/-- In the explicit non-diagonal matrix model, the adjoint-corrected Peirce
mirror is non-injective because it annihilates the nonzero upper-corner
witness. -/
theorem d63_tilted_positive_mirror_not_injective :
    ¬ Function.Injective
      (d63PositivePeirceMirror d63TiltedProjection d63TiltedAmplitude 0) := by
  intro hinj
  obtain ⟨X, hcorner, hne⟩ := d63_tilted_upper_corner_witness
  have hkernel := d63_positive_peirce_mirror_annihilates_upper_corner
    d63TiltedProjection d63TiltedAmplitude 0 X
    d63_tilted_projection_is_star_projection.isIdempotentElem.eq
    d63_tilted_projection_is_star_projection.isSelfAdjoint hcorner
  have hzero : d63PositivePeirceMirror d63TiltedProjection d63TiltedAmplitude 0 0 = 0 := by
    simp [d63PositivePeirceMirror]
  have hXzero : X = 0 := hinj (by rw [hkernel, hzero])
  exact hne hXzero

/-- The horizon shear remains two-sided invertible for this matrix example. -/
theorem d63_matrix_shear_has_two_sided_inverse :
    horizonShear d63TiltedProjection d63TiltedAmplitude 0 *
        horizonShearInv d63TiltedProjection d63TiltedAmplitude 0 = 1 ∧
    horizonShearInv d63TiltedProjection d63TiltedAmplitude 0 *
        horizonShear d63TiltedProjection d63TiltedAmplitude 0 = 1 := by
  exact peirce_shear_two_sided_inverse
    d63_tilted_projection_is_star_projection.isIdempotentElem.eq
    d63TiltedAmplitude 0

/-- Exact operator matrix for the shear generated by the tilted cut and
self-adjoint amplitude. -/
theorem d63_matrix_tilted_shear_value :
    horizonShear d63TiltedProjection d63TiltedAmplitude 0 =
      !![(3 / 2 : ℂ), -(1 / 2 : ℂ); (1 / 2 : ℂ), (1 / 2 : ℂ)] := by
  have hCone : conePlus d63TiltedProjection d63TiltedAmplitude =
      !![(1 / 2 : ℂ), -(1 / 2 : ℂ); (1 / 2 : ℂ), -(1 / 2 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [conePlus, d63TiltedProjection, d63TiltedAmplitude,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [horizonShear, hCone]
  simp [coneMinus]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.add_apply]

/-- Exact adjoint of the tilted shear matrix. -/
theorem d63_matrix_tilted_shear_adjoint_value :
    star (horizonShear d63TiltedProjection d63TiltedAmplitude 0) =
      !![(3 / 2 : ℂ), (1 / 2 : ℂ); -(1 / 2 : ℂ), (1 / 2 : ℂ)] := by
  rw [d63_matrix_tilted_shear_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- The positive operator `S⋆ S` is computed explicitly; it is not the identity. -/
theorem d63_matrix_tilted_shear_adjoint_product_value :
    star (horizonShear d63TiltedProjection d63TiltedAmplitude 0) *
      horizonShear d63TiltedProjection d63TiltedAmplitude 0 =
        !![(5 / 2 : ℂ), -(1 / 2 : ℂ); -(1 / 2 : ℂ), (1 / 2 : ℂ)] := by
  rw [d63_matrix_tilted_shear_adjoint_value, d63_matrix_tilted_shear_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- This invertible Peirce shear is not unitary: its adjoint times itself is
not the identity. Thus the algebraic inverse theorem does not establish
unitarity of the evaporation map. -/
theorem d63_matrix_shear_not_unitary :
    star (horizonShear d63TiltedProjection d63TiltedAmplitude 0) *
      horizonShear d63TiltedProjection d63TiltedAmplitude 0 ≠ 1 := by
  rw [d63_matrix_tilted_shear_adjoint_product_value]
  intro h
  have h00 := congrArg (fun M : D63Mat2 => M 0 0) h
  norm_num at h00

/-- The Gram operator of the explicit shear is not central: its product with
the first coordinate projection depends on the order of multiplication. -/
theorem d63_matrix_shear_gram_not_central :
    ¬ ∀ Y : D63Mat2,
      (Y * star (horizonShear d63TiltedProjection d63TiltedAmplitude 0)) *
          horizonShear d63TiltedProjection d63TiltedAmplitude 0 =
        (star (horizonShear d63TiltedProjection d63TiltedAmplitude 0) *
          horizonShear d63TiltedProjection d63TiltedAmplitude 0) * Y := by
  intro hCentral
  have h := hCentral (!![(1 : ℂ), 0; 0, 0])
  rw [d63_matrix_tilted_shear_adjoint_value,
    d63_matrix_tilted_shear_value] at h
  have h01 := congrArg (fun M : D63Mat2 => M 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- The algebraic Peirce mirror map in this non-diagonal example sends the
self-adjoint amplitude to the forward cone, which is not self-adjoint. Thus
the mirror identities alone do not make this map a star-preserving channel. -/
theorem d63_matrix_mirror_not_star_preserving :
    star d63TiltedAmplitude = d63TiltedAmplitude ∧
    star (peirceMirrorMap d63TiltedProjection d63TiltedAmplitude 0
      d63TiltedAmplitude) ≠
      peirceMirrorMap d63TiltedProjection d63TiltedAmplitude 0
        d63TiltedAmplitude := by
  refine ⟨d63_tilted_amplitude_is_selfAdjoint, ?_⟩
  have hCone : conePlus d63TiltedProjection d63TiltedAmplitude =
      !![(1 / 2 : ℂ), -(1 / 2 : ℂ); (1 / 2 : ℂ), -(1 / 2 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [conePlus, d63TiltedProjection, d63TiltedAmplitude,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hMirror : peirceMirrorMap d63TiltedProjection d63TiltedAmplitude 0
      d63TiltedAmplitude =
      !![(1 / 2 : ℂ), -(1 / 2 : ℂ); (1 / 2 : ℂ), -(1 / 2 : ℂ)] := by
    unfold peirceMirrorMap
    rw [hCone]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coneMinus, d63TiltedProjection, d63TiltedAmplitude,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [hMirror]
  intro h
  have h01 := congrArg (fun M : D63Mat2 => M 0 1) h
  norm_num [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at h01

/-- A non-diagonal matrix factor for a positive Gram-operator witness. -/
def d63PositiveProbeFactor : D63Mat2 := !![(1 : ℂ), 1; 0, 0]

/-- The associated non-diagonal Gram operator. -/
def d63PositiveProbeState : D63Mat2 :=
  star d63PositiveProbeFactor * d63PositiveProbeFactor

/-- A genuinely non-diagonal Gram operator, used as a positive input to test
the shear similarity. -/
theorem d63_positive_probe_state_is_posSemidef :
    d63PositiveProbeState.PosSemidef := by
  unfold d63PositiveProbeState
  exact Matrix.posSemidef_conjTranspose_mul_self d63PositiveProbeFactor

/-- Similarity by the invertible shear sends a non-diagonal positive operator
to an operator that is not positive semidefinite. -/
theorem d63_matrix_shear_similarity_not_positive :
    d63PositiveProbeState.PosSemidef ∧
    ¬ (horizonShear d63TiltedProjection d63TiltedAmplitude 0 *
      d63PositiveProbeState *
      horizonShearInv d63TiltedProjection d63TiltedAmplitude 0).PosSemidef := by
  refine ⟨d63_positive_probe_state_is_posSemidef, ?_⟩
  rw [d63_matrix_tilted_shear_value]
  have hProbe : d63PositiveProbeState = !![(1 : ℂ), 1; 1, 1] := by
    unfold d63PositiveProbeState d63PositiveProbeFactor
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hShearInv : horizonShearInv d63TiltedProjection d63TiltedAmplitude 0 =
      !![(1 / 2 : ℂ), (1 / 2 : ℂ); -(1 / 2 : ℂ), (3 / 2 : ℂ)] := by
    have hInv := (d63_matrix_shear_has_two_sided_inverse).2
    have hCandidate :
        horizonShear d63TiltedProjection d63TiltedAmplitude 0 *
          (!![(1 / 2 : ℂ), (1 / 2 : ℂ); -(1 / 2 : ℂ), (3 / 2 : ℂ)] : D63Mat2) = 1 := by
      rw [d63_matrix_tilted_shear_value]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    calc
      horizonShearInv d63TiltedProjection d63TiltedAmplitude 0 =
          horizonShearInv d63TiltedProjection d63TiltedAmplitude 0 * 1 := by simp
      _ = horizonShearInv d63TiltedProjection d63TiltedAmplitude 0 *
          (horizonShear d63TiltedProjection d63TiltedAmplitude 0 *
            !![(1 / 2 : ℂ), (1 / 2 : ℂ); -(1 / 2 : ℂ), (3 / 2 : ℂ)]) := by
              rw [hCandidate]
      _ = (horizonShearInv d63TiltedProjection d63TiltedAmplitude 0 *
          horizonShear d63TiltedProjection d63TiltedAmplitude 0) *
            (!![(1 / 2 : ℂ), (1 / 2 : ℂ); -(1 / 2 : ℂ), (3 / 2 : ℂ)] : D63Mat2) := by
              noncomm_ring
      _ = !![(1 / 2 : ℂ), (1 / 2 : ℂ); -(1 / 2 : ℂ), (3 / 2 : ℂ)] := by
              rw [hInv]
              simp
  rw [hProbe, hShearInv]
  intro h
  have h01 := congrArg (fun M : D63Mat2 => M 0 1) h.isHermitian.eq
  norm_num [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Fin.sum_univ_two] at h01

/-! ## Proof-carrying boundaries for decoding and unitarity claims -/

/-- A concrete non-diagonal two-by-two matrix input certifies failure of
injectivity for the corrected Peirce mirror. This archetype prevents complete
positivity from being mistaken for lossless recovery. -/
def d63MatrixMirrorNoninjectiveArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixMirrorNoninjectiveArchetype
  phase := 63
  claim := fun _ =>
    ¬ Function.Injective
      (d63PositivePeirceMirror d63TiltedProjection d63TiltedAmplitude 0)
  evidence := fun _ => d63_tilted_positive_mirror_not_injective

/-- The same concrete shear is two-sided invertible and fails the unitary
equation `S⋆ S = 1`; this separates algebraic reversibility from unitarity. -/
def d63MatrixShearInvertibleNonunitaryArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixShearInvertibleNonunitaryArchetype
  phase := 63
  claim := fun _ =>
    horizonShear d63TiltedProjection d63TiltedAmplitude 0 *
        horizonShearInv d63TiltedProjection d63TiltedAmplitude 0 = 1 ∧
      horizonShearInv d63TiltedProjection d63TiltedAmplitude 0 *
        horizonShear d63TiltedProjection d63TiltedAmplitude 0 = 1 ∧
      star (horizonShear d63TiltedProjection d63TiltedAmplitude 0) *
        horizonShear d63TiltedProjection d63TiltedAmplitude 0 ≠ 1
  evidence := fun _ =>
    ⟨d63_matrix_shear_has_two_sided_inverse.1,
      ⟨d63_matrix_shear_has_two_sided_inverse.2,
        d63_matrix_shear_not_unitary⟩⟩

#register_archetype d63MatrixSheetArchetype
#audit_archetype d63MatrixSheetArchetype
#register_archetype d63MatrixPageDefectArchetype
#audit_archetype d63MatrixPageDefectArchetype
#register_archetype d63MatrixMirrorCPArchetype
#audit_archetype d63MatrixMirrorCPArchetype
#register_archetype d63MatrixMirrorKernelArchetype
#audit_archetype d63MatrixMirrorKernelArchetype
#register_archetype d63MatrixMirrorTracePreservationArchetype
#audit_archetype d63MatrixMirrorTracePreservationArchetype
#register_archetype d63MatrixMirrorNoninjectiveArchetype
#audit_archetype d63MatrixMirrorNoninjectiveArchetype
#register_archetype d63MatrixShearInvertibleNonunitaryArchetype
#audit_archetype d63MatrixShearInvertibleNonunitaryArchetype

end InfoGeometry.OperatorAlgebra.PeirceSpine
