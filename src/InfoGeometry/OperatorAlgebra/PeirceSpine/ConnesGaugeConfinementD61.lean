/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ArchitecturalBlueprintD59
import InfoGeometry.Meta.ArchetypePipeline

/-!
# D₆₁: Peirce differential forms and curvature confinement

This module extends the existing Peirce–Dirac algebraic results. It formalizes
commutator Leibniz, parity of one-forms from even coordinates, finite sums of
inner one-forms, diagonal closure of the algebraic curvature `dA + A²`, and the
star-twisted reflection of the two transition corners. It makes no analytic
index, particle-physics, or gauge-group classification claim.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.MetaCompiler

/-! ## Operator identities -/

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- The commutator with an even Peirce element is an odd transition. -/
theorem d61_one_form_odd (A C a : B) (hEven : comm P a = 0) :
    anticomm (invS P) (comm (genPhi P A C) a) = 0 :=
  peirce_yukawa_commutator_is_odd hP A C a hEven

/-- One-forms obtained by differentiating an even Peirce component have zero
even projection and are fixed by the odd projection. -/
theorem d61_one_form_projection (A C X : B) :
    evenGrade P (comm (genPhi P A C) (evenGrade P X)) = 0 ∧
    oddGrade P (comm (genPhi P A C) (evenGrade P X)) =
      comm (genPhi P A C) (evenGrade P X) := by
  constructor
  · unfold evenGrade comm genPhi conePlus coneMinus
    peirce_nf hP
  · unfold oddGrade comm genPhi conePlus coneMinus
    peirce_nf hP

omit hP in
/-- The inner commutator obeys Leibniz in every associative ring. -/
theorem d61_one_form_leibniz (A C a b : B) :
    comm (genPhi P A C) (a * b) =
      comm (genPhi P A C) a * b + a * comm (genPhi P A C) b := by
  unfold comm
  noncomm_ring

/-- Inputs for the algebraic Connes one-form Leibniz archetype. -/
structure D61LeibnizInput (B : Type*) [Ring B] where
  cut : B
  forwardAmplitude : B
  backwardAmplitude : B
  leftCoordinate : B
  rightCoordinate : B

/-- The inner Yukawa commutator's Leibniz rule, registered as a proved
operator-algebra archetype with its actual input data. -/
def d61ConnesLeibnizArchetype {B : Type*} [Ring B] :
    TypedArchetype (D61LeibnizInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d61ConnesLeibnizArchetype
  phase := 61
  claim := fun input =>
    comm (genPhi input.cut input.forwardAmplitude input.backwardAmplitude)
        (input.leftCoordinate * input.rightCoordinate) =
      comm (genPhi input.cut input.forwardAmplitude input.backwardAmplitude)
          input.leftCoordinate * input.rightCoordinate +
        input.leftCoordinate *
          comm (genPhi input.cut input.forwardAmplitude input.backwardAmplitude)
            input.rightCoordinate
  evidence := fun input => d61_one_form_leibniz
    input.forwardAmplitude input.backwardAmplitude
    input.leftCoordinate input.rightCoordinate

/-- The product of two odd Peirce elements has no off-diagonal component. -/
theorem d61_odd_product_is_even (X Y : B) :
    oddGrade P X * oddGrade P Y =
      qgtPlus P X Y + qgtMinus P Y X ∧
    oddGrade P (oddGrade P X * oddGrade P Y) = 0 ∧
    comm P (oddGrade P X * oddGrade P Y) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [oddGrade, qgtPlus, qgtMinus, conePlus, coneMinus]
    peirce_nf hP
  · simp only [oddGrade]
    peirce_nf hP
  · simp only [oddGrade, comm]
    peirce_nf hP

/-- The commutator of two odd Peirce elements is even. -/
theorem d61_odd_commutator_is_even (A C X : B) :
    comm P (comm (genPhi P A C) (oddGrade P X)) = 0 := by
  simp only [comm, genPhi, oddGrade, conePlus, coneMinus]
  peirce_nf hP

/-- Algebraic curvature `d_D Ω + Ω²`, where `d_D Ω = [Φ, Ω]`. -/
def peirceGaugeCurvature (P A C X : B) : B :=
  comm (genPhi P A C) (oddGrade P X) + oddGrade P X * oddGrade P X

/-- Curvature formed from an odd Peirce potential is confined to the two
diagonal corners: both its derivative term and quadratic term commute with P. -/
theorem d61_gauge_curvature_is_even (A C X : B) :
    comm P (peirceGaugeCurvature P A C X) = 0 := by
  have hD := d61_odd_commutator_is_even hP A C X
  have hQ := (d61_odd_product_is_even hP X X).2.2
  unfold peirceGaugeCurvature
  calc
    comm P (comm (genPhi P A C) (oddGrade P X) + oddGrade P X * oddGrade P X) =
        comm P (comm (genPhi P A C) (oddGrade P X)) +
          comm P (oddGrade P X * oddGrade P X) := by
            unfold comm
            noncomm_ring
    _ = 0 := by rw [hD, hQ, add_zero]

/-- Input data for the idempotent-cut gauge-curvature archetype. -/
structure D61CurvatureInput (B : Type*) [Ring B] where
  cut : D59IdempotentCut B
  forwardAmplitude : B
  backwardAmplitude : B
  potential : B

/-- The curvature confinement theorem registered as an operator-algebra
archetype, with idempotency carried by the input witness. -/
def d61CurvatureConfinementArchetype {B : Type*} [Ring B] :
    TypedArchetype (D61CurvatureInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d61CurvatureConfinementArchetype
  phase := 61
  claim := fun input =>
    comm (input.cut : B) (peirceGaugeCurvature (input.cut : B) input.forwardAmplitude
      input.backwardAmplitude input.potential) = 0
  evidence := fun input => d61_gauge_curvature_is_even
    input.cut.property input.forwardAmplitude input.backwardAmplitude input.potential

/-- A product of two one-forms generated from even coordinates is even. -/
theorem d61_one_form_curvature_is_even (A C A' C' a b : B)
    (ha : comm P a = 0) (hb : comm P b = 0) :
    comm P (comm (genPhi P A C) a * comm (genPhi P A' C') b) = 0 :=
  peirce_one_form_product_is_even hP A C A' C' a b ha hb

omit hP in
/-- The odd Peirce projection is additive. -/
theorem d61_oddGrade_add (X Y : B) :
    oddGrade P (X + Y) = oddGrade P X + oddGrade P Y := by
  simp only [oddGrade, add_mul, mul_add]
  noncomm_ring

omit hP in
/-- Left multiplication by an even Peirce element preserves the odd
projection and commutes with that projection. -/
theorem d61_even_left_odd_projection (a X : B) (ha : comm P a = 0) :
    oddGrade P (a * X) = a * oddGrade P X := by
  have hPa : P * a = a * P := sub_eq_zero.mp ha
  have hComp : (1 - P) * a = a * (1 - P) := by
    noncomm_ring [hPa]
  unfold oddGrade
  calc
    P * (a * X) * (1 - P) + (1 - P) * (a * X) * P =
        (P * a) * X * (1 - P) + ((1 - P) * a) * X * P := by noncomm_ring
    _ = (a * P) * X * (1 - P) + (a * (1 - P)) * X * P := by
        rw [hPa, hComp]
    _ = a * (P * X * (1 - P) + (1 - P) * X * P) := by noncomm_ring

/-- An element commuting with the cut is fixed by the even Peirce projection. -/
theorem d61_even_projection_eq (a : B) (ha : comm P a = 0) :
    evenGrade P a = a := by
  have hPa : P * a = a * P := sub_eq_zero.mp ha
  have hComp : (1 - P) * a = a * (1 - P) := by
    noncomm_ring [hPa]
  unfold evenGrade
  noncomm_ring [hP, hPa, hComp]

/-- A basic algebraic inner one-form with even coefficients is fixed by the
odd Peirce projection, not merely parity-invariant. -/
theorem d61_inner_one_form_is_oddGrade (A C a b : B)
    (ha : comm P a = 0) (hb : comm P b = 0) :
    oddGrade P (peirceInnerOneFormTerm P A C a b) =
      peirceInnerOneFormTerm P A C a b := by
  have hBodd : oddGrade P (comm (genPhi P A C) b) =
      comm (genPhi P A C) b := by
    simpa only [d61_even_projection_eq hP b hb] using
      (d61_one_form_projection hP A C b).2
  unfold peirceInnerOneFormTerm
  rw [d61_even_left_odd_projection (P := P) a _ ha, hBodd]

/-- Finite sums of algebraic Connes one-form terms with even coefficients are
fixed by the odd Peirce projection. -/
theorem d61_finite_sum_inner_one_forms_is_oddGrade {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (A C : B) (a b : ι → B)
    (ha : ∀ i ∈ s, comm P (a i) = 0)
    (hb : ∀ i ∈ s, comm P (b i) = 0) :
    oddGrade P (∑ i ∈ s, peirceInnerOneFormTerm P A C (a i) (b i)) =
      ∑ i ∈ s, peirceInnerOneFormTerm P A C (a i) (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [oddGrade]
  | @insert i s hi ih =>
      have hiTerm := d61_inner_one_form_is_oddGrade hP A C (a i) (b i)
        (ha i (Finset.mem_insert_self i s))
        (hb i (Finset.mem_insert_self i s))
      have hsA : ∀ j ∈ s, comm P (a j) = 0 := by
        intro j hj
        exact ha j (Finset.mem_insert_of_mem hj)
      have hsB : ∀ j ∈ s, comm P (b j) = 0 := by
        intro j hj
        exact hb j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      rw [d61_oddGrade_add (P := P), hiTerm, ih hsA hsB]

/-- The Yang–Mills polynomial `d_D A + A²` for a finite sum of even-coefficient
inner one-forms is diagonal in the Peirce decomposition. -/
theorem d61_finite_sum_gauge_curvature_is_even {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (A C : B) (a b : ι → B)
    (ha : ∀ i ∈ s, comm P (a i) = 0)
    (hb : ∀ i ∈ s, comm P (b i) = 0) :
    let Ω := ∑ i ∈ s, peirceInnerOneFormTerm P A C (a i) (b i)
    comm P (comm (genPhi P A C) Ω + Ω * Ω) = 0 := by
  dsimp
  have hOdd := d61_finite_sum_inner_one_forms_is_oddGrade hP s A C a b ha hb
  simpa only [peirceGaugeCurvature, hOdd] using
    (d61_gauge_curvature_is_even hP A C
      (∑ i ∈ s, peirceInnerOneFormTerm P A C (a i) (b i)))

/-- Finite even-coefficient inner one-forms form an odd connection, and the
associated polynomial `d_D Ω + Ω²` is even. -/
theorem stage_D61_finite_inner_form_curvature {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (A C : B) (a b : ι → B)
    (ha : ∀ i ∈ s, comm P (a i) = 0)
    (hb : ∀ i ∈ s, comm P (b i) = 0) :
    let Ω := ∑ i ∈ s, peirceInnerOneFormTerm P A C (a i) (b i)
    oddGrade P Ω = Ω ∧
      comm P (comm (genPhi P A C) Ω + Ω * Ω) = 0 := by
  dsimp
  exact ⟨d61_finite_sum_inner_one_forms_is_oddGrade hP s A C a b ha hb,
    d61_finite_sum_gauge_curvature_is_even hP s A C a b ha hb⟩

variable [StarRing B]

/-- The star-twisted reflection reverses products and is involutive. -/
theorem d61_real_structure_anti_involution (hPstar : star P = P) (X Y : B) :
    peirceRealTwist P (peirceRealTwist P X) = X ∧
    peirceRealTwist P (X * Y) = peirceRealTwist P Y * peirceRealTwist P X ∧
    peirceRealTwist P (invS P) = invS P :=
  peirce_real_twist_anti_involution (P := P) hP hPstar X Y

/-- The star-twisted reflection maps the forward corner to the negative
backward corner with starred amplitude. -/
theorem d61_real_structure_reflects_forward (hPstar : star P = P) (A : B) :
    peirceRealTwist P (conePlus P A) = -coneMinus P (star A) := by
  have hStarCone : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPstar, mul_assoc]
  unfold peirceRealTwist
  rw [hStarCone]
  have hOdd : anticomm (invS P) (coneMinus P (star A)) = 0 := by
    simp only [anticomm, coneMinus]
    peirce_nf hP
  exact peirce_odd_conjugation_neg hP (coneMinus P (star A)) hOdd

/-- The star-twisted reflection also maps the starred backward corner to the
negative forward corner. -/
theorem d61_real_structure_reflects_backward (hPstar : star P = P) (A : B) :
    peirceRealTwist P (coneMinus P (star A)) = -conePlus P A := by
  have hStarCone : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPstar, mul_assoc]
  have hStarConeM : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hStarCone, star_star]
  unfold peirceRealTwist
  rw [hStarConeM]
  have hOdd : anticomm (invS P) (conePlus P A) = 0 := by
    simp only [anticomm, conePlus]
    peirce_nf hP
  exact peirce_odd_conjugation_neg hP (conePlus P A) hOdd

omit [StarRing B] in
/-- The prior D₅₉ dispersion, quartic polynomial, and cyclic trace results
compose into this D₆₁ summary. The trace component is an algebraic cyclic-trace
identity only. -/
theorem d61_dirac_and_trace_summary
    {R : Type*} [Ring R] (τ : B → R)
    (hAdd : ∀ X Y : B, τ (X + Y) = τ X + τ Y)
    (hSub : ∀ X Y : B, τ (X - Y) = τ X - τ Y)
    (hCyc : ∀ X Y : B, τ (X * Y) = τ (Y * X)) (A C : B) :
    peirceMassDirac P A C * peirceMassDirac P A C = 1 + genV P A C ∧
    diracQuarticPolynomial (peirceMassDirac P A C) =
      (2 : ℤ) • genV P A C + idempotencyDefect (genV P A C) ∧
    τ (invS P * (peirceMassDirac P A C * peirceMassDirac P A C)) =
      τ P - τ (1 - P) := by
  exact ⟨peirce_mass_dirac_square hP A C,
    dirac_quartic_polynomial_split hP A C,
    peirce_cyclic_trace_mass_square hP τ hAdd hSub hCyc A C⟩

/-- Data for the Dirac polynomial and cyclic trace identity. -/
structure D61DiracTraceInput (B R : Type*) [Ring B] [Ring R] where
  cut : D59IdempotentCut B
  trace : B → R
  traceAdd : ∀ X Y : B, trace (X + Y) = trace X + trace Y
  traceSub : ∀ X Y : B, trace (X - Y) = trace X - trace Y
  traceCyclic : ∀ X Y : B, trace (X * Y) = trace (Y * X)
  forwardAmplitude : B
  backwardAmplitude : B

/-- The massive Peirce square, its quartic polynomial, and the cyclic-trace
identity form one proved operator archetype over the actual ring carrier. -/
def d61DiracTraceArchetype {B R : Type*} [Ring B] [Ring R] :
    TypedArchetype (D61DiracTraceInput B R) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d61DiracTraceArchetype
  phase := 61
  claim := fun input =>
    peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude =
      1 + genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude ∧
    diracQuarticPolynomial
        (peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude) =
      (2 : ℤ) • genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude +
        idempotencyDefect
          (genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude) ∧
    input.trace (invS (input.cut : B) *
        (peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
         peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude)) =
      input.trace (input.cut : B) - input.trace (1 - (input.cut : B))
  evidence := fun input => d61_dirac_and_trace_summary input.cut.property
    input.trace input.traceAdd input.traceSub input.traceCyclic
    input.forwardAmplitude input.backwardAmplitude

omit [Ring B] hP [StarRing B] in
theorem d61_trace_kills_commutator {B R : Type*} [Ring B] [Ring R]
    (τ : B → R) (hSub : ∀ X Y, τ (X - Y) = τ X - τ Y)
    (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X)) (X Y : B) :
    τ (comm X Y) = 0 := by
  unfold comm
  rw [hSub, hCyc X Y, sub_self]

/-- Input for the cyclic-trace cancellation archetype. -/
structure D61TraceInput (B R : Type*) [Ring B] [Ring R] where
  trace : B → R
  traceSub : ∀ X Y : B, trace (X - Y) = trace X - trace Y
  traceCyclic : ∀ X Y : B, trace (X * Y) = trace (Y * X)
  leftOperator : B
  rightOperator : B

/-- A cyclic trace kills commutators for arbitrary operators on the same
noncommutative ring. -/
def d61CyclicTraceArchetype {B R : Type*} [Ring B] [Ring R] :
    TypedArchetype (D61TraceInput B R) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d61CyclicTraceArchetype
  phase := 61
  claim := fun input => input.trace (comm input.leftOperator input.rightOperator) = 0
  evidence := fun input => d61_trace_kills_commutator input.trace input.traceSub
    input.traceCyclic input.leftOperator input.rightOperator

/-- Master synthesis of the five D₆₁ strata. The odd-fluctuation clause is
scoped to fixed points of `oddGrade`; the trace conclusion is the algebraic
cyclic-trace identity inherited from D₅₉. -/
theorem stage_D61_connes_forms_curvature_real_structure_and_trace
    {R : Type*} [Ring R] (τ : B → R)
    (hAdd : ∀ X Y : B, τ (X + Y) = τ X + τ Y)
    (hSub : ∀ X Y : B, τ (X - Y) = τ X - τ Y)
    (hCyc : ∀ X Y : B, τ (X * Y) = τ (Y * X))
    (hPstar : star P = P) (A C a b X Y : B)
    (hEven : comm P a = 0) :
    -- Differential stratum: parity and Leibniz.
    anticomm (invS P) (comm (genPhi P A C) a) = 0 ∧
    comm (genPhi P A C) (a * b) =
      comm (genPhi P A C) a * b + a * comm (genPhi P A C) b ∧
    evenGrade P (comm (genPhi P A C) (evenGrade P X)) = 0 ∧
    oddGrade P (comm (genPhi P A C) (evenGrade P X)) =
      comm (genPhi P A C) (evenGrade P X) ∧
    -- Curvature stratum: odd products land in the diagonal Peirce algebra.
    oddGrade P (oddGrade P X * oddGrade P Y) = 0 ∧
    comm P (oddGrade P X * oddGrade P Y) = 0 ∧
    comm P (peirceGaugeCurvature P A C X) = 0 ∧
    -- Real-structure stratum.
    peirceRealTwist P (peirceRealTwist P X) = X ∧
    peirceRealTwist P (X * Y) = peirceRealTwist P Y * peirceRealTwist P X ∧
    peirceRealTwist P (conePlus P A) = -coneMinus P (star A) ∧
    peirceRealTwist P (coneMinus P (star A)) = -conePlus P A ∧
    -- Every odd Peirce perturbation has a two-wave parameterization.
    (∀ Ω : B, oddGrade P Ω = Ω → ∃ Aω Cω : B, genPhi P Aω Cω = Ω) ∧
    -- Polynomial and cyclic-trace strata.
    peirceMassDirac P A C * peirceMassDirac P A C = 1 + genV P A C ∧
    diracQuarticPolynomial (peirceMassDirac P A C) =
      (2 : ℤ) • genV P A C + idempotencyDefect (genV P A C) ∧
    τ (invS P * (peirceMassDirac P A C * peirceMassDirac P A C)) =
      τ P - τ (1 - P) := by
  have hOneFormOdd := d61_one_form_odd hP A C a hEven
  have hLeibniz := d61_one_form_leibniz (P := P) A C a b
  have hProjection := d61_one_form_projection hP A C X
  have hCurvature := d61_odd_product_is_even hP X Y
  have hReal := d61_real_structure_anti_involution hP hPstar X Y
  have hReflection := d61_real_structure_reflects_forward hP hPstar A
  have hReflectionBack := d61_real_structure_reflects_backward hP hPstar A
  have hOddRepresentation := fun Ω hΩ =>
    peirce_odd_grade_representation (P := P) Ω hΩ
  have hDirac := d61_dirac_and_trace_summary hP τ hAdd hSub hCyc A C
  exact ⟨hOneFormOdd, hLeibniz, hProjection.1, hProjection.2,
    hCurvature.2.1, hCurvature.2.2, d61_gauge_curvature_is_even hP A C X,
    hReal.1, hReal.2.1, hReflection, hReflectionBack,
    hOddRepresentation, hDirac.1, hDirac.2.1, hDirac.2.2⟩

/-! ## Proof-carrying parity and real-structure archetypes -/

/-- Data for the parity localization of a one-form generated from an even
Peirce coordinate. -/
structure D61ParityInput (B : Type*) [Ring B] where
  cut : D59IdempotentCut B
  forwardAmplitude : B
  backwardAmplitude : B
  coordinate : B

/-- Differentiating an even Peirce coordinate has zero even component and is
fixed by the odd component. -/
def d61OneFormParityArchetype {B : Type*} [Ring B] :
    TypedArchetype (D61ParityInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d61OneFormParityArchetype
  phase := 61
  claim := fun input =>
    evenGrade (input.cut : B)
        (comm (genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude)
          (evenGrade (input.cut : B) input.coordinate)) = 0 ∧
    oddGrade (input.cut : B)
        (comm (genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude)
          (evenGrade (input.cut : B) input.coordinate)) =
      comm (genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude)
        (evenGrade (input.cut : B) input.coordinate)
  evidence := fun input => d61_one_form_projection
    input.cut.property input.forwardAmplitude input.backwardAmplitude input.coordinate

/-- A self-adjoint idempotent Peirce cut, represented by a subtype. -/
abbrev D61SelfAdjointCut (B : Type*) [Ring B] [StarRing B] :=
  {P : D59IdempotentCut B // star (P : B) = (P : B)}

/-- Inputs for the involutive real-structure action and its two corner
reflections. -/
structure D61RealStructureInput (B : Type*) [Ring B] [StarRing B] where
  cut : D61SelfAdjointCut B
  leftOperator : B
  rightOperator : B
  amplitude : B

/-- The star-twisted Peirce real structure is an involutive
anti-automorphism and exchanges the two transition corners with a sign. -/
def d61RealStructureArchetype {B : Type*} [Ring B] [StarRing B] :
    TypedArchetype (D61RealStructureInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d61RealStructureArchetype
  phase := 61
  claim := fun input =>
    peirceRealTwist (input.cut.1 : B)
        (peirceRealTwist (input.cut.1 : B) input.leftOperator) = input.leftOperator ∧
    peirceRealTwist (input.cut.1 : B) (input.leftOperator * input.rightOperator) =
      peirceRealTwist (input.cut.1 : B) input.rightOperator *
        peirceRealTwist (input.cut.1 : B) input.leftOperator ∧
    peirceRealTwist (input.cut.1 : B) (conePlus (input.cut.1 : B) input.amplitude) =
      -coneMinus (input.cut.1 : B) (star input.amplitude) ∧
    peirceRealTwist (input.cut.1 : B)
        (coneMinus (input.cut.1 : B) (star input.amplitude)) =
      -conePlus (input.cut.1 : B) input.amplitude
  evidence := fun input => by
    rcases d61_real_structure_anti_involution input.cut.1.property
      input.cut.2 input.leftOperator input.rightOperator with
      ⟨hInvol, hAnti, _⟩
    exact ⟨hInvol, hAnti,
      d61_real_structure_reflects_forward input.cut.1.property input.cut.2 input.amplitude,
      d61_real_structure_reflects_backward input.cut.1.property input.cut.2 input.amplitude⟩

#register_archetype d61OneFormParityArchetype
#audit_archetype d61OneFormParityArchetype
#register_archetype d61RealStructureArchetype
#audit_archetype d61RealStructureArchetype

#register_archetype d61ConnesLeibnizArchetype
#register_archetype d61CurvatureConfinementArchetype
#register_archetype d61DiracTraceArchetype
#register_archetype d61CyclicTraceArchetype
#audit_archetype d61ConnesLeibnizArchetype
#audit_archetype d61CurvatureConfinementArchetype
#audit_archetype d61DiracTraceArchetype
#audit_archetype d61CyclicTraceArchetype

/-! ## The D₆₁ causal archetypes -/

variable {R : Type*} [Ring R]

omit hP in
inductive D61Stage (B : Type*) [Ring B] [StarRing B] (R : Type*) [Ring R] where
  | peirceCore
  | differential
  | curvature
  | realStructure
  | diracPolynomial
  | traceLaws
  | cyclicTrace
  deriving DecidableEq, Repr

omit hP in
def D61Stage.rank : D61Stage B R → ℕ
  | .peirceCore => 0
  | .differential => 1
  | .curvature => 2
  | .realStructure => 1
  | .diracPolynomial => 1
  | .traceLaws => 0
  | .cyclicTrace => 2

omit hP in
def D61Stage.edge : D61Stage B R → D61Stage B R → Prop
  | .peirceCore, .differential =>
      ∀ input : D61LeibnizInput B, d61ConnesLeibnizArchetype.claim input
  | .peirceCore, .realStructure =>
      ∀ input : D61RealStructureInput B, d61RealStructureArchetype.claim input
  | .peirceCore, .diracPolynomial =>
      ∀ input : D61DiracTraceInput B R, d61DiracTraceArchetype.claim input
  | .differential, .curvature =>
      ∀ input : D61CurvatureInput B, d61CurvatureConfinementArchetype.claim input
  | .diracPolynomial, .cyclicTrace =>
      ∀ input : D61DiracTraceInput B R, d61DiracTraceArchetype.claim input
  | .traceLaws, .cyclicTrace =>
      ∀ input : D61TraceInput B R, d61CyclicTraceArchetype.claim input
  | _, _ => False

omit hP in
inductive D61Stage.Reachable : D61Stage B R → D61Stage B R → Prop where
  | refl (a : D61Stage B R) : Reachable a a
  | edge {a b : D61Stage B R} : a.edge b → Reachable a b
  | trans {a b c : D61Stage B R} : Reachable a b → Reachable b c → Reachable a c

omit hP in
def D61Stage.causalLE : D61Stage B R → D61Stage B R → Prop := Reachable

omit hP in
theorem D61Stage.causalLE_refl (a : D61Stage B R) : a.causalLE a :=
  Reachable.refl a

omit hP in
theorem D61Stage.causalLE_trans {a b c : D61Stage B R}
    (hab : a.causalLE b) (hbc : b.causalLE c) : a.causalLE c :=
  Reachable.trans hab hbc

omit hP in
theorem D61Stage.edge_rank_strict {a b : D61Stage B R} (h : a.edge b) :
    a.rank < b.rank := by
  cases a <;> cases b <;> simp_all [rank, D61Stage.edge]

omit hP in
theorem D61Stage.reachable_rank_strict_of_ne {a b : D61Stage B R}
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

omit hP in
theorem D61Stage.causalLE_antisymm {a b : D61Stage B R}
    (hab : a.causalLE b) (hba : b.causalLE a) : a = b := by
  by_cases hEq : a = b
  · exact hEq
  · exact (lt_asymm (reachable_rank_strict_of_ne hab hEq)
      (reachable_rank_strict_of_ne hba (Ne.symm hEq))).elim

omit hP in
instance : PartialOrder (D61Stage B R) where
  le := D61Stage.causalLE
  le_refl := D61Stage.causalLE_refl
  le_trans := fun _ _ _ hab hbc => D61Stage.causalLE_trans hab hbc
  le_antisymm := fun _ _ hab hba => D61Stage.causalLE_antisymm hab hba

omit hP in
theorem D61Stage.edge_causal {a b : D61Stage B R} (h : a.edge b) : a.causalLE b :=
  Reachable.edge h

/-! ## Native typed closure of the seven D₆₁ stages -/

omit hP in
/-- The proposition carried by each D₆₁ stage. The clauses retain the ring,
star, idempotent, and trace hypotheses required by their source theorems. -/
def d61NativeMathlibClaim {B R : Type*} [Ring B] [StarRing B] [Ring R] :
    D61Stage B R → Prop
  | .peirceCore =>
      ∀ (P : B), P * P = P → ∀ X : B,
        evenGrade P X + oddGrade P X = X
  | .differential =>
      ∀ (P A C a b : B), P * P = P → comm P a = 0 →
        comm (genPhi P A C) (a * b) =
          comm (genPhi P A C) a * b + a * comm (genPhi P A C) b
  | .curvature =>
      ∀ (P A C X : B), P * P = P →
        comm P (peirceGaugeCurvature P A C X) = 0
  | .realStructure =>
      ∀ (P A X Y : B), P * P = P → star P = P →
        peirceRealTwist P (peirceRealTwist P X) = X ∧
         peirceRealTwist P (X * Y) = peirceRealTwist P Y * peirceRealTwist P X ∧
         peirceRealTwist P (conePlus P A) = -coneMinus P (star A) ∧
         peirceRealTwist P (coneMinus P (star A)) = -conePlus P A
  | .diracPolynomial =>
      ∀ (P A C : B), P * P = P →
        peirceMassDirac P A C * peirceMassDirac P A C = 1 + genV P A C ∧
        diracQuarticPolynomial (peirceMassDirac P A C) =
          (2 : ℤ) • genV P A C + idempotencyDefect (genV P A C)
  | .traceLaws =>
      ∀ (τ : B → R),
        (∀ X Y, τ (X - Y) = τ X - τ Y) →
        (∀ X Y, τ (X * Y) = τ (Y * X)) →
        ∀ X Y, τ (comm X Y) = 0
  | .cyclicTrace =>
      ∀ (P : B) (τ : B → R), P * P = P →
        (∀ X Y, τ (X + Y) = τ X + τ Y) →
        (∀ X Y, τ (X - Y) = τ X - τ Y) →
        (∀ X Y, τ (X * Y) = τ (Y * X)) →
        ∀ A C,
          τ (invS P * (peirceMassDirac P A C * peirceMassDirac P A C)) =
            τ P - τ (1 - P)

omit hP in
/-- Every D₆₁ stage claim follows from the corresponding native operator
theorem. The stage order itself is the existing `D61Stage.causalLE` partial
order, whose edges are separately defined in terms of the registered claims. -/
theorem d61NativeMathlibClaim_all {B R : Type*} [Ring B] [StarRing B] [Ring R]
    (stage : D61Stage B R) : d61NativeMathlibClaim (B := B) (R := R) stage := by
  cases stage with
  | peirceCore =>
      intro P hP X
      unfold evenGrade oddGrade
      noncomm_ring
  | differential =>
      intro P A C a b hP hEven
      exact d61_one_form_leibniz (P := P) A C a b
  | curvature =>
      intro P A C X hP
      exact d61_gauge_curvature_is_even (P := P) hP A C X
  | realStructure =>
      intro P A X Y hP hPstar
      rcases d61_real_structure_anti_involution (P := P) hP hPstar X Y with
        ⟨hInvol, hAnti, _⟩
      exact ⟨hInvol, hAnti,
        d61_real_structure_reflects_forward (P := P) hP hPstar A,
        d61_real_structure_reflects_backward (P := P) hP hPstar A⟩
  | diracPolynomial =>
      intro P A C hP
      exact ⟨peirce_mass_dirac_square (P := P) hP A C,
        dirac_quartic_polynomial_split (P := P) hP A C⟩
  | traceLaws =>
      intro τ hSub hCyc X Y
      exact d61_trace_kills_commutator τ hSub hCyc X Y
  | cyclicTrace =>
      intro P τ hP hAdd hSub hCyc A C
      exact (d61_dirac_and_trace_summary (P := P) hP τ hAdd hSub hCyc A C).2.2

omit hP in
/-- Typed archetype closure of the seven D₆₁ stages with their native claims. -/
def d61NativeMathlibProvedArchetype {B R : Type*} [Ring B] [StarRing B] [Ring R] :
    TypedArchetype (D61Stage B R) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d61NativeMathlibProvedArchetype
  phase := 61
  claim := d61NativeMathlibClaim
  evidence := d61NativeMathlibClaim_all

#register_archetype d61NativeMathlibProvedArchetype
#audit_archetype d61NativeMathlibProvedArchetype

end InfoGeometry.OperatorAlgebra.PeirceSpine
