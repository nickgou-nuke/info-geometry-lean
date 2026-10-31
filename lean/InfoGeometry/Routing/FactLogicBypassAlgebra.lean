/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing

/-!
# Three-corner algebra for a fact/logic/prompt attention support pattern

This file proves consequences of an abstract decomposition by three pairwise
orthogonal idempotents in an associative ring. The result models block support
and composition. It does not identify real-valued additive attention masks,
token embeddings, or a neural network with Peirce corners, and it says nothing
about empirical benchmark results or lossless retention of information.
-/

namespace InfoGeometry.Routing.FactLogicBypassAlgebra

variable {B : Type*} [Ring B]

/-- An operator with fact-diagonal, globally addressed logic-column, and
prompt-diagonal components relative to three Peirce idempotents. -/
def fullOperator (P_f P_l P_p F L Q : B) : B :=
  P_f * F * P_f + L * P_l + P_p * Q * P_p

/-- Removing the fact corner by compression to the complementary two corners. -/
def withoutFact (P_f T : B) : B := (1 - P_f) * T * (1 - P_f)

/-- The remaining prompt idempotent when the fact and logic projections are
orthogonal idempotents whose sum is a subprojection of `1`. -/
def promptProj (P_f P_l : B) : B := 1 - P_f - P_l

/-- The three-track decoder operator: diagonal fact and prompt corners, with a
globally addressable logic column. This is an abstract support algebra, not a
model of token embeddings or learned attention values. -/
def decoderFullOp (P_f P_l F L Q : B) : B :=
  P_f * F * P_f + L * P_l + promptProj P_f P_l * Q * promptProj P_f P_l

/-- The three projections sum to the identity. -/
theorem promptProj_partition (P_f P_l : B) :
    P_f + P_l + promptProj P_f P_l = 1 := by
  simp [promptProj]

/-- Orthogonality and idempotence of the fact and logic projections make the
derived prompt projection an idempotent orthogonal to both on either side. -/
theorem promptProj_orthogonal_idempotent
    {P_f P_l : B}
    (hff : P_f * P_f = P_f) (hll : P_l * P_l = P_l)
    (hfl : P_f * P_l = 0) (hlf : P_l * P_f = 0) :
    promptProj P_f P_l * promptProj P_f P_l = promptProj P_f P_l ∧
    P_f * promptProj P_f P_l = 0 ∧ promptProj P_f P_l * P_f = 0 ∧
    P_l * promptProj P_f P_l = 0 ∧ promptProj P_f P_l * P_l = 0 := by
  unfold promptProj
  constructor
  · noncomm_ring [hff, hll, hfl, hlf]
  constructor
  · noncomm_ring [hff, hfl]
  constructor
  · noncomm_ring [hff, hlf]
  constructor
  · noncomm_ring [hll, hlf]
  · noncomm_ring [hll, hfl]

/-- Support pattern read from the published TCR-Former decoder: factual rows
are causal within their corner, logic rows may read every corner, and prompt
rows may read facts and logic plus their causal prompt corner. The letters
`G`, `R`, and `S` stand for unrestricted allowed blocks; this records support,
not numerical attention weights or a model-level equivalence. -/
def publishedMaskSupport (P_f P_l P_p F G R S Q : B) : B :=
  P_f * F * P_f + P_l * G + P_p * R * P_f + P_p * S * P_l + P_p * Q * P_p

private lemma idempotent_left_mul {e x : B} (he : e * e = e) :
    e * (e * x) = e * x := by
  rw [← mul_assoc, he]

private lemma idempotent_right_mul {e x : B} (he : e * e = e) :
    (x * e) * e = x * e := by
  rw [mul_assoc, he]

private lemma orthogonal_left_mul {e f x : B} (hef : e * f = 0) :
    e * (f * x) = 0 := by
  rw [← mul_assoc, hef, zero_mul]

private lemma orthogonal_right_mul {e f x : B} (hef : e * f = 0) :
    (x * e) * f = 0 := by
  rw [mul_assoc, hef, mul_zero]

/-- Right multiplication by the logic idempotent selects the complete logic
column; this is an algebraic support statement only. -/
theorem fullOperator_logic_column
    {P_f P_l P_p F L Q : B}
    (hfl : P_f * P_l = 0) (hpf_l : P_p * P_l = 0)
    (hll : P_l * P_l = P_l) :
    fullOperator P_f P_l P_p F L Q * P_l = L * P_l := by
  unfold fullOperator
  simp only [add_mul]
  simp only [mul_assoc, orthogonal_right_mul hfl, orthogonal_right_mul hpf_l,
    idempotent_right_mul hll, mul_zero, zero_add]
  simp

/-- The logic row has no component in the fact or prompt columns. -/
theorem fullOperator_logic_row
    {P_f P_l P_p F L Q : B}
    (hlf : P_l * P_f = 0) (hlp : P_l * P_p = 0) :
    P_l * fullOperator P_f P_l P_p F L Q * P_f = 0 ∧
    P_l * fullOperator P_f P_l P_p F L Q * P_p = 0 := by
  constructor
  · unfold fullOperator
    calc
      P_l * (P_f * F * P_f + L * P_l + P_p * Q * P_p) * P_f =
          P_l * (P_f * F * P_f) * P_f +
            P_l * (L * P_l) * P_f + P_l * (P_p * Q * P_p) * P_f := by
              noncomm_ring
      _ = 0 := by
        simp only [mul_assoc, orthogonal_left_mul hlf, orthogonal_left_mul hlp,
          orthogonal_right_mul hlf, zero_mul, mul_zero]
        simp
  · unfold fullOperator
    calc
      P_l * (P_f * F * P_f + L * P_l + P_p * Q * P_p) * P_p =
          P_l * (P_f * F * P_f) * P_p +
            P_l * (L * P_l) * P_p + P_l * (P_p * Q * P_p) * P_p := by
              noncomm_ring
      _ = 0 := by
        simp only [mul_assoc, orthogonal_left_mul hlf, orthogonal_left_mul hlp,
          orthogonal_right_mul hlp, zero_mul, mul_zero]
        simp

/-- Composition of two such operators is again of the same form. The new
fact and prompt blocks are the corresponding corner products, while the new
logic column records the three ways to enter that column. -/
theorem fullOperator_mul
    {P_f P_l P_p F₁ L₁ Q₁ F₂ L₂ Q₂ : B}
    (hff : P_f * P_f = P_f) (hpp : P_p * P_p = P_p)
    (hlf : P_l * P_f = 0)
    (hfp : P_f * P_p = 0) (hpf : P_p * P_f = 0)
    (hlp : P_l * P_p = 0) :
    fullOperator P_f P_l P_p F₁ L₁ Q₁ *
        fullOperator P_f P_l P_p F₂ L₂ Q₂ =
      fullOperator P_f P_l P_p
        (F₁ * P_f * F₂)
        (P_f * F₁ * P_f * L₂ + L₁ * P_l * L₂ + P_p * Q₁ * P_p * L₂)
        (Q₁ * P_p * Q₂) := by
  unfold fullOperator
  simp only [mul_add, add_mul]
  simp [mul_assoc, hff, hpp, hlf, hfp, hpf, hlp,
    idempotent_left_mul, orthogonal_left_mul]

/-- Compression to the complementary corners removes the fact block and
retains the logic column and prompt block. The three idempotents are assumed
to form a partition of unity. -/
theorem withoutFact_fullOperator
    {P_f P_l P_p F L Q : B}
    (hll : P_l * P_l = P_l) (hpp : P_p * P_p = P_p)
    (hlf : P_l * P_f = 0) (hpf : P_p * P_f = 0)
    (hlp : P_l * P_p = 0) (hpl : P_p * P_l = 0)
    (hsum : P_f + P_l + P_p = 1) :
    withoutFact P_f (fullOperator P_f P_l P_p F L Q) =
      fullOperator P_f P_l P_p 0 ((1 - P_f) * L) Q := by
  unfold withoutFact fullOperator
  have hcomp : 1 - P_f = P_l + P_p := by
    rw [← hsum]
    abel
  rw [hcomp]
  simp only [mul_add, add_mul]
  simp [mul_assoc, hll, hpp, hlf, hpf, hlp, hpl,
    idempotent_left_mul, orthogonal_left_mul]

/-- The decoder operator's complete logic column is `L * P_l`. -/
theorem decoderFullOp_logic_column
    {P_f P_l F L Q : B}
    (hff : P_f * P_f = P_f) (hll : P_l * P_l = P_l)
    (hfl : P_f * P_l = 0) (hlf : P_l * P_f = 0) :
    decoderFullOp P_f P_l F L Q * P_l = L * P_l := by
  obtain ⟨_, _, _, _, hpl⟩ :=
    promptProj_orthogonal_idempotent hff hll hfl hlf
  simpa [decoderFullOp, fullOperator] using
    (fullOperator_logic_column (P_f := P_f) (P_l := P_l)
      (P_p := promptProj P_f P_l) hfl hpl hll)

/-- Neither the logic row nor the prompt/fact corners leak into the forbidden
fact and prompt blocks of the block-diagonal support pattern. -/
theorem decoderFullOp_mask_zeros
    {P_f P_l F L Q : B}
    (hff : P_f * P_f = P_f) (hll : P_l * P_l = P_l)
    (hfl : P_f * P_l = 0) (hlf : P_l * P_f = 0) :
    P_l * decoderFullOp P_f P_l F L Q * P_f = 0 ∧
    P_l * decoderFullOp P_f P_l F L Q * promptProj P_f P_l = 0 ∧
    P_f * decoderFullOp P_f P_l F L Q * promptProj P_f P_l = 0 ∧
    promptProj P_f P_l * decoderFullOp P_f P_l F L Q * P_f = 0 := by
  obtain ⟨hpp, hfp, hpf, hlp, hpl⟩ :=
    promptProj_orthogonal_idempotent hff hll hfl hlf
  have hrow := fullOperator_logic_row (P_f := P_f) (P_l := P_l)
    (P_p := promptProj P_f P_l) (F := F) (L := L) (Q := Q) hlf hlp
  have hfactPrompt :
      P_f * fullOperator P_f P_l (promptProj P_f P_l) F L Q *
          promptProj P_f P_l = 0 := by
    unfold fullOperator
    have hFact : P_f * (P_f * F * P_f) * promptProj P_f P_l = 0 := by
      simp [mul_assoc, hfp]
    have hLogic : P_f * (L * P_l) * promptProj P_f P_l = 0 := by
      calc
        P_f * (L * P_l) * promptProj P_f P_l = P_f * L * (P_l * promptProj P_f P_l) := by
          noncomm_ring
        _ = 0 := by rw [hlp]; simp
    have hPrompt :
        P_f * (promptProj P_f P_l * Q * promptProj P_f P_l) *
          promptProj P_f P_l = 0 := by
      calc
        _ = (P_f * promptProj P_f P_l) * Q * promptProj P_f P_l *
              promptProj P_f P_l := by noncomm_ring
        _ = 0 := by rw [hfp]; simp
    calc
      P_f * (P_f * F * P_f + L * P_l + promptProj P_f P_l * Q * promptProj P_f P_l) *
          promptProj P_f P_l =
        P_f * (P_f * F * P_f) * promptProj P_f P_l +
          P_f * (L * P_l) * promptProj P_f P_l +
          P_f * (promptProj P_f P_l * Q * promptProj P_f P_l) *
            promptProj P_f P_l := by noncomm_ring
      _ = 0 := by rw [hFact, hLogic, hPrompt]; simp
  have hpromptFact :
      promptProj P_f P_l * fullOperator P_f P_l (promptProj P_f P_l) F L Q *
          P_f = 0 := by
    unfold fullOperator
    have hFact : promptProj P_f P_l * (P_f * F * P_f) * P_f = 0 := by
      calc
        _ = (promptProj P_f P_l * P_f) * F * P_f * P_f := by noncomm_ring
        _ = 0 := by rw [hpf]; simp
    have hLogic : promptProj P_f P_l * (L * P_l) * P_f = 0 := by
      calc
        promptProj P_f P_l * (L * P_l) * P_f = promptProj P_f P_l * L * (P_l * P_f) := by
          noncomm_ring
        _ = 0 := by rw [hlf]; simp
    have hPrompt :
        promptProj P_f P_l * (promptProj P_f P_l * Q * promptProj P_f P_l) * P_f = 0 := by
      calc
        _ = promptProj P_f P_l * promptProj P_f P_l * Q *
              (promptProj P_f P_l * P_f) := by noncomm_ring
        _ = 0 := by rw [hpf]; simp
    calc
      promptProj P_f P_l *
          (P_f * F * P_f + L * P_l + promptProj P_f P_l * Q * promptProj P_f P_l) *
          P_f =
        promptProj P_f P_l * (P_f * F * P_f) * P_f +
          promptProj P_f P_l * (L * P_l) * P_f +
          promptProj P_f P_l * (promptProj P_f P_l * Q * promptProj P_f P_l) * P_f := by
            noncomm_ring
      _ = 0 := by rw [hFact, hLogic, hPrompt]; simp
  simpa [decoderFullOp] using ⟨hrow.1, hrow.2, hfactPrompt, hpromptFact⟩

/-- Composition of two decoder operators has the same three-track support
form. The three summands in the new logic operator are the fact-to-logic,
logic-to-logic, and prompt-to-logic routes. -/
theorem decoderFullOp_mul
    {P_f P_l F₁ L₁ Q₁ F₂ L₂ Q₂ : B}
    (hff : P_f * P_f = P_f) (hll : P_l * P_l = P_l)
    (hfl : P_f * P_l = 0) (hlf : P_l * P_f = 0) :
    decoderFullOp P_f P_l F₁ L₁ Q₁ * decoderFullOp P_f P_l F₂ L₂ Q₂ =
      decoderFullOp P_f P_l
        (F₁ * P_f * F₂)
        (P_f * F₁ * P_f * L₂ + L₁ * P_l * L₂ +
          promptProj P_f P_l * Q₁ * promptProj P_f P_l * L₂)
        (Q₁ * promptProj P_f P_l * Q₂) := by
  obtain ⟨hpp, hfp, hpf, hlp, _⟩ :=
    promptProj_orthogonal_idempotent hff hll hfl hlf
  simpa [decoderFullOp, fullOperator] using
    (fullOperator_mul (P_f := P_f) (P_l := P_l)
      (P_p := promptProj P_f P_l) hff hpp hlf hfp hpf hlp)

/-- Removing the fact track by complementary-corner compression gives the
exact algebraic ablation. This is a statement about the abstract operator. -/
theorem decoderFullOp_withoutFact
    {P_f P_l F L Q : B}
    (hff : P_f * P_f = P_f) (hll : P_l * P_l = P_l)
    (hfl : P_f * P_l = 0) (hlf : P_l * P_f = 0) :
    withoutFact P_f (decoderFullOp P_f P_l F L Q) =
      decoderFullOp P_f P_l 0 ((1 - P_f) * L) Q := by
  obtain ⟨hpp, _, hpf, hlp, hpl⟩ :=
    promptProj_orthogonal_idempotent hff hll hfl hlf
  simpa [decoderFullOp, fullOperator] using
    (withoutFact_fullOperator (P_f := P_f) (P_l := P_l)
      (P_p := promptProj P_f P_l) hll hpp hlf hpf hlp hpl
      (promptProj_partition P_f P_l))

/-- A86's abstract decoder-mask laws in one certificate: a three-idempotent
partition, globally selected logic column, forbidden block zeros, closure under
two decoder layers, and the exact complementary-corner ablation. This is an
algebraic theorem about the declared ring model only. -/
theorem archetypeA86_factLogicBypass
    {P_f P_l F L Q F₁ L₁ Q₁ F₂ L₂ Q₂ : B}
    (hff : P_f * P_f = P_f) (hll : P_l * P_l = P_l)
    (hfl : P_f * P_l = 0) (hlf : P_l * P_f = 0) :
    let P_p := promptProj P_f P_l
    P_f + P_l + P_p = 1 ∧
    P_p * P_p = P_p ∧
    P_f * P_p = 0 ∧ P_p * P_f = 0 ∧
    P_l * P_p = 0 ∧ P_p * P_l = 0 ∧
    decoderFullOp P_f P_l F L Q * P_l = L * P_l ∧
    P_l * decoderFullOp P_f P_l F L Q * P_f = 0 ∧
    P_l * decoderFullOp P_f P_l F L Q * P_p = 0 ∧
    P_f * decoderFullOp P_f P_l F L Q * P_p = 0 ∧
    P_p * decoderFullOp P_f P_l F L Q * P_f = 0 ∧
    decoderFullOp P_f P_l F₁ L₁ Q₁ * decoderFullOp P_f P_l F₂ L₂ Q₂ =
      decoderFullOp P_f P_l
        (F₁ * P_f * F₂)
        (P_f * F₁ * P_f * L₂ + L₁ * P_l * L₂ + P_p * Q₁ * P_p * L₂)
        (Q₁ * P_p * Q₂) ∧
    withoutFact P_f (decoderFullOp P_f P_l F L Q) =
      decoderFullOp P_f P_l 0 ((1 - P_f) * L) Q := by
  dsimp
  obtain ⟨hpp, hfp, hpf, hlp, hpl⟩ :=
    promptProj_orthogonal_idempotent hff hll hfl hlf
  obtain ⟨hrowFact, hrowPrompt, hfactPrompt, hpromptFact⟩ :=
    decoderFullOp_mask_zeros hff hll hfl hlf
  exact ⟨promptProj_partition P_f P_l, hpp, hfp, hpf, hlp, hpl,
    decoderFullOp_logic_column hff hll hfl hlf,
    hrowFact, hrowPrompt, hfactPrompt, hpromptFact,
    decoderFullOp_mul hff hll hfl hlf,
    decoderFullOp_withoutFact hff hll hfl hlf⟩

/-- Ablation annihilates a fact-corner operator supported by a nonzero
idempotent. This is the exact algebraic loss statement; it does not identify
the operator with text tokens or a semantic notion of information. -/
theorem withoutFact_erases_fact_corner
    {P_f P_l P_p : B}
    (hff : P_f * P_f = P_f) (hne : P_f ≠ 0) :
    fullOperator P_f P_l P_p P_f 0 0 = P_f ∧
      withoutFact P_f (fullOperator P_f P_l P_p P_f 0 0) = 0 ∧
      withoutFact P_f (fullOperator P_f P_l P_p P_f 0 0) ≠
        fullOperator P_f P_l P_p P_f 0 0 := by
  constructor
  · unfold fullOperator
    simp [hff]
  constructor
  · unfold withoutFact fullOperator
    noncomm_ring [hff]
  · rw [show fullOperator P_f P_l P_p P_f 0 0 = P_f by
      unfold fullOperator
      simp [hff]]
    have hzero : withoutFact P_f P_f = 0 := by
      unfold withoutFact
      noncomm_ring [hff]
    rw [hzero]
    exact Ne.symm hne

/-- The prompt-to-fact block is allowed by this support pattern, in contrast
to a block-diagonal prompt/fact interpretation. -/
theorem publishedMaskSupport_prompt_fact_block
    {P_f P_l P_p F G R S Q : B}
    (hpf : P_p * P_f = 0) (hpl : P_p * P_l = 0)
    (hlf : P_l * P_f = 0) (hff : P_f * P_f = P_f)
    (hpp : P_p * P_p = P_p) :
    P_p * publishedMaskSupport P_f P_l P_p F G R S Q * P_f =
      P_p * R * P_f := by
  unfold publishedMaskSupport
  have hFact : P_p * (P_f * F * P_f) * P_f = 0 := by
    calc
      _ = P_p * P_f * F * P_f * P_f := by noncomm_ring
      _ = 0 := by rw [hpf]; simp
  have hLogic : P_p * (P_l * G) * P_f = 0 := by
    calc
      _ = P_p * P_l * G * P_f := by noncomm_ring
      _ = 0 := by rw [hpl]; simp
  have hRoute : P_p * (P_p * R * P_f) * P_f = P_p * R * P_f := by
    calc
      _ = P_p * P_p * R * P_f * P_f := by noncomm_ring
      _ = P_p * R * P_f := by rw [hpp, mul_assoc, hff]
  have hPromptLogic : P_p * (P_p * S * P_l) * P_f = 0 := by
    calc
      _ = P_p * P_p * S * P_l * P_f := by noncomm_ring
      _ = 0 := by rw [hpp, mul_assoc, hlf]; simp
  have hPromptPrompt : P_p * (P_p * Q * P_p) * P_f = 0 := by
    calc
      _ = P_p * P_p * Q * P_p * P_f := by noncomm_ring
      _ = 0 := by rw [hpp, mul_assoc, hpf]; simp
  calc
    P_p * (P_f * F * P_f + P_l * G + P_p * R * P_f +
        P_p * S * P_l + P_p * Q * P_p) * P_f =
      P_p * (P_f * F * P_f) * P_f + P_p * (P_l * G) * P_f +
        P_p * (P_p * R * P_f) * P_f + P_p * (P_p * S * P_l) * P_f +
        P_p * (P_p * Q * P_p) * P_f := by noncomm_ring
    _ = P_p * R * P_f := by rw [hFact, hLogic, hRoute, hPromptLogic, hPromptPrompt]; abel

/-- Exact criterion for absence of the prompt-to-fact block in the published
support pattern. Orthogonality of the diagonal corners does not itself remove
this route; it vanishes precisely when its free block `R` is killed by the
outer corner projections. -/
theorem publishedMaskSupport_prompt_fact_block_eq_zero_iff
    {P_f P_l P_p F G R S Q : B}
    (hpf : P_p * P_f = 0) (hpl : P_p * P_l = 0)
    (hlf : P_l * P_f = 0) (hff : P_f * P_f = P_f)
    (hpp : P_p * P_p = P_p) :
    P_p * publishedMaskSupport P_f P_l P_p F G R S Q * P_f = 0 ↔
      P_p * R * P_f = 0 := by
  rw [publishedMaskSupport_prompt_fact_block hpf hpl hlf hff hpp]

end InfoGeometry.Routing.FactLogicBypassAlgebra
