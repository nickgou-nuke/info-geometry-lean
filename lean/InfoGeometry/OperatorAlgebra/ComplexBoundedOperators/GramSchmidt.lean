import Mathlib
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.VSConnect

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GramSchmidt

Lean-native finite-complex owner surface for the AFP
`Jordan_Normal_Form.Gram_Schmidt` corridor.

The AFP development works with a custom carrier-vector type and a locale
connecting those vectors to an abstract vector-space library.  In Lean, the
finite carrier `ι → ℂ` already has the required module structure, so the
VS-connect layer is represented by `listSpan` and its basic monotonicity and
membership lemmas.

This file formalizes the executable Gram-Schmidt spine with conjugate dot
products:

* list-level conjugate orthogonality,
* the projection `adjuster`,
* the accumulator and no-reversal formulations of Gram-Schmidt,
* the code equation connecting both formulations,
* witness-gated result packets for the full AFP correctness surface.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GramSchmidt

open scoped BigOperators

/-! ## Conjugate-orthogonality -/

/-- Ordinary dot product from the finite complex JNF core. -/
abbrev dot {ι : Type*} [Fintype ι] (v w : ι → ℂ) : ℂ :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.dot v w

/-- Hermitian/conjugate dot product, conjugate-linear in the first argument. -/
abbrev cDot {ι : Type*} [Fintype ι] (v w : ι → ℂ) : ℂ :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.cDot v w

/--
AFP `corthogonal`: vectors are pairwise conjugate-orthogonal, and each vector
has nonzero Hermitian norm.
-/
def Corthogonal {ι : Type*} [Fintype ι] (vs : List (ι → ℂ)) : Prop :=
  ∀ (i j : Nat) (hi : i < vs.length) (hj : j < vs.length),
    cDot (vs.get ⟨i, hi⟩) (vs.get ⟨j, hj⟩) = 0 ↔ i ≠ j

/-- Elimination form of `Corthogonal`, matching AFP `corthogonalD`. -/
theorem corthogonalD {ι : Type*} [Fintype ι] {vs : List (ι → ℂ)}
    (h : Corthogonal vs) {i j : Nat} (hi : i < vs.length) (hj : j < vs.length) :
    cDot (vs.get ⟨i, hi⟩) (vs.get ⟨j, hj⟩) = 0 ↔ i ≠ j :=
  h i j hi hj

/-- Introduction form of `Corthogonal`, matching AFP `corthogonalI`. -/
theorem corthogonalI {ι : Type*} [Fintype ι] {vs : List (ι → ℂ)}
    (h : ∀ (i j : Nat) (hi : i < vs.length) (hj : j < vs.length),
      cDot (vs.get ⟨i, hi⟩) (vs.get ⟨j, hj⟩) = 0 ↔ i ≠ j) :
    Corthogonal vs :=
  h

@[simp]
theorem corthogonal_nil {ι : Type*} [Fintype ι] :
    Corthogonal ([] : List (ι → ℂ)) := by
  intro i _ hi _
  exact (Nat.not_lt_zero i hi).elim

/-- Tail closure of list-level conjugate orthogonality. -/
theorem corthogonal_tail {ι : Type*} [Fintype ι]
    {u : ι → ℂ} {us : List (ι → ℂ)}
    (h : Corthogonal (u :: us)) :
    Corthogonal us := by
  intro i j hi hj
  simpa using h (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj)

/-! ## VS-connect style list spans -/

/-- Span of the vectors contained in a list. -/
def listSpan {ι : Type*} [Fintype ι] (vs : List (ι → ℂ)) :
    Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ {v | v ∈ vs}

/-- Any vector in the list belongs to its `listSpan`. -/
theorem mem_listSpan_of_mem {ι : Type*} [Fintype ι]
    {v : ι → ℂ} {vs : List (ι → ℂ)} (hv : v ∈ vs) :
    v ∈ listSpan vs :=
  Submodule.subset_span hv

/-- Monotonicity of `listSpan` under list-membership inclusion. -/
theorem listSpan_mono {ι : Type*} [Fintype ι]
    {vs ws : List (ι → ℂ)}
    (h : ∀ v : ι → ℂ, v ∈ vs → v ∈ ws) :
    listSpan vs ≤ listSpan ws :=
  Submodule.span_mono (by
    intro v hv
    exact h v hv)

@[simp]
theorem listSpan_nil {ι : Type*} [Fintype ι] :
    listSpan ([] : List (ι → ℂ)) = ⊥ := by
  ext v
  simp [listSpan]

/-- A list span is unchanged by replacing the list with an extensionally equal set. -/
theorem listSpan_ext {ι : Type*} [Fintype ι]
    {vs ws : List (ι → ℂ)}
    (h : ∀ v : ι → ℂ, v ∈ vs ↔ v ∈ ws) :
    listSpan vs = listSpan ws := by
  exact le_antisymm
    (listSpan_mono (fun v hv => (h v).1 hv))
    (listSpan_mono (fun v hv => (h v).2 hv))

/-! ## Gram-Schmidt executable spine -/

/-- AFP `adjuster`: sum of projections removing components along `us`. -/
def adjuster {ι : Type*} [Fintype ι]
    (w : ι → ℂ) : List (ι → ℂ) → ι → ℂ
  | [] => 0
  | u :: us => (-(cDot w u) / cDot u u) • u + adjuster w us

@[simp]
theorem adjuster_nil {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    adjuster w [] = 0 :=
  rfl

@[simp]
theorem adjuster_cons {ι : Type*} [Fintype ι]
    (w u : ι → ℂ) (us : List (ι → ℂ)) :
    adjuster w (u :: us) = (-(cDot w u) / cDot u u) • u + adjuster w us :=
  rfl

/-- The adjustment vector is in the span of the vectors it adjusts against. -/
theorem adjuster_mem_listSpan {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (us : List (ι → ℂ)) :
    adjuster w us ∈ listSpan us := by
  induction us with
  | nil =>
      simp [adjuster]
  | cons u us ih =>
      have hu : u ∈ listSpan (u :: us) :=
        mem_listSpan_of_mem (by simp)
      have hus : adjuster w us ∈ listSpan (u :: us) :=
        listSpan_mono (vs := us) (ws := u :: us) (by
          intro v hv
          simp [hv]) ih
      simpa [adjuster] using
        (Submodule.add_mem (listSpan (u :: us))
          (Submodule.smul_mem (listSpan (u :: us)) (-(cDot w u) / cDot u u) hu)
          hus)

/-- The adjusted vector lies in the span of the original vector and the prior list. -/
theorem adjusted_mem_cons_span {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (us : List (ι → ℂ)) :
    adjuster w us + w ∈ listSpan (w :: us) := by
  have ha : adjuster w us ∈ listSpan (w :: us) :=
    listSpan_mono (vs := us) (ws := w :: us) (by
      intro v hv
      simp [hv]) (adjuster_mem_listSpan w us)
  have hw : w ∈ listSpan (w :: us) :=
    mem_listSpan_of_mem (by simp)
  exact Submodule.add_mem (listSpan (w :: us)) ha hw

/-- AFP accumulator formulation. -/
def gramSchmidtSub {ι : Type*} [Fintype ι]
    (us : List (ι → ℂ)) : List (ι → ℂ) → List (ι → ℂ)
  | [] => us
  | w :: ws => gramSchmidtSub ((adjuster w us + w) :: us) ws

/-- AFP public algorithm: reverse the accumulator formulation. -/
def gramSchmidt {ι : Type*} [Fintype ι]
    (ws : List (ι → ℂ)) : List (ι → ℂ) :=
  (gramSchmidtSub [] ws).reverse

/-- AFP no-reversal formulation. -/
def gramSchmidtSub2 {ι : Type*} [Fintype ι]
    (us : List (ι → ℂ)) : List (ι → ℂ) → List (ι → ℂ)
  | [] => []
  | w :: ws =>
      let u := adjuster w us + w
      u :: gramSchmidtSub2 (u :: us) ws

@[simp]
theorem gramSchmidtSub_nil {ι : Type*} [Fintype ι] (us : List (ι → ℂ)) :
    gramSchmidtSub us [] = us :=
  rfl

@[simp]
theorem gramSchmidtSub_cons {ι : Type*} [Fintype ι]
    (us : List (ι → ℂ)) (w : ι → ℂ) (ws : List (ι → ℂ)) :
    gramSchmidtSub us (w :: ws) =
      gramSchmidtSub ((adjuster w us + w) :: us) ws :=
  rfl

@[simp]
theorem gramSchmidtSub2_nil {ι : Type*} [Fintype ι] (us : List (ι → ℂ)) :
    gramSchmidtSub2 us [] = [] :=
  rfl

@[simp]
theorem gramSchmidtSub2_cons {ι : Type*} [Fintype ι]
    (us : List (ι → ℂ)) (w : ι → ℂ) (ws : List (ι → ℂ)) :
    gramSchmidtSub2 us (w :: ws) =
      let u := adjuster w us + w
      u :: gramSchmidtSub2 (u :: us) ws :=
  rfl

/-- The accumulator and no-reversal formulations agree. -/
theorem gramSchmidtSub_eq {ι : Type*} [Fintype ι]
    (us ws : List (ι → ℂ)) :
    (gramSchmidtSub us ws).reverse = us.reverse ++ gramSchmidtSub2 us ws := by
  induction ws generalizing us with
  | nil =>
      simp [gramSchmidtSub, gramSchmidtSub2]
  | cons w ws ih =>
      simp [gramSchmidtSub, gramSchmidtSub2, ih, List.append_assoc]

/-- Code equation matching AFP `gram_schmidt_code`. -/
theorem gramSchmidt_code {ι : Type*} [Fintype ι]
    (ws : List (ι → ℂ)) :
    gramSchmidt ws = gramSchmidtSub2 [] ws := by
  simp [gramSchmidt, gramSchmidtSub_eq]

@[simp]
theorem gramSchmidt_nil {ι : Type*} [Fintype ι] :
    gramSchmidt ([] : List (ι → ℂ)) = [] := by
  simp [gramSchmidt_code]

/-- The first vector is preserved by the no-reversal/public formulation. -/
@[simp]
theorem gramSchmidt_head? {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (ws : List (ι → ℂ)) :
    (gramSchmidt (w :: ws)).head? = some w := by
  rw [gramSchmidt_code]
  simp [gramSchmidtSub2, adjuster]

/-- Gram-Schmidt preserves list length. -/
theorem gramSchmidtSub2_length {ι : Type*} [Fintype ι]
    (us ws : List (ι → ℂ)) :
    (gramSchmidtSub2 us ws).length = ws.length := by
  induction ws generalizing us with
  | nil =>
      simp [gramSchmidtSub2]
  | cons w ws ih =>
      simp [gramSchmidtSub2, ih]

@[simp]
theorem gramSchmidt_length {ι : Type*} [Fintype ι]
    (ws : List (ι → ℂ)) :
    (gramSchmidt ws).length = ws.length := by
  rw [gramSchmidt_code]
  exact gramSchmidtSub2_length [] ws

/-! ## witness-gated (Native Closure Mandated: Closure Debt) AFP correctness surface -/

/--
Certified output of Gram-Schmidt for a list of finite complex vectors.

The algorithmic field pins `output` to `gramSchmidt input`; the remaining fields
are explicit witnesses for the AFP theorem surface: same span, conjugate
orthogonality, preserved length, and distinct output.
-/
structure GramSchmidtResult {ι : Type*} [Fintype ι]
    (input output : List (ι → ℂ)) : Prop where
  /-- The output is the executable Gram-Schmidt output. -/
  output_eq : output = gramSchmidt input
  /-- The output spans the same subspace as the input. -/
  span_eq : listSpan input = listSpan output
  /-- Output vectors are conjugate-orthogonal. -/
  corthogonal : Corthogonal output
  /-- Output length agrees with input length. -/
  length_eq : output.length = input.length
  /-- The output list has no repeated vectors. -/
  nodup : output.Nodup

/-- A bundled version of `GramSchmidtResult`. -/
structure GramSchmidtPacket {ι : Type*} [Fintype ι]
    (input : List (ι → ℂ)) where
  /-- Certified output list. -/
  output : List (ι → ℂ)
  /-- AFP result witnesses for the output. -/
  result : GramSchmidtResult input output

namespace GramSchmidtResult

variable {ι : Type*} [Fintype ι]
variable {input output : List (ι → ℂ)}

theorem algorithm (R : GramSchmidtResult input output) :
    output = gramSchmidt input :=
  R.output_eq

theorem span (R : GramSchmidtResult input output) :
    listSpan input = listSpan output :=
  R.span_eq

theorem orthogonal (R : GramSchmidtResult input output) :
    Corthogonal output :=
  R.corthogonal

theorem length (R : GramSchmidtResult input output) :
    output.length = input.length :=
  R.length_eq

theorem distinct (R : GramSchmidtResult input output) :
    output.Nodup :=
  R.nodup

end GramSchmidtResult

/--
Projection theorem corresponding to AFP `gram_schmidt_result`: once a
`GramSchmidtPacket` is supplied, the theorem surface is available without
reopening the packet internals.
-/
theorem gramSchmidt_result {ι : Type*} [Fintype ι]
    {input : List (ι → ℂ)} (P : GramSchmidtPacket input) :
    listSpan input = listSpan P.output ∧
      Corthogonal P.output ∧
      P.output.length = input.length ∧
      P.output.Nodup := by
  exact ⟨P.result.span_eq, P.result.corthogonal, P.result.length_eq, P.result.nodup⟩

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GramSchmidt
