/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.DiracHodgeDoubledSpace

/-!
# Chiral Krein adjoint on the real doubled carrier

This owner deliberately uses `chiralKreinForm`, whose matrix is the cross-sheet
Witt metric.  It is therefore distinct from the canonical `KreinSpace`
adjoint, which uses the diagonal fundamental symmetry `spectral_epsilon`.
Only finite algebraic adjoint and isometry laws are recorded here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev ChiralEnd := DoubledSpace E →L[ℝ] DoubledSpace E

/-- Chiral Krein adjoint: `A♯ = R A† R` for the cross-sheet fundamental
symmetry `R = etaChiral`. -/
noncomputable def chiralKreinAdjoint (A : ChiralEnd (E := E)) : ChiralEnd (E := E) :=
  (etaChiral (E := E)).comp
    ((ContinuousLinearMap.adjoint A).comp (etaChiral (E := E)))

/-- The adjoint relation for the cross-sheet chiral Krein form. -/
def IsChiralKreinAdjoint (A B : ChiralEnd (E := E)) : Prop :=
  ∀ u v, chiralKreinForm (A u) v = chiralKreinForm u (B v)

/-- A chiral Krein-Hermitian operator is equal to its chiral Krein adjoint. -/
def IsChiralKreinHermitian (A : ChiralEnd (E := E)) : Prop :=
  IsChiralKreinAdjoint A A

/-- Equality-based form of J-Hermiticity. -/
def IsChiralKreinSelfAdjoint (A : ChiralEnd (E := E)) : Prop :=
  chiralKreinAdjoint A = A

/-- A chiral Krein-unitary operator preserves the cross-sheet form. -/
def IsChiralKreinUnitary (U : ChiralEnd (E := E)) : Prop :=
  ∀ u v, chiralKreinForm (U u) (U v) = chiralKreinForm u v

@[simp] theorem chiralKreinAdjoint_apply (A : ChiralEnd (E := E)) (u : H₂ (E := E)) :
    chiralKreinAdjoint A u =
      etaChiral ((ContinuousLinearMap.adjoint A) (etaChiral u)) := rfl

theorem etaChiral_hilbert_selfAdjoint (u v : H₂ (E := E)) :
    inner ℝ (etaChiral u) v = inner ℝ u (etaChiral v) := by
  simp [etaChiral, modular_j, WithLp.prod_inner_apply, real_inner_comm, add_comm]

theorem etaChiral_hilbert_isometry (u v : H₂ (E := E)) :
    inner ℝ (etaChiral u) (etaChiral v) = inner ℝ u v := by
  simp [etaChiral, modular_j, WithLp.prod_inner_apply, real_inner_comm, add_comm]

theorem etaChiral_eq_hilbert_adjoint :
    ContinuousLinearMap.adjoint (etaChiral (E := E)) = etaChiral (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (etaChiral_hilbert_selfAdjoint (E := E) u v).symm

theorem chiralKreinForm_eq_inner_eta (u v : H₂ (E := E)) :
    chiralKreinForm u v = inner ℝ (etaChiral u) v := by
  simp [chiralKreinForm, etaChiral, modular_j, WithLp.prod_inner_apply,
    real_inner_comm, add_comm]

theorem chiralKreinForm_kreinAdjoint (A : ChiralEnd (E := E)) (u v : H₂ (E := E)) :
    chiralKreinForm (A u) v =
      chiralKreinForm u (chiralKreinAdjoint A v) := by
  rw [chiralKreinForm_eq_inner_eta, chiralKreinForm_eq_inner_eta]
  rw [etaChiral_hilbert_selfAdjoint]
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [chiralKreinAdjoint_apply, etaChiral_hilbert_isometry]

theorem isChiralKreinSelfAdjoint_iff_form (A : ChiralEnd (E := E)) :
    IsChiralKreinSelfAdjoint A ↔ IsChiralKreinHermitian A := by
  constructor
  · intro h u v
    calc
      chiralKreinForm (A u) v =
          chiralKreinForm u (chiralKreinAdjoint A v) :=
            chiralKreinForm_kreinAdjoint A u v
      _ = chiralKreinForm u (A v) := by rw [h]
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_left ℝ
    intro u
    have hη (w : H₂ (E := E)) :
        etaChiral (etaChiral w) = w := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun T : ChiralEnd (E := E) => T w)
          (etaChiral_involution (E := E))
    calc
      inner ℝ u (chiralKreinAdjoint A v) =
          chiralKreinForm (etaChiral u) (chiralKreinAdjoint A v) := by
            rw [chiralKreinForm_eq_inner_eta, hη]
      _ = chiralKreinForm (A (etaChiral u)) v := by
            exact (chiralKreinForm_kreinAdjoint (A := A)
              (u := etaChiral u) (v := v)).symm
      _ = chiralKreinForm (etaChiral u) (A v) := h (etaChiral u) v
      _ = inner ℝ u (A v) := by
            rw [chiralKreinForm_eq_inner_eta, hη]

theorem isChiralKreinUnitary_iff_adjoint_comp_id (U : ChiralEnd (E := E)) :
    IsChiralKreinUnitary U ↔
      (chiralKreinAdjoint U).comp U =
        ContinuousLinearMap.id ℝ (H₂ (E := E)) := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_left ℝ
    intro u
    have hη (w : H₂ (E := E)) :
        etaChiral (etaChiral w) = w := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun T : ChiralEnd (E := E) => T w)
          (etaChiral_involution (E := E))
    calc
      inner ℝ u ((chiralKreinAdjoint U).comp U v) =
          chiralKreinForm (etaChiral u)
            ((chiralKreinAdjoint U).comp U v) := by
              rw [chiralKreinForm_eq_inner_eta, hη]
      _ = chiralKreinForm (U (etaChiral u)) (U v) := by
              exact (chiralKreinForm_kreinAdjoint (A := U)
                (u := etaChiral u) (v := U v)).symm
      _ = chiralKreinForm (etaChiral u) v := h (etaChiral u) v
      _ = inner ℝ u v := by
              rw [chiralKreinForm_eq_inner_eta, hη]
  · intro h u v
    calc
      chiralKreinForm (U u) (U v) =
          chiralKreinForm u (chiralKreinAdjoint U (U v)) :=
            chiralKreinForm_kreinAdjoint U u (U v)
      _ = chiralKreinForm u ((chiralKreinAdjoint U).comp U v) := rfl
      _ = chiralKreinForm u v := by rw [h]; rfl

@[simp] theorem chiralKreinAdjoint_id :
    chiralKreinAdjoint (ContinuousLinearMap.id ℝ (H₂ (E := E))) =
      ContinuousLinearMap.id ℝ (H₂ (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg (fun T : ChiralEnd (E := E) => T u)
    (etaChiral_involution (E := E))
  change etaChiral
      ((ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ (H₂ (E := E))))
        (etaChiral u)) = u
  rw [ContinuousLinearMap.adjoint_id]
  exact h

@[simp] theorem chiralKreinAdjoint_zero :
    chiralKreinAdjoint (0 : ChiralEnd (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp [chiralKreinAdjoint, ContinuousLinearMap.comp_apply]

@[simp] theorem chiralKreinAdjoint_add (A B : ChiralEnd (E := E)) :
    chiralKreinAdjoint (A + B) = chiralKreinAdjoint A + chiralKreinAdjoint B := by
  apply ContinuousLinearMap.ext
  intro u
  simp [chiralKreinAdjoint, ContinuousLinearMap.comp_apply]

@[simp] theorem chiralKreinAdjoint_smul (c : ℝ) (A : ChiralEnd (E := E)) :
    chiralKreinAdjoint (c • A) = c • chiralKreinAdjoint A := by
  apply ContinuousLinearMap.ext
  intro u
  simp [chiralKreinAdjoint, ContinuousLinearMap.comp_apply]

@[simp] theorem chiralKreinAdjoint_comp (A B : ChiralEnd (E := E)) :
    chiralKreinAdjoint (A.comp B) =
      (chiralKreinAdjoint B).comp (chiralKreinAdjoint A) := by
  apply ContinuousLinearMap.ext
  intro u
  have hη (w : H₂ (E := E)) :
      etaChiral (etaChiral w) = w := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : ChiralEnd (E := E) => T w)
        (etaChiral_involution (E := E))
  simp only [chiralKreinAdjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply]
  rw [hη]

theorem chiralKreinAdjoint_involutive (A : ChiralEnd (E := E)) :
    chiralKreinAdjoint (chiralKreinAdjoint A) = A := by
  apply ContinuousLinearMap.ext
  intro u
  have hη (w : H₂ (E := E)) :
      etaChiral (etaChiral w) = w := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : ChiralEnd (E := E) => T w)
        (etaChiral_involution (E := E))
  simp only [chiralKreinAdjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, etaChiral_eq_hilbert_adjoint,
    ContinuousLinearMap.comp_apply]
  exact congrArg A (hη u)

theorem chiralKreinSelfAdjoint_iff_adjoint_eq (A : ChiralEnd (E := E)) :
    IsChiralKreinSelfAdjoint A ↔ chiralKreinAdjoint A = A := Iff.rfl

theorem chiralKreinUnitary_comp (U V : ChiralEnd (E := E))
    (hU : IsChiralKreinUnitary U) (hV : IsChiralKreinUnitary V) :
    IsChiralKreinUnitary (U.comp V) := by
  intro u v
  exact hU (V u) (V v) |>.trans (hV u v)

/-- The sheet swap is chiral Krein-unitary. -/
theorem etaChiral_isChiralKreinUnitary :
    IsChiralKreinUnitary (etaChiral (E := E)) := by
  intro u v
  simp [IsChiralKreinUnitary, etaChiral, chiralKreinForm, modular_j,
    WithLp.prod_inner_apply, real_inner_comm, add_comm]

/-- The sheet flip is `J`-Hermitian for the cross-sheet Krein form. -/
theorem etaChiral_isChiralKreinHermitian :
    IsChiralKreinHermitian (etaChiral (E := E)) := by
  intro u v
  simp [IsChiralKreinAdjoint, chiralKreinForm, etaChiral, modular_j,
    WithLp.prod_inner_apply, real_inner_comm, add_comm]

/-- The sheet flip is simultaneously `J`-Hermitian and `J`-unitary. -/
theorem etaChiral_isChiralKreinHermitian_and_unitary :
    IsChiralKreinHermitian (etaChiral (E := E)) ∧
      IsChiralKreinUnitary (etaChiral (E := E)) := by
  exact ⟨etaChiral_isChiralKreinHermitian (E := E),
    etaChiral_isChiralKreinUnitary (E := E)⟩

/-- The doubled clock axis is Hermitian for the cross-sheet chiral form. -/
theorem clockAxis_isChiralKreinHermitian :
    IsChiralKreinHermitian (clockAxis (E := E)) := by
  intro u v
  simp [IsChiralKreinHermitian, IsChiralKreinAdjoint, clockAxis, complex_i,
    chiralKreinForm, modular_j, spectral_epsilon, WithLp.prod_inner_apply,
    real_inner_comm, add_comm, sub_eq_add_neg]

/-- The chiral grading is skew-Hermitian for the cross-sheet form. -/
theorem gamma5_isChiralKreinSkewHermitian :
    ∀ u v,
      chiralKreinForm ((gamma5 (E := E)) u) v =
        -chiralKreinForm u ((gamma5 (E := E)) v) := by
  intro u v
  simp [gamma5, chiralKreinForm, spectral_epsilon, WithLp.prod_inner_apply,
    real_inner_comm, add_comm, sub_eq_add_neg]

/-! ## The doubled complex-structure-shaped operator -/

theorem chiralComplexStructure_isChiralKreinAntiIsometry :
    ∀ u v,
      chiralKreinForm
          ((complex_i (E := E)) u)
          ((complex_i (E := E)) v) =
        -chiralKreinForm u v := by
  intro u v
  simp [complex_i, modular_j, spectral_epsilon, chiralKreinForm,
    WithLp.prod_inner_apply, real_inner_comm, add_comm, sub_eq_add_neg]

/-! ## Packet A: Krein-Adjoint Jordan–Lie Duality, Skew-Expectation Vanishing, and Peirce Corners -/

/-- A chiral Krein skew-adjoint operator satisfies `A♯ = -A`. -/
def IsChiralKreinSkewAdjoint (A : ChiralEnd (E := E)) : Prop :=
  chiralKreinAdjoint A = -A

@[simp] theorem chiralKreinAdjoint_neg (A : ChiralEnd (E := E)) :
    chiralKreinAdjoint (-A) = -chiralKreinAdjoint A := by
  apply ContinuousLinearMap.ext
  intro u
  simp [chiralKreinAdjoint]

@[simp] theorem chiralKreinAdjoint_sub (A B : ChiralEnd (E := E)) :
    chiralKreinAdjoint (A - B) = chiralKreinAdjoint A - chiralKreinAdjoint B := by
  rw [sub_eq_add_neg, chiralKreinAdjoint_add, chiralKreinAdjoint_neg, ← sub_eq_add_neg]

/-- Symmetry of the real cross-sheet chiral Krein bilinear form. -/
theorem chiralKreinForm_symm (u v : H₂ (E := E)) :
    chiralKreinForm u v = chiralKreinForm v u := by
  simp [chiralKreinForm, real_inner_comm, add_comm]

/-- Homayouni–Mingarelli Lemma 50(1a): if `A` and `B` are chiral-Krein self-adjoint, then
their Jordan anticommutator `A B + B A` is chiral-Krein self-adjoint. -/
theorem isChiralKreinSelfAdjoint_anticommutator {A B : ChiralEnd (E := E)}
    (hA : IsChiralKreinSelfAdjoint A) (hB : IsChiralKreinSelfAdjoint B) :
    IsChiralKreinSelfAdjoint (A.comp B + B.comp A) := by
  unfold IsChiralKreinSelfAdjoint at *
  rw [chiralKreinAdjoint_add, chiralKreinAdjoint_comp, chiralKreinAdjoint_comp, hA, hB, add_comm]

/-- Homayouni–Mingarelli Lemma 50(1b): if `A` and `B` are chiral-Krein self-adjoint, then
their Lie commutator `A B - B A` is chiral-Krein skew-adjoint. -/
theorem isChiralKreinSkewAdjoint_commutator {A B : ChiralEnd (E := E)}
    (hA : IsChiralKreinSelfAdjoint A) (hB : IsChiralKreinSelfAdjoint B) :
    IsChiralKreinSkewAdjoint (A.comp B - B.comp A) := by
  unfold IsChiralKreinSkewAdjoint IsChiralKreinSelfAdjoint at *
  rw [chiralKreinAdjoint_sub, chiralKreinAdjoint_comp, chiralKreinAdjoint_comp, hA, hB, neg_sub]

/-- Over `ℝ`, every chiral-Krein skew-adjoint operator has identically zero diagonal
Krein expectation `[K u, u] = 0`. -/
theorem chiralKreinForm_self_eq_zero_of_isChiralKreinSkewAdjoint
    {K : ChiralEnd (E := E)} (hK : IsChiralKreinSkewAdjoint K) (u : H₂ (E := E)) :
    chiralKreinForm (K u) u = 0 := by
  have h1 : chiralKreinForm (K u) u = -chiralKreinForm (K u) u := by
    calc
      chiralKreinForm (K u) u
          = chiralKreinForm u (chiralKreinAdjoint K u) := chiralKreinForm_kreinAdjoint K u u
      _ = chiralKreinForm u ((-K) u) := by rw [hK]
      _ = -chiralKreinForm u (K u) := by
            simp [chiralKreinForm, inner_neg_right, neg_add_rev, add_comm]
      _ = -chiralKreinForm (K u) u := by rw [chiralKreinForm_symm]
  linarith

/-- Homayouni–Mingarelli Lemma 50(2) over `ℝ`: for chiral-Krein self-adjoint `A, B`,
the commutator expectation `[[A, B] u, u]` vanishes identically. -/
theorem chiralKreinForm_commutator_self_eq_zero
    {A B : ChiralEnd (E := E)}
    (hA : IsChiralKreinSelfAdjoint A) (hB : IsChiralKreinSelfAdjoint B)
    (u : H₂ (E := E)) :
    chiralKreinForm ((A.comp B - B.comp A) u) u = 0 :=
  chiralKreinForm_self_eq_zero_of_isChiralKreinSkewAdjoint
    (isChiralKreinSkewAdjoint_commutator hA hB) u

/-- The chiral grading `γ₅` is skew-adjoint with respect to `chiralKreinAdjoint`. -/
@[simp] theorem chiralKreinAdjoint_gamma5 :
    chiralKreinAdjoint (gamma5 (E := E)) = -gamma5 (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  have hη (w : H₂ (E := E)) : etaChiral (etaChiral w) = w := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : ChiralEnd (E := E) => T w) (etaChiral_involution (E := E))
  calc
    inner ℝ u (chiralKreinAdjoint (gamma5 (E := E)) v)
        = chiralKreinForm (etaChiral u) (chiralKreinAdjoint (gamma5 (E := E)) v) := by
            rw [chiralKreinForm_eq_inner_eta, hη]
    _ = chiralKreinForm ((gamma5 (E := E)) (etaChiral u)) v :=
          (chiralKreinForm_kreinAdjoint (gamma5 (E := E)) (etaChiral u) v).symm
    _ = -chiralKreinForm (etaChiral u) ((gamma5 (E := E)) v) :=
          gamma5_isChiralKreinSkewHermitian (etaChiral u) v
    _ = -inner ℝ u ((gamma5 (E := E)) v) := by
          rw [chiralKreinForm_eq_inner_eta, hη]
    _ = inner ℝ u ((-gamma5 (E := E)) v) := by
          rw [neg_apply, inner_neg_right]

/-- The chiral Krein adjoint exchanges the left and right nullcone Peirce projectors. -/
@[simp] theorem chiralKreinAdjoint_leftChiralProjector :
    chiralKreinAdjoint (leftChiralProjector (E := E)) = rightChiralProjector (E := E) := by
  dsimp [leftChiralProjector, rightChiralProjector]
  rw [chiralKreinAdjoint_smul, chiralKreinAdjoint_add, chiralKreinAdjoint_id,
    chiralKreinAdjoint_gamma5, ← sub_eq_add_neg]

/-- The chiral Krein adjoint exchanges the right and left nullcone Peirce projectors. -/
@[simp] theorem chiralKreinAdjoint_rightChiralProjector :
    chiralKreinAdjoint (rightChiralProjector (E := E)) = leftChiralProjector (E := E) := by
  dsimp [leftChiralProjector, rightChiralProjector]
  rw [chiralKreinAdjoint_smul, chiralKreinAdjoint_sub, chiralKreinAdjoint_id,
    chiralKreinAdjoint_gamma5, sub_neg_eq_add]

/-- Chiral Peirce corner transformation under `chiralKreinAdjoint`:
diagonal corners `(P A P)` and `(Q A Q)` swap sectors, whereas off-diagonal nullcone corners
`(P A Q)` and `(Q A P)` are preserved in their respective corners. -/
theorem chiralKreinAdjoint_peirceCorners (A : ChiralEnd (E := E)) :
    let P := leftChiralProjector (E := E)
    let Q := rightChiralProjector (E := E)
    (chiralKreinAdjoint ((P.comp A).comp P) = (Q.comp (chiralKreinAdjoint A)).comp Q) ∧
    (chiralKreinAdjoint ((Q.comp A).comp Q) = (P.comp (chiralKreinAdjoint A)).comp P) ∧
    (chiralKreinAdjoint ((P.comp A).comp Q) = (P.comp (chiralKreinAdjoint A)).comp Q) ∧
    (chiralKreinAdjoint ((Q.comp A).comp P) = (Q.comp (chiralKreinAdjoint A)).comp P) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [chiralKreinAdjoint_comp, chiralKreinAdjoint_comp,
      chiralKreinAdjoint_leftChiralProjector, ContinuousLinearMap.comp_assoc]
  · rw [chiralKreinAdjoint_comp, chiralKreinAdjoint_comp,
      chiralKreinAdjoint_rightChiralProjector, ContinuousLinearMap.comp_assoc]
  · rw [chiralKreinAdjoint_comp, chiralKreinAdjoint_comp,
      chiralKreinAdjoint_leftChiralProjector, chiralKreinAdjoint_rightChiralProjector,
      ContinuousLinearMap.comp_assoc]
  · rw [chiralKreinAdjoint_comp, chiralKreinAdjoint_comp,
      chiralKreinAdjoint_leftChiralProjector, chiralKreinAdjoint_rightChiralProjector,
      ContinuousLinearMap.comp_assoc]

/-! ### Krein-Hilbert Norm Isometry, Majorant Inequality, and Centered Uncertainty Bound -/

/-- The fundamental symmetry `η_chiral = J ∘ γ₅` is a norm isometry on the real-doubled
chiral Hilbert space `H₂ (E := E)` (connecting the indefinite Krein form `[·, ·]_η` to its
associated majorant Hilbert norm `‖·‖`, Homayouni–Mingarelli `2103.04372v1.pdf`, Eq. 2.1). -/
@[simp]
theorem norm_etaChiral (u : H₂ (E := E)) :
    ‖etaChiral (E := E) u‖ = ‖u‖ := by
  have h1 : ‖etaChiral (E := E) u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      etaChiral_hilbert_isometry]
  have h2 : |‖etaChiral (E := E) u‖| = |‖u‖| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp h1
  simpa only [abs_norm] using h2

/-- **Krein-Hilbert Majorant / Cauchy–Schwarz Inequality**: the indefinite Krein inner
product `|[u, v]_η|` is dominated by the product of the majorant Hilbert norms `‖u‖ * ‖v‖`. -/
theorem abs_chiralKreinForm_le_norm (u v : H₂ (E := E)) :
    |chiralKreinForm u v| ≤ ‖u‖ * ‖v‖ := by
  calc
    |chiralKreinForm u v| = |inner ℝ (etaChiral (E := E) u) v| := by
      rw [chiralKreinForm_eq_inner_eta]
    _ ≤ ‖etaChiral (E := E) u‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ := by rw [norm_etaChiral]

/-- Centering two operators `A - a • I` and `B - b • I` by arbitrary real scalar shifts
leaves their commutator `[A, B]` invariant. -/
theorem centered_commutator_eq
    (A B : ChiralEnd (E := E)) (a b : ℝ) :
    let I := ContinuousLinearMap.id ℝ (H₂ (E := E))
    ((A - a • I).comp (B - b • I) - (B - b • I).comp (A - a • I)) =
      (A.comp B - B.comp A) := by
  intro I
  apply ContinuousLinearMap.ext
  intro u
  simp only [I, sub_apply, ContinuousLinearMap.comp_apply, map_sub,
    smul_apply, map_smul, ContinuousLinearMap.id_apply,
    smul_sub, smul_smul]
  rw [mul_comm b a]
  abel

/-- **Krein Commutator Expectation Expansion**: for two `η_chiral`-self-adjoint operators
`A, B`, the Krein expectation of their commutator `[u, (AB - BA) u]_η` equals the
antisymmetric Krein cross-pairing `[A u, B u]_η - [B u, A u]_η`. -/
theorem chiralKreinForm_commutator_etaChiral_eq
    {A B : ChiralEnd (E := E)}
    (hA : IsChiralKreinSelfAdjoint A)
    (hB : IsChiralKreinSelfAdjoint B)
    (u : H₂ (E := E)) :
    chiralKreinForm u ((A.comp B - B.comp A) u) =
      chiralKreinForm (A u) (B u) - chiralKreinForm (B u) (A u) := by
  have hsub :
      chiralKreinForm u ((A.comp B - B.comp A) u) =
        chiralKreinForm u (A (B u)) - chiralKreinForm u (B (A u)) := by
    rw [chiralKreinForm_eq_inner_eta, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      inner_sub_right, ← chiralKreinForm_eq_inner_eta, ← chiralKreinForm_eq_inner_eta]
  rw [hsub, ← (isChiralKreinSelfAdjoint_iff_form A).mp hA u (B u),
    ← (isChiralKreinSelfAdjoint_iff_form B).mp hB u (A u)]

/-- **Centered Robertson–Krein Commutator Uncertainty Bound**: for any two
`η_chiral`-self-adjoint operators `A, B`, any state `u`, and any scalar centering shifts
`a, b : ℝ` (in particular, the Krein expectations), the magnitude of the Krein commutator
expectation is bounded by `2 * ‖(A - a • I) u‖ * ‖(B - b • I) u‖` in the majorant Hilbert norm. -/
theorem chiralKreinForm_centered_uncertainty_bound
    {A B : ChiralEnd (E := E)}
    (hA : IsChiralKreinSelfAdjoint A)
    (hB : IsChiralKreinSelfAdjoint B)
    (a b : ℝ) (u : H₂ (E := E)) :
    let I := ContinuousLinearMap.id ℝ (H₂ (E := E))
    |chiralKreinForm u ((A.comp B - B.comp A) u)| ≤
      2 * ‖(A - a • I) u‖ * ‖(B - b • I) u‖ := by
  intro I
  set A' : ChiralEnd (E := E) := A - a • I
  set B' : ChiralEnd (E := E) := B - b • I
  have hA' : IsChiralKreinSelfAdjoint A' := by
    rw [IsChiralKreinSelfAdjoint, chiralKreinAdjoint_sub, chiralKreinAdjoint_smul,
      chiralKreinAdjoint_id, hA]
  have hB' : IsChiralKreinSelfAdjoint B' := by
    rw [IsChiralKreinSelfAdjoint, chiralKreinAdjoint_sub, chiralKreinAdjoint_smul,
      chiralKreinAdjoint_id, hB]
  have hcomm : A.comp B - B.comp A = A'.comp B' - B'.comp A' :=
    (centered_commutator_eq A B a b).symm
  rw [hcomm, chiralKreinForm_commutator_etaChiral_eq hA' hB' u]
  have h1 : |chiralKreinForm (A' u) (B' u)| ≤ ‖A' u‖ * ‖B' u‖ :=
    abs_chiralKreinForm_le_norm (A' u) (B' u)
  have h2 : |chiralKreinForm (B' u) (A' u)| ≤ ‖B' u‖ * ‖A' u‖ :=
    abs_chiralKreinForm_le_norm (B' u) (A' u)
  calc
    |chiralKreinForm (A' u) (B' u) - chiralKreinForm (B' u) (A' u)|
        ≤ |chiralKreinForm (A' u) (B' u)| + |chiralKreinForm (B' u) (A' u)| :=
      abs_sub _ _
    _ ≤ ‖A' u‖ * ‖B' u‖ + ‖B' u‖ * ‖A' u‖ := add_le_add h1 h2
    _ = 2 * ‖A' u‖ * ‖B' u‖ := by ring

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
