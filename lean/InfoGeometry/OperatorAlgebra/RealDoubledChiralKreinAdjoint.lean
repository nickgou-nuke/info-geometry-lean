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
  simpa [chiralKreinAdjoint, ContinuousLinearMap.comp_apply] using
    congrArg (fun T : ChiralEnd (E := E) => T u)
      (etaChiral_involution (E := E))

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

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
