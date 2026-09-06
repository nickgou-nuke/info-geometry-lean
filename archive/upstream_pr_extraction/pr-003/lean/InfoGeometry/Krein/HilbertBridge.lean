import InfoGeometry.Clifford.Cl11
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Diagonal Krein pairing on `E × E`: `[u,v] = ⟪u₁,v₁⟫ - ⟪u₂,v₂⟫`. -/
def kreinInner (u v : DoubledSpace E) : ℝ :=
  inner ℝ u.1 v.1 - inner ℝ u.2 v.2

/-- Fundamental symmetry `η(x,y) = (x,-y)` for the doubled model. -/
def fundamentalSymmetry : DoubledSpace E →L[ℝ] DoubledSpace E :=
  spectralEpsilon (E := E)

@[simp] lemma fundamentalSymmetry_apply (u : DoubledSpace E) :
    fundamentalSymmetry (E := E) u = (u.1, -u.2) := rfl

@[simp] lemma fundamentalSymmetry_involutive (u : DoubledSpace E) :
    fundamentalSymmetry (E := E) (fundamentalSymmetry (E := E) u) = u := by
  rcases u with ⟨x, y⟩
  simp [fundamentalSymmetry, spectralEpsilon]

@[simp] lemma fundamentalSymmetry_comp :
    (fundamentalSymmetry (E := E)).comp (fundamentalSymmetry (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  simpa [fundamentalSymmetry] using spectralEpsilon_involution (E := E)

/-- Krein-adjoint relation against `kreinInner`. -/
def IsKreinAdjointCLM
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  ∀ u v, kreinInner (E := E) (A u) v = kreinInner (E := E) u (B v)

/-- Krein self-adjointness against `kreinInner`. -/
def IsKreinSelfAdjointCLM
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  IsKreinAdjointCLM (E := E) A A

/-- Krein skew-adjointness against `kreinInner`. -/
def IsKreinSkewAdjointCLM
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  ∀ u v, kreinInner (E := E) (A u) v = -kreinInner (E := E) u (A v)

lemma fundamentalSymmetry_isKreinSelfAdjoint :
    IsKreinSelfAdjointCLM (E := E) (fundamentalSymmetry (E := E)) := by
  unfold IsKreinSelfAdjointCLM IsKreinAdjointCLM
  intro u v
  rcases u with ⟨x, ξ⟩
  rcases v with ⟨y, η⟩
  simp [kreinInner, fundamentalSymmetry, spectralEpsilon, sub_eq_add_neg]

lemma modularJ_isKreinSkewAdjoint :
    IsKreinSkewAdjointCLM (E := E) (modularJ (E := E)) := by
  unfold IsKreinSkewAdjointCLM
  intro u v
  rcases u with ⟨x, ξ⟩
  rcases v with ⟨y, η⟩
  simp [kreinInner, modularJ, sub_eq_add_neg]

lemma complexI_isKreinSelfAdjoint :
    IsKreinSelfAdjointCLM (E := E) (complexI (E := E)) := by
  unfold IsKreinSelfAdjointCLM IsKreinAdjointCLM
  intro u v
  rcases u with ⟨x, ξ⟩
  rcases v with ⟨y, η⟩
  simp [kreinInner, complexI, modularJ, spectralEpsilon, sub_eq_add_neg]
  ring

end KreinClifford

section KreinCliffordWithLp

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

instance withLpTwoFact : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-- Hilbert carrier for doubled states: `WithLp 2 (E × E)`. -/
abbrev HilbertDoubled (E : Type) := WithLp (2 : ENNReal) (DoubledSpace E)

/-- Canonical continuous linear equivalence `WithLp 2 (E × E) ≃L E × E`. -/
noncomputable def doubledToHilbertEquiv :
    HilbertDoubled E ≃L[ℝ] DoubledSpace E :=
  WithLp.prodContinuousLinearEquiv (p := (2 : ENNReal)) ℝ E E

@[simp] lemma doubledToHilbertEquiv_apply (u : HilbertDoubled E) :
    doubledToHilbertEquiv (E := E) u = WithLp.ofLp u := rfl

@[simp] lemma doubledToHilbertEquiv_symm_apply (u : DoubledSpace E) :
    (doubledToHilbertEquiv (E := E)).symm u = WithLp.toLp (2 : ENNReal) u := by
  rw [doubledToHilbertEquiv]
  exact WithLp.prodContinuousLinearEquiv_symm_apply
    (p := (2 : ENNReal)) (𝕜 := ℝ) (α := E) (β := E) u

/-- Transport an operator on `E × E` to the Hilbert carrier `WithLp 2 (E × E)`. -/
noncomputable def transportToHilbert
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  ((doubledToHilbertEquiv (E := E)).symm : DoubledSpace E →L[ℝ] HilbertDoubled E).comp
    (A.comp ((doubledToHilbertEquiv (E := E)) : HilbertDoubled E →L[ℝ] DoubledSpace E))

@[simp] lemma transportToHilbert_apply
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) (u : HilbertDoubled E) :
    transportToHilbert (E := E) A u
      = (doubledToHilbertEquiv (E := E)).symm (A ((doubledToHilbertEquiv (E := E)) u)) := rfl

lemma transportToHilbert_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    transportToHilbert (E := E) (A.comp B)
      = (transportToHilbert (E := E) A).comp (transportToHilbert (E := E) B) := by
  ext u
  rfl

/-- Transported `J` on the Hilbert carrier. -/
noncomputable def modularJH : HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  transportToHilbert (E := E) (modularJ (E := E))

/-- Transported `ε` on the Hilbert carrier. -/
noncomputable def spectralEpsilonH : HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  transportToHilbert (E := E) (spectralEpsilon (E := E))

/-- Transported `I = J ∘ ε` on the Hilbert carrier. -/
noncomputable def complexIH : HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  transportToHilbert (E := E) (complexI (E := E))

@[simp] lemma modularJH_apply (u : HilbertDoubled E) :
    modularJH (E := E) u
      = WithLp.toLp (2 : ENNReal) ((WithLp.ofLp u).2, (WithLp.ofLp u).1) := by
  simp [modularJH, transportToHilbert, modularJ]

@[simp] lemma spectralEpsilonH_apply (u : HilbertDoubled E) :
    spectralEpsilonH (E := E) u
      = WithLp.toLp (2 : ENNReal) ((WithLp.ofLp u).1, -(WithLp.ofLp u).2) := by
  simp [spectralEpsilonH, transportToHilbert, spectralEpsilon]

@[simp] lemma complexIH_apply (u : HilbertDoubled E) :
    complexIH (E := E) u
      = WithLp.toLp (2 : ENNReal) (-(WithLp.ofLp u).2, (WithLp.ofLp u).1) := by
  simp [complexIH, transportToHilbert, complexI, modularJ, spectralEpsilon]

/-- Fundamental symmetry on the Hilbert carrier. -/
noncomputable def fundamentalSymmetryH : HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  spectralEpsilonH (E := E)

/-- Krein pairing on the Hilbert carrier. -/
def kreinInnerH (u v : HilbertDoubled E) : ℝ :=
  inner ℝ (WithLp.ofLp u).1 (WithLp.ofLp v).1 -
    inner ℝ (WithLp.ofLp u).2 (WithLp.ofLp v).2

@[simp] lemma kreinInnerH_eq_inner_fundamentalSymmetryH
    (u v : HilbertDoubled E) :
    kreinInnerH (E := E) u v = inner ℝ (fundamentalSymmetryH (E := E) u) v := by
  simp [kreinInnerH, fundamentalSymmetryH, spectralEpsilonH_apply, sub_eq_add_neg,
    WithLp.prod_inner_apply (𝕜 := ℝ) (E := E) (F := E)]

section Adjoint

variable [CompleteSpace E]

@[simp] lemma fundamentalSymmetryH_adjoint :
    ContinuousLinearMap.adjoint (fundamentalSymmetryH (E := E))
      = fundamentalSymmetryH (E := E) := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := fundamentalSymmetryH (E := E))
    (B := fundamentalSymmetryH (E := E))).2 ?_
  intro u v
  have hL :
      inner ℝ (fundamentalSymmetryH (E := E) u) v
        = inner ℝ (WithLp.ofLp u).1 (WithLp.ofLp v).1 -
            inner ℝ (WithLp.ofLp u).2 (WithLp.ofLp v).2 := by
      simp [fundamentalSymmetryH, spectralEpsilonH_apply, sub_eq_add_neg,
        WithLp.prod_inner_apply (𝕜 := ℝ) (E := E) (F := E)]
  have hR :
      inner ℝ u (fundamentalSymmetryH (E := E) v)
        = inner ℝ (WithLp.ofLp u).1 (WithLp.ofLp v).1 -
            inner ℝ (WithLp.ofLp u).2 (WithLp.ofLp v).2 := by
      simp [fundamentalSymmetryH, spectralEpsilonH_apply, sub_eq_add_neg,
        WithLp.prod_inner_apply (𝕜 := ℝ) (E := E) (F := E)]
  exact hL.trans hR.symm

omit [CompleteSpace E] in
@[simp] lemma fundamentalSymmetryH_sq :
    (fundamentalSymmetryH (E := E)) * (fundamentalSymmetryH (E := E))
      = (1 : HilbertDoubled E →L[ℝ] HilbertDoubled E) := by
  calc
    (fundamentalSymmetryH (E := E)).comp (fundamentalSymmetryH (E := E))
        = transportToHilbert (E := E)
            ((spectralEpsilon (E := E)).comp (spectralEpsilon (E := E))) := by
              simpa [fundamentalSymmetryH, spectralEpsilonH] using
                (transportToHilbert_comp (E := E)
                  (A := spectralEpsilon (E := E))
                  (B := spectralEpsilon (E := E))).symm
    _ = transportToHilbert (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
          simp [spectralEpsilon_involution (E := E)]
    _ = ContinuousLinearMap.id ℝ (HilbertDoubled E) := by
          ext u
          simp [transportToHilbert]

omit [CompleteSpace E] in
@[simp] lemma fundamentalSymmetryH_involutive (u : HilbertDoubled E) :
    fundamentalSymmetryH (E := E) (fundamentalSymmetryH (E := E) u) = u := by
  have hsq := congrArg
    (fun T : HilbertDoubled E →L[ℝ] HilbertDoubled E => T u)
    (fundamentalSymmetryH_sq (E := E))
  convert hsq using 1

lemma inner_fundamentalSymmetryH_left (u v : HilbertDoubled E) :
    inner ℝ (fundamentalSymmetryH (E := E) u) v
      = inner ℝ u (fundamentalSymmetryH (E := E) v) := by
  simpa [fundamentalSymmetryH_adjoint (E := E)] using
    (ContinuousLinearMap.adjoint_inner_left
      (A := fundamentalSymmetryH (E := E)) (x := v) (y := u))

lemma inner_fundamentalSymmetryH_fundamentalSymmetryH
    (u v : HilbertDoubled E) :
    inner ℝ (fundamentalSymmetryH (E := E) u) (fundamentalSymmetryH (E := E) v)
      = inner ℝ u v := by
  have h := (ContinuousLinearMap.adjoint_inner_left
    (A := fundamentalSymmetryH (E := E))
    (x := v) (y := fundamentalSymmetryH (E := E) u))
  calc
    inner ℝ (fundamentalSymmetryH (E := E) u) (fundamentalSymmetryH (E := E) v)
        = inner ℝ
            ((ContinuousLinearMap.adjoint (fundamentalSymmetryH (E := E)))
              (fundamentalSymmetryH (E := E) u)) v := by
              simpa using h.symm
    _ = inner ℝ (fundamentalSymmetryH (E := E) (fundamentalSymmetryH (E := E) u)) v := by
          simp [fundamentalSymmetryH_adjoint (E := E)]
    _ = inner ℝ u v := by
          simp [fundamentalSymmetryH, spectralEpsilonH_apply]

/-- Krein adjoint on the Hilbert carrier: `A♯ = η ∘ A† ∘ η`. -/
noncomputable def kreinAdjointH
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  (fundamentalSymmetryH (E := E)).comp
    ((ContinuousLinearMap.adjoint A).comp (fundamentalSymmetryH (E := E)))

/-- Krein-adjoint relation with respect to `kreinInnerH`. -/
def IsKreinAdjointH
    (A B : HilbertDoubled E →L[ℝ] HilbertDoubled E) : Prop :=
  ∀ u v, kreinInnerH (E := E) (A u) v = kreinInnerH (E := E) u (B v)

lemma kreinAdjointH_isKreinAdjoint
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    IsKreinAdjointH (E := E) A (kreinAdjointH (E := E) A) := by
  intro u v
  calc
    kreinInnerH (E := E) (A u) v
        = inner ℝ (fundamentalSymmetryH (E := E) (A u)) v := by
            exact kreinInnerH_eq_inner_fundamentalSymmetryH (E := E) (A u) v
    _ = inner ℝ (A u) (fundamentalSymmetryH (E := E) v) := by
          exact inner_fundamentalSymmetryH_left (E := E) (A u) v
    _ = inner ℝ u ((ContinuousLinearMap.adjoint A) (fundamentalSymmetryH (E := E) v)) := by
          exact (ContinuousLinearMap.adjoint_inner_right (A := A) (x := u)
            (y := fundamentalSymmetryH (E := E) v)).symm
    _ = inner ℝ (fundamentalSymmetryH (E := E) u)
          (fundamentalSymmetryH (E := E)
            ((ContinuousLinearMap.adjoint A) (fundamentalSymmetryH (E := E) v))) := by
          exact (inner_fundamentalSymmetryH_fundamentalSymmetryH (E := E) u
            ((ContinuousLinearMap.adjoint A) (fundamentalSymmetryH (E := E) v))).symm
    _ = inner ℝ (fundamentalSymmetryH (E := E) u)
          ((kreinAdjointH (E := E) A) v) := by
            simp [kreinAdjointH, fundamentalSymmetryH]
    _ = kreinInnerH (E := E) u ((kreinAdjointH (E := E) A) v) := by
          exact (kreinInnerH_eq_inner_fundamentalSymmetryH (E := E) u
            ((kreinAdjointH (E := E) A) v)).symm

lemma isKreinAdjointH_self_iff_adjoint
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    IsKreinAdjointH (E := E) A A ↔
      A = (fundamentalSymmetryH (E := E)).comp
        ((ContinuousLinearMap.adjoint A).comp (fundamentalSymmetryH (E := E)) ) := by
  let η : HilbertDoubled E →L[ℝ] HilbertDoubled E := fundamentalSymmetryH (E := E)
  constructor
  · intro hSelf
    have hsym : ∀ u v, inner ℝ ((η.comp A) u) v = inner ℝ u ((η.comp A) v) := by
      intro u v
      have hk : kreinInnerH (E := E) (A u) v = kreinInnerH (E := E) u (A v) := hSelf u v
      have hk' : inner ℝ (η (A u)) v = inner ℝ (η u) (A v) := by
        simpa [η, kreinInnerH_eq_inner_fundamentalSymmetryH (E := E)] using hk
      calc
        inner ℝ ((η.comp A) u) v = inner ℝ (η (A u)) v := by rfl
        _ = inner ℝ (η u) (A v) := hk'
        _ = inner ℝ u (η (A v)) := inner_fundamentalSymmetryH_left (E := E) u (A v)
        _ = inner ℝ u ((η.comp A) v) := by rfl
    have hEtaA : η.comp A = ContinuousLinearMap.adjoint (η.comp A) :=
      (ContinuousLinearMap.eq_adjoint_iff (A := η.comp A) (B := η.comp A)).2 hsym
    have hComm : η.comp A = (ContinuousLinearMap.adjoint A).comp η := by
      calc
        η.comp A = ContinuousLinearMap.adjoint (η.comp A) := hEtaA
        _ = (ContinuousLinearMap.adjoint A).comp (ContinuousLinearMap.adjoint η) := by
              exact (ContinuousLinearMap.adjoint_comp (A := η) (B := A))
        _ = (ContinuousLinearMap.adjoint A).comp η := by
              simp [η, fundamentalSymmetryH_adjoint (E := E)]
    ext u
    have hu : η (A u) = (ContinuousLinearMap.adjoint A) (η u) := by
      simpa [ContinuousLinearMap.comp_apply] using congrArg (fun f => f u) hComm
    calc
      A u = η (η (A u)) := by
              simp [η]
      _ = η ((ContinuousLinearMap.adjoint A) (η u)) := by
            exact congrArg η hu
      _ = (η.comp ((ContinuousLinearMap.adjoint A).comp η)) u := by
            rfl
  · intro hA u v
    have hηA : η (A v) = (ContinuousLinearMap.adjoint A) (η v) := by
      have hv : A v = η ((ContinuousLinearMap.adjoint A) (η v)) := by
        simpa [η, ContinuousLinearMap.comp_apply] using congrArg (fun f => f v) hA
      simpa [η] using congrArg η hv
    calc
      kreinInnerH (E := E) (A u) v = inner ℝ (η (A u)) v := by
          simp [η]
      _ = inner ℝ (A u) (η v) := by
            exact inner_fundamentalSymmetryH_left (E := E) (A u) v
      _ = inner ℝ u ((ContinuousLinearMap.adjoint A) (η v)) := by
            exact (ContinuousLinearMap.adjoint_inner_right (A := A) (x := u) (y := η v)).symm
      _ = inner ℝ u (η (A v)) := by
            rw [← hηA]
      _ = inner ℝ (η u) (A v) := by
            exact (inner_fundamentalSymmetryH_left (E := E) u (A v)).symm
      _ = kreinInnerH (E := E) u (A v) := by
            simp [η]

lemma isKreinAdjointH_self_iff_adjoint_mul
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    IsKreinAdjointH (E := E) A A ↔
      A = (fundamentalSymmetryH (E := E)) *
        (ContinuousLinearMap.adjoint A) *
        (fundamentalSymmetryH (E := E)) := by
  simpa [mul_assoc] using isKreinAdjointH_self_iff_adjoint (E := E) A

/-- Krein self-adjointness on the Hilbert carrier (`A♯ = A`). -/
def IsKreinSelfAdjointH
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) : Prop :=
  kreinAdjointH (E := E) A = A

/-- Krein skew-adjointness on the Hilbert carrier (`A♯ = -A`). -/
def IsKreinSkewAdjointH
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) : Prop :=
  kreinAdjointH (E := E) A = -A

end Adjoint

end KreinCliffordWithLp
