import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import InfoGeometry.Krein.KreinSpace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra

/-!
# InfoGeometry.Krein.DoubledSpace

Canonical diagonal (Pontryagin) model of the doubled information state space.
The carrier is `WithLp 2 (E × E)`, and the fundamental symmetry is the sign flip
`J(x, ξ) = (x, -ξ)`.
-/

namespace InfoGeometry.Krein

/-- The doubled space E ⊕ E as the canonical L² carrier. -/
abbrev DoubledSpace (E : Type*) :=
  WithLp 2 (E × E)

variable {E : Type*}

-- Projection and constructor API for DoubledSpace
def toDoubled (x ξ : E) : DoubledSpace E := WithLp.toLp 2 (x, ξ)

instance : Coe (E × E) (DoubledSpace E) where
  coe p := toDoubled p.1 p.2

def DoubledSpace.fst (u : DoubledSpace E) : E := (WithLp.ofLp u).1
def DoubledSpace.snd (u : DoubledSpace E) : E := (WithLp.ofLp u).2

@[simp] lemma coe_prod_toDoubled (x ξ : E) : ((x, ξ) : DoubledSpace E) = toDoubled x ξ := rfl
@[simp] lemma fst_toDoubled (x ξ : E) : (toDoubled x ξ).fst = x := rfl
@[simp] lemma snd_toDoubled (x ξ : E) : (toDoubled x ξ).snd = ξ := rfl
@[simp] lemma fst_snd_eq_ofLp (u : DoubledSpace E) : (u.fst, u.snd) = WithLp.ofLp u := by
  cases h : WithLp.ofLp u with
  | mk x ξ =>
      simp [DoubledSpace.fst, DoubledSpace.snd, h]
@[simp] lemma toDoubled_fst_snd (u : DoubledSpace E) : toDoubled u.fst u.snd = u := by
  simpa [toDoubled, fst_snd_eq_ofLp] using (WithLp.toLp_ofLp (p := (2 : ENNReal)) (x := u))

@[simp] lemma neg_toDoubled [AddCommGroup E] (x ξ : E) :
    -toDoubled x ξ = toDoubled (-x) (-ξ) := rfl

@[ext] lemma DoubledSpace.ext (u v : DoubledSpace E)
    (hfst : u.fst = v.fst) (hsnd : u.snd = v.snd) : u = v := by
  apply (WithLp.ofLp_injective 2)
  simpa [fst_snd_eq_ofLp] using Prod.ext hfst hsnd

section Algebraic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] lemma add_toDoubled (x ξ y η : E) :
    toDoubled x ξ + toDoubled y η = toDoubled (x + y) (ξ + η) := rfl

@[simp] lemma smul_toDoubled (c : ℝ) (x ξ : E) :
    c • toDoubled x ξ = toDoubled (c • x) (c • ξ) := rfl

@[simp] lemma fst_add (u v : DoubledSpace E) : (u + v).fst = u.fst + v.fst := rfl
@[simp] lemma snd_add (u v : DoubledSpace E) : (u + v).snd = u.snd + v.snd := rfl
@[simp] lemma fst_smul (c : ℝ) (u : DoubledSpace E) : (c • u).fst = c • u.fst := rfl
@[simp] lemma snd_smul (c : ℝ) (u : DoubledSpace E) : (c • u).snd = c • u.snd := rfl
@[simp] lemma fst_sub (u v : DoubledSpace E) : (u - v).fst = u.fst - v.fst := rfl
@[simp] lemma snd_sub (u v : DoubledSpace E) : (u - v).snd = u.snd - v.snd := rfl
@[simp] lemma fst_neg (u : DoubledSpace E) : (-u).fst = -u.fst := rfl
@[simp] lemma snd_neg (u : DoubledSpace E) : (-u).snd = -u.snd := rfl

end Algebraic

section Compatibility

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The swap involution `J(x, ξ) = (ξ, x)` on doubled space. -/
noncomputable def modularJ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    DoubledSpace E →L[ℝ] DoubledSpace E where
  toFun u := toDoubled u.snd u.fst
  cont := by
    simpa [toDoubled] using
      (WithLp.prod_continuous_toLp (p := 2) (α := E) (β := E)).comp
        ((WithLp.continuous_snd (p := 2) (α := E) (β := E)).prodMk
          (WithLp.continuous_fst (p := 2) (α := E) (β := E)))
  map_add' u v := by
    apply (WithLp.ofLp_injective 2)
    simp [toDoubled, DoubledSpace.fst, DoubledSpace.snd]
  map_smul' c u := by
    apply (WithLp.ofLp_injective 2)
    simp [toDoubled, DoubledSpace.fst, DoubledSpace.snd]

/-- The sign involution `ε(x, ξ) = (x, -ξ)` on doubled space. -/
noncomputable def spectralEpsilon (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    DoubledSpace E →L[ℝ] DoubledSpace E where
  toFun u := toDoubled u.fst (-u.snd)
  cont := by
    simpa [toDoubled] using
      (WithLp.prod_continuous_toLp (p := 2) (α := E) (β := E)).comp
        ((WithLp.continuous_fst (p := 2) (α := E) (β := E)).prodMk
          (continuous_neg.comp (WithLp.continuous_snd (p := 2) (α := E) (β := E))))
  map_add' u v := by
    apply (WithLp.ofLp_injective 2)
    simp [toDoubled, DoubledSpace.fst, DoubledSpace.snd, add_comm, add_left_comm, add_assoc]
  map_smul' c u := by
    apply (WithLp.ofLp_injective 2)
    simp [toDoubled, DoubledSpace.fst, DoubledSpace.snd]

/-- Canonical complex-like generator `I = J ∘ ε`. -/
noncomputable def complexI (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  (modularJ (E := E)).comp (spectralEpsilon (E := E))

/-- `Cl(1,1)` compatibility relation package on doubled-space endomorphisms. -/
def Cl11Relations (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  J.comp J = ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
    ε.comp ε = ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
      J.comp ε = -((ε).comp J)

/-- Marker alias used by legacy modules. -/
abbrev Cl11Algebra (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  Cl11Relations J ε

@[simp] lemma modularJ_apply (u : DoubledSpace E) :
    modularJ (E := E) u = toDoubled u.snd u.fst := rfl

@[simp] lemma spectralEpsilon_apply (u : DoubledSpace E) :
    spectralEpsilon (E := E) u = toDoubled u.fst (-u.snd) := rfl

@[simp] lemma complexI_apply (u : DoubledSpace E) :
    complexI (E := E) u = toDoubled (-u.snd) u.fst := by
  apply (WithLp.ofLp_injective 2)
  simp [complexI, modularJ, spectralEpsilon, toDoubled, DoubledSpace.fst, DoubledSpace.snd]

lemma modularJ_involution :
    (modularJ (E := E)).comp (modularJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro u
  rcases u with ⟨p⟩
  rcases p with ⟨x, ξ⟩
  rfl

lemma spectralEpsilon_involution :
    (spectralEpsilon (E := E)).comp (spectralEpsilon (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro u
  rcases u with ⟨p⟩
  rcases p with ⟨x, ξ⟩
  simp [spectralEpsilon, toDoubled, DoubledSpace.fst, DoubledSpace.snd]

lemma modularJ_spectralEpsilon_anticommute :
    (modularJ (E := E)).comp (spectralEpsilon (E := E))
      = -((spectralEpsilon (E := E)).comp (modularJ (E := E))) := by
  apply ContinuousLinearMap.ext
  intro u
  rcases u with ⟨p⟩
  rcases p with ⟨x, ξ⟩
  change WithLp.toLp 2 (-ξ, x) = -WithLp.toLp 2 (ξ, -x)
  simpa using (WithLp.toLp_neg (p := 2) (x := (ξ, -x)))

lemma complexI_sq :
    (complexI (E := E)).comp (complexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  apply ContinuousLinearMap.ext
  intro u
  rcases u with ⟨p⟩
  rcases p with ⟨x, ξ⟩
  change WithLp.toLp 2 (-x, -ξ) = -WithLp.toLp 2 (x, ξ)
  simpa using (WithLp.toLp_neg (p := 2) (x := (x, ξ)))

theorem modularJ_spectralEpsilon_hasCl11Relations :
    Cl11Relations (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  refine ⟨modularJ_involution (E := E), spectralEpsilon_involution (E := E), ?_⟩
  exact modularJ_spectralEpsilon_anticommute (E := E)

theorem modularJ_spectralEpsilon_isCl11 :
    Cl11Algebra (modularJ (E := E)) (spectralEpsilon (E := E)) :=
  modularJ_spectralEpsilon_hasCl11Relations (E := E)

end Compatibility

section KreinAnalytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Hessian indefinite form on DoubledSpace.
In the diagonal basis, this is exactly the Krein inner product: [x, ξ]·[y, η] = ⟪x, y⟫ - ⟪ξ, η⟫. -/
noncomputable def hessianIndefiniteForm (u v : DoubledSpace E) : ℝ :=
  KreinSpace.kreinInner u v

/-- Characterization of Krein skew-adjointness as infinitesimal Hessian invariance. -/
def IsKreinSkewAdjoint (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  KreinSpace.IsKreinSkewAdjoint A

theorem IsKreinSkewAdjoint.hessian_infinitesimal
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsKreinSkewAdjoint A)
    (x y : DoubledSpace E) :
    hessianIndefiniteForm (A x) y + hessianIndefiniteForm x (A y) = 0 :=
  (KreinSpace.isKreinSkewAdjoint_iff A).mp hA x y

/-- The Lie algebra of the information state space (Information Killing Fields). -/
noncomputable def informationLieAlgebra (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    LieSubalgebra ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) where
  carrier := {A | IsKreinSkewAdjoint A}
  zero_mem' := by simp [IsKreinSkewAdjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg]
  add_mem' hA hB := by
    simp [IsKreinSkewAdjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at hA hB ⊢
    simpa [hA, hB, add_comm, add_left_comm, add_assoc]
  smul_mem' c A hA := by
    simp [IsKreinSkewAdjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at hA ⊢
    simpa [hA, smul_neg]
  lie_mem' hA hB := by
    simpa [IsKreinSkewAdjoint] using (KreinSpace.isKreinSkewAdjoint_lie (hA := hA) (hB := hB))

end KreinAnalytic

end InfoGeometry.Krein
