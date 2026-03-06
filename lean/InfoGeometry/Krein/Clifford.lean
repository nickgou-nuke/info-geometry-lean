import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Clifford.SplitQ11
import Mathlib.Tactic.Module

/-!
# Krein-Clifford Bridge

This module starts Phase 5 of the canonical Krein stack:
- `KreinGradedModule`: Z/2-grading compatible with a Krein symmetry.
- `SymmetricCliffordModule`: Clifford action by Krein endomorphisms.
- `KreinClifford`: induced Clifford algebra from the Krein quadratic form.
-/

open scoped InnerProductSpace

class KreinGradedModule (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H] where
  /-- Grading involution `Γ` (chirality operator). -/
  grade : H ≃ₗᵢ[ℝ] H
  /-- `Γ² = 1`. -/
  grade_invol : ∀ x : H, grade (grade x) = x
  /-- `Γ` is Hilbert-self-adjoint. -/
  grade_selfAdj : ∀ u v : H, ⟪grade u, v⟫_ℝ = ⟪u, grade v⟫_ℝ

namespace KreinGradedModule

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- `Γ` as a continuous linear map. -/
noncomputable def gradeCLM : H →L[ℝ] H :=
  (KreinGradedModule.grade (H := H)).toLinearIsometry.toContinuousLinearMap

@[simp] lemma gradeCLM_apply (x : H) :
    gradeCLM (H := H) x = (KreinGradedModule.grade (H := H)) x := rfl

@[simp] lemma gradeCLM_comp_self :
    (gradeCLM (H := H)).comp (gradeCLM (H := H)) = ContinuousLinearMap.id ℝ H := by
  ext x
  simp [gradeCLM, KreinGradedModule.grade_invol]

lemma adjoint_gradeCLM :
    ContinuousLinearMap.adjoint (gradeCLM (H := H)) = gradeCLM (H := H) := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff (A := gradeCLM (H := H)) (B := gradeCLM (H := H))).2 ?_
  intro u v
  simpa [gradeCLM_apply] using (KreinGradedModule.grade_selfAdj (H := H) u v)

lemma gradeCLM_selfAdjoint :
    IsSelfAdjoint (gradeCLM (H := H)) :=
  adjoint_gradeCLM (H := H)

/-- Grading conjugation on endomorphisms: `A ↦ Γ A Γ`. -/
noncomputable def gradeConj (A : H →L[ℝ] H) : H →L[ℝ] H :=
  (gradeCLM (H := H)).comp (A.comp (gradeCLM (H := H)))

def IsEven (A : H →L[ℝ] H) : Prop := gradeConj (H := H) A = A

def IsOdd (A : H →L[ℝ] H) : Prop := gradeConj (H := H) A = -A

/-- Chirality projector `(Id + Γ)/2`. -/
noncomputable def gradeProjPlus : H →L[ℝ] H :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ H + gradeCLM (H := H))

/-- Chirality projector `(Id - Γ)/2`. -/
noncomputable def gradeProjMinus : H →L[ℝ] H :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ H - gradeCLM (H := H))

lemma gradeProj_sum :
    gradeProjPlus (H := H) + gradeProjMinus (H := H)
      = ContinuousLinearMap.id ℝ H := by
  ext x
  simp [gradeProjPlus, gradeProjMinus, sub_eq_add_neg]
  module

end KreinGradedModule

/-- Phase-5 canonical Clifford layer: a graded Krein module carrying a Clifford action. -/
class SymmetricCliffordModule (V H : Type*)
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H] (Q : QuadraticForm ℝ V) where
  /-- Clifford action `Cl(Q) → End(H)`. -/
  ρ : CliffordAlgebra Q →ₐ[ℝ] (H →L[ℝ] H)
  /-- Clifford generators are odd for the grading involution. -/
  odd_ι : ∀ v : V,
    (KreinGradedModule.gradeCLM (H := H)).comp (ρ (CliffordAlgebra.ι Q v))
      = -((ρ (CliffordAlgebra.ι Q v)).comp (KreinGradedModule.gradeCLM (H := H)))
  /-- Clifford generators are Krein-self-adjoint. -/
  kreinSelfAdj_ι : ∀ v : V,
    KreinSpace.kreinAdjoint (H := H) (ρ (CliffordAlgebra.ι Q v)) = ρ (CliffordAlgebra.ι Q v)

namespace SymmetricCliffordModule

variable {V H : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable {Q : QuadraticForm ℝ V}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H] [SymmetricCliffordModule V H Q]

noncomputable abbrev rho :
    CliffordAlgebra Q →ₐ[ℝ] (H →L[ℝ] H) :=
  (inferInstance : SymmetricCliffordModule V H Q).ρ

lemma rho_ι_sq_scalar (v : V) :
    rho (Q := Q) (CliffordAlgebra.ι Q v) *
      rho (Q := Q) (CliffordAlgebra.ι Q v)
      = algebraMap ℝ (H →L[ℝ] H) (Q v) := by
  simpa [rho] using
    (CliffordAlgebra.comp_ι_sq_scalar (Q := Q) (g := rho (Q := Q)) v)

lemma rho_ι_isOdd (v : V) :
    KreinGradedModule.IsOdd (H := H) (rho (Q := Q) (CliffordAlgebra.ι Q v)) := by
  let Γ : H →L[ℝ] H := KreinGradedModule.gradeCLM (H := H)
  let A : H →L[ℝ] H := rho (Q := Q) (CliffordAlgebra.ι Q v)
  have hΓA : Γ.comp A = -(A.comp Γ) :=
    (inferInstance : SymmetricCliffordModule V H Q).odd_ι v
  unfold KreinGradedModule.IsOdd KreinGradedModule.gradeConj
  calc
    Γ.comp (A.comp Γ)
        = (Γ.comp A).comp Γ := by simp [ContinuousLinearMap.comp_assoc]
    _ = (-(A.comp Γ)).comp Γ := by rw [hΓA]
    _ = -((A.comp Γ).comp Γ) := by simp
    _ = -(A.comp (Γ.comp Γ)) := by simp [ContinuousLinearMap.comp_assoc]
    _ = -(A.comp (ContinuousLinearMap.id ℝ H)) := by
          rw [show Γ.comp Γ = ContinuousLinearMap.id ℝ H by
                simpa [Γ] using (KreinGradedModule.gradeCLM_comp_self (H := H))]
    _ = -A := by simp

lemma rho_ι_isKreinSelfAdjoint (v : V) :
    KreinSpace.IsKreinSelfAdjoint (H := H)
      (rho (Q := Q) (CliffordAlgebra.ι Q v)) := by
  exact (inferInstance : SymmetricCliffordModule V H Q).kreinSelfAdj_ι v

end SymmetricCliffordModule

namespace KreinSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

/-- The Krein inner product viewed as a Mathlib `QuadraticForm`. -/
noncomputable abbrev kreinQForm : QuadraticForm ℝ H := kreinQuad (H := H)

/-- The Clifford algebra induced by the Krein indefinite metric. -/
noncomputable abbrev KreinClifford := CliffordAlgebra (kreinQForm (H := H))

end KreinSpace

namespace InfoGeometry.Krein

section Phase5Concrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private noncomputable def hilbertSwapMap : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E where
  toFun u := WithLp.toLp 2 ((WithLp.ofLp u).2, (WithLp.ofLp u).1)
  map_add' := by
    intro u v
    rcases u with ⟨x, ξ⟩
    rcases v with ⟨y, η⟩
    rfl
  map_smul' := by
    intro r u
    rcases u with ⟨x, ξ⟩
    rfl

@[simp] private lemma hilbertSwapMap_apply (u : HilbertDoubled E) :
    hilbertSwapMap (E := E) u = WithLp.toLp 2 ((WithLp.ofLp u).2, (WithLp.ofLp u).1) := rfl

private lemma hilbertSwap_invol (u : HilbertDoubled E) :
    hilbertSwapMap (E := E) (hilbertSwapMap (E := E) u) = u := by
  rcases u with ⟨x, ξ⟩
  rfl

private lemma hilbertSwap_selfAdj (u v : HilbertDoubled E) :
    ⟪hilbertSwapMap (E := E) u, v⟫_ℝ = ⟪u, hilbertSwapMap (E := E) v⟫_ℝ := by
  rcases u with ⟨x, ξ⟩
  rcases v with ⟨y, η⟩
  simp [hilbertSwapMap, WithLp.prod_inner_apply, add_comm]

private lemma hilbertSwap_norm (u : HilbertDoubled E) :
    ‖hilbertSwapMap (E := E) u‖ = ‖u‖ := by
  rcases u with ⟨x, ξ⟩
  have h1 : ‖(WithLp.toLp 2 (ξ, x) : HilbertDoubled E)‖ ^ 2
      = ‖(WithLp.toLp 2 (x, ξ) : HilbertDoubled E)‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    exact add_comm _ _
  have h2 : (‖(WithLp.toLp 2 (ξ, x) : HilbertDoubled E)‖ : ℝ)
      = (‖(WithLp.toLp 2 (x, ξ) : HilbertDoubled E)‖ : ℝ) := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (ξ, x) : HilbertDoubled E),
      norm_nonneg (WithLp.toLp 2 (x, ξ) : HilbertDoubled E)]
  simpa [hilbertSwapMap] using h2

/-- Swap as a `LinearIsometryEquiv` on `HilbertDoubled`. -/
noncomputable def hilbertSwapLIE : HilbertDoubled E ≃ₗᵢ[ℝ] HilbertDoubled E where
  toLinearEquiv := LinearEquiv.ofLinear (hilbertSwapMap (E := E)) (hilbertSwapMap (E := E))
    (LinearMap.ext (hilbertSwap_invol (E := E)))
    (LinearMap.ext (hilbertSwap_invol (E := E)))
  norm_map' := hilbertSwap_norm (E := E)

@[simp] lemma hilbertSwapLIE_apply (u : HilbertDoubled E) :
    hilbertSwapLIE (E := E) u = hilbertSwapMap (E := E) u := rfl

/-- Swap as a continuous linear map on `HilbertDoubled`. -/
noncomputable def hilbertSwapCLM : HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  (hilbertSwapLIE (E := E)).toLinearIsometry.toContinuousLinearMap

@[simp] lemma hilbertSwapCLM_apply (u : HilbertDoubled E) :
    hilbertSwapCLM (E := E) u = WithLp.toLp 2 ((WithLp.ofLp u).2, (WithLp.ofLp u).1) := by
  simp [hilbertSwapCLM, hilbertSwapLIE_apply, hilbertSwapMap_apply]

lemma hilbertSwap_selfAdj_clm (u v : HilbertDoubled E) :
    ⟪hilbertSwapCLM (E := E) u, v⟫_ℝ = ⟪u, hilbertSwapCLM (E := E) v⟫_ℝ := by
  simpa [hilbertSwapCLM, hilbertSwapLIE_apply] using hilbertSwap_selfAdj (E := E) u v

noncomputable instance instKreinGradedModuleHilbertDoubled :
    KreinGradedModule (HilbertDoubled E) where
  grade := hilbertSwapLIE (E := E)
  grade_invol := by
    intro u
    simpa [hilbertSwapLIE_apply] using hilbertSwap_invol (E := E) u
  grade_selfAdj := by
    intro u v
    simpa [hilbertSwapLIE_apply] using hilbertSwap_selfAdj (E := E) u v

@[simp] lemma gradeCLM_eq_hilbertSwapCLM :
    KreinGradedModule.gradeCLM (H := HilbertDoubled E) = hilbertSwapCLM (E := E) := rfl

@[simp] lemma jCLM_apply_coords (u : HilbertDoubled E) :
    KreinSpace.jCLM (H := HilbertDoubled E) u =
      WithLp.toLp 2 ((WithLp.ofLp u).1, -(WithLp.ofLp u).2) := by
  apply ext_inner_right ℝ
  intro v
  calc
    ⟪KreinSpace.jCLM (H := HilbertDoubled E) u, v⟫_ℝ
        = KreinSpace.kreinInner (H := HilbertDoubled E) u v := by
            simp [KreinSpace.kreinInner_def, KreinSpace.jCLM_apply]
    _ = ⟪(WithLp.ofLp u).1, (WithLp.ofLp v).1⟫_ℝ - ⟪(WithLp.ofLp u).2, (WithLp.ofLp v).2⟫_ℝ := by
          simpa using kreinInner_prodL2 (E := E) u v
    _ = ⟪WithLp.toLp 2 ((WithLp.ofLp u).1, -(WithLp.ofLp u).2), v⟫_ℝ := by
          simp [WithLp.prod_inner_apply, sub_eq_add_neg]

@[simp] lemma J_apply_coords (u : HilbertDoubled E) :
    (KreinSpace.J (H := HilbertDoubled E)) u =
      WithLp.toLp 2 ((WithLp.ofLp u).1, -(WithLp.ofLp u).2) := by
  simpa [KreinSpace.jCLM_apply] using (jCLM_apply_coords (E := E) u)

/-- Canonical `I = Γ ∘ J` on the diagonal model (`I^2 = -Id`). -/
noncomputable def hilbertComplexI : HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  (hilbertSwapCLM (E := E)).comp (KreinSpace.jCLM (H := HilbertDoubled E))

@[simp] lemma hilbertComplexI_apply (u : HilbertDoubled E) :
    hilbertComplexI (E := E) u =
      WithLp.toLp 2 (-(WithLp.ofLp u).2, (WithLp.ofLp u).1) := by
  simp [hilbertComplexI, jCLM_apply_coords]

lemma hilbertSwap_comp_jCLM :
    (hilbertSwapCLM (E := E)).comp (KreinSpace.jCLM (H := HilbertDoubled E))
      = -((KreinSpace.jCLM (H := HilbertDoubled E)).comp (hilbertSwapCLM (E := E))) := by
  ext u
  apply (WithLp.ofLp_injective 2)
  simp [hilbertSwapCLM_apply, jCLM_apply_coords]

lemma hilbertComplexI_sq :
    (hilbertComplexI (E := E)).comp (hilbertComplexI (E := E))
      = -(ContinuousLinearMap.id ℝ (HilbertDoubled E)) := by
  ext u
  rcases u with ⟨x, ξ⟩
  apply (WithLp.ofLp_injective 2)
  simp [hilbertComplexI_apply]

lemma hilbertSwap_comp_hilbertComplexI :
    (hilbertSwapCLM (E := E)).comp (hilbertComplexI (E := E))
      = -((hilbertComplexI (E := E)).comp (hilbertSwapCLM (E := E))) := by
  ext u
  apply (WithLp.ofLp_injective 2)
  simp [hilbertSwapCLM_apply, hilbertComplexI_apply]

lemma kreinAdjoint_jCLM_hilbert :
    KreinSpace.kreinAdjoint (H := HilbertDoubled E) (KreinSpace.jCLM (H := HilbertDoubled E))
      = KreinSpace.jCLM (H := HilbertDoubled E) := by
  simp [KreinSpace.kreinAdjoint, ContinuousLinearMap.comp_assoc]

lemma adjoint_hilbertSwapCLM :
    ContinuousLinearMap.adjoint (hilbertSwapCLM (E := E)) = hilbertSwapCLM (E := E) := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff (A := hilbertSwapCLM (E := E))
    (B := hilbertSwapCLM (E := E))).2 ?_
  intro u v
  simpa using hilbertSwap_selfAdj_clm (E := E) u v

lemma kreinAdjoint_hilbertComplexI :
    KreinSpace.kreinAdjoint (H := HilbertDoubled E) (hilbertComplexI (E := E))
      = hilbertComplexI (E := E) := by
  simp [KreinSpace.kreinAdjoint, hilbertComplexI, adjoint_hilbertSwapCLM,
    ContinuousLinearMap.comp_assoc]

noncomputable def cl11RepLinHilbert :
    (ℝ × ℝ) →ₗ[ℝ] (HilbertDoubled E →L[ℝ] HilbertDoubled E) where
  toFun v := v.1 • (KreinSpace.jCLM (H := HilbertDoubled E)) + v.2 • (hilbertComplexI (E := E))
  map_add' := by
    intro u v
    ext x <;> simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a v
    ext x <;> simp [smul_add, smul_smul]

lemma cl11RepLinHilbert_apply_pair (a b : ℝ) (x y : E) :
    cl11RepLinHilbert (E := E) (a, b) (WithLp.toLp 2 (x, y))
      = WithLp.toLp 2 (a • x - b • y, b • x - a • y) := by
  apply (WithLp.ofLp_injective 2)
  simp [cl11RepLinHilbert, hilbertComplexI_apply, jCLM_apply_coords, sub_eq_add_neg,
    add_smul, smul_add, add_assoc, add_left_comm, add_comm]

lemma cl11RepLinHilbert_sq (v : ℝ × ℝ) :
    (cl11RepLinHilbert (E := E) v) * (cl11RepLinHilbert (E := E) v)
      = algebraMap ℝ (HilbertDoubled E →L[ℝ] HilbertDoubled E) (InfoGeometry.Clifford.splitQ11 v) := by
  rcases v with ⟨a, b⟩
  ext u
  rcases u with ⟨x, y⟩
  apply (WithLp.ofLp_injective 2)
  simp [cl11RepLinHilbert_apply_pair, InfoGeometry.Clifford.splitQ11_apply, Algebra.algebraMap_eq_smul_one,
    sub_eq_add_neg, smul_smul]
  constructor <;> module

noncomputable def cl11RepHilbert :
    CliffordAlgebra InfoGeometry.Clifford.splitQ11 →ₐ[ℝ] (HilbertDoubled E →L[ℝ] HilbertDoubled E) :=
  CliffordAlgebra.lift InfoGeometry.Clifford.splitQ11
    ⟨cl11RepLinHilbert (E := E), cl11RepLinHilbert_sq (E := E)⟩

@[simp] lemma cl11RepHilbert_ι_apply (v : ℝ × ℝ) :
    cl11RepHilbert (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v)
      = cl11RepLinHilbert (E := E) v := by
  simp [cl11RepHilbert]

noncomputable instance instSymmetricCliffordModuleHilbertDoubled :
    SymmetricCliffordModule (ℝ × ℝ) (HilbertDoubled E) InfoGeometry.Clifford.splitQ11 where
  ρ := cl11RepHilbert (E := E)
  odd_ι := by
    intro v
    rcases v with ⟨a, b⟩
    ext u
    rcases u with ⟨x, ξ⟩
    apply (WithLp.ofLp_injective 2)
    simp [gradeCLM_eq_hilbertSwapCLM, cl11RepHilbert_ι_apply, cl11RepLinHilbert_apply_pair,
      hilbertSwapCLM_apply, sub_eq_add_neg]
  kreinSelfAdj_ι := by
    intro v
    rcases v with ⟨a, b⟩
    simpa [cl11RepHilbert_ι_apply, cl11RepLinHilbert, KreinSpace.kreinAdjoint_add,
      KreinSpace.kreinAdjoint_smul, kreinAdjoint_jCLM_hilbert, kreinAdjoint_hilbertComplexI]

section NeutralTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Grading on `NeutralSpace E` transported from the diagonal model by the 45-degree bridge. -/
private noncomputable def neutralGradeLIE : NeutralSpace E ≃ₗᵢ[ℝ] NeutralSpace E :=
  (NeutralSpace.rotation45Isometry (E := E)).trans
    ((hilbertSwapLIE (E := E)).trans (NeutralSpace.rotation45Isometry (E := E)).symm)

noncomputable instance instKreinGradedModuleNeutral :
    KreinGradedModule (NeutralSpace E) where
  grade := neutralGradeLIE (E := E)
  grade_invol := by
    intro u
    apply (NeutralSpace.rotation45Isometry (E := E)).injective
    simp [neutralGradeLIE]
  grade_selfAdj := by
    intro u v
    let R : NeutralSpace E ≃ₗᵢ[ℝ] HilbertDoubled E := NeutralSpace.rotation45Isometry (E := E)
    calc
      ⟪neutralGradeLIE (E := E) u, v⟫_ℝ
          = ⟪R (neutralGradeLIE (E := E) u), R v⟫_ℝ := by
              simpa [R] using (R.inner_map_map (neutralGradeLIE (E := E) u) v).symm
      _ = ⟪hilbertSwapLIE (E := E) (R u), R v⟫_ℝ := by
            simp [neutralGradeLIE, R]
      _ = ⟪R u, hilbertSwapLIE (E := E) (R v)⟫_ℝ := by
            simpa [R] using hilbertSwap_selfAdj (E := E) (R u) (R v)
      _ = ⟪R u, R (neutralGradeLIE (E := E) v)⟫_ℝ := by
            simp [neutralGradeLIE, R]
      _ = ⟪u, neutralGradeLIE (E := E) v⟫_ℝ := by
            simpa [R] using (R.inner_map_map u (neutralGradeLIE (E := E) v))

/-- Conjugation by the 45-degree bridge on endomorphisms. -/
private noncomputable def rot45Conj :
    (NeutralSpace E →L[ℝ] NeutralSpace E) ≃ₐ[ℝ] (HilbertDoubled E →L[ℝ] HilbertDoubled E) :=
  (NeutralSpace.rotation45 (E := E)).conjContinuousAlgEquiv

/-- `Cl(1,1)` action on `NeutralSpace E`, transported from the diagonal action. -/
private noncomputable def cl11RepNeutral :
    CliffordAlgebra InfoGeometry.Clifford.splitQ11 →ₐ[ℝ] (NeutralSpace E →L[ℝ] NeutralSpace E) :=
  (rot45Conj (E := E)).symm.toAlgHom.comp (cl11RepHilbert (E := E))

@[simp] lemma cl11RepNeutral_apply_apply
    (a : CliffordAlgebra InfoGeometry.Clifford.splitQ11) (u : NeutralSpace E) :
    cl11RepNeutral (E := E) a u =
      (NeutralSpace.rotation45 (E := E)).symm
        ((cl11RepHilbert (E := E) a) ((NeutralSpace.rotation45 (E := E)) u)) := by
  rfl

@[simp] lemma rotation45_cl11RepNeutral_apply
    (a : CliffordAlgebra InfoGeometry.Clifford.splitQ11) (u : NeutralSpace E) :
    (NeutralSpace.rotation45 (E := E)) (cl11RepNeutral (E := E) a u) =
      (cl11RepHilbert (E := E) a) ((NeutralSpace.rotation45 (E := E)) u) := by
  simpa using congrArg (NeutralSpace.rotation45 (E := E))
    (cl11RepNeutral_apply_apply (E := E) a u)

@[simp] lemma cl11RepNeutral_ι_apply (v : ℝ × ℝ) :
    cl11RepNeutral (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v) =
      (rot45Conj (E := E)).symm (cl11RepLinHilbert (E := E) v) := by
  simp [cl11RepNeutral, rot45Conj, cl11RepHilbert_ι_apply]

@[simp] lemma rotation45_gradeCLM_neutral_apply (u : NeutralSpace E) :
    (NeutralSpace.rotation45 (E := E)) ((KreinGradedModule.gradeCLM (H := NeutralSpace E)) u) =
      (KreinGradedModule.gradeCLM (H := HilbertDoubled E)) ((NeutralSpace.rotation45 (E := E)) u) := by
  change
    (NeutralSpace.rotation45Isometry (E := E)) (neutralGradeLIE (E := E) u) =
      hilbertSwapCLM (E := E) ((NeutralSpace.rotation45Isometry (E := E)) u)
  simpa [gradeCLM_eq_hilbertSwapCLM] using
    (show (NeutralSpace.rotation45Isometry (E := E)) (neutralGradeLIE (E := E) u) =
      hilbertSwapCLM (E := E) ((NeutralSpace.rotation45Isometry (E := E)) u) by
      simp [neutralGradeLIE, hilbertSwapCLM, hilbertSwapLIE_apply])

noncomputable instance instSymmetricCliffordModuleNeutral :
    SymmetricCliffordModule (ℝ × ℝ) (NeutralSpace E) InfoGeometry.Clifford.splitQ11 where
  ρ := cl11RepNeutral (E := E)
  odd_ι := by
    intro v
    let ΓN : NeutralSpace E →L[ℝ] NeutralSpace E := KreinGradedModule.gradeCLM (H := NeutralSpace E)
    let ΓH : HilbertDoubled E →L[ℝ] HilbertDoubled E := KreinGradedModule.gradeCLM (H := HilbertDoubled E)
    let AN : NeutralSpace E →L[ℝ] NeutralSpace E :=
      cl11RepNeutral (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v)
    let AH : HilbertDoubled E →L[ℝ] HilbertDoubled E := cl11RepLinHilbert (E := E) v
    have hΓ : ΓN = (rot45Conj (E := E)).symm ΓH := by
      rfl
    have hA : AN = (rot45Conj (E := E)).symm AH := by
      simpa [AN, AH] using cl11RepNeutral_ι_apply (E := E) v
    have hH : ΓH * AH = -(AH * ΓH) := by
      rcases v with ⟨a, b⟩
      ext u
      rcases u with ⟨x, ξ⟩
      apply (WithLp.ofLp_injective 2)
      simp [ΓH, AH, gradeCLM_eq_hilbertSwapCLM, cl11RepLinHilbert_apply_pair,
        hilbertSwapCLM_apply, sub_eq_add_neg]
    have hN : (rot45Conj (E := E)).symm (ΓH * AH) =
        (rot45Conj (E := E)).symm (-(AH * ΓH)) := congrArg ((rot45Conj (E := E)).symm) hH
    have hN' :
        ((rot45Conj (E := E)).symm ΓH) * ((rot45Conj (E := E)).symm AH) =
          -(((rot45Conj (E := E)).symm AH) * ((rot45Conj (E := E)).symm ΓH)) := by
      simpa using hN
    simpa [hΓ, hA, AH] using hN'
  kreinSelfAdj_ι := by
    intro v
    let R : KreinEquiv (NeutralSpace E) (HilbertDoubled E) :=
      NeutralSpace.rotation45KreinEquiv (E := E)
    let AN : NeutralSpace E →L[ℝ] NeutralSpace E :=
      cl11RepNeutral (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v)
    let AH : HilbertDoubled E →L[ℝ] HilbertDoubled E := cl11RepLinHilbert (E := E) v
    have hAH_self : KreinSpace.kreinAdjoint (H := HilbertDoubled E) AH = AH := by
      rcases v with ⟨a, b⟩
      simp [AH, cl11RepLinHilbert, KreinSpace.kreinAdjoint_add,
        KreinSpace.kreinAdjoint_smul, kreinAdjoint_jCLM_hilbert, kreinAdjoint_hilbertComplexI]
    have hAH_bilin : ∀ x y : HilbertDoubled E,
        KreinSpace.kreinInner (H := HilbertDoubled E) (AH x) y
          = KreinSpace.kreinInner (H := HilbertDoubled E) x (AH y) := by
      intro x y
      simpa [hAH_self] using
        (KreinSpace.kreinInner_kreinAdjoint (H := HilbertDoubled E) AH x y)
    have hRiso : ∀ x y : NeutralSpace E,
        KreinSpace.kreinInner (H := HilbertDoubled E)
          (R.toContinuousLinearEquiv x) (R.toContinuousLinearEquiv y)
          = KreinSpace.kreinInner (H := NeutralSpace E) x y := by
      intro x y
      simpa [R] using R.isometric x y
    have hAN_transport : ∀ x : NeutralSpace E,
        R.toContinuousLinearEquiv (AN x) = AH (R.toContinuousLinearEquiv x) := by
      intro x
      simpa [R, AN, AH] using
        (rotation45_cl11RepNeutral_apply (E := E)
          (a := CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v) (u := x))
    have hAN_bilin : ∀ x y : NeutralSpace E,
        KreinSpace.kreinInner (H := NeutralSpace E) (AN x) y
          = KreinSpace.kreinInner (H := NeutralSpace E) x (AN y) := by
      intro x y
      calc
        KreinSpace.kreinInner (H := NeutralSpace E) (AN x) y
            = KreinSpace.kreinInner (H := HilbertDoubled E)
                (R.toContinuousLinearEquiv (AN x)) (R.toContinuousLinearEquiv y) := by
                  symm
                  exact hRiso (AN x) y
        _ = KreinSpace.kreinInner (H := HilbertDoubled E)
              (AH (R.toContinuousLinearEquiv x)) (R.toContinuousLinearEquiv y) := by
                simpa [hAN_transport]
        _ = KreinSpace.kreinInner (H := HilbertDoubled E)
              (R.toContinuousLinearEquiv x) (AH (R.toContinuousLinearEquiv y)) := by
                exact hAH_bilin (R.toContinuousLinearEquiv x) (R.toContinuousLinearEquiv y)
        _ = KreinSpace.kreinInner (H := HilbertDoubled E)
              (R.toContinuousLinearEquiv x) (R.toContinuousLinearEquiv (AN y)) := by
                simpa [hAN_transport]
        _ = KreinSpace.kreinInner (H := NeutralSpace E) x (AN y) := by
              exact hRiso x (AN y)
    ext y
    apply ext_inner_left ℝ
    intro u
    let uu : NeutralSpace E := NeutralSpace.ofWithLp (E := E) u
    have huu1 :
        ⟪u, (KreinSpace.kreinAdjoint (H := NeutralSpace E) AN y).val⟫_ℝ
          = ⟪uu, (KreinSpace.kreinAdjoint (H := NeutralSpace E) AN) y⟫_ℝ := rfl
    have huu2 : ⟪u, (AN y).val⟫_ℝ = ⟪uu, AN y⟫_ℝ := rfl
    rw [huu1, huu2]
    calc
      ⟪uu, (KreinSpace.kreinAdjoint (H := NeutralSpace E) AN) y⟫_ℝ
          = KreinSpace.kreinInner (H := NeutralSpace E)
              ((KreinSpace.J (H := NeutralSpace E)) uu)
              ((KreinSpace.kreinAdjoint (H := NeutralSpace E) AN) y) := by
                change ⟪(KreinSpace.J (H := NeutralSpace E))
                    ((KreinSpace.J (H := NeutralSpace E)) uu),
                  (KreinSpace.kreinAdjoint (H := NeutralSpace E) AN) y⟫_ℝ = _
                simpa [KreinSpace.kreinInner_def, KreinSpace.J_invol]
      _ = KreinSpace.kreinInner (H := NeutralSpace E)
            (AN ((KreinSpace.J (H := NeutralSpace E)) uu)) y := by
            rw [KreinSpace.kreinInner_kreinAdjoint]
      _ = KreinSpace.kreinInner (H := NeutralSpace E)
            ((KreinSpace.J (H := NeutralSpace E)) uu) (AN y) := by
            exact hAN_bilin ((KreinSpace.J (H := NeutralSpace E)) uu) y
      _ = ⟪uu, AN y⟫_ℝ := by
            change KreinSpace.kreinInner (H := NeutralSpace E)
                ((KreinSpace.J (H := NeutralSpace E)) uu) (AN y) = ⟪uu, AN y⟫_ℝ
            simpa [KreinSpace.kreinInner_def, KreinSpace.J_invol]

end NeutralTransport

end Phase5Concrete
end InfoGeometry.Krein
