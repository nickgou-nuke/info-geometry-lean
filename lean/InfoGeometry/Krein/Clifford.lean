import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Clifford.SplitQ11
import Mathlib.Tactic.Module

namespace InfoGeometry.Krein

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
  calc
    rho (Q := Q) (CliffordAlgebra.ι Q v) *
        rho (Q := Q) (CliffordAlgebra.ι Q v)
        =
      rho (Q := Q) ((CliffordAlgebra.ι Q v) * (CliffordAlgebra.ι Q v)) := by
          simp
    _ = rho (Q := Q) (algebraMap ℝ (CliffordAlgebra Q) (Q v)) := by
          simp
    _ = algebraMap ℝ (H →L[ℝ] H) (Q v) := by
          simp

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
          have hΓΓ : Γ.comp Γ = ContinuousLinearMap.id ℝ H := by
            unfold Γ
            exact KreinGradedModule.gradeCLM_comp_self (H := H)
          rw [hΓΓ]
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

section Phase5Concrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private noncomputable def hilbertSwapMap : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E where
  toFun u := HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1)
  map_add' := by
    intro u v
    apply HilbertDoubled.ext
    simpa [HilbertDoubled.ofLp, HilbertDoubled.toLp, Prod.mk_add_mk] using
      (WithLp.toLp_add (p := (2 : ENNReal))
        (x := ((HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1))
        (y := ((HilbertDoubled.ofLp (E := E) v).2, (HilbertDoubled.ofLp (E := E) v).1)))
  map_smul' := by
    intro r u
    apply HilbertDoubled.ext
    simpa [HilbertDoubled.ofLp, HilbertDoubled.toLp, Prod.smul_mk] using
      (WithLp.toLp_smul (p := (2 : ENNReal)) (c := r)
        (x := ((HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1)))

@[simp] private lemma hilbertSwapMap_apply (u : HilbertDoubled E) :
    hilbertSwapMap (E := E) u =
      HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1) := rfl

private lemma hilbertSwap_invol (u : HilbertDoubled E) :
    hilbertSwapMap (E := E) (hilbertSwapMap (E := E) u) = u := by
  apply HilbertDoubled.ext
  change WithLp.toLp 2 (WithLp.ofLp ((u : DoubledSpace E))) = (u : DoubledSpace E)
  exact WithLp.toLp_ofLp (p := (2 : ENNReal)) ((u : DoubledSpace E))

private lemma hilbertSwap_selfAdj (u v : HilbertDoubled E) :
    ⟪hilbertSwapMap (E := E) u, v⟫_ℝ = ⟪u, hilbertSwapMap (E := E) v⟫_ℝ := by
  change
    ⟪(WithLp.toLp 2 (WithLp.snd ((u : DoubledSpace E)), WithLp.fst ((u : DoubledSpace E))) : DoubledSpace E),
      (v : DoubledSpace E)⟫_ℝ
      =
    ⟪(u : DoubledSpace E),
      (WithLp.toLp 2 (WithLp.snd ((v : DoubledSpace E)), WithLp.fst ((v : DoubledSpace E))) : DoubledSpace E)⟫_ℝ
  simp [WithLp.prod_inner_apply, add_comm]

private lemma hilbertSwap_norm (u : HilbertDoubled E) :
    ‖hilbertSwapMap (E := E) u‖ = ‖u‖ := by
  have h1 :
      ‖(HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1) : HilbertDoubled E)‖ ^ 2
        = ‖(HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).1, (HilbertDoubled.ofLp (E := E) u).2) : HilbertDoubled E)‖ ^ 2 := by
    simpa [HilbertDoubled.toLp] using
      (show ‖(WithLp.toLp 2 ((HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1) : DoubledSpace E)‖ ^ 2
            = ‖(WithLp.toLp 2 ((HilbertDoubled.ofLp (E := E) u).1, (HilbertDoubled.ofLp (E := E) u).2) : DoubledSpace E)‖ ^ 2 by
          rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
          exact add_comm _ _)
  have h2 :
      (‖(HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1) : HilbertDoubled E)‖ : ℝ)
        = (‖(HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).1, (HilbertDoubled.ofLp (E := E) u).2) : HilbertDoubled E)‖ : ℝ) := by
    nlinarith
      [norm_nonneg
        (HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1) : HilbertDoubled E),
       norm_nonneg
        (HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).1, (HilbertDoubled.ofLp (E := E) u).2) : HilbertDoubled E)]
  simpa [hilbertSwapMap, HilbertDoubled.ofLp] using h2

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
    hilbertSwapCLM (E := E) u =
      HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1) := by
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
      HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).1, -(HilbertDoubled.ofLp (E := E) u).2) := by
  apply ext_inner_right ℝ
  intro v
  calc
    ⟪KreinSpace.jCLM (H := HilbertDoubled E) u, v⟫_ℝ
        = KreinSpace.kreinInner (H := HilbertDoubled E) u v := by
            simp [KreinSpace.kreinInner_def, KreinSpace.jCLM_apply]
    _ = ⟪(HilbertDoubled.ofLp (E := E) u).1, (HilbertDoubled.ofLp (E := E) v).1⟫_ℝ
          - ⟪(HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) v).2⟫_ℝ := by
          simpa using krein_inner_prod_l2 (E := E) u v
    _ = ⟪HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).1, -(HilbertDoubled.ofLp (E := E) u).2), v⟫_ℝ := by
          change
            ⟪(HilbertDoubled.ofLp (E := E) u).1, (HilbertDoubled.ofLp (E := E) v).1⟫_ℝ
              + -⟪(HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) v).2⟫_ℝ
              =
            ⟪(WithLp.toLp 2 ((HilbertDoubled.ofLp (E := E) u).1, -(HilbertDoubled.ofLp (E := E) u).2) : DoubledSpace E),
              (v : DoubledSpace E)⟫_ℝ
          simp [WithLp.prod_inner_apply, sub_eq_add_neg]

@[simp] lemma J_apply_coords (u : HilbertDoubled E) :
    (KreinSpace.J (H := HilbertDoubled E)) u =
      HilbertDoubled.toLp (E := E) ((HilbertDoubled.ofLp (E := E) u).1, -(HilbertDoubled.ofLp (E := E) u).2) := by
  simpa [KreinSpace.jCLM_apply] using (jCLM_apply_coords (E := E) u)

/-- Canonical `I = Γ ∘ J` on the diagonal model (`I^2 = -Id`). -/
noncomputable def hilbertComplexI : HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  (hilbertSwapCLM (E := E)).comp (KreinSpace.jCLM (H := HilbertDoubled E))

@[simp] lemma hilbertComplexI_apply (u : HilbertDoubled E) :
    hilbertComplexI (E := E) u =
      HilbertDoubled.toLp (E := E) (-(HilbertDoubled.ofLp (E := E) u).2, (HilbertDoubled.ofLp (E := E) u).1) := by
  simp [hilbertComplexI]

lemma hilbertSwap_comp_jCLM :
    (hilbertSwapCLM (E := E)).comp (KreinSpace.jCLM (H := HilbertDoubled E))
      = -((KreinSpace.jCLM (H := HilbertDoubled E)).comp (hilbertSwapCLM (E := E))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply HilbertDoubled.ext
  simpa [HilbertDoubled.ofLp, Prod.smul_mk] using
    (WithLp.toLp_smul (p := (2 : ENNReal)) (c := (-1 : ℝ))
      (x := (WithLp.snd ((u : DoubledSpace E)), -WithLp.fst ((u : DoubledSpace E)))))

lemma hilbertComplexI_sq :
    (hilbertComplexI (E := E)).comp (hilbertComplexI (E := E))
      = -(ContinuousLinearMap.id ℝ (HilbertDoubled E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply HilbertDoubled.ext
  simpa [HilbertDoubled.ofLp, Prod.smul_mk] using
    (WithLp.toLp_smul (p := (2 : ENNReal)) (c := (-1 : ℝ))
      (x := (WithLp.fst ((u : DoubledSpace E)), WithLp.snd ((u : DoubledSpace E)))))

lemma hilbertSwap_comp_hilbertComplexI :
    (hilbertSwapCLM (E := E)).comp (hilbertComplexI (E := E))
      = -((hilbertComplexI (E := E)).comp (hilbertSwapCLM (E := E))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply HilbertDoubled.ext
  simpa [HilbertDoubled.ofLp, Prod.smul_mk] using
    (WithLp.toLp_smul (p := (2 : ENNReal)) (c := (-1 : ℝ))
      (x := (-WithLp.fst ((u : DoubledSpace E)), WithLp.snd ((u : DoubledSpace E)))))

lemma kreinAdjoint_jCLM_hilbert :
    KreinSpace.kreinAdjoint (H := HilbertDoubled E) (KreinSpace.jCLM (H := HilbertDoubled E))
      = KreinSpace.jCLM (H := HilbertDoubled E) := by
  simp [KreinSpace.kreinAdjoint]

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
    change (u.1 + v.1) • (KreinSpace.jCLM (H := HilbertDoubled E)) +
        (u.2 + v.2) • (hilbertComplexI (E := E))
      = (u.1 • (KreinSpace.jCLM (H := HilbertDoubled E)) + u.2 • (hilbertComplexI (E := E)))
        + (v.1 • (KreinSpace.jCLM (H := HilbertDoubled E)) + v.2 • (hilbertComplexI (E := E)))
    have h2 : (u.2 + v.2) • (hilbertComplexI (E := E))
        = u.2 • (hilbertComplexI (E := E)) + v.2 • (hilbertComplexI (E := E)) := by
      simpa using (add_smul u.2 v.2 (hilbertComplexI (E := E)))
    have h1 : (u.1 + v.1) • (KreinSpace.jCLM (H := HilbertDoubled E))
        = u.1 • (KreinSpace.jCLM (H := HilbertDoubled E))
          + v.1 • (KreinSpace.jCLM (H := HilbertDoubled E)) := by
      simpa using (add_smul u.1 v.1 (KreinSpace.jCLM (H := HilbertDoubled E)))
    rw [h1, h2]
    abel_nf
  map_smul' := by
    intro a v
    change (a * v.1) • (KreinSpace.jCLM (H := HilbertDoubled E)) +
        (a * v.2) • (hilbertComplexI (E := E))
      = a • (v.1 • (KreinSpace.jCLM (H := HilbertDoubled E)) + v.2 • (hilbertComplexI (E := E)))
    simp [smul_add, smul_smul]

lemma cl11RepLinHilbert_apply_pair (a b : ℝ) (x y : E) :
    cl11RepLinHilbert (E := E) (a, b) (HilbertDoubled.toLp (E := E) (x, y))
      = HilbertDoubled.toLp (E := E) (a • x - b • y, b • x - a • y) := by
  apply HilbertDoubled.ext
  simpa [cl11RepLinHilbert, hilbertComplexI_apply, sub_eq_add_neg, Prod.smul_mk,
    add_comm, add_left_comm, add_assoc] using
    (show a • (WithLp.toLp 2 (x, -y) : DoubledSpace E) + b • (WithLp.toLp 2 (-y, x) : DoubledSpace E)
        = (WithLp.toLp 2 (a • x + -(b • y), b • x + -(a • y)) : DoubledSpace E) by
      rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]
      simp [Prod.smul_mk, sub_eq_add_neg, add_comm, add_left_comm, add_assoc])

lemma cl11RepLinHilbert_sq (v : ℝ × ℝ) :
    (cl11RepLinHilbert (E := E) v) * (cl11RepLinHilbert (E := E) v)
      = algebraMap ℝ (HilbertDoubled E →L[ℝ] HilbertDoubled E) (InfoGeometry.Clifford.splitQ11 v) := by
  rcases v with ⟨a, b⟩
  apply ContinuousLinearMap.ext
  intro u
  cases huxy : HilbertDoubled.ofLp (E := E) u with
  | mk x y =>
      have hu : u = HilbertDoubled.toLp (E := E) (x, y) := by
        apply HilbertDoubled.ext
        simpa [HilbertDoubled.ofLp, HilbertDoubled.toLp] using
          congrArg (WithLp.toLp (2 : ENNReal)) huxy
      rw [hu]
      apply HilbertDoubled.ext
      apply InfoGeometry.Krein.DoubledSpace.ext <;>
        simp [cl11RepLinHilbert_apply_pair, InfoGeometry.Clifford.splitQ11_apply, Algebra.algebraMap_eq_smul_one,
          sub_eq_add_neg, smul_smul]
      all_goals module

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
    apply ContinuousLinearMap.ext
    intro u
    cases huξ : HilbertDoubled.ofLp (E := E) u with
    | mk x ξ =>
        have hu : u = HilbertDoubled.toLp (E := E) (x, ξ) := by
          apply HilbertDoubled.ext
          simpa [HilbertDoubled.ofLp, HilbertDoubled.toLp] using
            congrArg (WithLp.toLp (2 : ENNReal)) huξ
        rw [hu]
        apply HilbertDoubled.ext
        apply InfoGeometry.Krein.DoubledSpace.ext <;>
          simp [gradeCLM_eq_hilbertSwapCLM, cl11RepHilbert_ι_apply, cl11RepLinHilbert_apply_pair,
            hilbertSwapCLM_apply, sub_eq_add_neg]
  kreinSelfAdj_ι := by
    intro v
    rcases v with ⟨a, b⟩
    simp [cl11RepHilbert_ι_apply, cl11RepLinHilbert, KreinSpace.kreinAdjoint_add,
      KreinSpace.kreinAdjoint_smul, kreinAdjoint_jCLM_hilbert, kreinAdjoint_hilbertComplexI]

section NeutralTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[simp] private lemma rotation45_apply_rotation45Isometry (u : NeutralSpace E) :
    (NeutralSpace.rotation45 (E := E)) ((NeutralSpace.rotation45Isometry (E := E)) u) = u := by
  exact (NeutralSpace.rotation45 (E := E)).right_inv u

/-- Grading on `NeutralSpace E` transported from the diagonal model by the 45-degree bridge. -/
private noncomputable def neutralGradeLIE : NeutralSpace E ≃ₗᵢ[ℝ] NeutralSpace E :=
  (NeutralSpace.rotation45ToHilbert (E := E)).trans
    ((hilbertSwapLIE (E := E)).trans (NeutralSpace.rotation45ToHilbert (E := E)).symm)

noncomputable instance instKreinGradedModuleNeutral :
    KreinGradedModule (NeutralSpace E) where
  grade := neutralGradeLIE (E := E)
  grade_invol := by
    intro u
    simpa [neutralGradeLIE] using
      congrArg ((NeutralSpace.rotation45ToHilbert (E := E)).symm) (hilbertSwap_invol (E := E) ((NeutralSpace.rotation45ToHilbert (E := E)) u))
  grade_selfAdj := by
    intro u v
    let R : NeutralSpace E ≃ₗᵢ[ℝ] HilbertDoubled E := NeutralSpace.rotation45ToHilbert (E := E)
    calc
      ⟪neutralGradeLIE (E := E) u, v⟫_ℝ
          = ⟪R (neutralGradeLIE (E := E) u), R v⟫_ℝ := by
              simp [R]
      _ = ⟪hilbertSwapLIE (E := E) (R u), R v⟫_ℝ := by
            simp [neutralGradeLIE, R]
      _ = ⟪R u, hilbertSwapLIE (E := E) (R v)⟫_ℝ := by
            simpa [R] using hilbertSwap_selfAdj (E := E) (R u) (R v)
      _ = ⟪R u, R (neutralGradeLIE (E := E) v)⟫_ℝ := by
            simp [neutralGradeLIE, R]
      _ = ⟪u, neutralGradeLIE (E := E) v⟫_ℝ := by
            simp [R]

/-- Conjugation by the 45-degree bridge on endomorphisms. -/
private noncomputable def rot45Conj :
    (NeutralSpace E →L[ℝ] NeutralSpace E) ≃ₐ[ℝ] (HilbertDoubled E →L[ℝ] HilbertDoubled E) :=
  (NeutralSpace.rotation45ToHilbertContinuousLinearEquiv (E := E)).conjContinuousAlgEquiv

/-- `Cl(1,1)` action on `NeutralSpace E`, transported from the diagonal action. -/
private noncomputable def cl11RepNeutral :
    CliffordAlgebra InfoGeometry.Clifford.splitQ11 →ₐ[ℝ] (NeutralSpace E →L[ℝ] NeutralSpace E) :=
  (rot45Conj (E := E)).symm.toAlgHom.comp (cl11RepHilbert (E := E))

@[simp] lemma rot45Conj_symm_apply_apply
    (f : HilbertDoubled E →L[ℝ] HilbertDoubled E) (u : NeutralSpace E) :
    (rot45Conj (E := E)).symm f u =
      (NeutralSpace.rotation45 (E := E))
        ((HilbertDoubled.toDoubledLIE (E := E)) (f ((NeutralSpace.rotation45ToHilbert (E := E)) u))) := by
  change
      ((NeutralSpace.rotation45ToHilbertContinuousLinearEquiv (E := E)).conjContinuousAlgEquiv.symm f) u
        = (NeutralSpace.rotation45 (E := E))
            ((HilbertDoubled.toDoubledLIE (E := E)) (f ((NeutralSpace.rotation45ToHilbert (E := E)) u)))
  exact ContinuousLinearEquiv.symm_conjContinuousAlgEquiv_apply_apply
    (e := NeutralSpace.rotation45ToHilbertContinuousLinearEquiv (E := E))
    (f := f) (x := u)

@[simp] lemma cl11RepNeutral_apply_apply
    (a : CliffordAlgebra InfoGeometry.Clifford.splitQ11) (u : NeutralSpace E) :
    cl11RepNeutral (E := E) a u =
      (NeutralSpace.rotation45 (E := E))
        ((HilbertDoubled.toDoubledLIE (E := E))
          ((cl11RepHilbert (E := E) a) ((NeutralSpace.rotation45ToHilbert (E := E)) u))) := by
  change ((rot45Conj (E := E)).symm (cl11RepHilbert (E := E) a)) u =
      (NeutralSpace.rotation45 (E := E))
        ((HilbertDoubled.toDoubledLIE (E := E))
          ((cl11RepHilbert (E := E) a) ((NeutralSpace.rotation45ToHilbert (E := E)) u)))
  change
      ((NeutralSpace.rotation45ToHilbertContinuousLinearEquiv (E := E)).conjContinuousAlgEquiv.symm
          (cl11RepHilbert (E := E) a)) u
        = (NeutralSpace.rotation45 (E := E))
            ((HilbertDoubled.toDoubledLIE (E := E))
              ((cl11RepHilbert (E := E) a) ((NeutralSpace.rotation45ToHilbert (E := E)) u)))
  exact ContinuousLinearEquiv.symm_conjContinuousAlgEquiv_apply_apply
    (e := NeutralSpace.rotation45ToHilbertContinuousLinearEquiv (E := E))
    (f := cl11RepHilbert (E := E) a) (x := u)

@[simp] lemma rotation45_cl11RepNeutral_apply
    (a : CliffordAlgebra InfoGeometry.Clifford.splitQ11) (u : NeutralSpace E) :
    (NeutralSpace.rotation45ToHilbert (E := E)) (cl11RepNeutral (E := E) a u) =
      (cl11RepHilbert (E := E) a) ((NeutralSpace.rotation45ToHilbert (E := E)) u) := by
  rw [cl11RepNeutral_apply_apply]
  simp

@[simp] lemma cl11RepNeutral_ι_apply (v : ℝ × ℝ) :
    cl11RepNeutral (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v) =
      (rot45Conj (E := E)).symm (cl11RepLinHilbert (E := E) v) := by
  simp [cl11RepNeutral, rot45Conj, cl11RepHilbert_ι_apply]

@[simp] lemma rotation45_gradeCLM_neutral_apply (u : NeutralSpace E) :
    (NeutralSpace.rotation45ToHilbert (E := E))
      (((neutralGradeLIE (E := E)).toLinearIsometry.toContinuousLinearMap) u) =
      hilbertSwapCLM (E := E) ((NeutralSpace.rotation45ToHilbert (E := E)) u) := by
  simp [neutralGradeLIE, hilbertSwapCLM, hilbertSwapLIE_apply]

/-
The transported map `cl11RepNeutral` is an explicit bridge construction on the hardened
`NeutralSpace` wrapper. The remaining debt here is no longer carrier aliasing, but finishing the
transported `SymmetricCliffordModule` layer with the current non-diagonal neutral model.
-/

end NeutralTransport

end Phase5Concrete
end InfoGeometry.Krein
