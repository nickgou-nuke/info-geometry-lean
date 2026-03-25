import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Cartan.Involution
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# InfoGeometry.Krein.DoubledSpace

Direct canonical doubled states `WithLp 2 (E × E)` acting as an `L²` doubled model.
We equip this product with the $L^2$ sum norm and Krein symmetries.

Provides:
- `DoubledSpace E`: the canonical doubled space
- `modular_j`: swap isometry (modular swap)
- `spectral_epsilon`: fundamental symmetry (sign flip)
- `complex_i`: canonical complex structure $J \circ \epsilon$
-/

namespace InfoGeometry.Krein

open InfoGeometry.Cartan

section Compatibility

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Alias for the canonical doubled Hilbert space `WithLp 2 (E × E)`. -/
abbrev DoubledSpace (E : Type*) : Type _ := WithLp (2 : ENNReal) (E × E)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Extensionality lemma for `DoubledSpace`. -/
@[ext] lemma DoubledSpace.ext {u v : DoubledSpace E}
    (hfst : WithLp.fst u = WithLp.fst v)
    (hsnd : WithLp.snd u = WithLp.snd v) : u = v := by
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  exact Prod.ext hfst hsnd

/-- Create a doubled state from a physical and a ghost component. -/
abbrev to_doubled (x ξ : E) : DoubledSpace E := WithLp.toLp (2 : ENNReal) (x, ξ)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] lemma fst_to_doubled (x ξ : E) :
    WithLp.fst (to_doubled x ξ : DoubledSpace E) = x := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] lemma snd_to_doubled (x ξ : E) :
    WithLp.snd (to_doubled x ξ : DoubledSpace E) = ξ := rfl

/-- Physical coordinate projection as a continuous linear map. -/
noncomputable abbrev fst_L : DoubledSpace E →L[ℝ] E :=
  WithLp.fstL (p := (2 : ENNReal)) ℝ E E

/-- Ghost coordinate projection as a continuous linear map. -/
noncomputable abbrev snd_L : DoubledSpace E →L[ℝ] E :=
  WithLp.sndL (p := (2 : ENNReal)) ℝ E E

/-- The modular swap $J(x, \xi) = (\xi, x)$ as a continuous linear map. -/
noncomputable def modular_j : DoubledSpace E →L[ℝ] DoubledSpace E where
  toFun u := WithLp.toLp (2 : ENNReal) (WithLp.snd u, WithLp.fst u)
  map_add' u v := by
    simpa [WithLp.add_snd, WithLp.add_fst] using
      (WithLp.toLp_add (p := (2 : ENNReal))
        (x := (WithLp.snd u, WithLp.fst u))
        (y := (WithLp.snd v, WithLp.fst v)))
  map_smul' c u := by
    simpa [WithLp.smul_snd, WithLp.smul_fst] using
      (WithLp.toLp_smul (p := (2 : ENNReal)) (c := c)
        (x := (WithLp.snd u, WithLp.fst u)))
  cont := by
    simpa using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
        ((WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := E)).prodMk
         (WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := E)))

/-- The fundamental symmetry $\epsilon(x, \xi) = (x, -\xi)$ as a continuous linear map. -/
noncomputable def spectral_epsilon : DoubledSpace E →L[ℝ] DoubledSpace E where
  toFun u := WithLp.toLp (2 : ENNReal) (WithLp.fst u, -WithLp.snd u)
  map_add' u v := by
    simpa [WithLp.add_fst, WithLp.add_snd, neg_add, add_comm] using
      (WithLp.toLp_add (p := (2 : ENNReal))
        (x := (WithLp.fst u, -WithLp.snd u))
        (y := (WithLp.fst v, -WithLp.snd v)))
  map_smul' c u := by
    simpa [WithLp.smul_fst, WithLp.smul_snd, smul_neg] using
      (WithLp.toLp_smul (p := (2 : ENNReal)) (c := c)
        (x := (WithLp.fst u, -WithLp.snd u)))
  cont := by
    simpa using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
        ((WithLp.continuous_fst (p := (2 : ENNReal)) (α := E) (β := E)).prodMk
         (continuous_neg.comp (WithLp.continuous_snd (p := (2 : ENNReal)) (α := E) (β := E))))

/-- Canonical complex-like generator $I = J \circ \epsilon$. -/
noncomputable def complex_i : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modular_j.comp spectral_epsilon

/-- $Cl(1,1)$ compatibility relation package on doubled-space endomorphisms. -/
def cl11_relations (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  J.comp J = ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
  ε.comp ε = ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
  J.comp ε = -(ε.comp J)

/-- Typeclass alias for the Clifford structure. -/
abbrev cl11_algebra (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  cl11_relations J ε

omit [CompleteSpace E] in
@[simp] lemma modular_j_apply (u : DoubledSpace E) :
    modular_j u = WithLp.toLp (2 : ENNReal) (WithLp.snd u, WithLp.fst u) := rfl

omit [CompleteSpace E] in
@[simp] lemma spectral_epsilon_apply (u : DoubledSpace E) :
    spectral_epsilon u = WithLp.toLp (2 : ENNReal) (WithLp.fst u, -WithLp.snd u) := rfl

omit [CompleteSpace E] in
@[simp] lemma complex_i_apply (u : DoubledSpace E) :
    complex_i u = WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u) := by
  apply DoubledSpace.ext <;> simp [complex_i]

lemma modular_j_involution (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (modular_j (E := E)).comp modular_j = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext; intro u
  apply DoubledSpace.ext <;> simp

lemma spectral_epsilon_involution (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (spectral_epsilon (E := E)).comp spectral_epsilon = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext; intro u
  apply DoubledSpace.ext <;> simp

lemma modular_j_spectral_epsilon_anticommute (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (modular_j (E := E)).comp spectral_epsilon = -(spectral_epsilon.comp modular_j) := by
  apply ContinuousLinearMap.ext; intro u
  apply DoubledSpace.ext <;> simp [modular_j_apply, spectral_epsilon_apply]

lemma complex_i_sq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (complex_i (E := E)).comp complex_i = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  apply ContinuousLinearMap.ext; intro u
  apply DoubledSpace.ext <;> simp [complex_i]

theorem modular_j_spectral_epsilon_has_cl11_relations (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    cl11_relations (modular_j (E := E)) spectral_epsilon :=
  ⟨modular_j_involution E, spectral_epsilon_involution E, modular_j_spectral_epsilon_anticommute E⟩

theorem modular_j_spectral_epsilon_is_cl11 (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    cl11_algebra (modular_j (E := E)) spectral_epsilon :=
  modular_j_spectral_epsilon_has_cl11_relations E

/-- Modular J as a linear equivalence. -/
noncomputable def modular_jLE (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E ≃ₗ[ℝ] DoubledSpace E :=
  { modular_j (E := E).toLinearMap with
    invFun := modular_j (E := E)
    left_inv := fun x => by
      have h := congrArg (fun f => f x) (modular_j_involution E)
      simpa using h
    right_inv := fun x => by
      have h := congrArg (fun f => f x) (modular_j_involution E)
      simpa using h }

/-- Spectral epsilon as a linear equivalence. -/
noncomputable def spectral_epsilonLE (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E ≃ₗ[ℝ] DoubledSpace E :=
  { spectral_epsilon (E := E).toLinearMap with
    invFun := spectral_epsilon (E := E)
    left_inv := fun x => by
      have h := congrArg (fun f => f x) (spectral_epsilon_involution E)
      simpa using h
    right_inv := fun x => by
      have h := congrArg (fun f => f x) (spectral_epsilon_involution E)
      simpa using h }

lemma modular_j_is_cartan (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCartanInvolution (modular_jLE E).toLinearMap := by
  have h := modular_j_involution E
  exact congrArg ContinuousLinearMap.toLinearMap h

lemma spectral_epsilon_is_cartan (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCartanInvolution (spectral_epsilonLE E).toLinearMap := by
  have h := spectral_epsilon_involution E
  exact congrArg ContinuousLinearMap.toLinearMap h

end Compatibility

section KreinAnalytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => WithLp (2 : ENNReal) (E × E)

/-- The Hessian indefinite form on DoubledSpace. -/
noncomputable def hessian_indefinite_form (u v : H₂) : ℝ :=
  KreinSpace.kreinInner (H := H₂) u v

/-- Characterization of Krein skew-adjointness. -/
def is_krein_skew_adjoint (A : H₂ →L[ℝ] H₂) : Prop :=
  KreinSpace.IsKreinSkewAdjoint (H := H₂) A

theorem is_krein_skew_adjoint_hessian_infinitesimal
    {A : H₂ →L[ℝ] H₂}
    (hA : is_krein_skew_adjoint A)
    (x y : H₂) :
    hessian_indefinite_form (A x) y + hessian_indefinite_form x (A y) = 0 :=
  (KreinSpace.isKreinSkewAdjoint_iff (H := H₂) A).mp hA x y

/-- The Lie algebra of the information state space. -/
noncomputable def information_lie_algebra :
    LieSubalgebra ℝ (H₂ →L[ℝ] H₂) where
  carrier := {A | is_krein_skew_adjoint A}
  zero_mem' := by
    simp [is_krein_skew_adjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg (H := H₂)]
  add_mem' hA hB := by
    simp [is_krein_skew_adjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg (H := H₂)] at hA hB ⊢
    rw [hA, hB]
    simp [add_comm]
  smul_mem' c A hA := by
    simp [is_krein_skew_adjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg (H := H₂)] at hA ⊢
    rw [hA, smul_neg]
  lie_mem' hA hB := by
    simpa [is_krein_skew_adjoint] using
      (KreinSpace.isKreinSkewAdjoint_lie (H := H₂) (hA := hA) (hB := hB))

end KreinAnalytic

end InfoGeometry.Krein
