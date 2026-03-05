import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Linarith

/-!
# Real Krein Spaces — Canonical Mathlib 4.28.0 Implementation

## Mathematical Definition

A **real Krein space** `(H, [·,·])` is a real Hilbert space `(H, ⟪·,·⟫)` equipped with a
**fundamental symmetry** `J : H → H`:
- `J` is an involutive bounded linear operator: `J² = id`
- `J` is self-adjoint: `⟪Ju, v⟫ = ⟪u, Jv⟫`

The **Krein inner product** is `[u, v]_J = ⟪Ju, v⟫`.

## Canonical instances

- **Hilbert**: Any Hilbert space `H` with `J = id` (signature `(n, 0)`).
- **Diagonal**: `WithLp 2 (E × E)` with `J(x, y) = (x, -y)` (signature `(n, n)`).

## References

Azizov–Iokhvidov, *Linear Operators in Spaces with Indefinite Metric*
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

open scoped InnerProductSpace

/-! ## The KreinSpace Typeclass -/

/-- A **real Krein space**: a complete real inner product space with a fundamental symmetry `J`.

**Usage**: `variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]`
-/
class KreinSpace (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  /-- Fundamental symmetry: an involutive, self-adjoint, linear isometric equivalence. -/
  J : H ≃ₗᵢ[ℝ] H
  /-- J is an involution: J(Jx) = x. -/
  J_invol : ∀ x : H, J (J x) = x
  /-- J is self-adjoint: ⟪Ju, v⟫_ℝ = ⟪u, Jv⟫_ℝ. -/
  J_selfAdj : ∀ u v : H, ⟪J u, v⟫_ℝ = ⟪u, J v⟫_ℝ

namespace KreinSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

/-! ### Fundamental symmetry as a CLM -/

/-- `J` as a continuous linear map. -/
noncomputable def jCLM : H →L[ℝ] H :=
  (J : H ≃ₗᵢ[ℝ] H).toLinearIsometry.toContinuousLinearMap

@[simp] lemma jCLM_apply (x : H) : jCLM x = (J : H ≃ₗᵢ[ℝ] H) x := rfl

@[simp] lemma jCLM_comp_self :
    jCLM.comp (jCLM (H := H)) = ContinuousLinearMap.id ℝ H := by
  ext x; apply J_invol

/-- J is its own Hilbert adjoint: `J† = J`. -/
lemma jCLM_adjoint :
    ContinuousLinearMap.adjoint (jCLM (H := H)) = jCLM := by
  ext x; apply ext_inner_right ℝ; intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [jCLM_apply]
  exact (J_selfAdj x y).symm

/-! ### The Krein inner product -/

/-- The Krein inner product `[u, v]_J = ⟪Ju, v⟫_ℝ`. -/
noncomputable def kreinInner (u v : H) : ℝ :=
  ⟪(J : H ≃ₗᵢ[ℝ] H) u, v⟫_ℝ

/-- Simp lemma: `kreinInner u v = ⟪J u, v⟫_ℝ`. -/
@[simp] lemma kreinInner_def (u v : H) :
    kreinInner u v = ⟪(J : H ≃ₗᵢ[ℝ] H) u, v⟫_ℝ := rfl

/-- `[u, v]_J = [v, u]_J`. -/
lemma kreinInner_symm (u v : H) : kreinInner u v = kreinInner v u := by
  simp only [kreinInner_def]; rw [J_selfAdj]; exact real_inner_comm _ _

lemma kreinInner_add_left (u₁ u₂ v : H) :
    kreinInner (u₁ + u₂) v = kreinInner u₁ v + kreinInner u₂ v := by
  simp [kreinInner_def, map_add, inner_add_left]

lemma kreinInner_smul_left (c : ℝ) (u v : H) :
    kreinInner (c • u) v = c * kreinInner u v := by
  simp [kreinInner_def, map_smul, real_inner_smul_left]

/-! ### The Krein adjoint -/

/-- The Krein adjoint `A♯ = J A† J` (where `A†` is the Hilbert adjoint). -/
noncomputable def kreinAdjoint (A : H →L[ℝ] H) : H →L[ℝ] H :=
  jCLM.comp (ContinuousLinearMap.adjoint A |>.comp jCLM)

/-- `[Au, v]_J = [u, A♯v]_J` — the adjoint identity in the Krein inner product. -/
lemma kreinInner_kreinAdjoint (A : H →L[ℝ] H) (u v : H) :
    kreinInner (A u) v = kreinInner u (kreinAdjoint A v) := by
  simp only [kreinInner_def, kreinAdjoint, jCLM_apply, ContinuousLinearMap.comp_apply]
  calc ⟪(J : H ≃ₗᵢ[ℝ] H) (A u), v⟫_ℝ
      = ⟪A u, (J : H ≃ₗᵢ[ℝ] H) v⟫_ℝ := J_selfAdj (A u) v
    _ = ⟪u, ContinuousLinearMap.adjoint A ((J : H ≃ₗᵢ[ℝ] H) v)⟫_ℝ := by
          rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪(J : H ≃ₗᵢ[ℝ] H) u,
          (J : H ≃ₗᵢ[ℝ] H) (ContinuousLinearMap.adjoint A ((J : H ≃ₗᵢ[ℝ] H) v))⟫_ℝ := by
          rw [J_selfAdj, J_invol]

/-- `A` is **Krein-self-adjoint** if `A♯ = A`. -/
def IsKreinSelfAdjoint (A : H →L[ℝ] H) : Prop := kreinAdjoint A = A

/-- `A` is **Krein-skew-adjoint** if `A♯ = -A`. -/
def IsKreinSkewAdjoint (A : H →L[ℝ] H) : Prop := kreinAdjoint A = -A

/-- Characterization: Krein-skew-adjoint iff `[Au, v] + [u, Av] = 0`. -/
lemma isKreinSkewAdjoint_iff (A : H →L[ℝ] H) :
    IsKreinSkewAdjoint A ↔ ∀ u v : H, kreinInner (A u) v + kreinInner u (A v) = 0 := by
  constructor
  · intro h u v
    rw [kreinInner_kreinAdjoint, h]
    simp [kreinInner_def, inner_neg_right, ContinuousLinearMap.neg_apply]
  · intro h
    ext v; apply ext_inner_left ℝ; intro u
    calc ⟪u, (kreinAdjoint A) v⟫_ℝ
        = ⟪(J : H ≃ₗᵢ[ℝ] H) ((J : H ≃ₗᵢ[ℝ] H) u), (kreinAdjoint A) v⟫_ℝ := by rw [J_invol]
      _ = kreinInner ((J : H ≃ₗᵢ[ℝ] H) u) (kreinAdjoint A v) := rfl
      _ = kreinInner (A ((J : H ≃ₗᵢ[ℝ] H) u)) v := by rw [kreinInner_kreinAdjoint]
      _ = -kreinInner ((J : H ≃ₗᵢ[ℝ] H) u) (A v) := by
            have key := h ((J : H ≃ₗᵢ[ℝ] H) u) v
            exact add_eq_zero_iff_eq_neg.mp key
      _ = -⟪(J : H ≃ₗᵢ[ℝ] H) ((J : H ≃ₗᵢ[ℝ] H) u), A v⟫_ℝ := rfl
      _ = -⟪u, A v⟫_ℝ := by rw [J_invol]
      _ = ⟪u, (-A) v⟫_ℝ := by
            simp only [ContinuousLinearMap.neg_apply, inner_neg_right]

/-- `U` is a **Krein isometry** if `[Uu, Uv]_J = [u,v]_J` for all `u, v`. -/
def IsKreinIsometry (U : H →L[ℝ] H) : Prop :=
  ∀ u v : H, kreinInner (U u) (U v) = kreinInner u v

end KreinSpace

/-! ## Instance 1: Any Hilbert space with `J = id` -/

/-- Every complete real Hilbert space is a Krein space with `J = id`. -/
noncomputable instance (priority := 50) instKreinSpaceOfHilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    KreinSpace H where
  J := LinearIsometryEquiv.refl ℝ H
  J_invol := fun _ => rfl
  J_selfAdj := fun _ _ => rfl

/-! ## Instance 2: `WithLp 2 (E × E)` — the canonical diagonal (n,n) Krein space -/

section WithLpKrein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Explicitly provide the L2 instances to prevent synthesizer loops
noncomputable instance instL2NormedGroup : NormedAddCommGroup (WithLp 2 (E × E)) :=
  inferInstance
noncomputable instance instL2InnerProduct : InnerProductSpace ℝ (WithLp 2 (E × E)) :=
  WithLp.instProdInnerProductSpace
noncomputable instance instL2Complete : CompleteSpace (WithLp 2 (E × E)) :=
  inferInstance

/-! ### Sign-flip `J(x,y) = (x,-y)` as a `LinearIsometryEquiv` -/

/-- The sign-flip `(x,y) ↦ (x,-y)` as a linear map on `WithLp 2 (E × E)`. -/
private noncomputable def signFlipMap : WithLp 2 (E × E) →ₗ[ℝ] WithLp 2 (E × E) :=
  (WithLp.linearEquiv 2 ℝ (E × E)).symm.comp
    ((LinearMap.prod (LinearMap.fst ℝ E E) (-(LinearMap.snd ℝ E E))).comp
      (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap)

@[simp]
private lemma signFlipMap_apply (u : WithLp 2 (E × E)) :
    signFlipMap u = WithLp.toLp 2 ((WithLp.ofLp u).1, -(WithLp.ofLp u).2) := rfl

private lemma signFlipMap_invol (u : WithLp 2 (E × E)) :
    signFlipMap (signFlipMap u) = u := by
  rcases u with ⟨x, y⟩
  simp [signFlipMap_apply]

private lemma signFlipMap_norm (u : WithLp 2 (E × E)) : ‖signFlipMap u‖ = ‖u‖ := by
  -- Show inner product equality at the component level
  have hinner : ⟪signFlipMap u, signFlipMap u⟫_ℝ = ⟪u, u⟫_ℝ := by
    rcases u with ⟨x, ξ⟩
    rw [signFlipMap_apply, WithLp.prod_inner_apply, WithLp.prod_inner_apply, inner_neg_neg]

  -- Convert to equality of squares of norms
  have hsq : ‖signFlipMap u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner]

  -- Final bridge: a² = b² ∧ a ≥ 0 ∧ b ≥ 0 → a = b
  nlinarith [norm_nonneg u, norm_nonneg (signFlipMap u)]

private lemma signFlipMap_selfAdj (u v : WithLp 2 (E × E)) :
    ⟪signFlipMap u, v⟫_ℝ = ⟪u, signFlipMap v⟫_ℝ := by
  rcases u with ⟨x, ξ⟩
  rcases v with ⟨y, η⟩
  simp [signFlipMap_apply, WithLp.prod_inner_apply]

/-- The sign-flip `(x,y) ↦ (x,-y)` as a **linear isometric equivalence**
on `WithLp 2 (E × E)`. Fundamental symmetry for the diagonal `(n, n)` Krein space. -/
noncomputable def signFlipLIE : WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E) where
  toLinearEquiv := LinearEquiv.ofLinear (signFlipMap (E:=E)) (signFlipMap (E:=E))
    (LinearMap.ext signFlipMap_invol)
    (LinearMap.ext signFlipMap_invol)
  norm_map' := signFlipMap_norm

@[simp]
lemma signFlipLIE_apply (u : WithLp 2 (E × E)) :
    signFlipLIE (E := E) u = signFlipMap u := rfl

/-- **The canonical diagonal `(n,n) ` Krein space**: `WithLp 2 (E × E)` with `J(x,y) = (x,-y)`.

Krein inner product: `[u,v]_J = ⟪u₁,v₁⟫_ℝ - ⟪u₂,v₂⟫_ℝ`. -/
noncomputable instance instKreinSpaceProdL2 :
    KreinSpace (WithLp 2 (E × E)) where
  J := signFlipLIE (E := E)
  J_invol := signFlipMap_invol
  J_selfAdj := signFlipMap_selfAdj

/-- Krein inner product on `WithLp 2 (E × E)` equals `⟪u₁,v₁⟫_ℝ - ⟪u₂,v₂⟫_ℝ`. -/
lemma kreinInner_prodL2 (u v : WithLp 2 (E × E)) :
    KreinSpace.kreinInner u v =
    ⟪(WithLp.ofLp u).1, (WithLp.ofLp v).1⟫_ℝ -
    ⟪(WithLp.ofLp u).2, (WithLp.ofLp v).2⟫_ℝ := by
  rcases u with ⟨x, ξ⟩
  rcases v with ⟨y, η⟩
  simp [KreinSpace.kreinInner_def, instKreinSpaceProdL2, signFlipLIE_apply,
        signFlipMap_apply, WithLp.prod_inner_apply, sub_eq_add_neg]

namespace DoubleHilbert
/-- Explicit alias for `WithLp 2 (E × E)` as a `KreinSpace`. -/
abbrev Doubled (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  WithLp 2 (E × E)
end DoubleHilbert

end WithLpKrein

/-! ## KreinSpace morphisms (categorical structure) -/

/-- A **Krein homomorphism** `H → K`: a continuous linear map preserving the Krein inner product. -/
structure KreinHom (H K : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] [KreinSpace K] where
  hom : H →L[ℝ] K
  isometric : ∀ u v : H,
    KreinSpace.kreinInner (hom u) (hom v) = KreinSpace.kreinInner u v

/-- A **Krein isometric equivalence** `H ≃ K`: bijective Krein homomorphism. -/
structure KreinEquiv (H K : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] [KreinSpace K]
    extends H ≃L[ℝ] K where
  isometric : ∀ u v : H,
    KreinSpace.kreinInner (toFun u) (toFun v) = KreinSpace.kreinInner u v
