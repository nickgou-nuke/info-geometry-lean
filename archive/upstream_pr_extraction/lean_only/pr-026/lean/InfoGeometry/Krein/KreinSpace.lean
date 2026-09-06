import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Basic
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Tactic.Abel

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

namespace InfoGeometry.Krein
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

/-- Mathlib's `exp_units_conj`, `star_exp`, etc. go through a `ℚ`-normed-algebra path.
This global instance provides it via scalar restriction along `ℚ → ℝ`. -/
noncomputable instance instNormedAlgebraRat_end :
    NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

/-! ### Fundamental symmetry as a CLM -/

/-- `J` as a continuous linear map. -/
noncomputable def jCLM : H →L[ℝ] H :=
  (J : H ≃ₗᵢ[ℝ] H).toLinearIsometry.toContinuousLinearMap

@[simp] lemma jCLM_apply (x : H) : jCLM x = (J : H ≃ₗᵢ[ℝ] H) x := rfl

@[simp] lemma jCLM_comp_self :
    jCLM.comp (jCLM (H := H)) = ContinuousLinearMap.id ℝ H := by
  ext x; simp [KreinSpace.J_invol]

@[simp] lemma jCLM_comp_jCLM_comp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : F →L[ℝ] H) : jCLM.comp (jCLM.comp A) = A := by
  rw [← ContinuousLinearMap.comp_assoc, jCLM_comp_self, ContinuousLinearMap.id_comp]

@[simp] lemma comp_jCLM_comp_jCLM {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : H →L[ℝ] F) : (A.comp jCLM).comp jCLM = A := by
  rw [ContinuousLinearMap.comp_assoc, jCLM_comp_self, ContinuousLinearMap.comp_id]

lemma jCLM_adjoint_eq :
    ContinuousLinearMap.adjoint (jCLM (H := H)) = jCLM := by
  ext x; apply ext_inner_right ℝ; intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [jCLM_apply, KreinSpace.J_selfAdj]

/-- J is its own Hilbert adjoint: `J† = J`. -/
@[simp] lemma adjoint_jCLM :
    ContinuousLinearMap.adjoint (jCLM (H := H)) = jCLM (H := H) :=
  jCLM_adjoint_eq (H := H)

lemma jCLM_selfAdjoint : IsSelfAdjoint (jCLM (H := H)) := jCLM_adjoint_eq

/-! ### Krein inner product and adjoint -/

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

lemma kreinInner_add_right (u v₁ v₂ : H) :
    kreinInner u (v₁ + v₂) = kreinInner u v₁ + kreinInner u v₂ := by
  simp [kreinInner_def, inner_add_right]

lemma kreinInner_smul_left (c : ℝ) (u v : H) :
    kreinInner (c • u) v = c * kreinInner u v := by
  simp [kreinInner_def, map_smul, real_inner_smul_left]

lemma kreinInner_smul_right (c : ℝ) (u v : H) :
    kreinInner u (c • v) = c * kreinInner u v := by
  simp [kreinInner_def, real_inner_smul_right]

/-- The Krein adjoint `A♯ = J A† J` (where `A†` is the Hilbert adjoint). -/
noncomputable def kreinAdjoint (A : H →L[ℝ] H) : H →L[ℝ] H :=
    jCLM.comp ((ContinuousLinearMap.adjoint A).comp jCLM)

@[simp] lemma kreinAdjoint_apply (A : H →L[ℝ] H) (u : H) :
    kreinAdjoint A u = (J : H ≃ₗᵢ[ℝ] H) (ContinuousLinearMap.adjoint A ((J : H ≃ₗᵢ[ℝ] H) u)) := rfl

/-- `[Au, v]_J = [u, A♯v]_J` — the adjoint identity in the Krein inner product. -/
lemma kreinInner_kreinAdjoint (A : H →L[ℝ] H) (u v : H) :
    kreinInner (A u) v = kreinInner u (kreinAdjoint A v) := by
  simp only [kreinInner_def, kreinAdjoint_apply]
  calc ⟪(J : H ≃ₗᵢ[ℝ] H) (A u), v⟫_ℝ
      = ⟪A u, (J : H ≃ₗᵢ[ℝ] H) v⟫_ℝ := J_selfAdj (A u) v
    _ = ⟪u, ContinuousLinearMap.adjoint A ((J : H ≃ₗᵢ[ℝ] H) v)⟫_ℝ := by
          rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪(J : H ≃ₗᵢ[ℝ] H) u,
          (J : H ≃ₗᵢ[ℝ] H) (ContinuousLinearMap.adjoint A ((J : H ≃ₗᵢ[ℝ] H) v))⟫_ℝ := by
          rw [J_selfAdj, KreinSpace.J_invol]

/-! ### Star Algebra Properties -/

@[simp] lemma kreinAdjoint_id :
    kreinAdjoint (H := H) (ContinuousLinearMap.id ℝ H) = ContinuousLinearMap.id ℝ H := by
  simp [kreinAdjoint]

@[simp] lemma kreinAdjoint_zero :
    kreinAdjoint (H := H) (0 : H →L[ℝ] H) = 0 := by
  ext; simp [kreinAdjoint]

@[simp] lemma kreinAdjoint_add (A B : H →L[ℝ] H) :
    kreinAdjoint (H := H) (A + B) = kreinAdjoint (H := H) A + kreinAdjoint (H := H) B := by
  simp [kreinAdjoint, map_add]

@[simp] lemma kreinAdjoint_smul (c : ℝ) (A : H →L[ℝ] H) :
    kreinAdjoint (H := H) (c • A) = c • kreinAdjoint (H := H) A := by
  simp [kreinAdjoint, map_smul]

@[simp] lemma kreinAdjoint_comp (A B : H →L[ℝ] H) :
    kreinAdjoint (H := H) (A.comp B) = (kreinAdjoint (H := H) B).comp (kreinAdjoint (H := H) A) := by
  simp [kreinAdjoint, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

lemma kreinAdjoint_involutive (A : H →L[ℝ] H) :
    kreinAdjoint (H := H) (kreinAdjoint (H := H) A) = A := by
  simp [kreinAdjoint, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

@[simp] lemma kreinAdjoint_sub (A B : H →L[ℝ] H) :
    kreinAdjoint (H := H) (A - B) = kreinAdjoint (H := H) A - kreinAdjoint (H := H) B := by
  ext; simp [kreinAdjoint, map_sub]

@[simp] lemma kreinAdjoint_mul (A B : H →L[ℝ] H) :
    kreinAdjoint (H := H) (A * B) = kreinAdjoint (H := H) B * kreinAdjoint (H := H) A :=
  kreinAdjoint_comp A B

lemma kreinAdjoint_lie (A B : H →L[ℝ] H) :
    kreinAdjoint (H := H) ⁅A, B⁆ = ⁅kreinAdjoint B, kreinAdjoint A⁆ := by
  simp [Ring.lie_def]

lemma kreinAdjoint_lie_neg (A B : H →L[ℝ] H) :
    kreinAdjoint (H := H) ⁅A, B⁆
      = - ⁅kreinAdjoint (H := H) A, kreinAdjoint (H := H) B⁆ := by
  simpa [lie_skew] using (kreinAdjoint_lie (H := H) A B)



/-- `A` is **Krein-self-adjoint** if `A♯ = A`. -/
def IsKreinSelfAdjoint (A : H →L[ℝ] H) : Prop := kreinAdjoint A = A

/-- `A` is **Krein-skew-adjoint** if `A♯ = -A`. -/
def IsKreinSkewAdjoint (A : H →L[ℝ] H) : Prop := kreinAdjoint A = -A

/-- `A` is Krein-self-adjoint iff `A† = J A J`. -/
lemma isKreinSelfAdjoint_iff_adjoint_eq_j_conj (A : H →L[ℝ] H) :
    IsKreinSelfAdjoint A ↔
      ContinuousLinearMap.adjoint A = jCLM.comp (A.comp jCLM) := by
  constructor
  · intro h
    ext x
    have hx :=
      congrArg (fun T : H →L[ℝ] H => T ((J : H ≃ₗᵢ[ℝ] H) x)) h
    have hxJ := congrArg (fun y : H => (J : H ≃ₗᵢ[ℝ] H) y) hx
    simpa [kreinAdjoint_apply, jCLM_apply, KreinSpace.J_invol] using hxJ
  · intro h
    ext x
    simp [kreinAdjoint_apply, h, jCLM_apply, KreinSpace.J_invol]

/-- Characterization: Krein-self-adjoint iff `[Au, v] = [u, Av]`. -/
lemma isKreinSelfAdjoint_iff (A : H →L[ℝ] H) :
    IsKreinSelfAdjoint A ↔ ∀ u v : H, kreinInner (A u) v = kreinInner u (A v) := by
  constructor
  · intro h u v
    rw [kreinInner_kreinAdjoint, h]
  · intro h
    ext v
    apply ext_inner_left ℝ
    intro u
    calc
      ⟪u, (kreinAdjoint A) v⟫_ℝ
          = ⟪(J : H ≃ₗᵢ[ℝ] H) ((J : H ≃ₗᵢ[ℝ] H) u), (kreinAdjoint A) v⟫_ℝ := by
              rw [KreinSpace.J_invol]
      _ = kreinInner ((J : H ≃ₗᵢ[ℝ] H) u) (kreinAdjoint A v) := rfl
      _ = kreinInner (A ((J : H ≃ₗᵢ[ℝ] H) u)) v := by rw [kreinInner_kreinAdjoint]
      _ = kreinInner ((J : H ≃ₗᵢ[ℝ] H) u) (A v) := h _ _
      _ = ⟪(J : H ≃ₗᵢ[ℝ] H) ((J : H ≃ₗᵢ[ℝ] H) u), A v⟫_ℝ := rfl
      _ = ⟪u, A v⟫_ℝ := by rw [KreinSpace.J_invol]

/-- Krein-self-adjointness of `A` is Hilbert-self-adjointness of `J ∘ A`. -/
lemma isKreinSelfAdjoint_iff_j_comp_selfAdjoint (A : H →L[ℝ] H) :
    IsKreinSelfAdjoint A ↔ IsSelfAdjoint ((jCLM (H := H)).comp A) := by
  rw [isKreinSelfAdjoint_iff, ContinuousLinearMap.isSelfAdjoint_iff']
  constructor
  · intro h
    ext v
    apply ext_inner_left ℝ
    intro u
    calc
      ⟪u, ContinuousLinearMap.adjoint ((jCLM (H := H)).comp A) v⟫_ℝ
          = ⟪ContinuousLinearMap.adjoint ((jCLM (H := H)).comp A) v, u⟫_ℝ := by
              rw [real_inner_comm]
      _ = ⟪v, ((jCLM (H := H)).comp A) u⟫_ℝ :=
              ContinuousLinearMap.adjoint_inner_left ((jCLM (H := H)).comp A) u v
      _ = ⟪((jCLM (H := H)).comp A) u, v⟫_ℝ := by
              rw [real_inner_comm]
      _ = kreinInner (A u) v := rfl
      _ = kreinInner u (A v) := h u v
      _ = ⟪(J : H ≃ₗᵢ[ℝ] H) u, A v⟫_ℝ := rfl
      _ = ⟪u, ((jCLM (H := H)).comp A) v⟫_ℝ := J_selfAdj u (A v)
  · intro h u v
    calc
      kreinInner (A u) v
          = ⟪((jCLM (H := H)).comp A) u, v⟫_ℝ := rfl
      _ = ⟪v, ((jCLM (H := H)).comp A) u⟫_ℝ := by
              rw [real_inner_comm]
      _ = ⟪ContinuousLinearMap.adjoint ((jCLM (H := H)).comp A) v, u⟫_ℝ :=
              (ContinuousLinearMap.adjoint_inner_left ((jCLM (H := H)).comp A) u v).symm
      _ = ⟪u, ContinuousLinearMap.adjoint ((jCLM (H := H)).comp A) v⟫_ℝ := by
              rw [real_inner_comm]
      _ = ⟪u, ((jCLM (H := H)).comp A) v⟫_ℝ := by rw [h]
      _ = kreinInner u (A v) := (J_selfAdj u (A v)).symm

/-- `A` is Krein-skew-adjoint iff `A♯ = -A`. -/
lemma isKreinSkewAdjoint_iff_eq_neg {A : H →L[ℝ] H} :
    IsKreinSkewAdjoint A ↔ kreinAdjoint A = -A := Iff.rfl

/-- The commutator of two Krein-skew-adjoint operators is Krein-skew-adjoint.
This formally proves the Lie algebra closure of infinitesimal isometries. -/
lemma isKreinSkewAdjoint_lie {A B : H →L[ℝ] H}
    (hA : IsKreinSkewAdjoint A) (hB : IsKreinSkewAdjoint B) :
    IsKreinSkewAdjoint ⁅A, B⁆ := by
  rw [isKreinSkewAdjoint_iff_eq_neg, kreinAdjoint_lie]
  rw [isKreinSkewAdjoint_iff_eq_neg.mp hA, isKreinSkewAdjoint_iff_eq_neg.mp hB]
  -- ⁅-B, -A⁆ = ⁅B, A⁆ = -⁅A, B⁆
  rw [Ring.lie_def, Ring.lie_def, neg_mul, mul_neg, neg_neg, neg_mul, mul_neg, neg_neg]
  exact (neg_sub (A * B) (B * A)).symm

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
        = ⟪(J : H ≃ₗᵢ[ℝ] H) ((J : H ≃ₗᵢ[ℝ] H) u), (kreinAdjoint A) v⟫_ℝ := by rw [KreinSpace.J_invol]
      _ = kreinInner ((J : H ≃ₗᵢ[ℝ] H) u) (kreinAdjoint A v) := rfl
      _ = kreinInner (A ((J : H ≃ₗᵢ[ℝ] H) u)) v := by rw [kreinInner_kreinAdjoint]
      _ = -kreinInner ((J : H ≃ₗᵢ[ℝ] H) u) (A v) := by
            have key := h ((J : H ≃ₗᵢ[ℝ] H) u) v
            exact add_eq_zero_iff_eq_neg.mp key
      _ = -⟪(J : H ≃ₗᵢ[ℝ] H) ((J : H ≃ₗᵢ[ℝ] H) u), A v⟫_ℝ := rfl
      _ = -⟪u, A v⟫_ℝ := by rw [KreinSpace.J_invol]
      _ = ⟪u, (-A) v⟫_ℝ := by
            simp only [ContinuousLinearMap.neg_apply, inner_neg_right]

/-- `U` is a **Krein isometry** if `[Uu, Uv]_J = [u,v]_J` for all `u, v`. -/
def IsKreinIsometry (U : H →L[ℝ] H) : Prop :=
  ∀ u v : H, kreinInner (U u) (U v) = kreinInner u v

lemma isKreinIsometry_iff_star_comp_self (U : H →L[ℝ] H) :
    IsKreinIsometry U ↔ (kreinAdjoint U).comp U = ContinuousLinearMap.id ℝ H := by
  constructor
  · intro h
    ext v; apply ext_inner_left ℝ; intro u
    calc ⟪u, (kreinAdjoint U).comp U v⟫_ℝ
        = ⟪(J : H ≃ₗᵢ[ℝ] H) ((J : H ≃ₗᵢ[ℝ] H) u), (kreinAdjoint U).comp U v⟫_ℝ := by rw [KreinSpace.J_invol]
      _ = kreinInner ((J : H ≃ₗᵢ[ℝ] H) u) ((kreinAdjoint U).comp U v) := rfl
      _ = kreinInner (U ((J : H ≃ₗᵢ[ℝ] H) u)) (U v) := by rw [kreinInner_kreinAdjoint]; rfl
      _ = kreinInner ((J : H ≃ₗᵢ[ℝ] H) u) v := h _ _
      _ = ⟪(J : H ≃ₗᵢ[ℝ] H) ((J : H ≃ₗᵢ[ℝ] H) u), v⟫_ℝ := rfl
      _ = ⟪u, v⟫_ℝ := by rw [KreinSpace.J_invol]
  · intro h u v
    rw [kreinInner_kreinAdjoint, ← ContinuousLinearMap.comp_apply, h]
    simp

lemma IsKreinIsometry.id : IsKreinIsometry (ContinuousLinearMap.id ℝ H) := fun _ _ => rfl

lemma IsKreinIsometry.comp {U V : H →L[ℝ] H} (hU : IsKreinIsometry U) (hV : IsKreinIsometry V) :
    IsKreinIsometry (U.comp V) := fun u v => by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hU, hV]

lemma IsKreinIsometry.inv {U : H ≃L[ℝ] H} (hU : IsKreinIsometry (U : H →L[ℝ] H)) :
    IsKreinIsometry (U.symm : H →L[ℝ] H) := fun u v =>
  (hU (U.symm u) (U.symm v)).symm.trans (by simp)

lemma IsKreinIsometry.J : IsKreinIsometry (J (H := H) : H →L[ℝ] H) := fun u v => by
  simp [kreinInner_def, J_invol, J_selfAdj]

/-! ### Bilinear and Quadratic forms -/

/-- The Krein inner product as a bilinear form. -/
noncomputable def kreinBilin : LinearMap.BilinForm ℝ H :=
  LinearMap.mk₂ ℝ (kreinInner (H := H))
    (by intro u₁ u₂ v; simp [kreinInner_def, map_add, inner_add_left])
    (by intro c u v; simp [kreinInner_def, map_smul, real_inner_smul_left, smul_eq_mul])
    (by intro u v₁ v₂; simp [kreinInner_def, inner_add_right])
    (by intro c u v; simp [kreinInner_def, real_inner_smul_right, smul_eq_mul])

/-- The Krein metric as a quadratic map. -/
noncomputable def kreinQuad : QuadraticMap ℝ H ℝ :=
  (kreinBilin (H := H)).toQuadraticMap

@[simp] lemma kreinQuad_apply (v : H) :
    kreinQuad (H := H) v = kreinInner (H := H) v v := by
  simp [kreinQuad, kreinBilin]

@[simp] lemma kreinQuad_smul (c : ℝ) (v : H) :
    kreinQuad (H := H) (c • v) = c^2 * kreinQuad (H := H) v := by
  simp [kreinQuad_apply, kreinInner_def, inner_smul_left, inner_smul_right]
  ring

end KreinSpace

/-! ## Instance 1: Any Hilbert space with `J = id` -/

/-- Every complete real Hilbert space is a Krein space with `J = id`.
Priority is set lower than specific instances like `WithLp 2 (E × E)`. -/
noncomputable instance (priority := 100) instKreinSpaceOfHilbert
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
  (WithLp.linearEquiv 2 ℝ (E × E)).symm.toLinearMap.comp
    ((LinearMap.prod (LinearMap.fst ℝ E E) (-(LinearMap.snd ℝ E E))).comp
      (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap)

@[simp]
private lemma signFlipMap_apply (u : WithLp 2 (E × E)) :
    signFlipMap u = WithLp.toLp 2 ((WithLp.ofLp u).1, -(WithLp.ofLp u).2) := by
  simp [signFlipMap]

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

Higher priority than the generic Hilbert instance. -/
noncomputable instance (priority := 1000) instKreinSpaceProdL2 :
    KreinSpace (WithLp 2 (E × E)) where
  J := signFlipLIE (E := E)
  J_invol := signFlipMap_invol
  J_selfAdj := signFlipMap_selfAdj

/-- Krein inner product on `WithLp 2 (E × E)` equals `⟪u₁,v₁⟫_ℝ - ⟪u₂,v₂⟫_ℝ`. -/
lemma krein_inner_prod_l2 (u v : WithLp 2 (E × E)) :
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

/-- Centralized ContinuousLinearEquiv conjugation for Krein automorphisms.
Replaces ad-hoc `U ∘ A ∘ U⁻¹` throughout the codebase. -/
noncomputable def conjKreinEquiv {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] [KreinSpace K]
    (U : KreinEquiv H K) :
    (H →L[ℝ] H) ≃ₐ[ℝ] (K →L[ℝ] K) :=
  ContinuousLinearEquiv.conjContinuousAlgEquiv U.toContinuousLinearEquiv


end InfoGeometry.Krein
