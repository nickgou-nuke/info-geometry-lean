import InfoGeometry.Krein.KreinSpace
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

open scoped InnerProductSpace

namespace InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Diagonal Doubled Hilbert Space -/

abbrev HilbertDoubled (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  WithLp (2 : ENNReal) (E × E)

noncomputable instance instKreinSpaceHilbertDoubled :
    KreinSpace (HilbertDoubled E) :=
  instKreinSpaceProdL2

/-! ## NeutralSpace — Hessian / Bogoliubov neutral Krein model

Distinct type wrapping `WithLp 2 (E×E)` to prevent instance resonance with the diagonal model.
Fundamental symmetry: swap `J(x,y) = (y,x)`.
Krein form: `[u,v]_J = ⟪x₁,y₂⟫ + ⟪x₂,y₁⟫` (Hessian cross-term / Bogoliubov metric).
-/
structure NeutralSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  val : WithLp (2 : ENNReal) (E × E)

namespace NeutralSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

instance : Coe (NeutralSpace E) (WithLp (2 : ENNReal) (E × E)) := ⟨NeutralSpace.val⟩

@[simp] def ofWithLp (u : WithLp (2 : ENNReal) (E × E)) : NeutralSpace E := ⟨u⟩
@[simp] lemma val_ofWithLp (u : WithLp (2 : ENNReal) (E × E)) :
    (ofWithLp (E := E) u).val = u := rfl
@[simp] lemma ofWithLp_val (u : NeutralSpace E) :
    ofWithLp (E := E) u.val = u := by cases u; rfl
@[ext] lemma ext {u v : NeutralSpace E} (h : u.val = v.val) : u = v := by
  cases u; cases v; cases h; rfl

abbrev ofLp (u : NeutralSpace E) : E × E := WithLp.ofLp u.val
abbrev toLp (v : E × E) : NeutralSpace E := ofWithLp (E := E) (WithLp.toLp 2 v)
@[simp] lemma ofLp_toLp (v : E × E) : ofLp (E := E) (toLp (E := E) v) = v := rfl
@[simp] lemma toLp_ofLp (u : NeutralSpace E) : toLp (E := E) (ofLp (E := E) u) = u := by
  cases u; rfl

/-! ### Algebraic instances
Using the user-suggested pattern: explicit `@[simp]` val-lemmas + `ext; exact` axiom proofs
to delegate everything to the WithLp layer. -/

noncomputable instance : Zero (NeutralSpace E) := ⟨⟨0⟩⟩
noncomputable instance : Add (NeutralSpace E) := ⟨fun u v => ⟨u.val + v.val⟩⟩
noncomputable instance : Neg (NeutralSpace E) := ⟨fun u => ⟨-u.val⟩⟩

-- IMPORTANT: define subtraction as `a + -b` so `sub_eq_add_neg` is definitional.
noncomputable instance : Sub (NeutralSpace E) := ⟨fun a b => a + -b⟩

noncomputable instance : SMul ℝ (NeutralSpace E) := ⟨fun r u => ⟨r • u.val⟩⟩

-- Do NOT define `SMul ℕ` / `SMul ℤ` manually; they come from the group structure.

@[simp] lemma val_zero : (0 : NeutralSpace E).val = 0 := rfl
@[simp] lemma val_add (u v : NeutralSpace E) : (u + v).val = u.val + v.val := rfl
@[simp] lemma val_neg (u : NeutralSpace E) : (-u).val = -u.val := rfl
@[simp] lemma val_sub (u v : NeutralSpace E) : (u - v).val = u.val + -v.val := rfl
@[simp] lemma val_smul (a : ℝ) (u : NeutralSpace E) : (a • u).val = a • u.val := rfl

/-- Additive commutative group structure pulled back from the underlying `WithLp` carrier. -/
noncomputable instance instAddCommGroup : AddCommGroup (NeutralSpace E) where
  add_assoc a b c := by ext; exact add_assoc a.val b.val c.val
  zero_add a := by ext; exact zero_add a.val
  add_zero a := by ext; exact add_zero a.val
  neg_add_cancel a := by ext; exact neg_add_cancel a.val
  add_comm a b := by ext; exact add_comm a.val b.val
  sub_eq_add_neg a b := by rfl
  nsmul n a := ⟨n • a.val⟩
  nsmul_zero a := by ext; exact zero_smul ℕ a.val
  nsmul_succ n a := by
    apply ext; simp only [val_add]; exact succ_nsmul a.val n
  zsmul z a := ⟨z • a.val⟩
  zsmul_zero' a := by ext; exact zero_smul ℤ a.val
  zsmul_succ' n a := by
    apply ext; simp only [val_add]
    exact_mod_cast succ_nsmul a.val n
  zsmul_neg' n a := by
    apply ext; simp only [val_neg]
    exact_mod_cast negSucc_zsmul a.val n

/-- `ℝ`-module structure (needed downstream for `NormedSpace`, hence `InnerProductSpace`). -/
noncomputable instance instModule : Module ℝ (NeutralSpace E) where
  one_smul a := by ext; exact one_smul ℝ a.val
  mul_smul r s a := by ext; exact mul_smul r s a.val
  smul_add r a b := by ext; exact smul_add r a.val b.val
  add_smul r s a := by ext; exact add_smul r s a.val
  zero_smul a := by ext; exact zero_smul ℝ a.val
  smul_zero r := by ext; exact smul_zero r

/-! ### Norm and inner product (pulled back via `val`) -/

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (NeutralSpace E) :=
  { instAddCommGroup with
    norm := fun u => ‖u.val‖
    dist := fun u v => dist u.val v.val
    edist := fun u v => edist u.val v.val
    dist_eq := fun u v => by
      -- dist u v = dist u.val v.val = ‖u.val - v.val‖
      show dist u.val v.val = ‖u.val + -v.val‖
      rw [← sub_eq_add_neg]
      exact dist_eq_norm u.val v.val
    edist_dist := fun u v => edist_dist u.val v.val
    dist_self := fun u => dist_self u.val
    dist_comm := fun u v => dist_comm u.val v.val
    dist_triangle := fun u v w => dist_triangle u.val v.val w.val
    eq_of_dist_eq_zero := fun {u v} h => ext (eq_of_dist_eq_zero h) }

noncomputable instance instNormedSpace : NormedSpace ℝ (NeutralSpace E) :=
  { instModule with norm_smul_le := fun r u => norm_smul_le r u.val }

/-- Isometric linear equivalence `NeutralSpace E ≃ₗᵢ[ℝ] WithLp 2 (E×E)` via `.val`. -/
noncomputable def isoWithLp : NeutralSpace E ≃ₗᵢ[ℝ] WithLp (2 : ENNReal) (E × E) where
  toFun := val
  invFun := ofWithLp
  left_inv := ofWithLp_val
  right_inv := val_ofWithLp
  map_add' := val_add
  map_smul' := val_smul
  norm_map' := fun _ => rfl

-- To unstick `CompleteSpace`, we just use the topology equivalence directly:
noncomputable instance instCompleteSpace : CompleteSpace (NeutralSpace E) :=
  @IsometryEquiv.completeSpace (NeutralSpace E) (WithLp 2 (E × E)) _ _ _ (isoWithLp (E := E)).toIsometryEquiv

noncomputable instance instInnerProductSpace : InnerProductSpace ℝ (NeutralSpace E) :=
  { (instNormedAddCommGroup : NormedAddCommGroup (NeutralSpace E)) with
    inner := fun u v => ⟪u.val, v.val⟫_ℝ
    norm_sq_eq_re_inner := fun u => by
      show ‖u.val‖ ^ 2 = _
      exact norm_sq_eq_re_inner u.val
    conj_inner_symm := fun u v => real_inner_comm u.val v.val
    add_left := fun u v w => by simp [inner_add_left]
    smul_left := fun r _ v => by
      simp only [val_smul]
      rw [real_inner_smul_left]
      -- On ℝ, star r = r, so (starRingEnd ℝ) r * x = r * x
      simp }

/-! ### Neutral fundamental symmetry: swap `(x,y) ↦ (y,x)`

Build `neutralJ` as a `LinearIsometryEquiv` by composing the isometry `isoWithLp` with
a `LinearIsometryEquiv` on `WithLp 2 (E×E)` defined by the swap map. This avoids
having to prove `map_add'`/`map_smul'` goals about `WithLp.toLp` addition/scalar multiplication,
which are definitionally non-trivial. -/

/-- The swap `(x,y)↦(y,x)` as a `LinearIsometryEquiv` on `WithLp 2 (E×E)`.
Norm preservation: `‖(y,x)‖_L2 = ‖(x,y)‖_L2` since L2 norm is symmetric. -/
private noncomputable def swapLIE : WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E) where
  toFun u := WithLp.toLp 2 ((WithLp.ofLp u).2, (WithLp.ofLp u).1)
  invFun u := WithLp.toLp 2 ((WithLp.ofLp u).2, (WithLp.ofLp u).1)
  left_inv u := by rcases u with ⟨x, ξ⟩; rfl
  right_inv u := by rcases u with ⟨x, ξ⟩; rfl
  map_add' u v := by
    rcases u with ⟨x, ξ⟩; rcases v with ⟨y, η⟩; rfl
  map_smul' r u := by
    rcases u with ⟨x, ξ⟩; rfl
  norm_map' u := by
    rcases u with ⟨x, ξ⟩
    have h1 : ‖(WithLp.toLp 2 (ξ, x) : WithLp 2 (E × E))‖ ^ 2 =
              ‖(WithLp.toLp 2 (x, ξ) : WithLp 2 (E × E))‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
      exact add_comm _ _
    have h2 : (‖(WithLp.toLp 2 (ξ, x) : WithLp 2 (E × E))‖ : ℝ) =
              (‖(WithLp.toLp 2 (x, ξ) : WithLp 2 (E × E))‖ : ℝ) := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (ξ, x) : WithLp 2 (E × E)),
                 norm_nonneg (WithLp.toLp 2 (x, ξ) : WithLp 2 (E × E))]
    exact_mod_cast h2

omit [CompleteSpace E] in
private lemma swapLIE_selfAdj (u v : WithLp 2 (E × E)) :
    ⟪swapLIE (E := E) u, v⟫_ℝ = ⟪u, swapLIE (E := E) v⟫_ℝ := by
  rcases u with ⟨x, ξ⟩; rcases v with ⟨y, η⟩
  simp [swapLIE, WithLp.prod_inner_apply, add_comm]

/-- The swap `J(x,y)=(y,x)` as a `LinearIsometryEquiv` on `NeutralSpace E`,
built by conjugation through `isoWithLp`. -/
noncomputable def neutralJ : NeutralSpace E ≃ₗᵢ[ℝ] NeutralSpace E :=
  (isoWithLp (E := E)).trans ((swapLIE (E := E)).trans (isoWithLp (E := E)).symm)

@[simp] lemma val_neutralJ (u : NeutralSpace E) :
    (neutralJ u).val = swapLIE u.val := rfl

lemma neutralJ_invol (u : NeutralSpace E) :
    neutralJ (neutralJ u) = u := by
  apply ext
  rw [val_neutralJ, val_neutralJ]
  cases u with | mk u => rcases u with ⟨x, ξ⟩; rfl

lemma neutralJ_selfAdj (u v : NeutralSpace E) :
    ⟪neutralJ u, v⟫_ℝ = ⟪u, neutralJ v⟫_ℝ := by
  change ⟪(neutralJ u).val, v.val⟫_ℝ = ⟪u.val, (neutralJ v).val⟫_ℝ
  rw [val_neutralJ, val_neutralJ]
  exact swapLIE_selfAdj (E := E) u.val v.val

/-! ### KreinSpace instance -/

noncomputable instance instKreinSpaceNeutral : KreinSpace (NeutralSpace E) where
  J := neutralJ
  J_invol := neutralJ_invol
  J_selfAdj := neutralJ_selfAdj

/-! ### 45-degree bridge between neutral and diagonal models -/

private noncomputable def rotation45Coeff : ℝ := Real.sqrt ((1 : ℝ) / 2)

private lemma rotation45Coeff_sq :
    rotation45Coeff ^ 2 = (1 : ℝ) / 2 := by
  unfold rotation45Coeff
  have h : 0 ≤ (1 : ℝ) / 2 := by positivity
  exact Real.sq_sqrt h

private lemma rotation45Coeff_mul :
    rotation45Coeff * rotation45Coeff = (1 : ℝ) / 2 := by
  simpa [pow_two] using rotation45Coeff_sq

/-- The 45-degree rotation on raw doubled coordinates:
`(x, ξ) ↦ ((x + ξ)/√2, (x - ξ)/√2)`. -/
private noncomputable def rotation45CoordMap : E × E →ₗ[ℝ] E × E where
  toFun v :=
    (rotation45Coeff • v.1 + rotation45Coeff • v.2,
      rotation45Coeff • v.1 - rotation45Coeff • v.2)
  map_add' v w := by
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add]
  map_smul' a v := by
    ext <;>
      simp [smul_add, smul_sub, smul_smul, mul_comm]

omit [CompleteSpace E] in
@[simp] private lemma rotation45CoordMap_apply (v : E × E) :
    rotation45CoordMap v =
      (rotation45Coeff • v.1 + rotation45Coeff • v.2,
        rotation45Coeff • v.1 - rotation45Coeff • v.2) := rfl

omit [CompleteSpace E] in
private lemma rotation45CoordMap_invol (v : E × E) :
    rotation45CoordMap (rotation45CoordMap v) = v := by
  rcases v with ⟨x, ξ⟩
  have hsq : rotation45Coeff * rotation45Coeff = (1 : ℝ) / 2 := rotation45Coeff_mul
  ext
  · calc
      (rotation45CoordMap (rotation45CoordMap (x, ξ))).1
          = (rotation45Coeff * rotation45Coeff) • x + (rotation45Coeff * rotation45Coeff) • ξ +
              ((rotation45Coeff * rotation45Coeff) • x -
                (rotation45Coeff * rotation45Coeff) • ξ) := by
                simp [rotation45CoordMap_apply, smul_add, smul_smul, sub_eq_add_neg,
                  add_assoc, add_left_comm]
      _ = (rotation45Coeff * rotation45Coeff) • x + (rotation45Coeff * rotation45Coeff) • x := by
            abel_nf
      _ = ((rotation45Coeff * rotation45Coeff) + (rotation45Coeff * rotation45Coeff)) • x := by
            rw [add_smul]
      _ = x := by
            rw [hsq]
            module
  · calc
      (rotation45CoordMap (rotation45CoordMap (x, ξ))).2
          = (rotation45Coeff * rotation45Coeff) • x + (rotation45Coeff * rotation45Coeff) • ξ -
              ((rotation45Coeff * rotation45Coeff) • x -
                (rotation45Coeff * rotation45Coeff) • ξ) := by
                simp [rotation45CoordMap_apply, smul_add, smul_smul, sub_eq_add_neg,
                  add_assoc, add_left_comm]
      _ = (rotation45Coeff * rotation45Coeff) • ξ + (rotation45Coeff * rotation45Coeff) • ξ := by
            abel_nf
      _ = ((rotation45Coeff * rotation45Coeff) + (rotation45Coeff * rotation45Coeff)) • ξ := by
            rw [add_smul]
      _ = ξ := by
            rw [hsq]
            module

/-- The 45-degree rotation lifted to the `L²` doubled Hilbert carrier. -/
private noncomputable def rotation45Map : HilbertDoubled E →ₗ[ℝ] HilbertDoubled E :=
  (WithLp.linearEquiv 2 ℝ (E × E)).symm.toLinearMap.comp
    (rotation45CoordMap.comp (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap)

@[simp] private lemma rotation45Map_apply (u : HilbertDoubled E) :
    rotation45Map u = WithLp.toLp 2 (rotation45CoordMap (WithLp.ofLp u)) := by
  simp [rotation45Map]

private lemma rotation45Map_invol (u : HilbertDoubled E) :
    rotation45Map (rotation45Map u) = u := by
  apply (WithLp.ofLp_injective 2)
  simpa [rotation45Map_apply] using
    rotation45CoordMap_invol (E := E) (WithLp.ofLp u)

private lemma rotation45Map_inner (u v : HilbertDoubled E) :
    ⟪rotation45Map u, rotation45Map v⟫_ℝ = ⟪u, v⟫_ℝ := by
  rcases u with ⟨x, ξ⟩
  rcases v with ⟨y, η⟩
  simp [rotation45Map_apply, rotation45CoordMap_apply, WithLp.prod_inner_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    sub_eq_add_neg]
  ring_nf
  have hsq : rotation45Coeff ^ 2 = (1 : ℝ) / 2 := rotation45Coeff_sq
  rw [hsq]
  ring_nf

/-- The 45-degree Hilbert isometry on the diagonal `L²` doubled carrier. -/
private noncomputable def rotation45LIE : HilbertDoubled E ≃ₗᵢ[ℝ] HilbertDoubled E :=
  (LinearEquiv.ofLinear (rotation45Map (E := E)) (rotation45Map (E := E))
    (LinearMap.ext (rotation45Map_invol (E := E)))
    (LinearMap.ext (rotation45Map_invol (E := E)))).isometryOfInner
      (rotation45Map_inner (E := E))

@[simp] private lemma rotation45LIE_apply (u : HilbertDoubled E) :
    rotation45LIE u = rotation45Map u := rfl

private lemma rotation45LIE_intertwines_swap (u : HilbertDoubled E) :
    signFlipLIE (E := E) (rotation45LIE (E := E) u) =
      rotation45LIE (E := E) (swapLIE (E := E) u) := by
  rcases u with ⟨x, ξ⟩
  apply (WithLp.ofLp_injective 2)
  simp [rotation45LIE_apply, rotation45Map_apply, rotation45CoordMap_apply,
    signFlipLIE_apply, swapLIE, sub_eq_add_neg, add_comm]

/-- The 45-degree Hilbert isometric equivalence from the neutral Bogoliubov model
to the diagonal Pontryagin model. -/
noncomputable def rotation45Isometry : NeutralSpace E ≃ₗᵢ[ℝ] HilbertDoubled E :=
  (isoWithLp (E := E)).trans (rotation45LIE (E := E))

@[simp] lemma rotation45Isometry_apply (u : NeutralSpace E) :
    rotation45Isometry (E := E) u = rotation45LIE (E := E) (isoWithLp (E := E) u) := rfl

/-- The 45-degree continuous linear equivalence from the neutral Bogoliubov model
to the diagonal Pontryagin model. -/
noncomputable def rotation45 : NeutralSpace E ≃L[ℝ] HilbertDoubled E :=
  (rotation45Isometry (E := E)).toContinuousLinearEquiv

@[simp] lemma rotation45_apply (u : NeutralSpace E) :
    rotation45 (E := E) u =
      WithLp.toLp 2
        (rotation45Coeff • (ofLp u).1 + rotation45Coeff • (ofLp u).2,
          rotation45Coeff • (ofLp u).1 - rotation45Coeff • (ofLp u).2) := by
  change rotation45LIE (E := E) (isoWithLp (E := E) u) = _
  simp [rotation45LIE_apply, rotation45Map_apply, rotation45CoordMap_apply, isoWithLp]

/-- The 45-degree rotation conjugates the neutral symmetry into the diagonal symmetry. -/
lemma rotation45_intertwines_J (u : NeutralSpace E) :
    (KreinSpace.J (H := HilbertDoubled E)) (rotation45Isometry (E := E) u) =
      rotation45Isometry (E := E) ((KreinSpace.J (H := NeutralSpace E)) u) := by
  change signFlipLIE (E := E) (rotation45LIE (E := E) (isoWithLp (E := E) u)) =
    rotation45LIE (E := E) (isoWithLp (E := E) (neutralJ (E := E) u))
  simpa [rotation45Isometry_apply, val_neutralJ] using
    rotation45LIE_intertwines_swap (E := E) (isoWithLp (E := E) u)

/-- The neutral Hessian/Bogoliubov model and the diagonal Pontryagin model are
Krein-isometrically equivalent via the 45-degree rotation. -/
noncomputable def rotation45KreinEquiv : KreinEquiv (NeutralSpace E) (HilbertDoubled E) where
  toContinuousLinearEquiv := rotation45 (E := E)
  isometric := by
    intro u v
    calc
      KreinSpace.kreinInner (rotation45 (E := E) u) (rotation45 (E := E) v)
          = ⟪(KreinSpace.J (H := HilbertDoubled E)) (rotation45Isometry (E := E) u),
              rotation45Isometry (E := E) v⟫_ℝ := rfl
      _ = ⟪rotation45Isometry (E := E) ((KreinSpace.J (H := NeutralSpace E)) u),
              rotation45Isometry (E := E) v⟫_ℝ := by
              rw [rotation45_intertwines_J]
      _ = ⟪(KreinSpace.J (H := NeutralSpace E)) u, v⟫_ℝ := by
              simpa using (rotation45Isometry (E := E)).inner_map_map
                ((KreinSpace.J (H := NeutralSpace E)) u) v
      _ = KreinSpace.kreinInner u v := rfl

/-- The neutral Krein inner product equals the **Hessian cross-term** / Bogoliubov pairing:
`[u,v]_J = ⟪x₁,y₂⟫ + ⟪x₂,y₁⟫` for `u=(x₁,x₂)`, `v=(y₁,y₂)`. -/
lemma kreinInner_eq_hessian (u v : NeutralSpace E) :
    KreinSpace.kreinInner u v =
      ⟪(ofLp u).1, (ofLp v).2⟫_ℝ + ⟪(ofLp u).2, (ofLp v).1⟫_ℝ := by
  change ⟪(neutralJ u).val, v.val⟫_ℝ = _
  rw [val_neutralJ]
  rcases u with ⟨⟨x₁, x₂⟩⟩
  rcases v with ⟨⟨y₁, y₂⟩⟩
  -- The inner product expands into WithLp.prod_inner_apply
  change ⟪x₂, y₁⟫_ℝ + ⟪x₁, y₂⟫_ℝ = ⟪x₁, y₂⟫_ℝ + ⟪x₂, y₁⟫_ℝ
  exact add_comm _ _

/-- The swap `J(x,y)=(y,x)` as a `ContinuousLinearEquiv` on `NeutralSpace E`. -/
noncomputable def neutralJEquiv : NeutralSpace E ≃L[ℝ] NeutralSpace E :=
  (neutralJ (E := E)).toContinuousLinearEquiv

end NeutralSpace

end InfoGeometry.Krein
