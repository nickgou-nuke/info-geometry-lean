import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ExteriorAlgebra

variable {R V A : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Ring A] [Algebra R A]

/-!
=============================================================================
PART 1: Operator-Valued 1-Forms and Alternating 2-Forms
=============================================================================
-/

/-- An operator-valued 1-form is an R-linear map from V to the operator algebra A. -/
abbrev Op1Form (R V A : Type*) [CommRing R] [AddCommGroup V] [Module R V] [Ring A] [Algebra R A] :=
  V →ₗ[R] A

/-- An operator-valued alternating 2-form on V with values in A. -/
structure Op2Form (R V A : Type*) [CommRing R] [AddCommGroup V] [Module R V] [Ring A] [Algebra R A] where
  toBilin : V →ₗ[R] V →ₗ[R] A
  alt' : ∀ v, toBilin v v = 0

namespace Op2Form

variable (ω : Op2Form R V A)

instance : CoeFun (Op2Form R V A) (fun _ => V → V → A) where
  coe ω u v := ω.toBilin u v

instance : Add (Op2Form R V A) where
  add ω₁ ω₂ := {
    toBilin := ω₁.toBilin + ω₂.toBilin
    alt' := by
      intro v
      change ω₁.toBilin v v + ω₂.toBilin v v = 0
      rw [ω₁.alt' v, ω₂.alt' v, add_zero]
  }

instance : Zero (Op2Form R V A) where
  zero := {
    toBilin := 0
    alt' := by
      intro v
      simp
  }

@[simp] theorem zero_apply (u v : V) : (0 : Op2Form R V A) u v = 0 := rfl

instance : Neg (Op2Form R V A) where
  neg ω := {
    toBilin := -ω.toBilin
    alt' := by
      intro v
      change -(ω.toBilin v v) = 0
      rw [ω.alt' v, neg_zero]
  }

instance : Sub (Op2Form R V A) where
  sub ω₁ ω₂ := {
    toBilin := ω₁.toBilin - ω₂.toBilin
    alt' := by
      intro v
      change ω₁.toBilin v v - ω₂.toBilin v v = 0
      rw [ω₁.alt' v, ω₂.alt' v, sub_zero]
  }

instance : SMul R (Op2Form R V A) where
  smul c ω := {
    toBilin := c • ω.toBilin
    alt' := by
      intro v
      change c • (ω.toBilin v v) = 0
      rw [ω.alt' v, smul_zero]
  }

@[simp]
theorem map_zero_left
    (v : V) :
    ω 0 v = 0 := by
  have h := ω.toBilin.map_zero
  exact congr_fun (congr_arg DFunLike.coe h) v

@[simp]
theorem map_zero_right
    (u : V) :
    ω u 0 = 0 := by
  exact (ω.toBilin u).map_zero

@[simp]
theorem map_add_left
    (u₁ u₂ v : V) :
    ω (u₁ + u₂) v = ω u₁ v + ω u₂ v := by
  have h := ω.toBilin.map_add u₁ u₂
  exact congr_fun (congr_arg DFunLike.coe h) v

@[simp]
theorem map_add_right
    (u v₁ v₂ : V) :
    ω u (v₁ + v₂) = ω u v₁ + ω u v₂ := by
  exact (ω.toBilin u).map_add v₁ v₂

@[simp]
theorem map_smul_left
    (c : R) (u v : V) :
    ω (c • u) v = c • ω u v := by
  have h := ω.toBilin.map_smul c u
  exact congr_fun (congr_arg DFunLike.coe h) v

@[simp]
theorem map_smul_right
    (c : R) (u v : V) :
    ω u (c • v) = c • ω u v := by
  exact (ω.toBilin u).map_smul c v

@[simp]
theorem alt
    (v : V) :
    ω v v = 0 := by
  exact ω.alt' v

/-- Skew-symmetry in vector arguments: ω(u, v) = - ω(v, u). -/
theorem skew
    (u v : V) :
    ω u v = - ω v u := by
  have h : ω (u + v) (u + v) = 0 := ω.alt (u + v)
  have hexp : ω (u + v) (u + v) = ω u u + ω u v + ω v u + ω v v := by
    rw [map_add_left, map_add_right, map_add_right]
    abel
  rw [ω.alt u, ω.alt v, zero_add, add_zero] at hexp
  rw [hexp] at h
  have h_eq : ω u v + ω v u = 0 := h
  exact eq_neg_of_add_eq_zero_left h_eq

/-- Extensionality for 2-forms. -/
@[ext]
theorem ext
    (ω₁ ω₂ : Op2Form R V A)
    (h : ∀ u v, ω₁ u v = ω₂ u v) :
    ω₁ = ω₂ := by
  rcases ω₁ with ⟨b₁, a₁⟩
  rcases ω₂ with ⟨b₂, a₂⟩
  congr
  ext u v
  exact h u v

end Op2Form

/-!
=============================================================================
PART 2: Wedge Product of Operator 1-Forms
=============================================================================
-/

/--
  The Wedge Product of two operator-valued 1-forms α, β:
    (α ∧ β)(u, v) = α(u) * β(v) - α(v) * β(u)
-/
def wedge (α β : Op1Form R V A) : Op2Form R V A where
  toBilin := {
    toFun := fun u => {
      toFun := fun v => α u * β v - α v * β u
      map_add' := by
        intro v₁ v₂
        simp only [α.map_add, β.map_add, mul_add, add_mul]
        abel
      map_smul' := by
        intro c v
        dsimp
        simp only [α.map_smul, β.map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
    }
    map_add' := by
      intro u₁ u₂
      ext v
      dsimp
      simp only [α.map_add, β.map_add, add_mul, mul_add]
      abel
    map_smul' := by
      intro c u
      ext v
      dsimp
      simp only [α.map_smul, β.map_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  }
  alt' := by
    intro v
    dsimp
    simp only [sub_self]

@[simp]
theorem wedge_apply
    (α β : Op1Form R V A) (u v : V) :
    (wedge α β) u v = α u * β v - α v * β u :=
  rfl

/-- THEOREM 1 (Skew-Symmetry in Arguments of the Wedge Product):
    For any operator-valued 1-forms α, β:
      (α ∧ β)(u, v) = - (α ∧ β)(v, u)
-/
theorem wedge_skew_args
    (α β : Op1Form R V A) (u v : V) :
    (wedge α β) u v = - (wedge α β) v u := by
  exact (wedge α β).skew u v

/-- THEOREM 2 (Self-Wedge is the Operator Commutator):
    For any operator-valued 1-form α:
      (α ∧ α)(u, v) = [α(u), α(v)] = α(u)α(v) - α(v)α(u)
-/
theorem wedge_self_eq_commutator
    (α : Op1Form R V A) (u v : V) :
    (wedge α α) u v = α u * α v - α v * α u := by
  simp only [wedge_apply]

/-!
=============================================================================
PART 3: Pullback of Operator Forms
=============================================================================
-/

variable {W : Type*} [AddCommGroup W] [Module R W]

section ValueTransport

variable {B : Type*} [Ring B] [Algebra R B]

/-- Transport an operator-valued one-form through an algebra homomorphism. -/
def map1 (f : A →ₐ[R] B) (α : Op1Form R V A) : Op1Form R V B where
  toFun v := f (α v)
  map_add' u v := by
    rw [α.map_add]
    exact f.map_add _ _
  map_smul' c v := by
    rw [α.map_smul]
    simpa using map_smulₛₗ f c (α v)

@[simp] theorem map1_apply (f : A →ₐ[R] B) (α : Op1Form R V A) (v : V) :
    map1 f α v = f (α v) := rfl

/-- Transport an alternating operator-valued two-form through an algebra homomorphism. -/
def map2 (f : A →ₐ[R] B) (ω : Op2Form R V A) : Op2Form R V B where
  toBilin := {
    toFun := fun u => {
      toFun := fun v => f (ω u v)
      map_add' := by
        intro v w
        rw [ω.map_add_right]
        exact f.map_add _ _
      map_smul' := by
        intro c v
        rw [ω.map_smul_right]
        simpa using map_smulₛₗ f c (ω u v)
    }
    map_add' := by
      intro u v
      ext w
      change f (ω (u + v) w) = f (ω u w) + f (ω v w)
      rw [ω.map_add_left]
      exact f.map_add _ _
    map_smul' := by
      intro c u
      ext v
      change f (ω (c • u) v) = (RingHom.id R) c • f (ω u v)
      rw [ω.map_smul_left]
      simpa using map_smulₛₗ f c (ω u v)
  }
  alt' := by
    intro v
    change f (ω v v) = 0
    rw [ω.alt]
    exact f.map_zero

@[simp] theorem map2_apply (f : A →ₐ[R] B) (ω : Op2Form R V A) (u v : V) :
    map2 f ω u v = f (ω u v) := rfl

  theorem map2_wedge (f : A →ₐ[R] B)
    (α β : Op1Form R V A) :
    map2 f (wedge α β) = wedge (map1 f α) (map1 f β) := by
  ext u v
  change f (α u * β v - α v * β u) =
    f (α u) * f (β v) - f (α v) * f (β u)
  simp

  /-- Value transport of one-forms is functorial under composition. -/
  theorem map1_comp
      {C : Type*} [Ring C] [Algebra R C]
      (f : A →ₐ[R] B) (g : B →ₐ[R] C)
      (α : Op1Form R V A) :
      map1 (g.comp f) α = map1 g (map1 f α) := by
    ext v
    rfl

  /-- Value transport of two-forms is functorial under composition. -/
  theorem map2_comp
      {C : Type*} [Ring C] [Algebra R C]
      (f : A →ₐ[R] B) (g : B →ₐ[R] C)
      (ω : Op2Form R V A) :
      map2 (g.comp f) ω = map2 g (map2 f ω) := by
    apply Op2Form.ext
    intro u v
    rfl

end ValueTransport

/-- Pullback of an operator 1-form along a linear map ϕ : W → V. -/
def pullback1 (ϕ : W →ₗ[R] V) (α : Op1Form R V A) : Op1Form R W A :=
  α.comp ϕ

/-- Pullback of an operator 2-form along a linear map ϕ : W → V. -/
def pullback2 (ϕ : W →ₗ[R] V) (ω : Op2Form R V A) : Op2Form R W A where
  toBilin := {
    toFun := fun w₁ => {
      toFun := fun w₂ => ω (ϕ w₁) (ϕ w₂)
      map_add' := by
        intro x y
        simp only [ϕ.map_add, ω.map_add_right]
      map_smul' := by
        intro c x
        dsimp
        simp only [ϕ.map_smul, ω.map_smul_right]
    }
    map_add' := by
      intro x y
      ext z
      dsimp
      simp only [ϕ.map_add, ω.map_add_left]
    map_smul' := by
      intro c x
      ext z
      dsimp
      simp only [ϕ.map_smul, ω.map_smul_left]
  }
  alt' := by
    intro w
    dsimp
    exact ω.alt (ϕ w)

@[simp]
theorem pullback1_apply
    (ϕ : W →ₗ[R] V) (α : Op1Form R V A) (w : W) :
    (pullback1 ϕ α) w = α (ϕ w) :=
  rfl

@[simp]
theorem pullback2_apply
    (ϕ : W →ₗ[R] V) (ω : Op2Form R V A) (w₁ w₂ : W) :
    (pullback2 ϕ ω) w₁ w₂ = ω (ϕ w₁) (ϕ w₂) :=
  rfl

/-- THEOREM 3 (Pullback Commutes with Wedge Product):
    ϕ*(α ∧ β) = (ϕ*α) ∧ (ϕ*β)
-/
theorem pullback_wedge
    (ϕ : W →ₗ[R] V) (α β : Op1Form R V A) :
    pullback2 ϕ (wedge α β) = wedge (pullback1 ϕ α) (pullback1 ϕ β) := by
  ext w₁ w₂
  simp only [pullback2_apply, wedge_apply, pullback1_apply]

/-!
=============================================================================
PART 4: Operator Derivations and the Leibniz Rule for Wedge Products
=============================================================================
-/

structure OpDerivation (R A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  toLinearMap : A →ₗ[R] A
  leibniz' : ∀ x y : A, toLinearMap (x * y) = toLinearMap x * y + x * toLinearMap y

namespace OpDerivation

instance : CoeFun (OpDerivation R A) (fun _ => A → A) where
  coe D := D.toLinearMap

variable (D : OpDerivation R A)

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.toLinearMap.map_add x y
@[simp] theorem map_smul (c : R) (x : A) : D (c • x) = c • D x := D.toLinearMap.map_smul c x
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y
@[simp] theorem map_sub (x y : A) : D (x - y) = D x - D y := D.toLinearMap.map_sub x y

end OpDerivation

/-- Action of an operator derivation on a 1-form. -/
def applyDeriv1 (D : OpDerivation R A) (α : Op1Form R V A) : Op1Form R V A :=
  D.toLinearMap.comp α

/-- Action of an operator derivation on a 2-form. -/
def applyDeriv2 (D : OpDerivation R A) (ω : Op2Form R V A) : Op2Form R V A where
  toBilin := {
    toFun := fun u => {
      toFun := fun v => D (ω u v)
      map_add' := by
        intro v₁ v₂
        simp only [ω.map_add_right, D.map_add]
      map_smul' := by
        intro c v
        dsimp
        simp only [ω.map_smul_right, D.map_smul]
    }
    map_add' := by
      intro u₁ u₂
      ext v
      dsimp
      simp only [ω.map_add_left, D.map_add]
    map_smul' := by
      intro c u
      ext v
      dsimp
      simp only [ω.map_smul_left, D.map_smul]
  }
  alt' := by
    intro v
    dsimp
    have halt := ω.alt v
    dsimp [Op2Form.toBilin] at halt
    rw [halt, D.toLinearMap.map_zero]

@[simp]
theorem applyDeriv1_apply
    (D : OpDerivation R A) (α : Op1Form R V A) (v : V) :
    (applyDeriv1 D α) v = D (α v) :=
  rfl

@[simp]
theorem applyDeriv2_apply
    (D : OpDerivation R A) (ω : Op2Form R V A) (u v : V) :
    (applyDeriv2 D ω) u v = D (ω u v) :=
  rfl

/-- THEOREM 4 (Leibniz Rule for Wedge Products under Operator Derivation):
    D(α ∧ β) = (D α) ∧ β + α ∧ (D β)
-/
theorem deriv_wedge_leibniz
    (D : OpDerivation R A) (α β : Op1Form R V A) (u v : V) :
    (applyDeriv2 D (wedge α β)) u v =
      (wedge (applyDeriv1 D α) β) u v + (wedge α (applyDeriv1 D β)) u v := by
  simp only [applyDeriv2_apply, wedge_apply, applyDeriv1_apply, D.map_sub, D.leibniz]
  abel

/-!
=============================================================================
PART 5: Onsager Response Pairing on Operator 1-Forms
=============================================================================
-/

/-- The induced Onsager thermodynamic response pairing on operator 1-forms. -/
def onsager1FormPairing
    (L : LinearMap.BilinForm R A) (α β : Op1Form R V A) (u v : V) : R :=
  L (α u) (β v)

/-- THEOREM 5 (Onsager Reciprocity on Operator 1-Forms):
    If L is symmetric on operator algebra A, the 1-form response satisfies reciprocity on matching states:
      L(α u, β u) = L(β u, α u)
-/
theorem onsager1Form_reciprocity
    (L : LinearMap.BilinForm R A) (hL : ∀ x y, L x y = L y x)
    (α β : Op1Form R V A) (u : V) :
    onsager1FormPairing L α β u u = onsager1FormPairing L β α u u := by
  dsimp [onsager1FormPairing]
  exact hL (α u) (β u)

/-- THEOREM 6 (Non-negative Dissipation on Operator 1-Forms):
    Positive semi-definite Onsager operator response induces non-negative entropy production on 1-forms. -/
theorem onsager1Form_nonneg
    (L : LinearMap.BilinForm R A) [LinearOrder R] (hL : ∀ x, 0 ≤ L x x)
    (α : Op1Form R V A) (u : V) :
    0 ≤ onsager1FormPairing L α α u u := by
  dsimp [onsager1FormPairing]
  exact hL (α u)

end InfoGeometry.OperatorAlgebra.ExteriorAlgebra

end noncomputable section
