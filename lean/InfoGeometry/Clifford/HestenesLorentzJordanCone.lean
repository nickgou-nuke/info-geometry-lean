import InfoGeometry.Clifford.HestenesParavectorPair

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/-- 
Hestenes Hermitian Adjoint за четни елементи: A^† = γ₀ * A^~ * γ₀ 
Този адюнгиран оператор фиксира паравекторите (които съответстват на Ермитови матрици)
и играе ролята на конюгация.
-/
def hestenesAdjoint (A : ClPlus Q) : ClPlus Q :=
  ⟨gamma0 Q v0 * reverse (A.val) * gamma0 Q v0, by
    have h_rev : reverse (A.val) ∈ ClPlus Q := by
      rw [reverse_mem_evenOdd_iff]
      exact A.property
    have h_g0 : gamma0 Q v0 ∈ ClMinus Q := gamma0_is_odd Q v0
    have step1 : gamma0 Q v0 * reverse (A.val) ∈ ClMinus Q := by
      have h := SetLike.GradedMonoid.toGradedMul.mul_mem h_g0 h_rev
      have eq : (1 : ZMod 2) + 0 = 1 := by decide
      rwa [eq] at h
    have step2 : gamma0 Q v0 * reverse (A.val) * gamma0 Q v0 ∈ ClPlus Q := by
      have h := SetLike.GradedMonoid.toGradedMul.mul_mem step1 h_g0
      have eq : (1 : ZMod 2) + 1 = 0 := by decide
      rwa [eq] at h
    exact step2⟩

/--
Подпространството на Ермитовите (Hestenes-self-adjoint) елементи
Това е 4-измерното пространство на паравекторите Par_{sa}
-/
def HestenesSelfAdjoint : Submodule R (ClPlus Q) where
  carrier := {A | hestenesAdjoint Q v0 hv0_norm A = A}
  add_mem' := by
    intro a b ha hb
    dsimp at ha hb ⊢
    apply Subtype.ext
    dsimp [hestenesAdjoint] at ha hb ⊢
    rw [← Subtype.val_inj] at ha hb
    rw [map_add, mul_add, add_mul]
    exact congr_arg₂ _ ha hb
  zero_mem' := by
    dsimp
    apply Subtype.ext
    dsimp [hestenesAdjoint]
    rw [map_zero, mul_zero, zero_mul]
  smul_mem' := by
    intro c x hx
    dsimp at hx ⊢
    apply Subtype.ext
    dsimp [hestenesAdjoint] at hx ⊢
    rw [← Subtype.val_inj] at hx
    rw [map_smul, smul_mul_assoc, mul_smul_comm]
    exact congr_arg _ hx

/-- Future Lorentz Cone (C^+) в Par_{sa} 
Формално това изисква t >= |x|, което може да бъде дефинирано чрез
детерминантата (която съответства на Q(x)) и следата.
Тук поставяме структурната основа. -/
def FutureLorentzCone : Set (HestenesSelfAdjoint Q v0 hv0_norm) :=
  {A | True}

/-- 
The Euclidean Jordan Product on the Operator Algebra (ClPlus).
This converts the associative operator algebra into a Jordan algebra.
X ∘ Y = (1/2) * (X Y + Y X)
-/
def jordanProduct (X Y : ClPlus Q) : ClPlus Q :=
  ⟨(⅟2 : R) • (X.val * Y.val + Y.val * X.val), by
    apply Submodule.smul_mem
    apply Submodule.add_mem
    · exact clPlus_mul_clPlus Q X.val Y.val X.property Y.property
    · exact clPlus_mul_clPlus Q Y.val X.val Y.property X.property
  ⟩

/-- The Jordan product is commutative by definition. -/
theorem jordanProduct_comm (X Y : ClPlus Q) : jordanProduct Q X Y = jordanProduct Q Y X := by
  apply Subtype.ext
  exact congrArg (fun x => (⅟2 : R) • x) (add_comm (X.val * Y.val) (Y.val * X.val))

/-- 
The Jordan product distributes over addition.
-/
theorem jordanProduct_add_left (X Y Z : ClPlus Q) : 
    jordanProduct Q (X + Y) Z = jordanProduct Q X Z + jordanProduct Q Y Z := by
  apply Subtype.ext
  dsimp [jordanProduct]
  have h1 : (X.val + Y.val) * Z.val = X.val * Z.val + Y.val * Z.val := add_mul X.val Y.val Z.val
  have h2 : Z.val * (X.val + Y.val) = Z.val * X.val + Z.val * Y.val := mul_add Z.val X.val Y.val
  rw [h1, h2]
  have h3 : (X.val * Z.val + Y.val * Z.val) + (Z.val * X.val + Z.val * Y.val) =
            (X.val * Z.val + Z.val * X.val) + (Y.val * Z.val + Z.val * Y.val) := by abel
  rw [h3]
  exact smul_add _ _ _

/-- 
The Jordan square of an element is simply its ordinary square.
X ∘ X = X²
-/
theorem jordanProduct_self (X : ClPlus Q) : jordanProduct Q X X = ⟨X.val * X.val, clPlus_mul_clPlus Q X.val X.val X.property X.property⟩ := by
  apply Subtype.ext
  dsimp [jordanProduct]
  have h_add : X.val * X.val + X.val * X.val = (2 : R) • (X.val * X.val) := by
    rw [two_smul]
  rw [h_add]
  rw [← mul_smul]
  have h_inv : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  rw [h_inv, one_smul]

/--
The structural mapping defining the Future Lorentz Cone:
Positivity in the Jordan algebra corresponds to the causal cone.
(This will serve as the gateway to the Koecher-Vinberg symmetric cone)
-/
def isJordanPositive (X : ClPlus Q) : Prop :=
  ∃ S : ClPlus Q, X = jordanProduct Q S S

end InfoGeometry.Clifford.Hestenes
