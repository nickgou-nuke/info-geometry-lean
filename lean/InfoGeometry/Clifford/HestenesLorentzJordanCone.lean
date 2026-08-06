import InfoGeometry.Clifford.HestenesParavectorPair
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/-- 
Специалното Jordan произведение върху четния сектор ClPlus.
То превръща асоциативната операторна алгебра в комутативна неасоциативна Jordan алгебра.
-/
def jordanProduct (A B : ClPlus Q) : ClPlus Q :=
  ⟨(⅟(2 : R)) • (A.val * B.val + B.val * A.val), by
    have h1 := SetLike.GradedMonoid.toGradedMul.mul_mem A.property B.property
    have h2 := SetLike.GradedMonoid.toGradedMul.mul_mem B.property A.property
    have h3 : A.val * B.val + B.val * A.val ∈ ClPlus Q := Submodule.add_mem _ h1 h2
    exact Submodule.smul_mem _ _ h3⟩

local infixl:70 " ∘ " => jordanProduct Q

/-- Jordan произведението е комутативно по дефиниция (A ∘ B = B ∘ A) -/
theorem jordanProduct_comm (A B : ClPlus Q) :
    A ∘ B = B ∘ A := by
  dsimp [jordanProduct]
  apply Subtype.ext
  dsimp
  rw [add_comm]

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
  carrier := {A | hestenesAdjoint Q v0 A = A}
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
    simp only [map_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    exact congr_arg _ hx

/-- Future Lorentz Cone (C^+) в Par_{sa} 
Формално това изисква t >= |x|, което може да бъде дефинирано чрез
детерминантата (която съответства на Q(x)) и следата.
Тук поставяме структурната основа. -/
def FutureLorentzCone : Set (HestenesSelfAdjoint Q v0) :=
  {X | ∃ Y : ClPlus Q, X.val.val = Y.val * (hestenesAdjoint Q v0 Y).val}

end InfoGeometry.Clifford.Hestenes
