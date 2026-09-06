import proofs.HestenesQuaternionCore

/-!
# Split-octonion Cayley--Dickson doubling

`HRot × HRot` is an 8-dimensional Cayley--Dickson candidate for split
octonions.  It is distinct from the 4-dimensional associative split
quaternion algebra `M₂(ℝ)`, provided by `HestenesSplitQuaternion`.
-/
noncomputable section
namespace HestenesHyperbolicDoubling

open QuaternionAlgebra

abbrev HRot := Quaternion ℝ
abbrev Carrier := HRot × HRot

instance : Zero Carrier := inferInstance
instance : One Carrier := ⟨(1, 0)⟩

 def splitMul (x y : Carrier) : Carrier :=
  (x.1 * y.1 + star y.2 * x.2,
   y.2 * x.1 + x.2 * star y.1)

instance : Mul Carrier := ⟨splitMul⟩

def splitConj (x : Carrier) : Carrier :=
  (star x.1, -x.2)

def ell : Carrier := (0, 1)

def embed (a : HRot) : Carrier := (a, 0)

def rightLane (b : HRot) : Carrier := (0, b)

def splitNorm (x : Carrier) : ℝ :=
  Quaternion.normSq x.1 - Quaternion.normSq x.2

@[simp] theorem splitMul_def (a b c d : HRot) :
    (a, b) * (c, d) =
      (a * c + star d * b, d * a + b * star c) := rfl

@[simp] theorem ell_sq : ell * ell = 1 := by
  change ((0 : HRot) * 0 + star 1 * 1, 1 * 0 + 1 * star 0) = (1, 0)
  simp

@[simp] theorem ell_cross (a : HRot) :
    ell * embed a = embed (star a) * ell := by
  ext <;> simp [ell, embed, splitMul]

@[simp] theorem ell_mul_embed (a : HRot) :
    ell * embed a = rightLane (star a) := by
  ext <;> simp [ell, embed, rightLane]

@[simp] theorem embed_mul_ell (a : HRot) :
    embed a * ell = rightLane a := by
  ext <;> simp [ell, embed, rightLane]

@[simp] theorem embed_mul (a b : HRot) :
    embed a * embed b = embed (a * b) := by
  change (a * b + star 0 * 0, 0 * a + 0 * star b) = (a * b, 0)
  simp

@[simp] theorem rightLane_mul (a b : HRot) :
    rightLane a * rightLane b = embed (star b * a) := by
  change (0 * 0 + star b * a, b * 0 + a * star 0) = (star b * a, 0)
  simp

@[simp] theorem splitConj_involutive (x : Carrier) :
    splitConj (splitConj x) = x := by
  rcases x with ⟨a, b⟩
  change (star (star a), - -b) = (a, b)
  simp

set_option maxHeartbeats 1000000 in
@[simp] theorem splitConj_mul (x y : Carrier) :
    splitConj (x * y) = splitConj y * splitConj x := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  ext <;> simp [splitConj, splitMul] <;> ring

theorem mul_splitConj (x : Carrier) :
    x * splitConj x = embed (splitNorm x) := by
  rcases x with ⟨a, b⟩
  apply Prod.ext
  · simp [splitConj, splitNorm, embed, splitMul,
      Quaternion.self_mul_star, Quaternion.star_mul_self,
      sub_eq_add_neg]
  · simp [splitConj, embed, splitMul]

theorem splitConj_mul_self (x : Carrier) :
    splitConj x * x = embed (splitNorm x) := by
  rcases x with ⟨a, b⟩
  apply Prod.ext
  · simp [splitConj, splitNorm, embed, splitMul,
      Quaternion.self_mul_star, Quaternion.star_mul_self,
      sub_eq_add_neg]
  · simp [splitConj, embed, splitMul]

def qi : HRot := (QuaternionAlgebra.Basis.self ℝ).i
def qj : HRot := (QuaternionAlgebra.Basis.self ℝ).j

/-- The conjugation twist makes the hyperbolic doubling genuinely nonassociative. -/
theorem nonassociative_witness :
    (ell * embed qi) * embed qj ≠ ell * (embed qi * embed qj) := by
  intro h
  have hr := congrArg Prod.snd h
  simp [qi, qj, ell, embed, splitMul] at hr
  have hk := congrArg (fun q : HRot => q.imK) hr
  norm_num at hk

theorem left_alternative (x y : Carrier) :
    x * (x * y) = (x * x) * y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  ext <;>
    simp only [splitMul_def, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star] <;>
    ring

theorem right_alternative (x y : Carrier) :
    (x * y) * y = x * (y * y) := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  ext <;>
    simp only [splitMul_def, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star] <;>
    ring

theorem hyperbolic_doubling_packet :
    ell * ell = 1 ∧
      (∀ a : HRot, ell * embed a = rightLane (star a)) ∧
      (∀ a : HRot, embed a * ell = rightLane a) ∧
      (∀ x : Carrier, x * splitConj x = embed (splitNorm x)) ∧
      (∀ x y : Carrier, x * (x * y) = (x * x) * y) ∧
      (∀ x y : Carrier, (x * y) * y = x * (y * y)) := by
  exact ⟨ell_sq, ell_mul_embed, embed_mul_ell, mul_splitConj,
    left_alternative, right_alternative⟩

end HestenesHyperbolicDoubling
end noncomputable section
