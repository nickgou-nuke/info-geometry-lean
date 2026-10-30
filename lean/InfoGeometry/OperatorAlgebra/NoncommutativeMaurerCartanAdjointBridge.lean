import InfoGeometry.Lie.ContinuousDerivationExponential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Noncommutative Maurer--Cartan adjoint multiplier bridge

The associative Banach-algebra part of the Maurer--Cartan construction.  The
carrier is deliberately associative; this owner is not a claim about raw
split-octonion multiplication.
-/

noncomputable section
namespace InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def leftMulCLM (a : A) : A →L[ℝ] A :=
  (ContinuousLinearMap.mul ℝ A) a

def rightMulCLM (a : A) : A →L[ℝ] A :=
  (ContinuousLinearMap.mul ℝ A).flip a

@[simp] theorem leftMulCLM_apply (a x : A) :
    leftMulCLM a x = a * x := rfl

@[simp] theorem rightMulCLM_apply (a x : A) :
    rightMulCLM a x = x * a := rfl

theorem leftMul_rightMul_commute (a b : A) :
    Commute (leftMulCLM a) (rightMulCLM b) := by
  show leftMulCLM a * rightMulCLM b = rightMulCLM b * leftMulCLM a
  ext x
  simp [ContinuousLinearMap.mul_apply, mul_assoc]

def adCLM (a : A) : A →L[ℝ] A := leftMulCLM a - rightMulCLM a

@[simp] theorem adCLM_apply (a x : A) :
    adCLM a x = a * x - x * a := rfl

theorem adCLM_leibniz (a x y : A) :
    adCLM a (x * y) = adCLM a x * y + x * adCLM a y := by
  simp [adCLM_apply]
  noncomm_ring

/-- Noether closure for an inner derivation: products and both Lie--Jordan
combinations of conserved operators remain conserved. -/
theorem adCLM_noether_closure {a x y : A}
    (hx : adCLM a x = 0) (hy : adCLM a y = 0) :
    adCLM a (x * y) = 0 ∧
      adCLM a (x * y - y * x) = 0 ∧
      adCLM a (x * y + y * x) = 0 := by
  have hxy : adCLM a (x * y) = 0 := by
    rw [adCLM_leibniz, hx, hy, zero_mul, mul_zero, add_zero]
  have hyx : adCLM a (y * x) = 0 := by
    rw [adCLM_leibniz, hy, hx, zero_mul, mul_zero, add_zero]
  refine ⟨hxy, ?_, ?_⟩
  · simp only [map_sub, hxy, hyx, sub_self]
  · simp only [map_add, hxy, hyx, add_zero]

theorem adCLM_isDerivation (a : A) :
    InfoGeometry.Lie.ContinuousDerivationExponential.IsDerivation
      (ContinuousLinearMap.mul ℝ A) (adCLM a) := by
  intro x y
  exact adCLM_leibniz a x y

theorem adCLM_commutator (a b x : A) :
    adCLM a (adCLM b x) - adCLM b (adCLM a x) =
      adCLM (a * b - b * a) x := by
  simp [adCLM_apply]
  noncomm_ring

theorem adCLM_commutator_operator (a b : A) :
    (adCLM a).comp (adCLM b) - (adCLM b).comp (adCLM a) =
      adCLM (a * b - b * a) := by
  ext x
  exact adCLM_commutator a b x

/-! The same closure statement in Mathlib's associative Lie-bracket
notation.  This is the native `ad` readback used by the derivation-form
complex; it keeps the coefficient algebra associative and does not identify
it with the split-octonion commutator. -/

theorem adCLM_lieBracket (a b : A) :
    ⁅adCLM a, adCLM b⁆ = adCLM (a * b - b * a) := by
  rw [LieRing.of_associative_ring_bracket]
  exact adCLM_commutator_operator a b

theorem adCLM_flow_is_multiplicative (a : A) (t : ℝ) (x y : A) :
    InfoGeometry.Lie.ContinuousDerivationExponential.flow (adCLM a) t (x * y) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow (adCLM a) t x *
        InfoGeometry.Lie.ContinuousDerivationExponential.flow (adCLM a) t y := by
  exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_map_mul
    (ContinuousLinearMap.mul ℝ A) (adCLM a) (adCLM_isDerivation a) t x y

/-! ## Maurer--Cartan form for an invertible operator -/

/-- Two-sided inverse data for an operator used as a moving frame. -/
structure IsInvertiblePair (G Ginv : A) : Prop where
  mul_inv : G * Ginv = 1
  inv_mul : Ginv * G = 1

/-- The left Maurer--Cartan form associated with the inner derivation `adCLM H`. -/
def maurerCartanForm (G Ginv H : A) : A := Ginv * adCLM H G

/-- The left Maurer--Cartan form obeys the noncommutative product cocycle:
the form of a product is the conjugate of the first form by the second frame,
plus the second form. -/
theorem maurerCartan_product_cocycle {G₁ G₁inv G₂ G₂inv : A}
    (hG₁ : IsInvertiblePair G₁ G₁inv) (H : A) :
    maurerCartanForm (G₁ * G₂) (G₂inv * G₁inv) H =
      G₂inv * maurerCartanForm G₁ G₁inv H * G₂ +
        maurerCartanForm G₂ G₂inv H := by
  unfold maurerCartanForm
  rw [adCLM_leibniz]
  calc
    G₂inv * G₁inv * (adCLM H G₁ * G₂ + G₁ * adCLM H G₂) =
        G₂inv * G₁inv * adCLM H G₁ * G₂ +
          G₂inv * (G₁inv * G₁) * adCLM H G₂ := by noncomm_ring
    _ = G₂inv * G₁inv * adCLM H G₁ * G₂ +
          G₂inv * adCLM H G₂ := by rw [hG₁.inv_mul, mul_one]
    _ = G₂inv * (G₁inv * adCLM H G₁) * G₂ +
          G₂inv * adCLM H G₂ := by noncomm_ring

/-- Differentiating the two-sided inverse equation along an inner derivation
gives the noncommutative inverse rule. -/
theorem maurerCartan_inverse_deriv {G Ginv : A}
    (hG : IsInvertiblePair G Ginv) (H : A) :
    adCLM H Ginv = -(Ginv * adCLM H G * Ginv) := by
  change H * Ginv - Ginv * H = -(Ginv * (H * G - G * H) * Ginv)
  have hprod : Ginv * (H * G - G * H) * Ginv =
      Ginv * H - H * Ginv := by
    calc
      _ = Ginv * H * (G * Ginv) - (Ginv * G) * H * Ginv := by noncomm_ring
      _ = Ginv * H - H * Ginv := by rw [hG.mul_inv, hG.inv_mul]; simp [mul_assoc]
  rw [hprod]
  abel

/-- The Maurer--Cartan form reconstructs the original inner derivation after
transport back to the moving operator frame. -/
theorem maurerCartan_reconstruction {G Ginv : A}
    (hG : IsInvertiblePair G Ginv) (H : A) :
    G * maurerCartanForm G Ginv H = adCLM H G := by
  change G * (Ginv * (H * G - G * H)) = H * G - G * H
  rw [← mul_assoc, hG.mul_inv, one_mul]

/-- The covariant curl of two transported inner derivations is the inner
derivation of the generator commutator. In particular, commuting generators
give zero curl. -/
theorem maurerCartan_curl_identity {G Ginv H₁ H₂ : A}
    (hG : IsInvertiblePair G Ginv) :
    adCLM H₁ (G * maurerCartanForm G Ginv H₂) -
        adCLM H₂ (G * maurerCartanForm G Ginv H₁) =
      adCLM (H₁ * H₂ - H₂ * H₁) G := by
  rw [maurerCartan_reconstruction hG H₂,
    maurerCartan_reconstruction hG H₁]
  exact adCLM_commutator H₁ H₂ G

/-- Commuting generators have zero Maurer--Cartan curl. -/
theorem maurerCartan_zero_curl {G Ginv H₁ H₂ : A}
    (hG : IsInvertiblePair G Ginv) (hH : H₁ * H₂ = H₂ * H₁) :
    adCLM H₁ (G * maurerCartanForm G Ginv H₂) -
        adCLM H₂ (G * maurerCartanForm G Ginv H₁) = 0 := by
  rw [maurerCartan_curl_identity hG, hH, sub_self]
  simp [adCLM_apply]

end InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge
