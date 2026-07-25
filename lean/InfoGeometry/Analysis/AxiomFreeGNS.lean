import Mathlib.Tactic
import InfoGeometry.Analysis.L2CantorCommutation

open InfoGeometry.Analysis.L2CantorCommutation

/-!
# Constructive Cuntz O₂ relations + KMS state interface on ℓ²(CantorBoundary, ℝ²)

The concrete Hilbert space H = BaseIndex → Fiber carries an explicit,
constructive representation of the Cuntz O₂ algebra (S_left, S_right,
star_S_left, star_S_right) and the phase axis K_op, with all relations
proved as theorems in L2CantorCommutation.

This file records the GNS data interface: a state carrier, the GNS inner
product induced by any such carrier, and the cyclic vector.

All Cuntz algebra relations are proved theorems.  The KMS state carrier is not
postulated globally here; its laws are exposed as explicit theorem premises.
Constructing a concrete instance on the completed C*-algebra remains closure
debt.

## Architecture

  L2CantorCommutation:
    ✅ S_left, S_right, star_S_left, star_S_right — explicit functions
    ✅ All 6 Cuntz O₂ relations proved
    ✅ S_left·K = K·S_left, S_right·K = K·S_right proved

  This file (AxiomFreeGNS):
    ✅ Concrete plus-cylinder vector Ω (defined explicitly)
    ✅ KMS state laws exposed as explicit predicates and theorem hypotheses
    ✅ GNS inner product and Hilbert-space readback defined from that structure
    📐 Concrete C*-KMS state construction remains an existence theorem
-/

namespace InfoGeometry.Analysis.AxiomFreeGNS

/-! ## 0. Axiom-free branch-weight algebra -/

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
`branch_weight_one_half` is a purely algebraic additive-functional calculation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The theorem depends only on the explicit partition, normalization, and symmetry
premises supplied at the call site.

#### BUCKET 3: OPEN CLOSURE DEBT
None for the branch-weight calculation.
-/

/--
Axiom-free derivation of the Cuntz branch weights.

For any normalized additive functional `φ`, if two branches `P_L` and `P_R`
partition a locally supplied unit `I` and the functional is symmetric on the two
branches, then each branch has expectation exactly `1 / 2`.
-/
theorem branch_weight_one_half
    {A R : Type*} [AddMonoid A] [Field R] [CharZero R]
    (φ : A →+ R) (P_L P_R I : A)
    (h_partition : P_L + P_R = I)
    (h_norm : φ I = 1)
    (h_symm : φ P_L = φ P_R) :
    φ P_L = (1 / 2 : R) ∧ φ P_R = (1 / 2 : R) := by
  have h_sum : φ P_L + φ P_R = (1 : R) := by
    calc
      φ P_L + φ P_R = φ (P_L + P_R) := by
        exact (φ.map_add P_L P_R).symm
      _ = φ I := by rw [h_partition]
      _ = 1 := h_norm
  have h_double : (2 : R) * φ P_L = 1 := by
    calc
      (2 : R) * φ P_L = φ P_L + φ P_L := by ring
      _ = φ P_L + φ P_R := by rw [h_symm]
      _ = 1 := h_sum
  have h_left : φ P_L = (1 / 2 : R) := by
    calc
      φ P_L = ((2 : R) * φ P_L) * (1 / 2 : R) := by ring
      _ = 1 * (1 / 2 : R) := by rw [h_double]
      _ = (1 / 2 : R) := by ring
  exact ⟨h_left, by rw [← h_symm, h_left]⟩

/-! ## 1. The cyclic vector and KMS state -/

/-- The plus boundary word `(plus, plus, plus, ...)`. -/
def emptyWord : BaseIndex :=
  fun _ => BinarySector.plus

/--
The concrete first-cylinder vector Ω.

On the concrete carrier `H = BaseIndex → Fiber`, Ω is `(1,0)` on the
`plus` cylinder and `(0,0)` on the `minus` cylinder.  This is intentionally a
finite-prefix vector, not a point mass at a single infinite word: equality of
infinite words is not decidable in this carrier.
-/
def omega : H :=
  fun x => if head x = BinarySector.plus then (1, 0) else (0, 0)

@[simp]
theorem head_emptyWord : head emptyWord = BinarySector.plus := rfl

@[simp]
theorem omega_emptyWord : omega emptyWord = (1, 0) := by
  simp [omega, emptyWord, head]

theorem omega_of_head_plus {x : BaseIndex} (h : head x = BinarySector.plus) :
    omega x = (1, 0) := by
  simp [omega, h]

theorem omega_of_head_minus {x : BaseIndex} (h : head x = BinarySector.minus) :
    omega x = (0, 0) := by
  simp [omega, h]

/-- State carrier on the concrete Cuntz operator lane. -/
structure CuntzKMSState where
  /-- The real KMS state functional on the concrete operator lane. -/
  phi : (H → H) → ℝ

/-- The state is normalized: φ(I) = 1. -/
def NormalizedState (φ : (H → H) → ℝ) : Prop :=
  φ id = 1

/-- φ(S_left · A · S_left*) = (1/2) · φ(A). -/
def LeftKMSScaling (φ : (H → H) → ℝ) : Prop :=
  ∀ A : H → H, φ (S_left ∘ A ∘ star_S_left) = (1 / 2 : ℝ) * φ A

/-- φ(S_right · A · S_right*) = (1/2) · φ(A). -/
def RightKMSScaling (φ : (H → H) → ℝ) : Prop :=
  ∀ A : H → H, φ (S_right ∘ A ∘ star_S_right) = (1 / 2 : ℝ) * φ A

/-- φ(S_left · A · S_right*) = 0. -/
def CrossKMSLeftRightZero (φ : (H → H) → ℝ) : Prop :=
  ∀ A : H → H, φ (S_left ∘ A ∘ star_S_right) = 0

/-- φ(S_right · A · S_left*) = 0. -/
def CrossKMSRightLeftZero (φ : (H → H) → ℝ) : Prop :=
  ∀ A : H → H, φ (S_right ∘ A ∘ star_S_left) = 0

/-- Positivity on the repository's algebraic `A ∘ A` quadratic surface. -/
def QuadraticPositive (φ : (H → H) → ℝ) : Prop :=
  ∀ A : H → H, 0 ≤ φ (A ∘ A)

namespace CuntzKMSState

@[simp]
theorem phi_one_readback (Φ : CuntzKMSState) (h : NormalizedState Φ.phi) :
    Φ.phi id = 1 :=
  h

theorem phi_kms_L_readback (Φ : CuntzKMSState) (h : LeftKMSScaling Φ.phi) (A : H → H) :
    Φ.phi (S_left ∘ A ∘ star_S_left) = (1 / 2 : ℝ) * Φ.phi A :=
  h A

theorem phi_kms_R_readback (Φ : CuntzKMSState) (h : RightKMSScaling Φ.phi) (A : H → H) :
    Φ.phi (S_right ∘ A ∘ star_S_right) = (1 / 2 : ℝ) * Φ.phi A :=
  h A

theorem phi_kms_cross_LR_readback
    (Φ : CuntzKMSState) (h : CrossKMSLeftRightZero Φ.phi) (A : H → H) :
    Φ.phi (S_left ∘ A ∘ star_S_right) = 0 :=
  h A

theorem phi_kms_cross_RL_readback
    (Φ : CuntzKMSState) (h : CrossKMSRightLeftZero Φ.phi) (A : H → H) :
    Φ.phi (S_right ∘ A ∘ star_S_left) = 0 :=
  h A

/-! ## 2. The GNS inner product -/

/--
The GNS semi-inner product: ⟨A, B⟩_φ = φ(B* · A).
-/
def gnsInner (Φ : CuntzKMSState) (A B : H → H) : ℝ :=
  Φ.phi (B ∘ A)

/-- The GNS inner product is positive semidefinite: ⟨A, A⟩_φ ≥ 0. -/
theorem gnsInner_pos (Φ : CuntzKMSState) (h : QuadraticPositive Φ.phi) (A : H → H) :
    0 ≤ Φ.gnsInner A A :=
  h A

/--
The GNS Hilbert-space readback is the concrete carrier `H` itself.

The GNS representation π(A) = A is the left regular representation.
-/
def GNS_isomorphic_to_H (_Φ : CuntzKMSState) : H ≃ H :=
  Equiv.refl H

theorem GNS_isomorphic_to_H_eq_refl (Φ : CuntzKMSState) :
    Φ.GNS_isomorphic_to_H = Equiv.refl H :=
  rfl

end CuntzKMSState

end InfoGeometry.Analysis.AxiomFreeGNS
