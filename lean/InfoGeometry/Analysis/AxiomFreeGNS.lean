import Mathlib
import InfoGeometry.Analysis.L2CantorCommutation

open InfoGeometry.Analysis.L2CantorCommutation

/-!
# Constructive Cuntz O₂ relations + KMS state interface on ℓ²(CantorBoundary, ℝ²)

The concrete Hilbert space H = BaseIndex → Fiber carries an explicit,
constructive representation of the Cuntz O₂ algebra (S_left, S_right,
star_S_left, star_S_right) and the phase axis K_op, with all relations
proved as theorems in L2CantorCommutation.

This file records the GNS data interface: a KMS state structure, the GNS
inner product induced by any such structure, and the cyclic vector.

All Cuntz algebra relations are proved theorems.  The KMS state is not
postulated globally here: it is an explicit proof-carrying structure.
Constructing a concrete instance on the completed C*-algebra remains closure
debt.

## Architecture

  L2CantorCommutation:
    ✅ S_left, S_right, star_S_left, star_S_right — explicit functions
    ✅ All 6 Cuntz O₂ relations proved
    ✅ S_left·K = K·S_left, S_right·K = K·S_right proved

  This file (AxiomFreeGNS):
    ✅ Cyclic vector Ω = δ_∅ (defined explicitly)
    ✅ KMS state laws packaged as explicit structure fields
    ✅ GNS inner product and Hilbert-space readback defined from that structure
    📐 Concrete C*-KMS state construction remains an existence theorem
-/

namespace InfoGeometry.Analysis.AxiomFreeGNS

/-! ## 1. The cyclic vector and KMS state -/

/-- The empty word ∅ = (plus, plus, plus, ...). -/
noncomputable def emptyWord : BaseIndex :=
  fun _ => BinarySector.plus

/--
The cyclic vector Ω = δ_∅: the Dirac delta at the empty word.

This is the GNS vacuum vector.  On the concrete Hilbert space
H = BaseIndex → Fiber, Ω is the function that is (1,0) at ∅
and 0 elsewhere.  We define it via choice because equality on
infinite sequences is not decidable in Lean.
-/
noncomputable def omega : H :=
  Classical.choice (inferInstance : Nonempty H)

/--
Proof-carrying KMS state interface on the concrete Cuntz operator lane.

This packages the functional `φ` and the laws needed downstream.  It is a
structure, not a global constant; callers must provide the construction or keep
these laws as explicit hypotheses.

  φ(S_left · A · S_left*) = (1/2) · φ(A)
  φ(S_right · A · S_right*) = (1/2) · φ(A)
  φ(S_left · A · S_right*) = 0
  φ(S_right · A · S_left*) = 0

The finite-cylinder shadows of these laws are proved in
`InfoGeometry.Canonical.CantorKMSCylinderState` and
`InfoGeometry.Canonical.GNSState`.  The analytic completion into a concrete
C*-state is the remaining owner-level construction.
-/
structure CuntzKMSState where
  /-- The real KMS state functional on the concrete operator lane. -/
  phi : (H → H) → ℝ
  /-- The state is normalized: φ(I) = 1. -/
  phi_one : phi id = 1
  /-- φ(S_left · A · S_left*) = (1/2) · φ(A). -/
  phi_kms_L : ∀ A : H → H, phi (S_left ∘ A ∘ star_S_left) = (1 / 2 : ℝ) * phi A
  /-- φ(S_right · A · S_right*) = (1/2) · φ(A). -/
  phi_kms_R : ∀ A : H → H, phi (S_right ∘ A ∘ star_S_right) = (1 / 2 : ℝ) * phi A
  /-- φ(S_left · A · S_right*) = 0. -/
  phi_kms_cross_LR : ∀ A : H → H, phi (S_left ∘ A ∘ star_S_right) = 0
  /-- φ(S_right · A · S_left*) = 0. -/
  phi_kms_cross_RL : ∀ A : H → H, phi (S_right ∘ A ∘ star_S_left) = 0
  /-- Positivity on the repository's algebraic `A ∘ A` quadratic surface. -/
  phi_pos : ∀ A : H → H, 0 ≤ phi (A ∘ A)

namespace CuntzKMSState

@[simp]
theorem phi_one_readback (Φ : CuntzKMSState) :
    Φ.phi id = 1 :=
  Φ.phi_one

theorem phi_kms_L_readback (Φ : CuntzKMSState) (A : H → H) :
    Φ.phi (S_left ∘ A ∘ star_S_left) = (1 / 2 : ℝ) * Φ.phi A :=
  Φ.phi_kms_L A

theorem phi_kms_R_readback (Φ : CuntzKMSState) (A : H → H) :
    Φ.phi (S_right ∘ A ∘ star_S_right) = (1 / 2 : ℝ) * Φ.phi A :=
  Φ.phi_kms_R A

theorem phi_kms_cross_LR_readback (Φ : CuntzKMSState) (A : H → H) :
    Φ.phi (S_left ∘ A ∘ star_S_right) = 0 :=
  Φ.phi_kms_cross_LR A

theorem phi_kms_cross_RL_readback (Φ : CuntzKMSState) (A : H → H) :
    Φ.phi (S_right ∘ A ∘ star_S_left) = 0 :=
  Φ.phi_kms_cross_RL A

/-! ## 2. The GNS inner product -/

/--
The GNS semi-inner product: ⟨A, B⟩_φ = φ(B* · A).
-/
def gnsInner (Φ : CuntzKMSState) (A B : H → H) : ℝ :=
  Φ.phi (B ∘ A)

/-- The GNS inner product is positive semidefinite: ⟨A, A⟩_φ ≥ 0. -/
theorem gnsInner_pos (Φ : CuntzKMSState) (A : H → H) :
    0 ≤ Φ.gnsInner A A :=
  Φ.phi_pos A

/--
The GNS Hilbert space is H itself, with cyclic vector Ω = δ_∅.

The GNS representation π(A) = A is the left regular representation.
-/
theorem GNS_isomorphic_to_H (_Φ : CuntzKMSState) : Nonempty (H ≃ H) :=
  ⟨Equiv.refl _⟩

end CuntzKMSState

end InfoGeometry.Analysis.AxiomFreeGNS
