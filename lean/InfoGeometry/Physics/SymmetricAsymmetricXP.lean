import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.DoubledSpace

/-!
# Hestenes--Krein symmetric and antisymmetric quantization of `x p`

The canonical commutator is written on the real doubled carrier.  Its
quarter-turn is the Hestenes bivector axis `K = J ε`, while `ε` is the
hyperbolic/boost axis.  Thus the antisymmetric quantum term is a real
bivector operator, not a scalar written with an external complex unit.

This is the bounded algebraic core.  It does not identify a finite carrier
with the unbounded dilation operator on `L²`, and it makes no self-adjointness
or Mellin-spectrum claim.
-/

noncomputable section

namespace InfoGeometry.Physics.SymmetricAsymmetricXP

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-! ## Real Hestenes--Krein axes -/

/-- The real bivector/quarter-turn axis `K = J ε`, with square `-1`. -/
noncomputable def bivectorAxis : EndH :=
  clockAxis (E := E)

/-- The real hyperbolic boost axis `𝒦`, with square `+1`. -/
noncomputable def hyperbolicBoostAxis : EndH :=
  modular_j (E := E)

/-- The Krein fundamental involution `η`, with square `+1`. -/
noncomputable def kreinInvolutionAxis : EndH :=
  spectral_epsilon (E := E)

@[simp] theorem bivectorAxis_sq :
    (bivectorAxis (E := E)).comp bivectorAxis =
      -(ContinuousLinearMap.id ℝ H₂) := by
  exact clockAxis_sq (E := E)

@[simp] theorem hyperbolicBoostAxis_sq :
    (hyperbolicBoostAxis (E := E)).comp hyperbolicBoostAxis =
      ContinuousLinearMap.id ℝ H₂ := by
  exact modular_j_involution E

@[simp] theorem kreinInvolutionAxis_sq :
    (kreinInvolutionAxis (E := E)).comp kreinInvolutionAxis =
      ContinuousLinearMap.id ℝ H₂ := by
  exact spectral_epsilon_involution E

theorem bivectorAxis_boost_anticommute :
    (bivectorAxis (E := E)).comp hyperbolicBoostAxis =
      -(hyperbolicBoostAxis (E := E)).comp bivectorAxis := by
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext <;>
    simp [bivectorAxis, hyperbolicBoostAxis, clockAxis,
      clockAxis_apply, spectral_epsilon_apply]

/-! ## Rotor and boost packets -/

/-- A finite elliptic rotor packet in the real bivector plane. -/
noncomputable def bivectorRotor (a b : ℝ) : EndH :=
  a • ContinuousLinearMap.id ℝ H₂ + b • bivectorAxis (E := E)

/-- A finite hyperbolic rotor/boost packet in the real split plane. -/
noncomputable def hyperbolicRotor (a b : ℝ) : EndH :=
  a • ContinuousLinearMap.id ℝ H₂ + b • hyperbolicBoostAxis (E := E)

noncomputable def bivectorRotorReverse (a b : ℝ) : EndH :=
  a • ContinuousLinearMap.id ℝ H₂ - b • bivectorAxis (E := E)

noncomputable def hyperbolicRotorReverse (a b : ℝ) : EndH :=
  a • ContinuousLinearMap.id ℝ H₂ - b • hyperbolicBoostAxis (E := E)

theorem bivectorRotor_mul_reverse (a b : ℝ) :
    (bivectorRotor (E := E) a b).comp (bivectorRotorReverse (E := E) a b) =
      (a ^ 2 + b ^ 2) • ContinuousLinearMap.id ℝ H₂ := by
  unfold bivectorRotor
  unfold bivectorRotorReverse
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    bivectorAxis_sq]
  apply ContinuousLinearMap.ext
  intro v
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    map_add, map_smul, smul_add, smul_smul]
  module

theorem bivectorRotor_mul_reverse_of_unit
    (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    (bivectorRotor (E := E) a b).comp (bivectorRotorReverse (E := E) a b) =
      ContinuousLinearMap.id ℝ H₂ := by
  rw [bivectorRotor_mul_reverse, h]
  simp

theorem hyperbolicRotor_mul_reverse (a b : ℝ) :
    (hyperbolicRotor (E := E) a b).comp
        (hyperbolicRotorReverse (E := E) a b) =
      (a ^ 2 - b ^ 2) • ContinuousLinearMap.id ℝ H₂ := by
  unfold hyperbolicRotor
  unfold hyperbolicRotorReverse
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    hyperbolicBoostAxis_sq]
  apply ContinuousLinearMap.ext
  intro v
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    map_add, map_smul, smul_add, smul_smul]
  module

theorem hyperbolicRotor_mul_reverse_of_unit
    (a b : ℝ) (h : a ^ 2 - b ^ 2 = 1) :
    (hyperbolicRotor (E := E) a b).comp
        (hyperbolicRotorReverse (E := E) a b) =
      ContinuousLinearMap.id ℝ H₂ := by
  rw [hyperbolicRotor_mul_reverse, h]
  simp

/-! ## Canonical `x p` pair -/

/-- A bounded real canonical pair whose CCR is represented by the Hestenes
bivector axis. -/
structure CanonicalPair where
  xOp : EndH
  pOp : EndH
  hbar : ℝ
  commutation :
    xOp ∘L pOp - pOp ∘L xOp =
      hbar • bivectorAxis (E := E)

namespace CanonicalPair

variable (C : CanonicalPair (E := E))

/-- Weyl-symmetric part of the ordered product `x p`. -/
noncomputable def symmetric : EndH :=
  (1 / 2 : ℝ) • (C.xOp ∘L C.pOp + C.pOp ∘L C.xOp)

/-- Antisymmetric Hestenes commutator part of the ordered product `x p`. -/
noncomputable def antisymmetric : EndH :=
  (1 / 2 : ℝ) • (C.xOp ∘L C.pOp - C.pOp ∘L C.xOp)

@[simp] theorem orderedProduct_eq_symmetric_add_antisymmetric :
    C.xOp ∘L C.pOp = C.symmetric + C.antisymmetric := by
  dsimp [symmetric, antisymmetric]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  module

@[simp] theorem antisymmetric_eq_bivector_term :
    C.antisymmetric =
      (C.hbar / 2 : ℝ) • bivectorAxis (E := E) := by
  dsimp [antisymmetric]
  rw [C.commutation]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  module

theorem symmetric_eq_orderedProduct_sub_bivector :
    C.symmetric = C.xOp ∘L C.pOp -
      (C.hbar / 2 : ℝ) • bivectorAxis (E := E) := by
  have hsplit := C.orderedProduct_eq_symmetric_add_antisymmetric
  rw [C.antisymmetric_eq_bivector_term] at hsplit
  exact eq_sub_of_add_eq hsplit.symm

theorem antisymmetric_eq_half_commutator :
    C.antisymmetric =
      (1 / 2 : ℝ) • (C.xOp ∘L C.pOp - C.pOp ∘L C.xOp) :=
  rfl

end CanonicalPair

/-! ## Pointwise readouts -/

theorem canonicalPair_commutator_apply
    (C : CanonicalPair (E := E)) (v : H₂) :
    (C.xOp ∘L C.pOp - C.pOp ∘L C.xOp) v =
      C.hbar • bivectorAxis (E := E) v := by
  rw [C.commutation]
  rfl

theorem canonicalPair_orderedProduct_apply
    (C : CanonicalPair (E := E)) (v : H₂) :
    (C.xOp ∘L C.pOp) v =
      (CanonicalPair.symmetric C v +
        CanonicalPair.antisymmetric C v) := by
  exact congrArg (fun T : EndH => T v)
    (CanonicalPair.orderedProduct_eq_symmetric_add_antisymmetric C)

end InfoGeometry.Physics.SymmetricAsymmetricXP

end noncomputable section
