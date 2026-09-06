import Mathlib.Algebra.Algebra.Bilinear
import InfoGeometry.Canonical.SouriauKKSForm
import InfoGeometry.Canonical.SouriauKKSContragredientBridge
import InfoGeometry.Physics.SouriauLieThermodynamics

/-!
# Abstract operator-orbit response geometry

This file owns the physics-independent Level-2 response interface for the
operator-orbit architecture.

An `OperatorOrbitResponse` consists of two bilinear readouts on a Lie-algebra
carrier:

* a symmetric response `metric`;
* a skew response `symplectic`.

Transport invariance is expressed separately as a predicate on a linear
equivalence.  Concrete KKS and Souriau--Fisher/BKM owners enter only through
realization predicates; they are not definitionally identified with the
abstract response.

No spacetime, Berry, Yang--Mills, gravitational, pure-spinor, Pin/Spin, or von
Neumann interpretation is asserted here.  Those belong to Level-3 realization
owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorOrbitResponse

open SouriauKKS
open InfoGeometry.Physics.SouriauLieThermodynamics
open InfoGeometry.Canonical.SouriauKKSContragredientBridge

variable {R L : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/--
The invariant response packet on an operator-orbit tangent/Lie carrier.

The two forms are intentionally independent data.  A concrete realization may
later prove that they arise from Fisher/BKM and KKS/Berry constructions.
-/
structure OperatorOrbitResponse where
  metric : L →ₗ[R] L →ₗ[R] R
  symplectic : L →ₗ[R] L →ₗ[R] R
  metric_symm : ∀ X Y : L, metric X Y = metric Y X
  symplectic_skew : ∀ X Y : L, symplectic X Y = -symplectic Y X

namespace OperatorOrbitResponse

variable (D : OperatorOrbitResponse (R := R) (L := L))

/-- Re-export of symmetry for the symmetric response. -/
@[simp] theorem metric_swap (X Y : L) :
    D.metric X Y = D.metric Y X :=
  D.metric_symm X Y

/-- Re-export of skewness for the antisymmetric response. -/
@[simp] theorem symplectic_swap (X Y : L) :
    D.symplectic X Y = -D.symplectic Y X :=
  D.symplectic_skew X Y

/-- Over `ℝ`, the skew response is alternating. -/
theorem symplectic_self_zero
    {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    (D : OperatorOrbitResponse (R := ℝ) (L := L)) (X : L) :
    D.symplectic X X = 0 := by
  have h := D.symplectic_skew X X
  linarith

/--
Transport invariance of both response tensors under a linear symmetry
equivalence.

Bracket preservation is intentionally not built into this predicate: metric
and symplectic invariance are tensorial statements.  A KKS realization adds
the bracket-preservation hypothesis when deriving this predicate.
-/
def IsInvariantUnder (e : L ≃ₗ[R] L) : Prop :=
  (∀ X Y : L, D.metric (e X) (e Y) = D.metric X Y) ∧
  (∀ X Y : L, D.symplectic (e X) (e Y) = D.symplectic X Y)

/-- Identity transport preserves every response packet. -/
theorem invariantUnder_refl :
    D.IsInvariantUnder (LinearEquiv.refl R L) := by
  constructor <;> intro X Y <;> rfl

/-- Invariance is closed under composition of symmetry transports. -/
theorem invariantUnder_trans
    (e₁ e₂ : L ≃ₗ[R] L)
    (h₁ : D.IsInvariantUnder e₁)
    (h₂ : D.IsInvariantUnder e₂) :
    D.IsInvariantUnder (e₂.trans e₁) := by
  constructor
  · intro X Y
    change D.metric (e₁ (e₂ X)) (e₁ (e₂ Y)) = D.metric X Y
    rw [h₁.1, h₂.1]
  · intro X Y
    change D.symplectic (e₁ (e₂ X)) (e₁ (e₂ Y)) = D.symplectic X Y
    rw [h₁.2, h₂.2]

/-- Invariance under an equivalence implies invariance under its inverse. -/
theorem invariantUnder_symm
    (e : L ≃ₗ[R] L)
    (h : D.IsInvariantUnder e) :
    D.IsInvariantUnder e.symm := by
  constructor
  · intro X Y
    have hxy := h.1 (e.symm X) (e.symm Y)
    simpa only [e.apply_symm_apply] using hxy.symm
  · intro X Y
    have hxy := h.2 (e.symm X) (e.symm Y)
    simpa only [e.apply_symm_apply] using hxy.symm

/-! ## Realization predicates -/

/-- The abstract symmetric response is realized by a repository
Souriau--Fisher covariance tensor. -/
def MetricRealizesFisher
    (F : SouriauState.SouriauFisherMetric R L) : Prop :=
  ∀ X Y : L, D.metric X Y = F.cov X Y

/-- The abstract skew response is realized by the algebraic KKS form at `μ`. -/
def SymplecticRealizesKKS
    (μ : Module.Dual R L) : Prop :=
  ∀ X Y : L, D.symplectic X Y = kksForm μ X Y

/-- A Fisher realization transports the abstract metric symmetry to the
concrete covariance tensor. -/
theorem fisher_realization_symmetry
    (F : SouriauState.SouriauFisherMetric R L)
    (hF : D.MetricRealizesFisher F)
    (X Y : L) :
    F.cov X Y = F.cov Y X := by
  rw [← hF X Y, ← hF Y X]
  exact D.metric_symm X Y

/-- A KKS realization transports the repository KKS skew law to the abstract
skew response. -/
theorem kks_realization_skew
    (μ : Module.Dual R L)
    (hKKS : D.SymplecticRealizesKKS μ)
    (X Y : L) :
    D.symplectic X Y = -D.symplectic Y X := by
  rw [hKKS X Y, hKKS Y X]
  exact kksForm_skew μ X Y

/--
If the symmetric realization is itself invariant under `e`, the abstract
metric response is invariant under `e`.
-/
theorem metric_invariant_of_fisher_realization
    (e : L ≃ₗ[R] L)
    (F : SouriauState.SouriauFisherMetric R L)
    (hF : D.MetricRealizesFisher F)
    (hInv : ∀ X Y : L, F.cov (e X) (e Y) = F.cov X Y) :
    ∀ X Y : L, D.metric (e X) (e Y) = D.metric X Y := by
  intro X Y
  rw [hF (e X) (e Y), hF X Y]
  exact hInv X Y

/--
KKS equivariance supplies invariance of the abstract skew response provided the
transported dual state is represented by the same abstract response tensor.

The extra realization hypothesis on the contragredient state is essential:
KKS transport changes the dual state, so invariance cannot be inferred from a
single fixed-state realization alone.
-/
theorem symplectic_invariant_of_kks_contragredient_realization
    (e : L ≃ₗ[R] L)
    (hLie : ∀ X Y : L, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (μ : Module.Dual R L)
    (hSource : D.SymplecticRealizesKKS μ)
    (hTransported : D.SymplecticRealizesKKS
      (InfoGeometry.Canonical.SouriauContragredientPairing.contragredient e μ)) :
    ∀ X Y : L, D.symplectic (e X) (e Y) = D.symplectic X Y := by
  intro X Y
  rw [hTransported (e X) (e Y), hSource X Y]
  exact kksForm_contragredient_invariant e hLie μ X Y

/--
Combined response invariance from independent symmetric and KKS realization
proofs.  This is the Level-2 commuting-square constructor used by concrete
Level-3 adapters.
-/
theorem invariantUnder_of_realizations
    (e : L ≃ₗ[R] L)
    (hLie : ∀ X Y : L, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (F : SouriauState.SouriauFisherMetric R L)
    (μ : Module.Dual R L)
    (hF : D.MetricRealizesFisher F)
    (hFInv : ∀ X Y : L, F.cov (e X) (e Y) = F.cov X Y)
    (hSource : D.SymplecticRealizesKKS μ)
    (hTransported : D.SymplecticRealizesKKS
      (InfoGeometry.Canonical.SouriauContragredientPairing.contragredient e μ)) :
    D.IsInvariantUnder e := by
  exact ⟨D.metric_invariant_of_fisher_realization e F hF hFInv,
    D.symplectic_invariant_of_kks_contragredient_realization
      e hLie μ hSource hTransported⟩

end OperatorOrbitResponse

end InfoGeometry.Canonical.OperatorOrbitResponse
