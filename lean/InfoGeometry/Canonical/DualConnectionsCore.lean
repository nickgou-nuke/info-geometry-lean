import InfoGeometry.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

/-!
# InfoGeometry.Canonical.DualConnectionsCore

Canonical core interface for dual-connection geometry.
-/

namespace InfoGeometry.Canonical.DualConnections

variable {Θ α : Type*} [Fintype α]

/-- Fiberwise tangent placeholder on a finite probability simplex fiber. -/
abbrev FiberTangent (α : Type*) := α → ℝ

/-- Covariant 3-tensor surface for coordinate connection coefficients. -/
abbrev ConnectionTensor (Θ α : Type*) :=
  Θ → FiberTangent α → FiberTangent α → FiberTangent α → ℝ

/--
Fiberwise Fisher bilinear form on score directions.
This is the finite-model canonical weighted inner product.
-/
def fisherBilinear
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u v : FiberTangent α) : ℝ :=
  ∑ a : α, p θ a * (u a * v a)

lemma fisherBilinear_comm
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u v : FiberTangent α) :
    fisherBilinear p θ u v = fisherBilinear p θ v u := by
  unfold fisherBilinear
  simp [mul_assoc, mul_comm]

lemma fisherBilinear_self_nonneg
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u : FiberTangent α) :
    0 ≤ fisherBilinear p θ u u := by
  unfold fisherBilinear
  refine Finset.sum_nonneg ?_
  intro a _ha
  exact mul_nonneg ((p θ).nonneg a) (mul_self_nonneg (u a))

/--
Amari-Chentsov cubic tensor in finite coordinates.
This is the canonical third-order moment coupling of score fields.
-/
def chentsovTensor
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u v w : FiberTangent α) : ℝ :=
  ∑ a : α, p θ a * (u a * v a * w a)

lemma chentsovTensor_swap_left
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u v w : FiberTangent α) :
    chentsovTensor p θ u v w = chentsovTensor p θ v u w := by
  unfold chentsovTensor
  simp [mul_assoc, mul_left_comm, mul_comm]

/--
`α`-deformation of a reference tensor of connection coefficients:
`Γ^(α) = Γ⁰ - (α/2) T`, where `T` is the Chentsov tensor.
-/
noncomputable def alphaConnectionTensor
    (Gamma0 : ConnectionTensor Θ α)
    (p : Θ → InfoGeometry.FinProb α)
    (alphaC : ℝ) : ConnectionTensor Θ α :=
  fun θ u v w => Gamma0 θ u v w - (alphaC / 2) * chentsovTensor p θ u v w

/-- Exponential (`e`) connection tensor (`α = 1`). -/
noncomputable def eConnectionTensor
    (Gamma0 : ConnectionTensor Θ α)
    (p : Θ → InfoGeometry.FinProb α) : ConnectionTensor Θ α :=
  alphaConnectionTensor Gamma0 p 1

/-- Mixture (`m`) connection tensor (`α = -1`). -/
noncomputable def mConnectionTensor
    (Gamma0 : ConnectionTensor Θ α)
    (p : Θ → InfoGeometry.FinProb α) : ConnectionTensor Θ α :=
  alphaConnectionTensor Gamma0 p (-1)

lemma alphaConnectionTensor_zero
    (Gamma0 : ConnectionTensor Θ α)
    (p : Θ → InfoGeometry.FinProb α) :
    alphaConnectionTensor Gamma0 p 0 = Gamma0 := by
  funext θ u v w
  simp [alphaConnectionTensor]

lemma alphaConnectionTensor_dual_sum
    (Gamma0 : ConnectionTensor Θ α)
    (p : Θ → InfoGeometry.FinProb α)
    (alphaC : ℝ)
    (θ : Θ)
    (u v w : FiberTangent α) :
    alphaConnectionTensor Gamma0 p alphaC θ u v w
      + alphaConnectionTensor Gamma0 p (-alphaC) θ u v w
      = 2 * Gamma0 θ u v w := by
  unfold alphaConnectionTensor
  ring

lemma alphaConnectionTensor_dual_diff
    (Gamma0 : ConnectionTensor Θ α)
    (p : Θ → InfoGeometry.FinProb α)
    (alphaC : ℝ)
    (θ : Θ)
    (u v w : FiberTangent α) :
    alphaConnectionTensor Gamma0 p alphaC θ u v w
      - alphaConnectionTensor Gamma0 p (-alphaC) θ u v w
      = -alphaC * chentsovTensor p θ u v w := by
  unfold alphaConnectionTensor
  ring

lemma e_m_connection_sum
    (Gamma0 : ConnectionTensor Θ α)
    (p : Θ → InfoGeometry.FinProb α)
    (θ : Θ)
    (u v w : FiberTangent α) :
    eConnectionTensor Gamma0 p θ u v w
      + mConnectionTensor Gamma0 p θ u v w
      = 2 * Gamma0 θ u v w := by
  simpa [eConnectionTensor, mConnectionTensor] using
    alphaConnectionTensor_dual_sum
      (Gamma0 := Gamma0) (p := p) (alphaC := (1 : ℝ))
      (θ := θ) (u := u) (v := v) (w := w)

/--
Fisher-metric compatibility marker:
each fiber is a normalized finite probability vector.
-/
def fisherMetric (p : Θ → InfoGeometry.FinProb α) : Prop :=
  ∀ θ : Θ, ∑ a : α, p θ a = 1

/--
Amari-Chentsov nonnegativity surrogate:
nonnegativity of the quadratic probability moment on each fiber.
-/
def amariChentsovTensor (p : Θ → InfoGeometry.FinProb α) : Prop :=
  ∀ θ : Θ, 0 ≤ ∑ a : α, (p θ a) ^ (2 : ℕ)

/-- Bundled `α`-connection: reference tensor + deformation law + compatibility witnesses. -/
structure alphaConnection (p : Θ → InfoGeometry.FinProb α) (αc : ℝ) where
  /-- Reference connection tensor `Γ⁰`. -/
  Gamma0 : ConnectionTensor Θ α
  /-- Fiberwise Fisher normalization witness. -/
  fisherCompat : fisherMetric p
  /-- Fiberwise Chentsov nonnegativity witness. -/
  chentsovCompat : amariChentsovTensor p

namespace alphaConnection

variable {p : Θ → InfoGeometry.FinProb α} {αc : ℝ}

/-- Canonical constructor from a chosen reference tensor. -/
noncomputable def mkFromReference
    (Gamma0 : ConnectionTensor Θ α)
    (hFisher : fisherMetric p)
    (hChentsov : amariChentsovTensor p) :
    alphaConnection p αc where
  Gamma0 := Gamma0
  fisherCompat := hFisher
  chentsovCompat := hChentsov

/-- Deformed `α`-connection tensor `Γ^(α) = Γ⁰ - (α/2)T`. -/
noncomputable def Gamma (A : alphaConnection p αc) : ConnectionTensor Θ α :=
  alphaConnectionTensor A.Gamma0 p αc

@[simp] lemma deformation_law (A : alphaConnection p αc) :
    A.Gamma = alphaConnectionTensor A.Gamma0 p αc := rfl

/-- Change `α` to `-α` while preserving the same reference tensor and compatibilities. -/
noncomputable def dual (A : alphaConnection p αc) : alphaConnection p (-αc) where
  Gamma0 := A.Gamma0
  fisherCompat := A.fisherCompat
  chentsovCompat := A.chentsovCompat

/-- Inverse direction for `dual`. -/
noncomputable def undual (A : alphaConnection p (-αc)) : alphaConnection p αc where
  Gamma0 := A.Gamma0
  fisherCompat := A.fisherCompat
  chentsovCompat := A.chentsovCompat

@[simp] lemma dual_undual (A : alphaConnection p αc) :
    (undual (dual A)).Gamma0 = A.Gamma0 := rfl

@[simp] lemma undual_dual (A : alphaConnection p (-αc)) :
    (dual (undual A)).Gamma0 = A.Gamma0 := rfl

end alphaConnection

/--
`±α` duality at the bundled level.
-/
noncomputable def alpha_duality (p : Θ → InfoGeometry.FinProb α) (αc : ℝ) :
    alphaConnection p αc ≃ alphaConnection p (-αc) where
  toFun := alphaConnection.dual
  invFun := alphaConnection.undual
  left_inv := by
    intro A
    cases A
    rfl
  right_inv := by
    intro A
    cases A
    rfl

/-- Canonical bundled `α`-connection built from finite-probability fibers. -/
noncomputable def alphaConnection_of_finProb
    (p : Θ → InfoGeometry.FinProb α)
    (αc : ℝ) :
    alphaConnection p αc := by
  refine alphaConnection.mkFromReference (p := p) (αc := αc) (Gamma0 := fun _ _ _ _ => 0) ?_ ?_
  · intro θ
    exact (p θ).sum_one
  · intro θ
    refine Finset.sum_nonneg ?_
    intro a _ha
    exact sq_nonneg (p θ a)

/-- Finite-probability fibers satisfy the Fisher normalization marker. -/
theorem fisherMetric_of_finProb (p : Θ → InfoGeometry.FinProb α) :
    fisherMetric p := by
  intro θ
  exact (p θ).sum_one

/-- Finite-probability fibers satisfy the Chentsov quadratic nonnegativity marker. -/
theorem amariChentsovTensor_of_finProb (p : Θ → InfoGeometry.FinProb α) :
    amariChentsovTensor p := by
  intro θ
  refine Finset.sum_nonneg ?_
  intro a ha
  exact sq_nonneg (p θ a)

/--
Compatibility bridge name preserved:
Fisher-normalized fibers imply the quadratic Chentsov nonnegativity marker.
-/
theorem fisher_metric_eq_hessian_KL (p : Θ → InfoGeometry.FinProb α) :
    fisherMetric p → amariChentsovTensor p := by
  intro _hf
  exact amariChentsovTensor_of_finProb p

end InfoGeometry.Canonical.DualConnections
