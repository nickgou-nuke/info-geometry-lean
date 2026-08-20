import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Noncommutative KMS-GNS Core Consolidation

This module serves as the **Single Source of Truth** for algebraic KMS states
and the Gel'fand-Naimark-Segal (GNS) construction on non-commutative $*$-algebras:

1. **Universal KMS State**:
   A state `φ : A →ₗ[R] R` on a ring `A` with modular automorphism `σ : A → A`
   satisfying the non-commutative thermal boundary condition:
   `φ(a * b) = φ(b * σ(a))`
2. **Modular State Invariance**:
   `φ(σ(a)) = φ(a)` whenever `σ` is unital (`σ(1) = 1`).
3. **Centralizer Commutativity**:
   If `x` is in the modular fixed point subalgebra (`σ(x) = x`), then `φ(x * y) = φ(y * x)`.
4. **GNS Sesquilinear Form**:
   `⟨a, b⟩_φ = φ(star b * a)` for any $*$-ring `A`.
5. **GNS Bilinearity & Left Regular *-Intertwining**:
   `⟨x * a, b⟩_φ = ⟨a, star x * b⟩_φ`
6. **GNS Shift Invariance**:
   If an endomorphism `Φ : A → A` preserves the state (`φ(Φ(x)) = φ(x)`),
   the GNS inner product is isometric: `⟨Φ(a), Φ(b)⟩_φ = ⟨a, b⟩_φ`.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.NCG.Core

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-!
=============================================================================
SECTION 1: Universal KMS Modular States
=============================================================================
-/

/-- A linear functional `φ : A →ₗ[R] R` is a KMS state with respect to automorphism `σ`
    if it satisfies the non-commutative KMS boundary condition `φ(a * b) = φ(b * σ(a))`. -/
structure KMSState (σ : A → A) (φ : A →ₗ[R] R) : Prop where
  apply_kms : ∀ a b : A, φ (a * b) = φ (b * σ a)

namespace KMSState

/-- 🏆 THEOREM 1: Modular State Invariance:
    The KMS state is invariant under `σ`:
    `φ(σ(a)) = φ(a)` -/
theorem state_modular_invariance {σ : A → A} {φ : A →ₗ[R] R}
    (hKMS : KMSState σ φ) (a : A) :
    φ (σ a) = φ a := by
  have h := hKMS.apply_kms a 1
  simp only [mul_one, one_mul] at h
  exact h.symm

/-- 🏆 THEOREM 2: Centralizer Commutativity:
    If `x` is in the modular fixed-point subalgebra (`σ(x) = x`), then `φ(x * y) = φ(y * x)`. -/
theorem centralizer_comm {σ : A → A} {φ : A →ₗ[R] R}
    (hKMS : KMSState σ φ) (x : A) (hx : σ x = x) (y : A) :
    φ (x * y) = φ (y * x) := by
  have h := hKMS.apply_kms x y
  rw [hx] at h
  exact h

/-- 🏆 THEOREM 3: Identity Modular Automorphism is Tracial:
    If `σ = id`, the KMS state is a trace `φ(a * b) = φ(b * a)`. -/
theorem identity_is_tracial {σ : A → A} {φ : A →ₗ[R] R}
    (hKMS : KMSState σ φ) (h_id : σ = id) (a b : A) :
    φ (a * b) = φ (b * a) := by
  have h := hKMS.apply_kms a b
  simp only [h_id, id_eq] at h
  exact h

end KMSState

/-!
=============================================================================
SECTION 2: Universal GNS Construction on Star-Algebras
=============================================================================
-/

variable {S : Type*} [Ring S] [StarRing S] [Algebra R S]

/-- The GNS Sesquilinear Pre-Inner Product: `⟨a, b⟩_φ = φ(star b * a)` -/
def gnsInner (φ : S →ₗ[R] R) (a b : S) : R :=
  φ (star b * a)

/-- 🏆 THEOREM 4: GNS Inner Product Left-Additivity:
    `⟨a₁ + a₂, b⟩_φ = ⟨a₁, b⟩_φ + ⟨a₂, b⟩_φ` -/
theorem gnsInner_add_left (φ : S →ₗ[R] R) (a₁ a₂ b : S) :
    gnsInner φ (a₁ + a₂) b = gnsInner φ a₁ b + gnsInner φ a₂ b := by
  dsimp [gnsInner]
  rw [mul_add, φ.map_add]

/-- 🏆 THEOREM 5: GNS Inner Product Right-Additivity:
    `⟨a, b₁ + b₂⟩_φ = ⟨a, b₁⟩_φ + ⟨a, b₂⟩_φ` -/
theorem gnsInner_add_right (φ : S →ₗ[R] R) (a b₁ b₂ : S) :
    gnsInner φ a (b₁ + b₂) = gnsInner φ a b₁ + gnsInner φ a b₂ := by
  dsimp [gnsInner]
  rw [star_add, add_mul, φ.map_add]

/-- 🏆 THEOREM 6: GNS Left-Regular Representation *-Intertwining:
    `⟨x * a, b⟩_φ = ⟨a, star x * b⟩_φ` -/
theorem gnsInner_left_regular (φ : S →ₗ[R] R) (x a b : S) :
    gnsInner φ (x * a) b = gnsInner φ a (star x * b) := by
  dsimp [gnsInner]
  have h : star b * (x * a) = star (star x * b) * a := by
    simp only [star_mul, star_star, mul_assoc]
  rw [h]

/-- 🏆 THEOREM 7: GNS Endomorphism Invariance (Shift / Tilt Isometry):
    If `Φ : S → S` is a $*$-homomorphism preserving `φ`, then `⟨Φ(a), Φ(b)⟩_φ = ⟨a, b⟩_φ`. -/
theorem gnsInner_isometry (φ : S →ₗ[R] R) (Φ : S → S)
    (h_star : ∀ x, Φ (star x) = star (Φ x))
    (h_mul : ∀ x y, Φ (x * y) = Φ x * Φ y)
    (h_inv : ∀ x, φ (Φ x) = φ x)
    (a b : S) :
    gnsInner φ (Φ a) (Φ b) = gnsInner φ a b := by
  dsimp [gnsInner]
  rw [← h_star, ← h_mul, h_inv]

/-- Connes Perturbation of a linear functional `φ` by an element `h ∈ S`:
    `φ_h(x) = φ(h * x * h)` -/
def connesPerturb (φ : S →ₗ[R] R) (h : S) : S →ₗ[R] R where
  toFun x := φ (h * x * h)
  map_add' x y := by
    simp only [mul_add, add_mul, φ.map_add]
  map_smul' r x := by
    have h_smul : h * (r • x) * h = r • (h * x * h) := by
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    simp only [h_smul, φ.map_smul, smul_eq_mul, RingHom.id_apply]

end InfoGeometry.NCG.Core

end noncomputable section
