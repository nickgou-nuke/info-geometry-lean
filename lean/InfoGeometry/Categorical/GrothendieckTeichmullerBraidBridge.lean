import Mathlib.Tactic
import InfoGeometry.Algebra.AnyonFiniteSpinBraid

open InfoGeometry.Algebra.AnyonFiniteSpinBraid

namespace InfoGeometry.Categorical.GrothendieckTeichmullerBraidBridge

/-- Native subtype of generator pairs satisfying the `B₃` Artin relation.

This restores the historical API without introducing an evidence-record
wrapper: the proof is the subtype membership certificate.
-/
abbrev B3BraidWitness (G : Type*) [Monoid G] :=
  {p : G × G // p.1 * p.2 * p.1 = p.2 * p.1 * p.2}

namespace B3BraidWitness

variable {G : Type*} [Monoid G]

/-- First Artin generator of a native `B₃` witness. -/
def σ1 (w : B3BraidWitness G) : G :=
  w.1.1

/-- Second Artin generator of a native `B₃` witness. -/
def σ2 (w : B3BraidWitness G) : G :=
  w.1.2

/-- The subtype certificate read back as the `B₃` relation. -/
theorem braid_relation (w : B3BraidWitness G) :
    w.σ1 * w.σ2 * w.σ1 = w.σ2 * w.σ1 * w.σ2 :=
  w.2

/-- Construct the native witness directly from an Artin relation. -/
def mk (σ₁ σ₂ : G)
    (hbraid : σ₁ * σ₂ * σ₁ = σ₂ * σ₁ * σ₂) :
    B3BraidWitness G :=
  ⟨(σ₁, σ₂), hbraid⟩

@[simp] theorem mk_σ1 (σ₁ σ₂ : G)
    (hbraid : σ₁ * σ₂ * σ₁ = σ₂ * σ₁ * σ₂) :
    (mk σ₁ σ₂ hbraid).σ1 = σ₁ :=
  rfl

@[simp] theorem mk_σ2 (σ₁ σ₂ : G)
    (hbraid : σ₁ * σ₂ * σ₁ = σ₂ * σ₁ * σ₂) :
    (mk σ₁ σ₂ hbraid).σ2 = σ₂ :=
  rfl

end B3BraidWitness

/-- Historical name for a genuine multiplicative automorphism. -/
abbrev GTAutomorphism (G : Type*) [Mul G] :=
  G ≃* G

/-- Every monoid homomorphism carries a pair satisfying the `B₃` braid
relation to another such pair. -/
theorem gt_automorphism_preserves_b3
    {G H : Type*} [Monoid G] [Monoid H]
    (ϕ : G →* H) (σ₁ σ₂ : G)
    (hbraid : σ₁ * σ₂ * σ₁ = σ₂ * σ₁ * σ₂) :
    ϕ σ₁ * ϕ σ₂ * ϕ σ₁ = ϕ σ₂ * ϕ σ₁ * ϕ σ₂ := by
  simpa only [map_mul] using congrArg ϕ hbraid

/-- A multiplicative equivalence transports a native `B₃` witness. -/
def B3BraidWitness.map
    {G H : Type*} [Monoid G] [Monoid H]
    (ϕ : G ≃* H) (w : B3BraidWitness G) :
    B3BraidWitness H :=
  B3BraidWitness.mk (ϕ w.σ1) (ϕ w.σ2)
    (gt_automorphism_preserves_b3 ϕ.toMonoidHom
      w.σ1 w.σ2 w.braid_relation)

@[simp] theorem B3BraidWitness.map_σ1
    {G H : Type*} [Monoid G] [Monoid H]
    (ϕ : G ≃* H) (w : B3BraidWitness G) :
    (B3BraidWitness.map ϕ w).σ1 = ϕ w.σ1 :=
  rfl

@[simp] theorem B3BraidWitness.map_σ2
    {G H : Type*} [Monoid G] [Monoid H]
    (ϕ : G ≃* H) (w : B3BraidWitness G) :
    (B3BraidWitness.map ϕ w).σ2 = ϕ w.σ2 :=
  rfl

/-- The image braid generators are explicit witnesses of the transported
`B₃` relation. -/
theorem gt_braid_action_exists
    {G H : Type*} [Monoid G] [Monoid H]
    (ϕ : G →* H) (σ₁ σ₂ : G)
    (hbraid : σ₁ * σ₂ * σ₁ = σ₂ * σ₁ * σ₂) :
    ∃ τ₁ τ₂ : H, τ₁ * τ₂ * τ₁ = τ₂ * τ₁ * τ₂ :=
  ⟨ϕ σ₁, ϕ σ₂, gt_automorphism_preserves_b3 ϕ σ₁ σ₂ hbraid⟩

end InfoGeometry.Categorical.GrothendieckTeichmullerBraidBridge
