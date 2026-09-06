import Mathlib
import proofs.JonesBraidB3
import Mathlib.GroupTheory.PresentedGroup

/-!
# B₃ Matrix Representation — invertibility + PresentedGroup homomorphism

Proved:
- `s₀² = -I`, `s₁² = -I` — braid generators are invertible
- `s0_unit`, `s1_unit` — them as units of GL₈(ℂ)
- `braid_square_eq_neg_one` — key identity for the group hom
- `phi : B₃ →* GL₈(ℂ)` — group homomorphism from presented B₃
- `phi_sigma1`, `phi_sigma2` — φ(σᵢ) = sᵢ as matrices
-/

noncomputable section

namespace B3PresentedGroup

open Matrix
open PresentedGroup

/-- The group of invertible 8×8 complex matrices. -/
abbrev GL8 := (Matrix (Fin 8) (Fin 8) ℂ)ˣ

/-- s₀² = -I. Follows algebraically from (I-e₀)² = I (since e₀²=2e₀). -/
theorem s0_sq_eq_neg_one : JonesBraidB3.s0 * JonesBraidB3.s0 = -(1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  dsimp [JonesBraidB3.s0]
  have h : ((1 : Matrix (Fin 8) (Fin 8) ℂ) - TLChain.e0) *
      ((1 : Matrix (Fin 8) (Fin 8) ℂ) - TLChain.e0) = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
    calc
      (1 - TLChain.e0) * (1 - TLChain.e0) = 1 - TLChain.e0 - TLChain.e0 + TLChain.e0 * TLChain.e0 := by
        noncomm_ring
      _ = 1 - TLChain.e0 - TLChain.e0 + (2 : ℂ) • TLChain.e0 := by rw [TLChain.e0_sq]
      _ = 1 := by simp [two_smul]
  calc
    (Complex.I • (1 - TLChain.e0)) * (Complex.I • (1 - TLChain.e0))
        = (Complex.I * Complex.I) • ((1 - TLChain.e0) * (1 - TLChain.e0)) := by
      simp [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (-1 : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by rw [h]; simp
    _ = -(1 : Matrix (Fin 8) (Fin 8) ℂ) := by simp

/-- s₁² = -I. Follows algebraically from (I-e₁)² = I (since e₁²=2e₁). -/
theorem s1_sq_eq_neg_one : JonesBraidB3.s1 * JonesBraidB3.s1 = -(1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  dsimp [JonesBraidB3.s1]
  have h : ((1 : Matrix (Fin 8) (Fin 8) ℂ) - TLChain.e1) *
      ((1 : Matrix (Fin 8) (Fin 8) ℂ) - TLChain.e1) = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
    calc
      (1 - TLChain.e1) * (1 - TLChain.e1) = 1 - TLChain.e1 - TLChain.e1 + TLChain.e1 * TLChain.e1 := by
        noncomm_ring
      _ = 1 - TLChain.e1 - TLChain.e1 + (2 : ℂ) • TLChain.e1 := by rw [TLChain.e1_sq]
      _ = 1 := by simp [two_smul]
  calc
    (Complex.I • (1 - TLChain.e1)) * (Complex.I • (1 - TLChain.e1))
        = (Complex.I * Complex.I) • ((1 - TLChain.e1) * (1 - TLChain.e1)) := by
      simp [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (-1 : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by rw [h]; simp
    _ = -(1 : Matrix (Fin 8) (Fin 8) ℂ) := by simp

/-- s₀ as an invertible matrix (unit of GL₈(ℂ)). -/
def s0_unit : GL8 :=
  { val := JonesBraidB3.s0
    inv := -JonesBraidB3.s0
    val_inv := by
      calc
        JonesBraidB3.s0 * (-JonesBraidB3.s0) = -(JonesBraidB3.s0 * JonesBraidB3.s0) := by simp
        _ = -(-(1 : Matrix (Fin 8) (Fin 8) ℂ)) := by rw [s0_sq_eq_neg_one]
        _ = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by simp
    inv_val := by
      calc
        (-JonesBraidB3.s0) * JonesBraidB3.s0 = -(JonesBraidB3.s0 * JonesBraidB3.s0) := by simp
        _ = -(-(1 : Matrix (Fin 8) (Fin 8) ℂ)) := by rw [s0_sq_eq_neg_one]
        _ = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by simp
  }

/-- s₁ as an invertible matrix (unit of GL₈(ℂ)). -/
def s1_unit : GL8 :=
  { val := JonesBraidB3.s1
    inv := -JonesBraidB3.s1
    val_inv := by
      calc
        JonesBraidB3.s1 * (-JonesBraidB3.s1) = -(JonesBraidB3.s1 * JonesBraidB3.s1) := by simp
        _ = -(-(1 : Matrix (Fin 8) (Fin 8) ℂ)) := by rw [s1_sq_eq_neg_one]
        _ = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by simp
    inv_val := by
      calc
        (-JonesBraidB3.s1) * JonesBraidB3.s1 = -(JonesBraidB3.s1 * JonesBraidB3.s1) := by simp
        _ = -(-(1 : Matrix (Fin 8) (Fin 8) ℂ)) := by rw [s1_sq_eq_neg_one]
        _ = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by simp
  }

/-- Key identity: (s₀·s₁·s₀)·(s₁·s₀·s₁) = -I.
Follows from Artin relation and s₀²=s₁²=-I. -/
theorem braid_square_eq_neg_one : (JonesBraidB3.s0 * JonesBraidB3.s1 * JonesBraidB3.s0) *
    (JonesBraidB3.s1 * JonesBraidB3.s0 * JonesBraidB3.s1) = -(1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  calc
    (JonesBraidB3.s0 * JonesBraidB3.s1 * JonesBraidB3.s0) *
      (JonesBraidB3.s1 * JonesBraidB3.s0 * JonesBraidB3.s1)
        = (JonesBraidB3.s1 * JonesBraidB3.s0 * JonesBraidB3.s1) *
          (JonesBraidB3.s1 * JonesBraidB3.s0 * JonesBraidB3.s1) := by
      rw [← JonesBraidB3.artin_braid_relation]
    _ = JonesBraidB3.s1 * JonesBraidB3.s0 * (JonesBraidB3.s1 * JonesBraidB3.s1) *
        JonesBraidB3.s0 * JonesBraidB3.s1 := by noncomm_ring
    _ = JonesBraidB3.s1 * JonesBraidB3.s0 * (-(1 : Matrix (Fin 8) (Fin 8) ℂ)) *
        JonesBraidB3.s0 * JonesBraidB3.s1 := by rw [s1_sq_eq_neg_one]
    _ = -(JonesBraidB3.s1 * (JonesBraidB3.s0 * JonesBraidB3.s0) * JonesBraidB3.s1) := by
      noncomm_ring
    _ = -(JonesBraidB3.s1 * (-(1 : Matrix (Fin 8) (Fin 8) ℂ)) * JonesBraidB3.s1) := by
      rw [s0_sq_eq_neg_one]
    _ = JonesBraidB3.s1 * JonesBraidB3.s1 := by simp
    _ = -(1 : Matrix (Fin 8) (Fin 8) ℂ) := by rw [s1_sq_eq_neg_one]

/-! ## Presented group B₃ → GL₈(ℂ) -/

/-- The two abstract Artin generators of `B₃`. -/
inductive B3Gen where
  | sig0
  | sig1
  deriving DecidableEq, Repr

open B3Gen

/-- The single Artin relation word `σ₀σ₁σ₀(σ₁σ₀σ₁)⁻¹`. -/
def b3Relation : FreeGroup B3Gen :=
  (FreeGroup.of sig0 * FreeGroup.of sig1 * FreeGroup.of sig0) *
    (FreeGroup.of sig1 * FreeGroup.of sig0 * FreeGroup.of sig1)⁻¹

/-- Presentation relations for the braid group `B₃`. -/
def b3Relations : Set (FreeGroup B3Gen) := {b3Relation}

/-- The finitely presented braid group `B₃ = ⟨σ₀,σ₁ | σ₀σ₁σ₀=σ₁σ₀σ₁⟩`. -/
abbrev B3 := PresentedGroup b3Relations

/-- Abstract generators mapped to the Jones/Temperley--Lieb matrix units. -/
def braidMap : B3Gen → GL8
  | sig0 => s0_unit
  | sig1 => s1_unit

/-- The Artin relation lifted from matrices to units. -/
theorem units_artin_relation : s0_unit * s1_unit * s0_unit = s1_unit * s0_unit * s1_unit := by
  apply Units.ext
  exact JonesBraidB3.artin_braid_relation

/-- The defining relation evaluates to `1` under the Jones matrix-unit assignment. -/
theorem b3_relation_holds : FreeGroup.lift braidMap b3Relation = 1 := by
  simp only [b3Relation, map_mul, map_inv, FreeGroup.lift_apply_of]
  simp only [braidMap]
  rw [units_artin_relation]
  group

/-- The formal group homomorphism from the presented braid group `B₃` to `GL₈(ℂ)`. -/
def phi : B3 →* GL8 :=
  PresentedGroup.toGroup (f := braidMap) (rels := b3Relations) (by
    intro r hr
    simp [b3Relations] at hr
    subst r
    exact b3_relation_holds)

/-- The first abstract generator maps to the first Jones braid unit. -/
theorem phi_sig0 : phi (PresentedGroup.of sig0 : B3) = s0_unit := by
  change PresentedGroup.toGroup (f := braidMap) (rels := b3Relations) _
      (PresentedGroup.of sig0) = s0_unit
  rw [PresentedGroup.toGroup.of]
  simp [braidMap]

/-- The second abstract generator maps to the second Jones braid unit. -/
theorem phi_sig1 : phi (PresentedGroup.of sig1 : B3) = s1_unit := by
  change PresentedGroup.toGroup (f := braidMap) (rels := b3Relations) _
      (PresentedGroup.of sig1) = s1_unit
  rw [PresentedGroup.toGroup.of]
  simp [braidMap]

#check s0_sq_eq_neg_one
#check s1_sq_eq_neg_one
#check s0_unit
#check s1_unit
#check braid_square_eq_neg_one
#check phi
#check phi_sig0
#check phi_sig1

end B3PresentedGroup
