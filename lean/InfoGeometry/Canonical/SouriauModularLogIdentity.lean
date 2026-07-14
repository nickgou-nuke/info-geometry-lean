import InfoGeometry.External.Virasoro.Commutator

/-!
# InfoGeometry.Canonical.SouriauModularLogIdentity

Constructive modular-log commutator transport lemmas.

This file is algebraic only: no `exp`, no `log`, no placeholders.
-/

namespace SouriauModularLogIdentity

open LinearMap

variable {𝕜 V : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Algebraic modular data for commutator transport. -/
structure ModularLogData where
  Delta : V →ₗ[𝕜] V
  K : V →ₗ[𝕜] V
  Delta_inv : ∃ Inv : V →ₗ[𝕜] V, Delta.comp Inv = 1 ∧ Inv.comp Delta = 1
  K_derivation :
    ∀ A : V →ₗ[𝕜] V, (K.commutator A).comp Delta = Delta.comp (K.commutator A)

namespace ModularLogData

variable (M : ModularLogData (𝕜 := 𝕜) (V := V))

/-- Readout of the defining derivation compatibility. -/
theorem commutator_comp_Delta_eq_Delta_comp_commutator
    (A : V →ₗ[𝕜] V) :
    (M.K.commutator A).comp M.Delta = M.Delta.comp (M.K.commutator A) :=
  M.K_derivation A

/-- If `[K,A]=0`, then both commutator channels composed with `Δ` are zero. -/
theorem commutator_zero_implies_composed_zero
    (A : V →ₗ[𝕜] V)
    (hKA : M.K.commutator A = 0) :
    (M.K.commutator A).comp M.Delta = 0 ∧
      M.Delta.comp (M.K.commutator A) = 0 := by
  constructor <;> simp [hKA]

/-- Right cancellation through invertible `Δ`. -/
theorem comp_Delta_eq_zero_iff
    (X : V →ₗ[𝕜] V) :
    X.comp M.Delta = 0 ↔ X = 0 := by
  constructor
  · intro h
    rcases M.Delta_inv with ⟨Inv, hL, _hR⟩
    calc
      X = X.comp (M.Delta.comp Inv) := by
        rw [hL]
        ext v
        rfl
      _ = (X.comp M.Delta).comp Inv := by simp [LinearMap.comp_assoc]
      _ = 0 := by simp [h]
  · intro h
    simp [h]

/-- Left cancellation through invertible `Δ`. -/
theorem Delta_comp_eq_zero_iff
    (X : V →ₗ[𝕜] V) :
    M.Delta.comp X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rcases M.Delta_inv with ⟨Inv, _hL, hR⟩
    calc
      X = (Inv.comp M.Delta).comp X := by
        rw [hR]
        ext v
        rfl
      _ = Inv.comp (M.Delta.comp X) := by simp [LinearMap.comp_assoc]
      _ = 0 := by simp [h]
  · intro h
    simp [h]

/--
Equivalent vanishing tests for `[K,A]` through composed channels with `Δ`.
-/
theorem commutator_zero_iff_composed_zero
    (A : V →ₗ[𝕜] V) :
    M.K.commutator A = 0 ↔
      (M.K.commutator A).comp M.Delta = 0 ∧
      M.Delta.comp (M.K.commutator A) = 0 := by
  constructor
  · intro h
    exact M.commutator_zero_implies_composed_zero A h
  · intro h
    exact (M.comp_Delta_eq_zero_iff (M.K.commutator A)).1 h.1

end ModularLogData
end SouriauModularLogIdentity
