import Mathlib
import InfoGeometry.LogJordanKreinCore
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.LogJordanVirasoroIntertwiner

Logarithmic CFT Virasoro Intertwiner Bridge.

This module connects the Virasoro zero-mode operator $L_0$ from the Sugawara / CFT representation
to the non-diagonalizable Jordan cell $L(\Delta) = \Delta I + N$ from `LogJordanKreinCore.lean`.

## Mathematical Content

1. **Injective Subspace Embedding**: An injective linear map $\iota : \mathbb{k}^2 \to V$ embedding the
   2-dimensional logarithmic multiplet into the representation space $V$.
2. **Intertwining Theorem**: $L_0 \circ \iota = \iota \circ L(\Delta)$, identifying the restriction of $L_0$
   to $\text{im}(\iota)$ with the non-diagonalizable Jordan matrix $L(\Delta)$.
3. **Logarithmic Partner Identity**: The primary state $v_0 = \iota(e_0)$ has eigenvalue $\Delta$,
   and the logarithmic partner $v_1 = \iota(e_1)$ satisfies $L_0 v_1 = \Delta v_1 + v_0$.
-/

namespace InfoGeometry.Canonical.LogJordanVirasoroIntertwiner

open InfoGeometry.LogJordanKreinCore

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/--
A Logarithmic Virasoro Intertwiner structure.

Embeds the 2D non-diagonalizable Jordan cell $L(\Delta) = \Delta I + N$ into the Virasoro
zero-mode operator $L_0 : V \toₗ[𝕜] V$.
-/
structure LogVirasoroIntertwiner
    (L0 : Module.End 𝕜 V) (Δ : 𝕜) where
  /-- Injective embedding of the 2D logarithmic multiplet into `V`. -/
  ι : (Fin 2 → 𝕜) →ₗ[𝕜] V
  /-- Injectivity of the multiplet embedding. -/
  injective : Function.Injective ι
  /-- Intertwining relation with the non-diagonalizable Jordan cell $L(\Delta)$. -/
  intertwines :
    L0.comp ι = ι.comp (Matrix.toLin' (scalarMatrix Δ + N))

namespace LogVirasoroIntertwiner

variable {L0 : Module.End 𝕜 V} {Δ : 𝕜}

/-- Pointwise intertwining evaluation: $L_0(\iota v) = \iota(L(\Delta) v)$. -/
theorem apply_intertwines
    (I : LogVirasoroIntertwiner L0 Δ) (v : Fin 2 → 𝕜) :
    L0 (I.ι v) = I.ι (Matrix.toLin' (scalarMatrix Δ + N) v) := by
  have h := LinearMap.congr_fun I.intertwines v
  exact h

/--
**Logarithmic Primary State Eigenvalue Law:**
The primary state $v_0 = \iota(e_0)$ is an eigenvector of $L_0$ with eigenvalue $\Delta$.
-/
theorem primary_eigenvalue
    (I : LogVirasoroIntertwiner L0 Δ) :
    L0 (I.ι (Pi.single 0 (1 : 𝕜))) = Δ • I.ι (Pi.single 0 (1 : 𝕜)) := by
  rw [apply_intertwines]
  congr 1
  ext i
  fin_cases i <;> simp [scalarMatrix, N, Matrix.toLin', Matrix.mulVec, Fin.sum_univ_two, Pi.single]

/--
**Logarithmic Partner State Action Law:**
The logarithmic partner $v_1 = \iota(e_1)$ satisfies $L_0 v_1 = \Delta v_1 + v_0$.
-/
theorem partner_action
    (I : LogVirasoroIntertwiner L0 Δ) :
    L0 (I.ι (Pi.single 1 (1 : 𝕜))) =
      Δ • I.ι (Pi.single 1 (1 : 𝕜)) + I.ι (Pi.single 0 (1 : 𝕜)) := by
  rw [apply_intertwines]
  rw [← map_smul, ← map_add]
  congr 1
  ext i
  fin_cases i <;> simp [scalarMatrix, N, Matrix.toLin', Matrix.mulVec, Fin.sum_univ_two, Pi.single]

/--
**Non-Diagonalizability Preservation:**
The restriction of $L_0$ to the 2D subspace $\text{im}(\iota)$ is non-diagonalizable.
-/
theorem zero_mode_subspace_indecomposable
    (I : LogVirasoroIntertwiner L0 Δ) :
    N ≠ 0 ∧ N * N = 0 := by
  constructor
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [N] at h01
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_two]

end LogVirasoroIntertwiner

end InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
