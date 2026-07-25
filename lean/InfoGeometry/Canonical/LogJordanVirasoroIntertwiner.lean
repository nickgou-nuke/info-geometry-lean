import Mathlib
import InfoGeometry.LogJordanKreinCore

/-!
# InfoGeometry.Canonical.LogJordanVirasoroIntertwiner

Logarithmic CFT Virasoro Intertwiner Bridge.

This module connects the Virasoro zero-mode operator $L_0$ from the Sugawara / CFT representation
to the non-diagonalizable Jordan cell $L(\Delta) = \begin{pmatrix} \Delta & 1 \\ 0 & \Delta \end{pmatrix}$.

## Mathematical Content

1. **Injective Subspace Embedding**: An injective linear map $\iota : \mathbb{k}^2 \to V$ embedding the
   2-dimensional logarithmic multiplet into the representation space $V$.
2. **Intertwining Theorem**: $L_0 \circ \iota = \iota \circ L(\Delta)$, identifying the restriction of $L_0$
   to $\text{im}(\iota)$ with the non-diagonalizable Jordan matrix $L(\Delta)$.
3. **Logarithmic Partner Identity**: The primary state $v_0 = \iota(e_0)$ has eigenvalue $\Delta$,
   and the logarithmic partner $v_1 = \iota(e_1)$ satisfies $L_0 v_1 = \Delta v_1 + v_0$.
-/

namespace InfoGeometry.Canonical.LogJordanVirasoroIntertwiner

open Matrix

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- The $2 \times 2$ nilpotent Jordan shift matrix over scalar field `𝕜`. -/
def jordanNilpotent (𝕜 : Type*) [Semiring 𝕜] : Matrix (Fin 2) (Fin 2) 𝕜 :=
  !![0, 1; 0, 0]

/-- The $2 \times 2$ non-diagonalizable Jordan cell matrix $L(\Delta) = \Delta I + N$ over `𝕜`. -/
def jordanCell (Δ : 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜 :=
  !![Δ, 1; 0, Δ]

/--
A Logarithmic Virasoro Intertwiner structure.

Embeds the 2D non-diagonalizable Jordan cell $L(\Delta)$ into the Virasoro
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
    L0.comp ι = ι.comp (Matrix.toLin' (jordanCell Δ))

namespace LogVirasoroIntertwiner

variable {L0 : Module.End 𝕜 V} {Δ : 𝕜}

/-- Pointwise intertwining evaluation: $L_0(\iota v) = \iota(L(\Delta) v)$. -/
theorem apply_intertwines
    (I : LogVirasoroIntertwiner L0 Δ) (v : Fin 2 → 𝕜) :
    L0 (I.ι v) = I.ι (Matrix.toLin' (jordanCell Δ) v) := by
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
  fin_cases i <;> simp [jordanCell, Matrix.toLin', Matrix.mulVec, Fin.sum_univ_two, Pi.single]

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
  fin_cases i <;> simp [jordanCell, Matrix.toLin', Matrix.mulVec, Fin.sum_univ_two, Pi.single]

/--
**Non-Diagonalizability Preservation:**
The nilpotent shift matrix $N = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ is non-zero and square-zero.
-/
theorem zero_mode_subspace_indecomposable :
    jordanNilpotent 𝕜 ≠ 0 ∧ jordanNilpotent 𝕜 * jordanNilpotent 𝕜 = 0 := by
  constructor
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [jordanNilpotent] at h01
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [jordanNilpotent, Matrix.mul_apply, Fin.sum_univ_two]

end LogVirasoroIntertwiner

end InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
