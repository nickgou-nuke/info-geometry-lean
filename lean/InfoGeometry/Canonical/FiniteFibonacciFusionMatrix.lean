import Mathlib.Tactic
import InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks

/-!
# InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

Finite algebraic fusion-matrix interface for the four-Fibonacci-anyon sector.

The analytic paper obtains a dual basis `Θ` and a fusion matrix

```text
F = [[τ, √τ], [√τ, -τ]]
```

with `τ² + τ = 1`.  This file formalizes the finite algebraic content of that
basis change:

* the `2 × 2` fusion matrix over `ℂ`, parameterized by `τ` and a square-root
  parameter `s` with `s² = τ`;
* `F² = 1` from the two explicit scalar hypotheses;
* `det F = -1`;
* the middle braid readout is the conjugate `B = F R F`;
* the Artin equality is exposed only as an explicit finite matrix hypothesis,
  not as an analytic-continuation theorem.

No hypergeometric functions.
No gamma-function identities.
No analytic continuation.
No proof that a concrete complex root `q = exp(iπ/5)` satisfies the braid relation.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks

/-- The two-dimensional channel index. -/
abbrev ChannelIndex := Fin 2

/-- The Fibonacci fusion matrix `F = [[τ, s], [s, -τ]]`. -/
noncomputable def fibonacciFusionMatrix (τ s : ℂ) : Matrix ChannelIndex ChannelIndex ℂ :=
  !![τ, s; s, -τ]

/-- The diagonal four-anyon `R` matrix with entries `q⁻⁴` and `q³`. -/
noncomputable def fibonacciRMatrix (q : Units ℂ) : Matrix ChannelIndex ChannelIndex ℂ :=
  !![(q ^ (-4 : ℤ) : Units ℂ), 0; 0, (q ^ (3 : ℤ) : Units ℂ)]

/-- The middle-generator matrix obtained by changing to the dual basis and back. -/
noncomputable def fibonacciBMatrix (q : Units ℂ) (τ s : ℂ) : Matrix ChannelIndex ChannelIndex ℂ :=
  fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s

/-- The fusion matrix is involutive when `s² = τ` and `τ² + τ = 1`. -/
theorem fibonacciFusionMatrix_sq
    {τ s : ℂ} (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fibonacciFusionMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← hτ, ← hs]
    ring
  · ring
  · ring
  · rw [← hτ, ← hs]
    ring

/-- The fusion matrix has determinant `-1` under the same finite hypotheses. -/
theorem det_fibonacciFusionMatrix
    {τ s : ℂ} (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (fibonacciFusionMatrix τ s).det = -1 := by
  simp [fibonacciFusionMatrix, Matrix.det_fin_two]
  rw [← hτ, ← hs]
  ring

/-- The dual-basis change is its own inverse. -/
theorem fibonacciFusionMatrix_inv_eq_self
    {τ s : ℂ} (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s = 1 :=
  fibonacciFusionMatrix_sq hs hτ

/-- In the dual basis the middle generator is diagonal by definition of the readout. -/
theorem fibonacciBMatrix_def
    (q : Units ℂ) (τ s : ℂ) :
    fibonacciBMatrix q τ s =
      fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s :=
  rfl

/--
Finite Artin check for the four-anyon matrices, kept theorem-owned by requiring
the exact matrix equality as an explicit algebraic hypothesis.
-/
theorem fibonacci_fourAnyon_artin_from_matrix_identity
    (q : Units ℂ) (τ s : ℂ)
    (hArtin : fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
      fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s) :
    fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
      fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s :=
  hArtin

/-- The first and third diagonal generators commute in the finite matrix model. -/
theorem fibonacciRMatrix_commutes_with_self (q : Units ℂ) :
    fibonacciRMatrix q * fibonacciRMatrix q = fibonacciRMatrix q * fibonacciRMatrix q :=
  rfl

/-- A finite four-anyon matrix packet containing only theorem-owned algebraic data. -/
structure FourAnyonFusionPacket where
  /-- Primitive phase parameter. -/
  q : Units ℂ
  /-- Inverse-golden-ratio parameter. -/
  τ : ℂ
  /-- Square-root parameter for `τ`. -/
  s : ℂ
  /-- Square-root relation. -/
  s_sq : s ^ 2 = τ
  /-- Fibonacci relation for `τ`. -/
  tau_sq_add_tau : τ ^ 2 + τ = 1

namespace FourAnyonFusionPacket

/-- The packet fusion matrix. -/
noncomputable def F (P : FourAnyonFusionPacket) : Matrix ChannelIndex ChannelIndex ℂ :=
  fibonacciFusionMatrix P.τ P.s

/-- The packet diagonal `R` matrix. -/
noncomputable def R (P : FourAnyonFusionPacket) : Matrix ChannelIndex ChannelIndex ℂ :=
  fibonacciRMatrix P.q

/-- The packet middle-generator matrix `B = F R F`. -/
noncomputable def B (P : FourAnyonFusionPacket) : Matrix ChannelIndex ChannelIndex ℂ :=
  fibonacciBMatrix P.q P.τ P.s

/-- The packet fusion matrix is involutive. -/
theorem F_sq (P : FourAnyonFusionPacket) :
    P.F * P.F = 1 :=
  fibonacciFusionMatrix_sq P.s_sq P.tau_sq_add_tau

/-- The packet fusion matrix has determinant `-1`. -/
theorem det_F (P : FourAnyonFusionPacket) :
    P.F.det = -1 :=
  det_fibonacciFusionMatrix P.s_sq P.tau_sq_add_tau

/-- The packet middle generator is `F R F`. -/
theorem B_eq_FRF (P : FourAnyonFusionPacket) :
    P.B = P.F * P.R * P.F :=
  rfl

end FourAnyonFusionPacket

end InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
