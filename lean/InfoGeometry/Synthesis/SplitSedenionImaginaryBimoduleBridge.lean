/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import InfoGeometry.Canonical.SplitOctonionClifford33Soldering
import InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
import InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly

/-!
# Split-Sedenion Imaginary Bimodule Coordinate Chart and Two-Sheet Derivation Intertwining

This module constructs the explicit coordinate charts for the 7-dimensional imaginary
split-octonion subspace $\operatorname{Im}(\mathbb{O}_s) \cong \mathbb{R}^7$ and the
15-dimensional imaginary split-sedenion subspace
$\operatorname{Im}(\mathbb{S}_s) \cong (\mathbb{R}^7 \times \mathbb{R}^7) \times \mathbb{R}$
($15 = 7 \times 2 + 1$) over the Zorn split-octonion carrier `ZornSplitOctonion ℝ` and
the Cayley–Dickson pair carrier `SplitSedenion ℝ`:

1. **Section 1 — 7-Dimensional Imaginary Split-Octonion Coordinate Chart (`Im(𝕆ₛ) ≃ (Fin 7 → ℝ)`)**:
   - Defines `imZornToFin7 : ZornSplitOctonion ℝ → (Fin 7 → ℝ)` and its section
     `fin7ToImZorn : (Fin 7 → ℝ) → ZornSplitOctonion ℝ` parameterizing the trace-free
     subspace $\{x \in \mathbb{O}_s \mid x.a + x.b = 0\}$.
   - Proves trace vanishing `fin7ToImZorn_trace_zero`, anti-self-conjugacy
     `fin7ToImZorn_conj_eq_neg` ($x^\star = -x$), left inverse `imZornToFin7_fin7ToImZorn`,
     and right inverse `fin7ToImZorn_imZornToFin7` on trace-free split-octonions.
2. **Section 2 — 15-Dimensional Imaginary Split-Sedenion Decomposition (`15 = (7 × 2) + 1`)**:
   - Defines `IsImaginarySedenion X` ($X.1.a + X.1.b = 0$), the coordinate decomposition
     `imSedenionToBimoduleAndEll : SplitSedenion ℝ → ((Fin 7 → ℝ) × (Fin 7 → ℝ)) × ℝ`, and
     the reconstruction map `imSedenionFromBimoduleAndEll`.
   - Certifies `imSedenionFromBimoduleAndEll_isImaginary`, the left inverse
     `imSedenionToBimoduleAndEll_from`, and the right inverse
     `imSedenionFromBimoduleAndEll_to` on `IsImaginarySedenion`.
3. **Section 3 — Bimodule Commutativity of Diagonal `cdLift D₀` and Two-Sheet Linear Mixing**:
   - Defines the 4-parameter two-sheet linear mixing operator `sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁`
     on `SplitSedenion ℝ`.
   - Proves `cdLift_commutes_with_sheetLinearMix`, showing that the diagonal Cayley–Dickson
     lift `cdLift D₀` of any $\mathbb{R}$-linear operator $D_0 : \mathbb{O}_s \to \mathbb{O}_s$
     commutes with `sheetLinearMix`.
   - Proves `sheetLinearMix_preserves_bimodule_sector`, showing that `sheetLinearMix` preserves
     the 14-dimensional trace-free bimodule sector $\operatorname{Im}(\mathbb{O}_s) \times \operatorname{Im}(\mathbb{O}_s)$.
-/

noncomputable section

namespace InfoGeometry.Synthesis.SplitSedenionImaginaryBimoduleBridge

open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly

/-!
## Section 1: 7-Dimensional Imaginary Split-Octonion Coordinate Chart `Im(𝕆ₛ) ≃ (Fin 7 → ℝ)`
-/

/-- Extracts the 7 imaginary coordinates of a Zorn split-octonion $x \in \mathbb{O}_s$:
the diagonal para-grading coordinate $x.a - x.b$ followed by the three primal coordinates
$x.u_0, x.u_1, x.u_2$ and three dual coordinates $x.v_0, x.v_1, x.v_2$. -/
def imZornToFin7 (x : ZornSplitOctonion ℝ) : Fin 7 → ℝ :=
  ![x.a - x.b, x.u 0, x.u 1, x.u 2, x.v 0, x.v 1, x.v 2]

/-- Reconstructs a trace-free Zorn split-octonion $x \in \operatorname{Im}(\mathbb{O}_s)$
from a 7-component coordinate vector $w : \mathrm{Fin}\, 7 \to \mathbb{R}$, placing
$\tfrac{1}{2} w_0$ and $-\tfrac{1}{2} w_0$ on the diagonal and $(w_1, w_2, w_3)$, $(w_4, w_5, w_6)$
in the off-diagonal vector slots. -/
def fin7ToImZorn (w : Fin 7 → ℝ) : ZornSplitOctonion ℝ :=
  ⟨(1 / 2 : ℝ) * w 0, ![w 1, w 2, w 3], ![w 4, w 5, w 6], -(1 / 2 : ℝ) * w 0⟩

/-- Every split-octonion reconstructed by `fin7ToImZorn` has vanishing scalar trace $a + b = 0$. -/
theorem fin7ToImZorn_trace_zero (w : Fin 7 → ℝ) :
    (fin7ToImZorn w).a + (fin7ToImZorn w).b = 0 := by
  have _ := w
  dsimp [fin7ToImZorn]
  ring

/-- Every split-octonion reconstructed by `fin7ToImZorn` is negated by Zorn conjugation:
$z^\star = -z$. -/
theorem fin7ToImZorn_conj_eq_neg (w : Fin 7 → ℝ) :
    zornConj (fin7ToImZorn w) = zornSmul (-1 : ℝ) (fin7ToImZorn w) := by
  have _ := w
  ext i
  · dsimp [zornConj, zornSmul, fin7ToImZorn]
    ring
  · fin_cases i <;> (dsimp [zornConj, zornSmul, fin7ToImZorn]; ring)
  · fin_cases i <;> (dsimp [zornConj, zornSmul, fin7ToImZorn]; ring)
  · dsimp [zornConj, zornSmul, fin7ToImZorn]
    ring

/-- `imZornToFin7` is a left inverse to `fin7ToImZorn` on `Fin 7 → ℝ`. -/
theorem imZornToFin7_fin7ToImZorn (w : Fin 7 → ℝ) :
    imZornToFin7 (fin7ToImZorn w) = w := by -- [repo-owned: InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge#ZornSplitOctonion]
  have _ := w
  ext i
  fin_cases i <;> (dsimp [imZornToFin7, fin7ToImZorn]; try ring)

/-- `fin7ToImZorn` is a left inverse to `imZornToFin7` on the 7-dimensional trace-free
imaginary subspace $\{x \in \mathbb{O}_s \mid x.a + x.b = 0\}$. -/
theorem fin7ToImZorn_imZornToFin7 (x : ZornSplitOctonion ℝ) (hx : x.a + x.b = 0) :
    fin7ToImZorn (imZornToFin7 x) = x := by
  have hb : x.b = -x.a := eq_neg_of_add_eq_zero_right hx
  ext i
  · dsimp [fin7ToImZorn, imZornToFin7]
    rw [hb]
    ring
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · dsimp [fin7ToImZorn, imZornToFin7]
    rw [hb]
    ring

/-!
## Section 2: 15-Dimensional Imaginary Split-Sedenion Decomposition `15 = (7 × 2) + 1`
-/

/-- Predicate characterizing an imaginary split-sedenion $X = (X_1, X_2) \in \mathbb{S}_s$:
the scalar trace of the first octonion component vanishes ($X_1.a + X_1.b = 0$), leaving
$7$ imaginary coordinates in $X_1$ and $8 = 7 + 1$ coordinates in $X_2$. -/
def IsImaginarySedenion (X : SplitSedenion ℝ) : Prop :=
  X.1.a + X.1.b = 0

/-- Decomposes an imaginary split-sedenion $X = (X_1, X_2) \in \operatorname{Im}(\mathbb{S}_s)$
into its $7 \times 2$ bimodule coordinates `(imZornToFin7 X.1, imZornToFin7 X.2)` in
$\operatorname{Im}(\mathbb{O}_s) \times \operatorname{Im}(\mathbb{O}_s)$ together with its scalar
doubling-axis coordinate $\tfrac{1}{2}(X_2.a + X_2.b)$ along $\ell = (0, 1_{\mathbb{O}_s})$. -/
def imSedenionToBimoduleAndEll (X : SplitSedenion ℝ) :
    ((Fin 7 → ℝ) × (Fin 7 → ℝ)) × ℝ :=
  ((imZornToFin7 X.1, imZornToFin7 X.2), (1 / 2 : ℝ) * (X.2.a + X.2.b))

/-- Reconstructs an imaginary split-sedenion $X \in \operatorname{Im}(\mathbb{S}_s)$ from its
14-dimensional bimodule pair $(w_1, w_2) \in (\mathrm{Fin}\, 7 \to \mathbb{R})^2$ and its
1-dimensional doubling-unit coordinate $c \in \mathbb{R}$. -/
def imSedenionFromBimoduleAndEll (p : ((Fin 7 → ℝ) × (Fin 7 → ℝ)) × ℝ) :
    SplitSedenion ℝ :=
  (fin7ToImZorn p.1.1, zornAdd (fin7ToImZorn p.1.2) (zornSmul p.2 zornOne))

/-- Adding a scalar multiple of `zornOne` leaves the 7 imaginary coordinates `imZornToFin7`
unchanged. -/
theorem imZornToFin7_add_smul_zornOne (y : ZornSplitOctonion ℝ) (c : ℝ) :
    imZornToFin7 (zornAdd y (zornSmul c zornOne)) = imZornToFin7 y := by -- [repo-owned: InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge#ZornSplitOctonion]
  have _ := (y, c)
  ext i
  fin_cases i <;> (dsimp [imZornToFin7, zornAdd, zornSmul, zornOne]; try ring)

/-- Every split-sedenion reconstructed by `imSedenionFromBimoduleAndEll` lies in the
15-dimensional imaginary subspace `IsImaginarySedenion`. -/
theorem imSedenionFromBimoduleAndEll_isImaginary
    (p : ((Fin 7 → ℝ) × (Fin 7 → ℝ)) × ℝ) :
    IsImaginarySedenion (imSedenionFromBimoduleAndEll p) := by -- [repo-owned: InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge#ZornSplitOctonion]
  dsimp [IsImaginarySedenion, imSedenionFromBimoduleAndEll]
  exact fin7ToImZorn_trace_zero p.1.1

/-- `imSedenionToBimoduleAndEll` is a left inverse to `imSedenionFromBimoduleAndEll`
on `((Fin 7 → ℝ) × (Fin 7 → ℝ)) × ℝ`. -/
theorem imSedenionToBimoduleAndEll_from
    (p : ((Fin 7 → ℝ) × (Fin 7 → ℝ)) × ℝ) :
    imSedenionToBimoduleAndEll (imSedenionFromBimoduleAndEll p) = p := by -- [repo-owned: InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge#ZornSplitOctonion]
  rcases p with ⟨⟨w₁, w₂⟩, c⟩
  apply Prod.ext
  · apply Prod.ext
    · dsimp [imSedenionToBimoduleAndEll, imSedenionFromBimoduleAndEll]
      exact imZornToFin7_fin7ToImZorn w₁
    · dsimp [imSedenionToBimoduleAndEll, imSedenionFromBimoduleAndEll]
      rw [imZornToFin7_add_smul_zornOne]
      exact imZornToFin7_fin7ToImZorn w₂
  · dsimp [imSedenionToBimoduleAndEll, imSedenionFromBimoduleAndEll,
      zornAdd, fin7ToImZorn, zornSmul, zornOne]
    ring

/-- `imSedenionFromBimoduleAndEll` is a left inverse to `imSedenionToBimoduleAndEll` on every
imaginary split-sedenion $X \in \operatorname{Im}(\mathbb{S}_s)$. -/
theorem imSedenionFromBimoduleAndEll_to
    (X : SplitSedenion ℝ) (hX : IsImaginarySedenion X) :
    imSedenionFromBimoduleAndEll (imSedenionToBimoduleAndEll X) = X := by -- [repo-owned: InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge#ZornSplitOctonion]
  apply Prod.ext
  · dsimp [imSedenionFromBimoduleAndEll, imSedenionToBimoduleAndEll]
    exact fin7ToImZorn_imZornToFin7 X.1 hX
  · dsimp [imSedenionFromBimoduleAndEll, imSedenionToBimoduleAndEll]
    ext i
    · dsimp [zornAdd, fin7ToImZorn, imZornToFin7, zornSmul, zornOne]
      ring
    · fin_cases i <;> (dsimp [zornAdd, fin7ToImZorn, imZornToFin7, zornSmul, zornOne]; ring)
    · fin_cases i <;> (dsimp [zornAdd, fin7ToImZorn, imZornToFin7, zornSmul, zornOne]; ring)
    · dsimp [zornAdd, fin7ToImZorn, imZornToFin7, zornSmul, zornOne]
      ring

/-!
## Section 3: Bimodule Commutativity of Diagonal `cdLift D₀` and Two-Sheet Mixing
-/

/-- The 4-parameter two-sheet linear mixing operator on `SplitSedenion ℝ`, mapping
$(X_1, X_2) \mapsto (s_{00} X_1 + s_{01} X_2,\; s_{10} X_1 + s_{11} X_2)$. -/
def sheetLinearMix (s₀₀ s₀₁ s₁₀ s₁₁ : ℝ) (X : SplitSedenion ℝ) : SplitSedenion ℝ :=
  (zornAdd (zornSmul s₀₀ X.1) (zornSmul s₀₁ X.2),
   zornAdd (zornSmul s₁₀ X.1) (zornSmul s₁₁ X.2))

/-- **Bimodule Commutativity of Diagonal Cayley–Dickson Lift and Two-Sheet Mixing**:
For any $\mathbb{R}$-linear operator $D_0 : \mathbb{O}_s \to \mathbb{O}_s$ (such as a derivation
$D_0 \in \mathfrak{g}_{2(2)} = \operatorname{Der}(\mathbb{O}_s)$), its diagonal Cayley–Dickson
lift `cdLift D₀` commutes identically with the two-sheet linear mixing operator
`sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁` on `SplitSedenion ℝ`. -/
theorem cdLift_commutes_with_sheetLinearMix
    (D₀ : ZornSplitOctonion ℝ → ZornSplitOctonion ℝ)
    (h_add : ∀ x y, D₀ (zornAdd x y) = zornAdd (D₀ x) (D₀ y))
    (h_smul : ∀ c x, D₀ (zornSmul c x) = zornSmul c (D₀ x))
    (s₀₀ s₀₁ s₁₀ s₁₁ : ℝ) (X : SplitSedenion ℝ) :
    cdLift D₀ (sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁ X) =
      sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁ (cdLift D₀ X) := by
  apply Prod.ext
  · dsimp [cdLift, sheetLinearMix]
    rw [h_add (zornSmul s₀₀ X.1) (zornSmul s₀₁ X.2), h_smul s₀₀ X.1, h_smul s₀₁ X.2]
  · dsimp [cdLift, sheetLinearMix]
    rw [h_add (zornSmul s₁₀ X.1) (zornSmul s₁₁ X.2), h_smul s₁₀ X.1, h_smul s₁₁ X.2]

/-- **Invariance of the 14-Dimensional Bimodule Sector under Two-Sheet Linear Mixing**:
Whenever $X = (X_1, X_2)$ lies in the 14-dimensional bimodule sector
$\operatorname{Im}(\mathbb{O}_s) \times \operatorname{Im}(\mathbb{O}_s)$
(`IsImaginarySedenion X` and `X.2.a + X.2.b = 0`), the mixed sedenion
`sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁ X` remains in `IsImaginarySedenion` and also preserves
trace-freeness of the second sheet. -/
theorem sheetLinearMix_preserves_bimodule_sector
    (s₀₀ s₀₁ s₁₀ s₁₁ : ℝ) (X : SplitSedenion ℝ)
    (hX1 : IsImaginarySedenion X) (hX2 : X.2.a + X.2.b = 0) :
    IsImaginarySedenion (sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁ X) ∧
      (sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁ X).2.a +
        (sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁ X).2.b = 0 := by
  have hb1 : X.1.b = -X.1.a := eq_neg_of_add_eq_zero_right hX1
  have hb2 : X.2.b = -X.2.a := eq_neg_of_add_eq_zero_right hX2
  have _ := (s₀₀, s₀₁, s₁₀, s₁₁)
  refine ⟨?_, ?_⟩
  · dsimp [IsImaginarySedenion, sheetLinearMix, zornAdd, zornSmul]
    rw [hb1, hb2]
    ring
  · dsimp [sheetLinearMix, zornAdd, zornSmul]
    rw [hb1, hb2]
    ring

end InfoGeometry.Synthesis.SplitSedenionImaginaryBimoduleBridge
