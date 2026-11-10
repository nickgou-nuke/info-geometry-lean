/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.Decomposition
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Tomita–Takesaki Modular Spin Intertwining & Hawking Horizon Unitarity

Target: `InfoGeometry/Superalgebra/TomitaTakesakiModularSpinHawkingUnitarity.lean`

Epistemically compiled from AI Studio archive `1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or`
(Section 133, Turn 268) directly on the canonical 8-dimensional split-octonion carrier
`ZornCell R` (`InfoGeometry.Algebra.Zorn.ConcreteComposition`):

1. **Hyperbolic Modular Operator $\Delta(c, s) = c\,\mathbf{1} + s\,K_0 = \mathrm{diag}(c+s, c-s)$:**
   - Exact hyperbolic composition law:
     $$\Delta(c_1, s_1)\,\Delta(c_2, s_2) = \Delta(c_1 c_2 + s_1 s_2,\; c_1 s_2 + s_1 c_2);$$
   - On the unit mass shell $c^2 - s^2 = 1$:
     $$\Delta(c, s)\,\Delta(c, -s) = \mathbf{1}, \qquad \det_Z(\Delta(c, s)) = 1.$$
2. **Bogoliubov Spin–Boost Intertwining & Fisher Metric Invariance:**
   - For the compact spin generator $I(\mathbf{x}) = U(\mathbf{x}) - V(\mathbf{x})$ and
     hyperbolic boost generator $H(\mathbf{x}) = U(\mathbf{x}) + V(\mathbf{x})$:
     $$\Delta(c, s)\,I(\mathbf{x}) = c\,I(\mathbf{x}) + s\,H(\mathbf{x}), \qquad
       \Delta(c, s)\,H(\mathbf{x}) = s\,I(\mathbf{x}) + c\,H(\mathbf{x}),$$
     and on the mass shell $c^2 - s^2 = 1$,
     $\det_Z(\Delta(c, s)\,I(\mathbf{x})) = \|\mathbf{x}\|^2$.
3. **Rindler–Tomita Modular Automorphism on Twistor Projectors & Hawking Unitarity:**
   - Under $\sigma_{c,s}(X) = \Delta(c, s)\,X\,\Delta(c, -s)$ with $c^2 - s^2 = 1$, the
     forward twistor projector $P_+(\mathbf{u}) = e_1 + U(\mathbf{u})$ blueshifts by
     $(c + s)^2$ while the backward projector $P_-(\mathbf{v}) = e_2 + V(\mathbf{v})$
     redshifts by $(c - s)^2$, yet both the symmetric metric correlator
     $\{\sigma_{c,s}(U(\mathbf{u})), \sigma_{c,s}(V(\mathbf{v}))\} = (\mathbf{u}\cdot\mathbf{v})\mathbf{1}$
     and the para-symplectic horizon charge
     $[\sigma_{c,s}(U(\mathbf{u})), \sigma_{c,s}(V(\mathbf{v}))] = (\mathbf{u}\cdot\mathbf{v})K_0$
     are strictly conserved across the horizon.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Modular & Hawking Unitarity Theorems (`[kernel_verified]`):**
  - `modular_delta_group_composition` and `modular_delta_unitarity`.
  - `modular_bogoliubov_spin_boost_intertwining` and `modular_spin_preserves_fisher_interval`.
  - `modular_automorphism_scales_twistor_projectors`,
    `hawking_horizon_information_strictly_conserved`, and `tomita_zorn_noncommutative`.

* **BUCKET 2 — Eliminated Duplicate Carriers & Certificate Wrappers (Zero Remaining):**
  - Eliminates the raw transcript's duplicate `SplitOctonion` carrier and
    `TomitaTakesakiHawkingCertificate : Prop` wrapper in favor of `ZornCell R`.

* **BUCKET 3 — Infinite-Dimensional Type-$\mathrm{III}_1$ Von Neumann Modular Theory (`[bucket_3_open_debt]`):**
  - Unbounded operator domains for Tomita's $S = J \Delta^{1/2}$ on infinite-dimensional
    Hilbert spaces remain outside this finite-dimensional `ZornCell R` scope.
-/

namespace InfoGeometry.Superalgebra.TomitaTakesakiHawking

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

variable {R : Type*} [Ring R]

/-- Multiplicative identity $\mathbf{1} = \mathrm{diag}(1, 1)$ in `ZornCell R`. -/
def oneZ : ZornCell R :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

/-- Para-symplectic chiral parity generator $K_0 = \mathrm{diag}(1, -1)$ in `ZornCell R`. -/
def paraSymplecticK0 : ZornCell R :=
  ⟨1, -1, 0, 0, 0, 0, 0, 0⟩

/-- Coordinatewise subtraction on `ZornCell R`. -/
def subZ (X Y : ZornCell R) : ZornCell R :=
  ⟨X.r - Y.r, X.s - Y.s,
   X.x1 - Y.x1, X.x2 - Y.x2, X.x3 - Y.x3,
   X.y1 - Y.y1, X.y2 - Y.y2, X.y3 - Y.y3⟩

/-- Scalar multiplication $k \cdot X$ on `ZornCell R`. -/
def smulZ (k : R) (X : ZornCell R) : ZornCell R :=
  ⟨k * X.r, k * X.s,
   k * X.x1, k * X.x2, k * X.x3,
   k * X.y1, k * X.y2, k * X.y3⟩

/-- Symmetric Jordan anticommutator $\{X, Y\} = X Y + Y X$ on `ZornCell R`. -/
def anticommutatorZ (X Y : ZornCell R) : ZornCell R :=
  addZ (mulZ X Y) (mulZ Y X)

/-- Skew-symmetric commutator $[X, Y] = X Y - Y X$ on `ZornCell R`. -/
def commutatorZ (X Y : ZornCell R) : ZornCell R :=
  subZ (mulZ X Y) (mulZ Y X)

/-- Forward isotropic chiral sheet $U(\mathbf{u})$ in `ZornCell R`. -/
def sheetU (u₁ u₂ u₃ : R) : ZornCell R :=
  ⟨0, 0, u₁, u₂, u₃, 0, 0, 0⟩

/-- Backward isotropic chiral sheet $V(\mathbf{v})$ in `ZornCell R`. -/
def sheetV (v₁ v₂ v₃ : R) : ZornCell R :=
  ⟨0, 0, 0, 0, 0, v₁, v₂, v₃⟩

/-- Compact spin generator $I(\mathbf{x}) = U(\mathbf{x}) - V(\mathbf{x})$ in `ZornCell R`. -/
def spinGenI (x₁ x₂ x₃ : R) : ZornCell R :=
  subZ (sheetU x₁ x₂ x₃) (sheetV x₁ x₂ x₃)

/-- Hyperbolic boost generator $H(\mathbf{x}) = U(\mathbf{x}) + V(\mathbf{x})$ in `ZornCell R`. -/
def boostGenH (x₁ x₂ x₃ : R) : ZornCell R :=
  addZ (sheetU x₁ x₂ x₃) (sheetV x₁ x₂ x₃)

/-- Forward super-Grassmannian twistor projector $P_+(\mathbf{u}) = e_1 + U(\mathbf{u})$. -/
def twistorProjPlus (u₁ u₂ u₃ : R) : ZornCell R :=
  ⟨1, 0, u₁, u₂, u₃, 0, 0, 0⟩

/-- Backward super-Grassmannian twistor projector $P_-(\mathbf{v}) = e_2 + V(\mathbf{v})$. -/
def twistorProjMinus (v₁ v₂ v₃ : R) : ZornCell R :=
  ⟨0, 1, 0, 0, 0, v₁, v₂, v₃⟩

/-- Hyperbolic Tomita–Takesaki modular operator $\Delta(c, s) = c\,\mathbf{1} + s\,K_0$. -/
def modularDelta (c s : R) : ZornCell R :=
  ⟨c + s, c - s, 0, 0, 0, 0, 0, 0⟩

/-- Two-sided modular automorphism $\sigma_{c,s}(X) = \Delta(c, s)\,X\,\Delta(c, -s)$. -/
def modularAutomorphism (c s : R) (X : ZornCell R) : ZornCell R :=
  mulZ (mulZ (modularDelta c s) X) (modularDelta c (-s))

variable {R : Type*} [CommRing R]

/-- **Hyperbolic Group Composition Law (`modular_delta_group_composition`):**
$\Delta(c_1, s_1)\,\Delta(c_2, s_2) = \Delta(c_1 c_2 + s_1 s_2,\; c_1 s_2 + s_1 c_2)$. -/
theorem modular_delta_group_composition (c₁ s₁ c₂ s₂ : R) :
    mulZ (modularDelta c₁ s₁) (modularDelta c₂ s₂) =
      modularDelta (c₁ * c₂ + s₁ * s₂) (c₁ * s₂ + s₁ * c₂) := by
  refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp [mulZ, modularDelta]; ring)

/-- **Hyperbolic Mass-Shell Unitarity (`modular_delta_unitarity`):**
When $c^2 - s^2 = 1$, $\Delta(c, s)\,\Delta(c, -s) = \mathbf{1}$ and $\det_Z(\Delta(c, s)) = 1$. -/
theorem modular_delta_unitarity (c s : R) (h_hyp : c ^ 2 - s ^ 2 = 1) :
    mulZ (modularDelta c s) (modularDelta c (-s)) = oneZ ∧
    detZ (modularDelta c s) = 1 := by
  refine ⟨?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp [mulZ, modularDelta, oneZ]; linear_combination h_hyp
    · dsimp [mulZ, modularDelta, oneZ]; linear_combination h_hyp
    · dsimp [mulZ, modularDelta, oneZ]; ring
    · dsimp [mulZ, modularDelta, oneZ]; ring
    · dsimp [mulZ, modularDelta, oneZ]; ring
    · dsimp [mulZ, modularDelta, oneZ]; ring
    · dsimp [mulZ, modularDelta, oneZ]; ring
    · dsimp [mulZ, modularDelta, oneZ]; ring
  · dsimp [detZ, modularDelta]
    linear_combination h_hyp

/-- **Bogoliubov Spin–Boost Intertwining (`modular_bogoliubov_spin_boost_intertwining`):**
Left multiplication by $\Delta(c, s)$ mixes compact spin $I(\mathbf{x})$ and hyperbolic
boost $H(\mathbf{x})$ according to
$\Delta(c, s)\,I(\mathbf{x}) = c\,I(\mathbf{x}) + s\,H(\mathbf{x})$ and
$\Delta(c, s)\,H(\mathbf{x}) = s\,I(\mathbf{x}) + c\,H(\mathbf{x})$. -/
theorem modular_bogoliubov_spin_boost_intertwining (c s x₁ x₂ x₃ : R) :
    mulZ (modularDelta c s) (spinGenI x₁ x₂ x₃) =
      addZ (smulZ c (spinGenI x₁ x₂ x₃)) (smulZ s (boostGenH x₁ x₂ x₃)) ∧
    mulZ (modularDelta c s) (boostGenH x₁ x₂ x₃) =
      addZ (smulZ s (spinGenI x₁ x₂ x₃)) (smulZ c (boostGenH x₁ x₂ x₃)) := by
  refine ⟨?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [mulZ, modularDelta, spinGenI, boostGenH, sheetU, sheetV, addZ, subZ, smulZ]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [mulZ, modularDelta, spinGenI, boostGenH, sheetU, sheetV, addZ, subZ, smulZ]; ring)

/-- **Fisher Interval Invariance Under Modular Spin (`modular_spin_preserves_fisher_interval`):**
On the hyperbolic shell $c^2 - s^2 = 1$, $\det_Z(\Delta(c, s)\,I(\mathbf{x})) = x_1^2 + x_2^2 + x_3^2$. -/
theorem modular_spin_preserves_fisher_interval (c s x₁ x₂ x₃ : R)
    (h_hyp : c ^ 2 - s ^ 2 = 1) :
    detZ (mulZ (modularDelta c s) (spinGenI x₁ x₂ x₃)) =
      x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 := by
  dsimp [detZ, mulZ, modularDelta, spinGenI, subZ, sheetU, sheetV]
  linear_combination (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) * h_hyp

/-- **Rindler Blueshift/Redshift on Twistor Projectors
(`modular_automorphism_scales_twistor_projectors`):**
Under $\sigma_{c,s}$ with $c^2 - s^2 = 1$, $P_+(\mathbf{u})$ scales by $(c+s)^2$ while
$P_-(\mathbf{v})$ scales by $(c-s)^2$. -/
theorem modular_automorphism_scales_twistor_projectors (c s u₁ u₂ u₃ v₁ v₂ v₃ : R)
    (h_hyp : c ^ 2 - s ^ 2 = 1) :
    modularAutomorphism c s (twistorProjPlus u₁ u₂ u₃) =
      twistorProjPlus ((c + s) ^ 2 * u₁) ((c + s) ^ 2 * u₂) ((c + s) ^ 2 * u₃) ∧
    modularAutomorphism c s (twistorProjMinus v₁ v₂ v₃) =
      twistorProjMinus ((c - s) ^ 2 * v₁) ((c - s) ^ 2 * v₂) ((c - s) ^ 2 * v₃) := by
  refine ⟨?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp [modularAutomorphism, modularDelta, twistorProjPlus, mulZ]
      linear_combination h_hyp
    · dsimp [modularAutomorphism, modularDelta, twistorProjPlus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjPlus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjPlus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjPlus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjPlus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjPlus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjPlus, mulZ]; ring
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp [modularAutomorphism, modularDelta, twistorProjMinus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjMinus, mulZ]
      linear_combination h_hyp
    · dsimp [modularAutomorphism, modularDelta, twistorProjMinus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjMinus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjMinus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjMinus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjMinus, mulZ]; ring
    · dsimp [modularAutomorphism, modularDelta, twistorProjMinus, mulZ]; ring

/-- **Two-Sheet Hawking Horizon Unitarity (`hawking_horizon_information_strictly_conserved`):**
Despite the opposite Rindler scaling factors $(c+s)^2$ and $(c-s)^2$ on the forward and
backward sheets, both the symmetric metric correlator $\{\sigma(U(\mathbf{u})), \sigma(V(\mathbf{v}))\}$
and the para-symplectic horizon commutator $[\sigma(U(\mathbf{u})), \sigma(V(\mathbf{v}))]$
are strictly invariant when $c^2 - s^2 = 1$. -/
theorem hawking_horizon_information_strictly_conserved (c s u₁ u₂ u₃ v₁ v₂ v₃ : R)
    (h_hyp : c ^ 2 - s ^ 2 = 1) :
    anticommutatorZ (modularAutomorphism c s (sheetU u₁ u₂ u₃))
                    (modularAutomorphism c s (sheetV v₁ v₂ v₃)) =
      smulZ (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) oneZ ∧
    commutatorZ (modularAutomorphism c s (sheetU u₁ u₂ u₃))
                (modularAutomorphism c s (sheetV v₁ v₂ v₃)) =
      smulZ (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) paraSymplecticK0 := by
  have h_prod : (c + s) ^ 2 * (c - s) ^ 2 = 1 := by
    calc (c + s) ^ 2 * (c - s) ^ 2
      _ = (c ^ 2 - s ^ 2) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [h_hyp]
      _ = 1 := by ring
  refine ⟨?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp [anticommutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, oneZ, mulZ, addZ, smulZ]
      linear_combination (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) * h_prod
    · dsimp [anticommutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, oneZ, mulZ, addZ, smulZ]
      linear_combination (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) * h_prod
    · dsimp [anticommutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, oneZ, mulZ, addZ, smulZ]; ring
    · dsimp [anticommutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, oneZ, mulZ, addZ, smulZ]; ring
    · dsimp [anticommutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, oneZ, mulZ, addZ, smulZ]; ring
    · dsimp [anticommutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, oneZ, mulZ, addZ, smulZ]; ring
    · dsimp [anticommutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, oneZ, mulZ, addZ, smulZ]; ring
    · dsimp [anticommutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, oneZ, mulZ, addZ, smulZ]; ring
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp [commutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, paraSymplecticK0, mulZ, subZ, smulZ]
      linear_combination (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) * h_prod
    · dsimp [commutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, paraSymplecticK0, mulZ, subZ, smulZ]
      linear_combination -(u₁ * v₁ + u₂ * v₂ + u₃ * v₃) * h_prod
    · dsimp [commutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, paraSymplecticK0, mulZ, subZ, smulZ]; ring
    · dsimp [commutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, paraSymplecticK0, mulZ, subZ, smulZ]; ring
    · dsimp [commutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, paraSymplecticK0, mulZ, subZ, smulZ]; ring
    · dsimp [commutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, paraSymplecticK0, mulZ, subZ, smulZ]; ring
    · dsimp [commutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, paraSymplecticK0, mulZ, subZ, smulZ]; ring
    · dsimp [commutatorZ, modularAutomorphism, modularDelta, sheetU, sheetV, paraSymplecticK0, mulZ, subZ, smulZ]; ring

/-- Explicit non-commutativity witness on `ZornCell ℤ` for the modular operator and spin generator. -/
theorem tomita_zorn_noncommutative :
    mulZ (modularDelta (1 : ℤ) 1) (spinGenI 1 0 0) ≠
      mulZ (spinGenI (1 : ℤ) 0 0) (modularDelta 1 1) := by
  intro h
  have hx1 := congrArg ZornCell.x1 h
  revert hx1
  decide

end InfoGeometry.Superalgebra.TomitaTakesakiHawking
