/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.Decomposition
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Split-Octonion Maurer–Cartan–Twistor–Albert 13-Pillar Grand Unified Tower

Target: `InfoGeometry/Superalgebra/SplitOctonionGrandUnifiedTowerArchive.lean`

Epistemically compiled from AI Studio archive `1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or`
(Section 138, Turn 283) directly on the canonical 8-dimensional split-octonion carrier
`ZornCell R` (`InfoGeometry.Algebra.Zorn.ConcreteComposition`):

1. **Pillars $\mathcal{A}_1$–$\mathcal{A}_3$ (`pillar_1_3_hestenes_majorana_triad`):**
   Isotropic chiral sheet nilpotency $U(\mathbf{u})^2 = 0$, Hestenes geometric product
   $2\,U(\mathbf{u})V(\mathbf{v}) = (\mathbf{u}\cdot\mathbf{v})\mathbf{1} + (\mathbf{u}\cdot\mathbf{v})K_0$,
   and para-symplectic spin–boost transmutation $K_0\,I(\mathbf{x}) = H(\mathbf{x})$.
2. **Pillar $\mathcal{A}_4$ (`pillar_4_cayley_dickson_norm`):**
   Cayley–Dickson $(4,4)$ Krein interval splitting
   $\det_Z(\mathrm{CD}(p, q)) = \|p\|_{\mathbb{H}}^2 - \|q\|_{\mathbb{H}}^2$.
3. **Pillars $\mathcal{A}_5$ & $\mathcal{A}_7$ (`pillar_5_7_confinement_and_jacobi_anomaly`):**
   Baryonic associator $[U(\mathbf{u}_1), U(\mathbf{u}_2), U(\mathbf{u}_3)] = -\det_3(\mathbf{u}_1,\mathbf{u}_2,\mathbf{u}_3)\,K_0$,
   symmetrized singlet $\{U(\mathbf{u}_1), U(\mathbf{u}_2), U(\mathbf{u}_3)\}_+ = \det_3(\mathbf{u}_1,\mathbf{u}_2,\mathbf{u}_3)\,\mathbf{1}$,
   and Akivis–Malcev Jacobiator $J(U(\mathbf{u}_1), U(\mathbf{u}_2), U(\mathbf{u}_3)) = -6\det_3(\mathbf{u}_1,\mathbf{u}_2,\mathbf{u}_3)\,K_0$.
4. **Pillars $\mathcal{A}_8$ & $\mathcal{A}_9$ (`pillar_8_9_rotor_and_einstein_fisher_dispersion`):**
   Maurer–Cartan nilpotency $\omega_L(\mathbf{u}, \mathbf{d})^2 = 0$, exponential twistor rotor
   $P_+(\mathbf{u})\,(\mathbf{1} + \omega_L(\mathbf{u}, \mathbf{d})) = P_+(\mathbf{u}+\mathbf{d}) + V(\mathbf{u}\times\mathbf{d})$,
   and Einstein–Fisher–Berry dispersion $\mathrm{Tr}(Q)^2 - \mathrm{STr}(Q)^2 = 4\|(\mathbf{u}\times\mathbf{d})\times\mathbf{d}\|^2$.
5. **Pillars $\mathcal{A}_{10}$–$\mathcal{A}_{13}$ (`pillar_10_tomita_takesaki_hawking_unitarity`,
   `pillar_11_12_spin_fusion_and_faraday_monopole`,
   `pillar_13_canonical_lagrangian_and_albert_trace`):**
   Tomita–Takesaki Hawking unitarity, spin-connection fusion, Faraday–Yang–Mills monopole
   reduction, canonical lightcone Lagrangian $\det_Z(H(\mathbf{k})(U(\mathbf{u})+V(\mathbf{v}))) = \|\mathbf{k}\|^2(\mathbf{u}\cdot\mathbf{v})$,
   and trace-associativity $\mathrm{Tr}([X, Y, Z]) = 0$.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved 13-Pillar Split-Octonion Theorems (`[kernel_verified]`):**
  - `pillar_1_3_hestenes_majorana_triad` and `pillar_4_cayley_dickson_norm`.
  - `pillar_5_7_confinement_and_jacobi_anomaly` and
    `pillar_8_9_rotor_and_einstein_fisher_dispersion`.
  - `pillar_10_tomita_takesaki_hawking_unitarity`,
    `pillar_11_12_spin_fusion_and_faraday_monopole`,
    `pillar_13_canonical_lagrangian_and_albert_trace`, and
    `grandUnifiedTower_zorn_noncommutative_and_nonassociative`.

* **BUCKET 2 — Eliminated Duplicate Carriers & Certificate Wrappers (Zero Remaining):**
  - Eliminates the raw transcript's duplicate `SplitOctonion`, `ColorVec3`, `Quat4`, and
    `Mat3` structures by building directly on `ZornCell R`.

* **BUCKET 3 — Infinite-Dimensional Continuum Gauge & Gravity Limits (`[bucket_3_open_debt]`):**
  - Continuum functional integration and infinite-dimensional operator-algebraic closures
    remain outside this exact finite-dimensional `ZornCell R` scope.
-/

namespace InfoGeometry.Superalgebra.GrandUnifiedArchive

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

variable {R : Type*} [CommRing R]

/-- Zero element of `ZornCell R`. -/
def zeroZ : ZornCell R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Multiplicative identity $\mathbf{1} = \mathrm{diag}(1, 1)$ of `ZornCell R`. -/
def oneZ : ZornCell R :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

/-- Para-symplectic chiral parity generator $K_0 = \mathrm{diag}(1, -1)$ of `ZornCell R`. -/
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

/-- Sheet-exchange involution $X^\dagger$ on `ZornCell R`. -/
def daggerZ (X : ZornCell R) : ZornCell R :=
  ⟨X.r, X.s, X.y1, X.y2, X.y3, X.x1, X.x2, X.x3⟩

/-- Ordinary trace $\mathrm{Tr}(X) = r + s$ on `ZornCell R`. -/
def traceZ (X : ZornCell R) : R :=
  X.r + X.s

/-- Graded chiral supertrace $\mathrm{STr}(X) = r - s$ on `ZornCell R`. -/
def superTraceZ (X : ZornCell R) : R :=
  X.r - X.s

/-- Symmetric Jordan anticommutator $\{X, Y\} = X Y + Y X$ on `ZornCell R`. -/
def anticommutatorZ (X Y : ZornCell R) : ZornCell R :=
  addZ (mulZ X Y) (mulZ Y X)

/-- Skew-symmetric commutator $[X, Y] = X Y - Y X$ on `ZornCell R`. -/
def commutatorZ (X Y : ZornCell R) : ZornCell R :=
  subZ (mulZ X Y) (mulZ Y X)

/-- Associator $[X, Y, Z] = (X Y) Z - X (Y Z)$ on `ZornCell R`. -/
def associatorZ (X Y Z : ZornCell R) : ZornCell R :=
  subZ (mulZ (mulZ X Y) Z) (mulZ X (mulZ Y Z))

/-- Symmetrized triple product $(X Y) Z + X (Y Z)$ on `ZornCell R`. -/
def symmTripleZ (X Y Z : ZornCell R) : ZornCell R :=
  addZ (mulZ (mulZ X Y) Z) (mulZ X (mulZ Y Z))

/-- Jacobiator $[[X, Y], Z] + [[Y, Z], X] + [[Z, X], Y]$ on `ZornCell R`. -/
def jacobiatorZ (X Y Z : ZornCell R) : ZornCell R :=
  addZ (addZ (commutatorZ (commutatorZ X Y) Z)
             (commutatorZ (commutatorZ Y Z) X))
       (commutatorZ (commutatorZ Z X) Y)

/-- Forward isotropic chiral sheet $U(\mathbf{u})$ in `ZornCell R`. -/
def sheetU (u₁ u₂ u₃ : R) : ZornCell R :=
  ⟨0, 0, u₁, u₂, u₃, 0, 0, 0⟩

/-- Backward isotropic chiral sheet $V(\mathbf{v})$ in `ZornCell R`. -/
def sheetV (v₁ v₂ v₃ : R) : ZornCell R :=
  ⟨0, 0, 0, 0, 0, v₁, v₂, v₃⟩

/-- Compact spin generator $I(\mathbf{x}) = U(\mathbf{x}) - V(\mathbf{x})$. -/
def spinGenI (x₁ x₂ x₃ : R) : ZornCell R :=
  subZ (sheetU x₁ x₂ x₃) (sheetV x₁ x₂ x₃)

/-- Hyperbolic boost generator $H(\mathbf{x}) = U(\mathbf{x}) + V(\mathbf{x})$. -/
def boostGenH (x₁ x₂ x₃ : R) : ZornCell R :=
  addZ (sheetU x₁ x₂ x₃) (sheetV x₁ x₂ x₃)

/-- Forward super-Grassmannian twistor projector $P_+(\mathbf{u}) = e_1 + U(\mathbf{u})$. -/
def twistorProjPlus (u₁ u₂ u₃ : R) : ZornCell R :=
  ⟨1, 0, u₁, u₂, u₃, 0, 0, 0⟩

/-- Maurer–Cartan 1-form $\omega_L(\mathbf{u}, \mathbf{d}) = U(\mathbf{d}) - V(\mathbf{u}\times\mathbf{d})$. -/
def maurerCartanForm (u₁ u₂ u₃ d₁ d₂ d₃ : R) : ZornCell R :=
  subZ (sheetU d₁ d₂ d₃)
       (sheetV (u₂ * d₃ - u₃ * d₂) (u₃ * d₁ - u₁ * d₃) (u₁ * d₂ - u₂ * d₁))

/-- Exponential twistor rotor $\mathbf{1} + \omega_L(\mathbf{u}, \mathbf{d})$. -/
def expRotor (u₁ u₂ u₃ d₁ d₂ d₃ : R) : ZornCell R :=
  addZ oneZ (maurerCartanForm u₁ u₂ u₃ d₁ d₂ d₃)

/-- Hyperbolic modular operator $\Delta(c, s) = \mathrm{diag}(c+s, c-s)$. -/
def modularDelta (c s : R) : ZornCell R :=
  ⟨c + s, c - s, 0, 0, 0, 0, 0, 0⟩

/-- Two-sided modular automorphism $\sigma_{c,s}(X) = \Delta(c, s)\,X\,\Delta(c, -s)$. -/
def modularAutomorphism (c s : R) (X : ZornCell R) : ZornCell R :=
  mulZ (mulZ (modularDelta c s) X) (modularDelta c (-s))

/-- Cayley–Dickson $(4,4)$ embedding into `ZornCell R` from two 4-tuples $(p_0, \mathbf{p})$ and $(q_0, \mathbf{q})$. -/
def fromCayleyDickson (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : R) : ZornCell R :=
  ⟨p₀ + q₀, p₀ - q₀,
   p₁ + q₁, p₂ + q₂, p₃ + q₃,
   -p₁ + q₁, -p₂ + q₂, -p₃ + q₃⟩

/-- Oriented scalar triple product $\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b}) = \mathbf{u}\cdot(\mathbf{a}\times\mathbf{b})$. -/
def det3R (u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ : R) : R :=
  u₁ * (a₂ * b₃ - a₃ * b₂) + u₂ * (a₃ * b₁ - a₁ * b₃) + u₃ * (a₁ * b₂ - a₂ * b₁)

/-- Faraday–Yang–Mills 2-form curvature $\mathcal{F}_{\mathrm{YM}}(\mathbf{u}, \mathbf{a}, \mathbf{b})$. -/
def faradayYangMills (u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ : R) : ZornCell R :=
  addZ (smulZ (-2) (sheetV (a₂ * b₃ - a₃ * b₂) (a₃ * b₁ - a₁ * b₃) (a₁ * b₂ - a₂ * b₁)))
       (commutatorZ (maurerCartanForm u₁ u₂ u₃ a₁ a₂ a₃)
                    (maurerCartanForm u₁ u₂ u₃ b₁ b₂ b₃))

/-- **Pillars $\mathcal{A}_1$–$\mathcal{A}_3$ (`pillar_1_3_hestenes_majorana_triad`):**
Isotropic nilpotency $U(\mathbf{u})^2 = 0$, Hestenes decomposition
$2\,U(\mathbf{u})V(\mathbf{v}) = (\mathbf{u}\cdot\mathbf{v})\mathbf{1} + (\mathbf{u}\cdot\mathbf{v})K_0$,
and para-symplectic spin–boost transmutation $K_0\,I(\mathbf{x}) = H(\mathbf{x})$. -/
theorem pillar_1_3_hestenes_majorana_triad (u₁ u₂ u₃ v₁ v₂ v₃ x₁ x₂ x₃ : R) :
    mulZ (sheetU u₁ u₂ u₃) (sheetU u₁ u₂ u₃) = zeroZ ∧
    detZ (sheetU u₁ u₂ u₃) = 0 ∧
    smulZ 2 (mulZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃)) =
      addZ (smulZ (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) oneZ)
           (smulZ (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) paraSymplecticK0) ∧
    mulZ paraSymplecticK0 (spinGenI x₁ x₂ x₃) = boostGenH x₁ x₂ x₃ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp [mulZ, sheetU, zeroZ]; ring)
  · dsimp [detZ, sheetU]; ring
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [smulZ, mulZ, sheetU, sheetV, addZ, oneZ, paraSymplecticK0]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [mulZ, paraSymplecticK0, spinGenI, boostGenH, subZ, addZ, sheetU, sheetV]; ring)

/-- **Pillar $\mathcal{A}_4$ (`pillar_4_cayley_dickson_norm`):**
Cayley–Dickson $(4,4)$ Krein interval diagonalization:
$\det_Z(\mathrm{CD}(p, q)) = (p_0^2 + p_1^2 + p_2^2 + p_3^2) - (q_0^2 + q_1^2 + q_2^2 + q_3^2)$. -/
theorem pillar_4_cayley_dickson_norm (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : R) :
    detZ (fromCayleyDickson p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃) =
      (p₀ ^ 2 + p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2) - (q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 + q₃ ^ 2) := by
  dsimp [detZ, fromCayleyDickson]
  ring

/-- **Pillars $\mathcal{A}_5$ & $\mathcal{A}_7$ (`pillar_5_7_confinement_and_jacobi_anomaly`):**
Baryonic associator, symmetrized singlet, and Akivis–Malcev Jacobiator anomaly $J = 6\,\mathrm{Assoc}$. -/
theorem pillar_5_7_confinement_and_jacobi_anomaly
    (u₁ u₂ u₃ w₁ w₂ w₃ v₁ v₂ v₃ : R) :
    associatorZ (sheetU u₁ u₂ u₃) (sheetU w₁ w₂ w₃) (sheetU v₁ v₂ v₃) =
      smulZ (-det3R u₁ u₂ u₃ w₁ w₂ w₃ v₁ v₂ v₃) paraSymplecticK0 ∧
    symmTripleZ (sheetU u₁ u₂ u₃) (sheetU w₁ w₂ w₃) (sheetU v₁ v₂ v₃) =
      smulZ (det3R u₁ u₂ u₃ w₁ w₂ w₃ v₁ v₂ v₃) oneZ ∧
    jacobiatorZ (sheetU u₁ u₂ u₃) (sheetU w₁ w₂ w₃) (sheetU v₁ v₂ v₃) =
      smulZ (-6 * det3R u₁ u₂ u₃ w₁ w₂ w₃ v₁ v₂ v₃) paraSymplecticK0 := by
  refine ⟨?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [associatorZ, subZ, mulZ, sheetU, smulZ, paraSymplecticK0, det3R]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [symmTripleZ, addZ, mulZ, sheetU, smulZ, oneZ, det3R]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [jacobiatorZ, commutatorZ, addZ, subZ, mulZ, sheetU, smulZ, paraSymplecticK0, det3R]; ring)

/-- **Pillars $\mathcal{A}_8$ & $\mathcal{A}_9$ (`pillar_8_9_rotor_and_einstein_fisher_dispersion`):**
Maurer–Cartan nilpotency $\omega_L^2 = 0$, twistor rotor transport, and Einstein–Fisher–Berry
dispersion identity. -/
theorem pillar_8_9_rotor_and_einstein_fisher_dispersion (u₁ u₂ u₃ d₁ d₂ d₃ : R) :
    mulZ (maurerCartanForm u₁ u₂ u₃ d₁ d₂ d₃) (maurerCartanForm u₁ u₂ u₃ d₁ d₂ d₃) = zeroZ ∧
    mulZ (twistorProjPlus u₁ u₂ u₃) (expRotor u₁ u₂ u₃ d₁ d₂ d₃) =
      addZ (twistorProjPlus (u₁ + d₁) (u₂ + d₂) (u₃ + d₃))
           (sheetV (u₂ * d₃ - u₃ * d₂) (u₃ * d₁ - u₁ * d₃) (u₁ * d₂ - u₂ * d₁)) ∧
    let Q := mulZ (maurerCartanForm u₁ u₂ u₃ d₁ d₂ d₃)
                  (daggerZ (maurerCartanForm u₁ u₂ u₃ d₁ d₂ d₃))
    let f1 := (u₃ * d₁ - u₁ * d₃) * d₃ - (u₁ * d₂ - u₂ * d₁) * d₂
    let f2 := (u₁ * d₂ - u₂ * d₁) * d₁ - (u₂ * d₃ - u₃ * d₂) * d₃
    let f3 := (u₂ * d₃ - u₃ * d₂) * d₂ - (u₃ * d₁ - u₁ * d₃) * d₁
    traceZ Q ^ 2 - superTraceZ Q ^ 2 = 4 * (f1 ^ 2 + f2 ^ 2 + f3 ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [maurerCartanForm, subZ, mulZ, sheetU, sheetV, zeroZ]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [twistorProjPlus, expRotor, maurerCartanForm, addZ, subZ, mulZ, oneZ, sheetU, sheetV]; ring)
  · dsimp [maurerCartanForm, daggerZ, subZ, mulZ, sheetU, sheetV, traceZ, superTraceZ]
    ring

/-- **Pillar $\mathcal{A}_{10}$ (`pillar_10_tomita_takesaki_hawking_unitarity`):**
Hawking horizon unitarity under the Tomita–Takesaki modular flow when $c^2 - s^2 = 1$. -/
theorem pillar_10_tomita_takesaki_hawking_unitarity (c s u₁ u₂ u₃ v₁ v₂ v₃ : R)
    (h_hyp : c ^ 2 - s ^ 2 = 1) :
    anticommutatorZ (modularAutomorphism c s (sheetU u₁ u₂ u₃))
                    (modularAutomorphism c s (sheetV v₁ v₂ v₃)) =
      smulZ (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) oneZ := by
  have h_prod : (c + s) ^ 2 * (c - s) ^ 2 = 1 := by
    calc (c + s) ^ 2 * (c - s) ^ 2 = (c ^ 2 - s ^ 2) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [h_hyp]
      _ = 1 := by ring
  refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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

/-- **Pillars $\mathcal{A}_{11}$ & $\mathcal{A}_{12}$ (`pillar_11_12_spin_fusion_and_faraday_monopole`):**
Spin-to-spin-connection fusion and Faraday–Yang–Mills monopole reduction. -/
theorem pillar_11_12_spin_fusion_and_faraday_monopole
    (u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ : R) :
    commutatorZ (sheetU u₁ u₂ u₃) (boostGenH a₁ a₂ a₃) =
      addZ (smulZ (u₁ * a₁ + u₂ * a₂ + u₃ * a₃) paraSymplecticK0)
           (smulZ 2 (sheetV (u₂ * a₃ - u₃ * a₂) (u₃ * a₁ - u₁ * a₃) (u₁ * a₂ - u₂ * a₁))) ∧
    faradayYangMills u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ =
      smulZ (-2 * det3R u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃)
            (addZ paraSymplecticK0 (sheetU u₁ u₂ u₃)) := by
  refine ⟨?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [commutatorZ, subZ, mulZ, sheetU, sheetV, boostGenH, addZ, smulZ, paraSymplecticK0]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [faradayYangMills, maurerCartanForm, commutatorZ, addZ, subZ, mulZ, smulZ,
              sheetU, sheetV, paraSymplecticK0, det3R]; ring)

/-- **Pillar $\mathcal{A}_{13}$ (`pillar_13_canonical_lagrangian_and_albert_trace`):**
Canonical lightcone Lagrangian $\det_Z(H(\mathbf{k})(U(\mathbf{u})+V(\mathbf{v}))) = \|\mathbf{k}\|^2(\mathbf{u}\cdot\mathbf{v})$
and trace-associativity $\mathrm{Tr}([X, Y, Z]) = 0$. -/
theorem pillar_13_canonical_lagrangian_and_albert_trace
    (k₁ k₂ k₃ u₁ u₂ u₃ v₁ v₂ v₃ : R) (X Y Z : ZornCell R) :
    detZ (mulZ (boostGenH k₁ k₂ k₃) ⟨0, 0, u₁, u₂, u₃, v₁, v₂, v₃⟩) =
      (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) ∧
    traceZ (associatorZ X Y Z) = 0 := by
  refine ⟨?_, ?_⟩
  · dsimp [detZ, mulZ, boostGenH, addZ, sheetU, sheetV]
    ring
  · dsimp [traceZ, associatorZ, subZ, mulZ]
    ring

/-- Explicit non-commutativity and non-associativity witness on `ZornCell ℤ` for the Grand Unified Tower. -/
theorem grandUnifiedTower_zorn_noncommutative_and_nonassociative :
    mulZ (sheetU (1 : ℤ) 0 0) (sheetV 1 0 0) ≠
      mulZ (sheetV 1 0 0) (sheetU 1 0 0) ∧
    mulZ (mulZ (sheetU (1 : ℤ) 0 0) (sheetU 0 1 0)) (sheetU 0 0 1) ≠
      mulZ (sheetU 1 0 0) (mulZ (sheetU 0 1 0) (sheetU 0 0 1)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hr := congrArg ZornCell.r h
    revert hr
    decide
  · intro h
    have hs := congrArg ZornCell.s h
    revert hs
    decide

end InfoGeometry.Superalgebra.GrandUnifiedArchive
