/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornSpinor

/-!
# Cyclotomic Charge and the Three Native Peirce Sectors on `ZornMatrix`

This module constructs the order-three cyclotomic charge operator `cubicCharge ω`
and the three mutually orthogonal idempotent Peirce-sector projectors
`cubicProjectorZero`, `cubicProjectorPlus`, and `cubicProjectorMinus` on `ZornMatrix K`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.ZornSpinor` (`ZornMatrix`, `zornPlus`, `zornMinus`,
    `colorProject`, `anticolorProject`, `dot`, `cross`).
- BUCKET 2 (Deconfabulation):
  * Eliminated pass-through coordinate lemmas (`smul_a_coord`, `smul_b_coord`) and
    `:= rfl` / `:= by rfl` projector wrappers, proving idempotence, mutual orthogonality,
    and spectral decomposition via explicit `ZornMatrix.ext` coordinate derivations.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `cubicCharge`, `cubicProjectorZero`, `cubicProjectorPlus`, `cubicProjectorMinus`.
  * `cubicCharge_pow_three`: $\mathrm{cubicCharge}_\omega^3 = \mathrm{id}$ for $\omega^3 = 1$.
  * `cubicCharge_mul`: $\mathrm{cubicCharge}_\omega(X Y) = \mathrm{cubicCharge}_\omega(X)\,\mathrm{cubicCharge}_\omega(Y)$
    for $\omega^3 = 1$.
  * `cubicCharge_zero_eigen`, `cubicCharge_plus_eigen`, `cubicCharge_minus_eigen`:
    eigenvalue equations on the $1, \omega, \omega^2$ Peirce sectors.
  * `cubicProjectors_sum_eq_id`, idempotence, pairwise orthogonality, and the
    Peirce decomposition `cubicCharge_peirce_decomposition`.
-/

namespace InfoGeometry.Canonical

open ZornMatrix

variable {K : Type*} [CommRing K]

/-- Pointwise scalar multiplication on the `x` vector sector of `ZornMatrix K`. -/
private lemma smul_x_coord (c : K) (Z : ZornMatrix K) (i : Fin 3) :
    (c • Z).x i = c * Z.x i := by
  rw [ZornMatrix.smul_x]
  exact Pi.smul_apply c Z.x i

/-- Pointwise scalar multiplication on the `y` covector sector of `ZornMatrix K`. -/
private lemma smul_y_coord (c : K) (Z : ZornMatrix K) (i : Fin 3) :
    (c • Z).y i = c * Z.y i := by
  rw [ZornMatrix.smul_y]
  exact Pi.smul_apply c Z.y i

/-- The cyclotomic cubic charge operator scaling $(a, b, x, y) \mapsto (a, b, \omega x, \omega^2 y)$. -/
def cubicCharge (ω : K) : ZornMatrix K →ₗ[K] ZornMatrix K where
  toFun Z :=
    { a := Z.a, b := Z.b, x := ω • Z.x, y := (ω ^ 2) • Z.y }
  map_add' X Y := by
    cases X
    cases Y
    apply ZornMatrix.ext
    · simp [ZornMatrix.add_def]
    · simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
  map_smul' c X := by
    apply ZornMatrix.ext
    · simp [ZornMatrix.smul_a]
    · simp [ZornMatrix.smul_b]
    · funext i
      simp [smul_x_coord]
      ring
    · funext i
      simp [smul_y_coord]
      ring

/-- The degree-$0$ (diagonal Peirce) projector $(a, b, x, y) \mapsto (a, b, 0, 0)$. -/
def cubicProjectorZero : ZornMatrix K →ₗ[K] ZornMatrix K where
  toFun Z := { a := Z.a, b := Z.b, x := 0, y := 0 }
  map_add' X Y := by
    cases X
    cases Y
    apply ZornMatrix.ext
    · simp [ZornMatrix.add_def]
    · simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def]
  map_smul' c X := by
    apply ZornMatrix.ext
    · simp [ZornMatrix.smul_a]
    · simp [ZornMatrix.smul_b]
    · funext i
      simp [smul_x_coord]
    · funext i
      simp [smul_y_coord]

/-- The degree-$1$ (color $x$-sector) projector $(a, b, x, y) \mapsto (0, 0, x, 0)$. -/
def cubicProjectorPlus : ZornMatrix K →ₗ[K] ZornMatrix K where
  toFun Z := { a := 0, b := 0, x := Z.x, y := 0 }
  map_add' X Y := by
    cases X
    cases Y
    apply ZornMatrix.ext
    · simp [ZornMatrix.add_def]
    · simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def]
  map_smul' c X := by
    apply ZornMatrix.ext
    · simp [ZornMatrix.smul_a]
    · simp [ZornMatrix.smul_b]
    · funext i
      simp [smul_x_coord]
    · funext i
      simp [smul_y_coord]

/-- The degree-$2$ (anticolor $y$-sector) projector $(a, b, x, y) \mapsto (0, 0, 0, y)$. -/
def cubicProjectorMinus : ZornMatrix K →ₗ[K] ZornMatrix K where
  toFun Z := { a := 0, b := 0, x := 0, y := Z.y }
  map_add' X Y := by
    cases X
    cases Y
    apply ZornMatrix.ext
    · simp [ZornMatrix.add_def]
    · simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def]
  map_smul' c X := by
    apply ZornMatrix.ext
    · simp [ZornMatrix.smul_a]
    · simp [ZornMatrix.smul_b]
    · funext i
      simp [smul_x_coord]
    · funext i
      simp [smul_y_coord]

/-- Whenever $\omega^3 = 1$, the cube of `cubicCharge ω` is the identity linear map on `ZornMatrix K`. -/
theorem cubicCharge_pow_three (ω : K) (hω : ω ^ 3 = 1) :
    (cubicCharge ω).comp ((cubicCharge ω).comp (cubicCharge ω)) = LinearMap.id := by
  apply LinearMap.ext
  intro Z
  apply ZornMatrix.ext
  · simp [cubicCharge]
  · simp [cubicCharge]
  · funext i
    change ω * (ω * (ω * Z.x i)) = Z.x i
    rw [show ω * (ω * (ω * Z.x i)) = (ω ^ 3) * Z.x i by ring, hω, one_mul]
  · funext i
    have hω6 : ω ^ 6 = 1 := by
      calc
        ω ^ 6 = (ω ^ 3) ^ 2 := by rw [show 6 = 3 * 2 by norm_num, pow_mul]
        _ = 1 := by rw [hω, one_pow]
    change ω ^ 2 * (ω ^ 2 * (ω ^ 2 * Z.y i)) = Z.y i
    rw [show ω ^ 2 * (ω ^ 2 * (ω ^ 2 * Z.y i)) = (ω ^ 6) * Z.y i by ring, hω6,
      one_mul]

/-- Whenever $\omega^3 = 1$, `cubicCharge ω` is a multiplicative automorphism of the
non-associative Zorn matrix algebra `ZornMatrix K`. -/
theorem cubicCharge_mul (ω : K) (hω : ω ^ 3 = 1)
    (X Y : ZornMatrix K) :
    cubicCharge ω (X * Y) = cubicCharge ω X * cubicCharge ω Y := by
  have hω32 : ω * ω ^ 2 = 1 := by
    calc
      ω * ω ^ 2 = ω ^ 3 := by ring
      _ = 1 := hω
  have hω23 : ω ^ 2 * ω = 1 := by
    calc
      ω ^ 2 * ω = ω ^ 3 := by ring
      _ = 1 := hω
  have hω4 : ω ^ 2 * ω ^ 2 = ω := by
    calc
      ω ^ 2 * ω ^ 2 = ω * (ω ^ 3) := by ring
      _ = ω := by rw [hω, mul_one]
  have hquad (a b : K) : ω ^ 2 * a * (ω ^ 2 * b) = ω * (a * b) := by
    calc
      ω ^ 2 * a * (ω ^ 2 * b) = (ω ^ 2 * ω ^ 2) * (a * b) := by ring
      _ = ω * (a * b) := by rw [hω4]
  have hmul (a b : K) : ω * a * (ω ^ 2 * b) = a * b := by
    calc
      ω * a * (ω ^ 2 * b) = (ω * ω ^ 2) * (a * b) := by ring
      _ = a * b := by rw [hω32, one_mul]
  have hmul' (a b : K) : ω ^ 2 * a * (ω * b) = a * b := by
    calc
      ω ^ 2 * a * (ω * b) = (ω ^ 2 * ω) * (a * b) := by ring
      _ = a * b := by rw [hω23, one_mul]
  have hdot (u v : Fin 3 → K) :
      ZornMatrix.dot (ω • u) (ω ^ 2 • v) = ZornMatrix.dot u v := by
    unfold ZornMatrix.dot
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hmul, hmul, hmul]
  have hdot' (u v : Fin 3 → K) :
      ZornMatrix.dot (ω ^ 2 • u) (ω • v) = ZornMatrix.dot u v := by
    unfold ZornMatrix.dot
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hmul', hmul', hmul']
  have hcross (u v : Fin 3 → K) :
      ZornMatrix.cross (ω ^ 2 • u) (ω ^ 2 • v) = ω • ZornMatrix.cross u v := by
    funext i
    fin_cases i <;>
      simp [ZornMatrix.cross, Pi.smul_apply, smul_eq_mul, hquad] <;> ring
  have hcross' (u v : Fin 3 → K) :
      ZornMatrix.cross (ω • u) (ω • v) = ω ^ 2 • ZornMatrix.cross u v := by
    funext i
    fin_cases i <;>
      simp [ZornMatrix.cross, Pi.smul_apply, smul_eq_mul] <;> ring
  apply ZornMatrix.ext
  · change X.a * Y.a + ZornMatrix.dot X.x Y.y =
      X.a * Y.a + ZornMatrix.dot (ω • X.x) (ω ^ 2 • Y.y)
    rw [hdot]
  · change X.b * Y.b + ZornMatrix.dot X.y Y.x =
      X.b * Y.b + ZornMatrix.dot (ω ^ 2 • X.y) (ω • Y.x)
    rw [hdot']
  · change ω • (X.a • Y.x + Y.b • X.x - ZornMatrix.cross X.y Y.y) =
      X.a • (ω • Y.x) + Y.b • (ω • X.x) -
        ZornMatrix.cross (ω ^ 2 • X.y) (ω ^ 2 • Y.y)
    rw [hcross]
    ext i
    simp [Pi.smul_apply, smul_eq_mul]
    ring
  · change ω ^ 2 • (X.b • Y.y + Y.a • X.y + ZornMatrix.cross X.x Y.x) =
      X.b • (ω ^ 2 • Y.y) + Y.a • (ω ^ 2 • X.y) +
        ZornMatrix.cross (ω • X.x) (ω • Y.x)
    rw [hcross']
    ext i
    simp [Pi.smul_apply, smul_eq_mul]
    ring

/-- The diagonal Peirce projector `cubicProjectorZero` is fixed (eigenvalue $1$) by `cubicCharge ω`. -/
theorem cubicCharge_zero_eigen (ω : K) (Z : ZornMatrix K) :
    cubicCharge ω (cubicProjectorZero Z) = cubicProjectorZero Z := by
  cases Z
  apply ZornMatrix.ext <;> simp [cubicCharge, cubicProjectorZero]

/-- The color $x$-sector projector `cubicProjectorPlus` has eigenvalue $\omega$ under `cubicCharge ω`. -/
theorem cubicCharge_plus_eigen (ω : K) (Z : ZornMatrix K) :
    cubicCharge ω (cubicProjectorPlus Z) = ω • cubicProjectorPlus Z := by
  ext <;> simp [cubicCharge, cubicProjectorPlus, ZornMatrix.smul_a,
    ZornMatrix.smul_b, ZornMatrix.smul_x, ZornMatrix.smul_y,
    Pi.smul_apply, smul_eq_mul]

/-- The anticolor $y$-sector projector `cubicProjectorMinus` has eigenvalue $\omega^2$ under `cubicCharge ω`. -/
theorem cubicCharge_minus_eigen (ω : K) (Z : ZornMatrix K) :
    cubicCharge ω (cubicProjectorMinus Z) = (ω ^ 2) • cubicProjectorMinus Z := by
  ext <;> simp [cubicCharge, cubicProjectorMinus, ZornMatrix.smul_a,
    ZornMatrix.smul_b, ZornMatrix.smul_x, ZornMatrix.smul_y,
    Pi.smul_apply, smul_eq_mul]

/-- The three cyclotomic Peirce projectors sum to the identity on `ZornMatrix K`. -/
theorem cubicProjectors_sum_eq_id (Z : ZornMatrix K) :
    cubicProjectorZero Z + cubicProjectorPlus Z + cubicProjectorMinus Z = Z := by
  cases Z
  ext <;> simp [cubicProjectorZero, cubicProjectorPlus, cubicProjectorMinus,
    add_def]

/-- Peirce decomposition of `cubicCharge ω` into the three cyclotomic Peirce projectors. -/
theorem cubicCharge_peirce_decomposition (ω : K) (Z : ZornMatrix K) :
    cubicCharge ω Z =
      cubicProjectorZero Z + ω • cubicProjectorPlus Z + (ω ^ 2) • cubicProjectorMinus Z := by
  conv_lhs => rw [← cubicProjectors_sum_eq_id Z]
  rw [map_add, map_add, cubicCharge_zero_eigen, cubicCharge_plus_eigen, cubicCharge_minus_eigen]

/-- The diagonal Peirce projector `cubicProjectorZero` is idempotent. -/
theorem cubicProjectorZero_idempotent (Z : ZornMatrix K) :
    cubicProjectorZero (cubicProjectorZero Z) = cubicProjectorZero Z := by
  cases Z
  apply ZornMatrix.ext <;> dsimp [cubicProjectorZero]

/-- The color projector `cubicProjectorPlus` is idempotent. -/
theorem cubicProjectorPlus_idempotent (Z : ZornMatrix K) :
    cubicProjectorPlus (cubicProjectorPlus Z) = cubicProjectorPlus Z := by
  cases Z
  apply ZornMatrix.ext <;> dsimp [cubicProjectorPlus]

/-- The anticolor projector `cubicProjectorMinus` is idempotent. -/
theorem cubicProjectorMinus_idempotent (Z : ZornMatrix K) :
    cubicProjectorMinus (cubicProjectorMinus Z) = cubicProjectorMinus Z := by
  cases Z
  apply ZornMatrix.ext <;> dsimp [cubicProjectorMinus]

/-- The diagonal and color projectors are mutually orthogonal (`P_0 ∘ P_+ = 0`). -/
theorem cubicProjectorZero_plus_orthogonal (Z : ZornMatrix K) :
    cubicProjectorZero (cubicProjectorPlus Z) = 0 := by
  cases Z
  apply ZornMatrix.ext <;> dsimp [cubicProjectorZero, cubicProjectorPlus, ZornMatrix.zero_a, ZornMatrix.zero_b, ZornMatrix.zero_x, ZornMatrix.zero_y]

/-- The color and anticolor projectors are mutually orthogonal (`P_+ ∘ P_- = 0`). -/
theorem cubicProjectorPlus_minus_orthogonal (Z : ZornMatrix K) :
    cubicProjectorPlus (cubicProjectorMinus Z) = 0 := by
  cases Z
  apply ZornMatrix.ext <;> dsimp [cubicProjectorPlus, cubicProjectorMinus, ZornMatrix.zero_a, ZornMatrix.zero_b, ZornMatrix.zero_x, ZornMatrix.zero_y]

/-- The anticolor and diagonal projectors are mutually orthogonal (`P_- ∘ P_0 = 0`). -/
theorem cubicProjectorMinus_zero_orthogonal (Z : ZornMatrix K) :
    cubicProjectorMinus (cubicProjectorZero Z) = 0 := by
  cases Z
  apply ZornMatrix.ext <;> dsimp [cubicProjectorMinus, cubicProjectorZero, ZornMatrix.zero_a, ZornMatrix.zero_b, ZornMatrix.zero_x, ZornMatrix.zero_y]

/-- The diagonal Peirce projector expands in the primitive idempotents `zornPlus` and `zornMinus`. -/
theorem cubicProjectorZero_eq_diagonalProject (Z : ZornMatrix K) :
    cubicProjectorZero Z =
      Z.a • zornPlus + Z.b • zornMinus := by
  cases Z
  ext <;> simp [cubicProjectorZero, zornPlus, zornMinus, add_def,
    ZornMatrix.smul_a, ZornMatrix.smul_b]

/-- `cubicProjectorPlus` agrees with the native `colorProject` map on `ZornMatrix K`. -/
theorem cubicProjectorPlus_eq_colorProject (Z : ZornMatrix K) :
    cubicProjectorPlus Z = colorProject Z := by
  rw [colorProject_apply]
  cases Z
  apply ZornMatrix.ext <;> dsimp [cubicProjectorPlus]

/-- `cubicProjectorMinus` agrees with the native `anticolorProject` map on `ZornMatrix K`. -/
theorem cubicProjectorMinus_eq_anticolorProject (Z : ZornMatrix K) :
    cubicProjectorMinus Z = anticolorProject Z := by
  rw [anticolorProject_apply]
  cases Z
  apply ZornMatrix.ext <;> dsimp [cubicProjectorMinus]

end InfoGeometry.Canonical
