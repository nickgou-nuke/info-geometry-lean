/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitOctonionClifford33Soldering
import Mathlib.Tactic

/-!
# Zorn left-multiplication anticommutator on the 8D matrix carrier

This owner promotes the left-alternative anticommutator identity from the
coordinate Zorn product to the genuine `8 × 8` real left-multiplication
matrices. It does not assert a `Cl(3,3) ≅ M₈(ℝ)` algebra isomorphism.
-/

noncomputable section

open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering

namespace InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR

abbrev Oct :=
  InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.ZornSplitOctonion ℝ

/-- Polarized left-alternative identity for the coordinate Zorn product:
`x(yz) + y(xz) = (xy)z + (yx)z`. -/
theorem zornMul_anticommutator (x y z : Oct) :
    zornAdd (zornMul x (zornMul y z)) (zornMul y (zornMul x z)) =
      zornAdd (zornMul (zornMul x y) z) (zornMul (zornMul y x) z) := by
  rcases x with ⟨a, u, v, b⟩
  rcases y with ⟨c, p, q, d⟩
  rcases z with ⟨e, r, s, f⟩
  apply ZornSplitOctonion.ext
  · simp [zornAdd, zornMul, vec3Dot, vec3Cross]
    ring
  · funext i
    fin_cases i <;>
      simp [zornAdd, zornMul, vec3Dot, vec3Cross] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornAdd, zornMul, vec3Dot, vec3Cross] <;> ring
  · simp [zornAdd, zornMul, vec3Dot, vec3Cross]
    ring

/-- The anticommutator law on the `ℝ⁸` left-action operators. -/
theorem zornLeftActFin8_anticommutator (x y : Oct) :
    zornLeftActFin8 x * zornLeftActFin8 y +
        zornLeftActFin8 y * zornLeftActFin8 x =
      zornLeftActFin8 (zornAdd (zornMul x y) (zornMul y x)) := by
  apply LinearMap.ext
  intro ψ
  ext i
  have h := zornMul_anticommutator x y (fin8ToZorn ψ)
  simpa [zornLeftActFin8, zornMul_add_left, zornToFin8_zornAdd,
    fin8ToZorn_right_inv, LinearMap.add_apply] using
    congrFun (congrArg zornToFin8 h) i

/-- The same anticommutator law on the genuine `8 × 8` matrices. -/
theorem zornLeftActMatrix_anticommutator (x y : Oct) :
    zornLeftActMatrix x * zornLeftActMatrix y +
        zornLeftActMatrix y * zornLeftActMatrix x =
      zornLeftActMatrix (zornAdd (zornMul x y) (zornMul y x)) := by
  unfold zornLeftActMatrix
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  rw [← zornLeftActFin8_anticommutator x y]
  simp

/-- Right unit law for the coordinate Zorn product. -/
theorem zornMul_one_right (x : Oct) : zornMul x zornOne = x := by
  rcases x with ⟨a, u, v, b⟩
  apply ZornSplitOctonion.ext
  · simp [zornOne, zornMul, vec3Dot, vec3Cross]
  · funext i
    fin_cases i <;> simp [zornOne, zornMul, vec3Dot, vec3Cross]
  · funext i
    fin_cases i <;> simp [zornOne, zornMul, vec3Dot, vec3Cross]
  · simp [zornOne, zornMul, vec3Dot, vec3Cross]

/-- The left-action operator on `ℝ⁸` is faithful. -/
theorem zornLeftActFin8_injective : Function.Injective zornLeftActFin8 := by
  intro x y hxy
  let e : Fin 8 → ℝ := zornToFin8 zornOne
  have he : fin8ToZorn e = zornOne := by
    dsimp [e]
    exact fin8ToZorn_right_inv zornOne
  have happly := congrArg (fun f => fin8ToZorn (f e)) hxy
  simpa [zornLeftActFin8, he, zornMul_one_right, fin8ToZorn_right_inv] using happly

/-- Left alternative law for the coordinate Zorn product. -/
theorem zornMul_left_alternative (x z : Oct) :
    zornMul x (zornMul x z) = zornMul (zornMul x x) z := by
  rcases x with ⟨a, u, v, b⟩
  rcases z with ⟨e, r, s, f⟩
  apply ZornSplitOctonion.ext
  · simp [zornMul, vec3Dot, vec3Cross]
    ring
  · funext i
    fin_cases i <;> simp [zornMul, vec3Dot, vec3Cross] <;> ring
  · funext i
    fin_cases i <;> simp [zornMul, vec3Dot, vec3Cross] <;> ring
  · simp [zornMul, vec3Dot, vec3Cross]
    ring

/-- The square of a left-action operator is the left action of the square. -/
theorem zornLeftActFin8_square (x : Oct) :
    zornLeftActFin8 x * zornLeftActFin8 x = zornLeftActFin8 (zornMul x x) := by
  apply LinearMap.ext
  intro ψ
  ext i
  have h := zornMul_left_alternative x (fin8ToZorn ψ)
  simpa [zornLeftActFin8, fin8ToZorn_right_inv] using
    congrFun (congrArg zornToFin8 h) i

/-- The matrix-level square law. -/
theorem zornLeftActMatrix_square (x : Oct) :
    zornLeftActMatrix x * zornLeftActMatrix x = zornLeftActMatrix (zornMul x x) := by
  unfold zornLeftActMatrix
  rw [← LinearMap.toMatrix_mul]
  rw [← zornLeftActFin8_square x]

/-- Clifford square law for the embedded split-signature vectors. -/
theorem zornLeftActMatrix_embedVec_sq (z : ParaKahlerVec ℝ) :
    zornLeftActMatrix (embedVec z) * zornLeftActMatrix (embedVec z) =
      (cl33QuadraticForm z) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [zornLeftActMatrix_square, zorn_vec_sq_eq_neg_norm_smul_one,
    zornNorm_embedVec]
  ext i j
  simp [zornLeftActMatrix, zornLeftActFin8_smul, zornLeftActFin8_zornOne,
    cl33QuadraticForm, Matrix.one_apply, Pi.single_apply]

end InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR
