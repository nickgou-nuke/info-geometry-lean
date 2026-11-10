/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Riemannian.CartanMetric
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Riemannian.ConeAction

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

open InfoGeometry.Clifford.Hestenes
open CliffordAlgebra
open InfoGeometry.Riemannian

namespace InfoGeometry.Clifford.SplitOctonionsDualProduct

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Дефинираме Сплит-Октониона като канонично Cayley-Dickson удвояване над паравекторите -/
structure SplitOctonion (Q : QuadraticForm R M) (v0 : M) where
  fst : evenOdd Q 0
  snd : evenOdd Q 0

namespace SplitOctonion

variable {Q : QuadraticForm R M} {v0 : M}

instance : Inhabited (SplitOctonion Q v0) :=
  ⟨⟨0, 0⟩⟩

/-- Новият дуален продукт ⋆ дефиниран строго чрез Cayley-Dickson умножение -/
def star_prod (X Y : SplitOctonion Q v0) : SplitOctonion Q v0 :=
  ⟨X.fst * Y.fst + (hestenesAdjoint Q v0 Y.snd) * X.snd,
   Y.snd * X.fst + X.snd * (hestenesAdjoint Q v0 Y.fst)⟩

/-- Нормата на Cayley-Dickson Сплит-Октонион -/
noncomputable def hNorm [Invertible (2 : R)] (X : SplitOctonion Q v0) : R :=
  InfoGeometry.Riemannian.hTrace Q (X.fst * hestenesAdjoint Q v0 X.fst) -
  InfoGeometry.Riemannian.hTrace Q (X.snd * hestenesAdjoint Q v0 X.snd)

end SplitOctonion

section NonCommCayleyDickson

variable {B : Type*} [Ring B] [StarRing B]

/-- Cayley-Dickson split multiplication on pairs `(a, b) ∈ B × B` over any non-commutative `*-ring` `[Ring B] [StarRing B]`. -/
def ringCayleyDicksonMul (X Y : B × B) : B × B :=
  (X.1 * Y.1 + star Y.2 * X.2, Y.2 * X.1 + X.2 * star Y.1)

@[simp]
theorem ringCayleyDicksonMul_zero_left (Y : B × B) :
    ringCayleyDicksonMul (0, 0) Y = (0, 0) := by
  simp [ringCayleyDicksonMul]

@[simp]
theorem ringCayleyDicksonMul_one_left (Y : B × B) :
    ringCayleyDicksonMul (1, 0) Y = Y := by
  ext <;> simp [ringCayleyDicksonMul]

end NonCommCayleyDickson

end InfoGeometry.Clifford.SplitOctonionsDualProduct
