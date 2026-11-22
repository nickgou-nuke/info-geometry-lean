/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.H3ZornKantorTripleSystemBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge
import InfoGeometry.Canonical.H3ZornTKKNative

/-!
# Native H3/Zorn Kantor capstone

This owner replaces the upstream Kantor capstone at the current theorem
surfaces.  It records only facts proved by the native Jordan/TKK owners; no
dimension or exceptional-Lie identification is inferred from the vanishing
Kantor operator alone.
-/

namespace InfoGeometry.Canonical.H3ZornJordanKantorCapstone

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.H3ZornTKKNative

abbrev H3 := H3Zorn ℝ

theorem kantor_boundary_packet (x y : H3) :
    kantorOperator x y = 0 ∧
    innerDerivation x y =
      (InfoGeometry.Algebra.h3ZornJordanInnerDerivation x y : Module.End ℝ H3) := by
  exact ⟨kantorOperator_zero x y, rfl⟩

theorem inner_derivation_packet (x y : H3) :
    H3ZornJordanDerivation (innerDerivation x y) ∧
    innerDerivation y x = -innerDerivation x y := by
  constructor
  · exact innerDerivation_is_jordan_derivation x y
  · apply LinearMap.ext
    intro z
    exact InfoGeometry.Canonical.H3ZornKantorTripleSystemBridge.innerDerivation_swap x y z

theorem triple_derivation_packet (x y u v w : H3) :
    innerDerivation x y (jordanTriple u v w) =
      jordanTriple (innerDerivation x y u) v w +
        jordanTriple u (innerDerivation x y v) w +
          jordanTriple u v (innerDerivation x y w) :=
  innerDerivation_triple x y u v w


theorem jordanInner_skew (x y : H3) : InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge.jordanInner y x =
      -InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge.jordanInner x y := by
  apply LinearMap.ext
  intro z
  simp only [InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge.jordanInner_apply, LinearMap.neg_apply]
  simp only [candidateJordanMul_eq_mul]
  abel

@[simp] theorem jordanTripleD_add_left (x₁ x₂ y : H3) :
    jordanTripleD (x₁ + x₂) y = jordanTripleD x₁ y + jordanTripleD x₂ y := by
  apply LinearMap.ext
  intro z
  simp [jordanTripleD_apply]

@[simp] theorem jordanTripleD_smul_left (r : ℝ) (x y : H3) :
    jordanTripleD (r • x) y = r • jordanTripleD x y := by
  apply LinearMap.ext
  intro z
  simp [jordanTripleD_apply]

@[simp] theorem jordanTripleD_add_middle (x y₁ y₂ : H3) :
    jordanTripleD x (y₁ + y₂) = jordanTripleD x y₁ + jordanTripleD x y₂ := by
  apply LinearMap.ext
  intro z
  simp [jordanTripleD_apply]

@[simp] theorem jordanTripleD_smul_middle (r : ℝ) (x y : H3) :
    jordanTripleD x (r • y) = r • jordanTripleD x y := by
  apply LinearMap.ext
  intro z
  simp [jordanTripleD_apply]

@[simp] theorem jordanTriple_zero_left (y z : H3) : jordanTriple 0 y z = 0 := by
  simpa using jordanTriple_smul_left (0 : ℝ) z y z

@[simp] theorem jordanTriple_zero_middle (x z : H3) : jordanTriple x 0 z = 0 := by
  simpa using jordanTriple_smul_middle (0 : ℝ) x z z

@[simp] theorem jordanTriple_zero_right (x y : H3) : jordanTriple x y 0 = 0 := by
  simpa using jordanTriple_smul_right (0 : ℝ) x y 0

end InfoGeometry.Canonical.H3ZornJordanKantorCapstone
