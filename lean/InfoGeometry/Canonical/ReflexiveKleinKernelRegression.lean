/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveKleinKernel
import InfoGeometry.Canonical.ReflexiveParabolicUnits

/-!
# Noncommuting rational specialization and false-identification regressions

Reuse the existing integer matrix pair through the native scalar map. The
parameter 2 has a distinct inverse, so the Klein relation is nontrivial.
The examples also distinguish an adjoint from a reflexive inverse, and
negating a grading from inverting that grading.
-/

namespace InfoGeometry.Canonical.ReflexiveKleinKernelRegression

open GrassmannianBundleCyclotomicOrientability ReflexiveNilpotentFlows KleinPresentedGroup

/-- Scalar extension of the existing integer nilpotent. -/
def rationalD : Matrix (Fin 2) (Fin 2) ℚ := matD.map (Int.castRingHom ℚ)

/-- Scalar extension of its existing reflexive partner. -/
def rationalB : Matrix (Fin 2) (Fin 2) ℚ := matB.map (Int.castRingHom ℚ)

theorem rational_pair :
    rationalD * rationalD = 0 ∧ rationalB * rationalB = 0 ∧
    rationalD * rationalB * rationalD = rationalD ∧
    rationalB * rationalD * rationalB = rationalB := by decide +kernel

/-- An actual representation, with nontrivial multiplicative parameter. -/
def rationalKleinRep : KleinGroup →* (Matrix (Fin 2) (Fin 2) ℚ)ˣ :=
  reflexiveKleinRep rational_pair.1 rational_pair.2.1
    rational_pair.2.2.1 rational_pair.2.2.2 (Units.mk0 (2 : ℚ) (by norm_num))

@[simp] theorem rationalKleinRep_genA :
    (rationalKleinRep (toKlein genA) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![0, 1; -1, 0] := by
  unfold rationalKleinRep
  rw [reflexiveKleinRep_genA]
  change weyl rationalD rationalB = _
  decide +kernel

@[simp] theorem rationalKleinRep_genB :
    (rationalKleinRep (toKlein genB) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![2, 0; 0, 1/2] := by
  unfold rationalKleinRep
  rw [reflexiveKleinRep_genB, diagonalUnit_val]
  decide +kernel

/-- The two generator images do not commute. -/
theorem rational_images_noncommute :
    rationalKleinRep (toKlein genA) * rationalKleinRep (toKlein genB) ≠
      rationalKleinRep (toKlein genB) * rationalKleinRep (toKlein genA) := by
  intro h
  have hv := congrArg (fun u : (Matrix (Fin 2) (Fin 2) ℚ)ˣ => (u : Matrix (Fin 2) (Fin 2) ℚ)) h
  simp only [Units.val_mul, rationalKleinRep_genA, rationalKleinRep_genB] at hv
  have hn : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![2, 0; 0, 1/2] ≠
      !![2, 0; 0, 1/2] * !![0, 1; -1, 0] := by decide +kernel
  exact hn hv

/-- Explicit noncommutativity witness for the rational matrix pair. -/
theorem rational_pair_noncommute :
    rationalD * rationalB ≠ rationalB * rationalD := by decide +kernel

/-- Involutive grading inversion is not grading sign reversal. -/
theorem grading_is_not_the_inverted_generator :
    let Γ := rationalD * rationalB - rationalB * rationalD
    Γ * Γ = 1 ∧
      (rationalD + rationalB) * Γ * (rationalD + rationalB) ≠ Γ := by decide +kernel

/-- A square-zero operator's transpose need not be its reflexive inverse. -/
theorem transpose_not_reflexive_inverse :
    let d := (2 : ℚ) • rationalD
    d * d = 0 ∧ d * d.transpose * d ≠ d := by decide +kernel

/-- The sign-reversed Jordan-operator identity in the proposed synthesis is false. -/
theorem reversed_jordan_bracket_false :
    let s := rationalD
    let t := rationalB
    let x := rationalD
    let j := fun a b : Matrix (Fin 2) (Fin 2) ℚ => a * b + b * a
    j s (j t x) - j t (j s x) ≠ (t * s - s * t) * x - x * (t * s - s * t) := by
  decide +kernel

/-- Square-zero localization does not make all Jordan associators vanish. -/
theorem local_jordan_associator_nonzero :
    let j := fun a b : Matrix (Fin 2) (Fin 2) ℚ => a * b + b * a
    j (j rationalD rationalD) rationalB - j rationalD (j rationalD rationalB) =
      -(2 • rationalD) ∧ -(2 • rationalD) ≠ 0 := by
  decide +kernel

end InfoGeometry.Canonical.ReflexiveKleinKernelRegression
