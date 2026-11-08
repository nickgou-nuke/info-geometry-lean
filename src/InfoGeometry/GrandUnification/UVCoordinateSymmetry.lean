/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GrandUnification.HodgeCartanTrifactor

/-!
# Centered-Coordinate Reflection and Cartan Sign Readouts

This module formalizes two algebraic facts: the affine coordinate
`1/2 + u + iv` sends the central inversion `(u,v) ↦ (-u,-v)` to `s ↦ 1 - s`,
and the Cartan involution fixes the harmonic sector while negating the
exact and coexact sectors under the tripotent projection hypotheses.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.GrandUnification.HodgeCartan`: `harmonic_op`, `exact_op`,
    `coexact_op`, `cartan_involution`, `cartan_symmetric_harmonic`,
    `cartan_antisymmetric_exact`, `cartan_antisymmetric_coexact`.
- BUCKET 2 (Deconfabulation):
  * Replaced the `Prop`-valued `survives_topology` wrapper with the explicit
    fixed-point equation `cartan_involution T * ρ = ρ` in `harmonic_trap_survives`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `functional_equation_isomorphism`, `harmonic_trap_survives`,
    `exact_annihilation`, `coexact_annihilation`.
-/

namespace InfoGeometry.GrandUnification.UVSymmetry

/-- The centered holomorphic coordinate chart at `s = 1/2`. -/
structure UVChart where
  /-- Real horizontal offset `u = Re(s) - 1/2`. -/
  u : ℝ
  /-- Imaginary vertical coordinate `v = Im(s)`. -/
  v : ℝ

/-- Canonical origin `(0, 0)` of `UVChart` corresponding to `s = 1/2`. -/
instance instInhabitedUVChart : Inhabited UVChart := ⟨⟨0, 0⟩⟩

/-- Map the centered `(u, v)` coordinates back to the complex plane `s = 1/2 + u + iv`. -/
noncomputable def UVChart.toComplex (z : UVChart) : ℂ :=
  ⟨(1 / 2 : ℝ) + z.u, z.v⟩

/-- The geometric central inversion `(u, v) ↦ (-u, -v)` (Parity + Time reversal). -/
def central_inversion (z : UVChart) : UVChart :=
  ⟨-z.u, -z.v⟩

/-- The affine coordinate reflection `s ↦ 1 - s` is central inversion in
centered `(u, v)` coordinates. -/
theorem functional_equation_isomorphism (z : UVChart) :
    (1 : ℂ) - z.toComplex = (central_inversion z).toComplex := by
  unfold UVChart.toComplex central_inversion
  apply Complex.ext
  · dsimp
    ring
  · dsimp
    ring

/-! ### Topological Annihilation on the Klein Bottle Seam -/

open InfoGeometry.GrandUnification.HodgeCartan
open InfoGeometry.Canonical.TrifactorDecomposition

section Basic

variable {R : Type*} [CommRing R]

/-- If `ρ` is fixed by the harmonic operator, then it is fixed by the
Cartan involution (`cartan_involution T * ρ = ρ`). -/
theorem harmonic_trap_survives (T : R) (hT : T ^ 3 = T) (ρ : R)
    (h_harmonic : harmonic_op T * ρ = ρ) :
    cartan_involution T * ρ = ρ := by
  calc
    cartan_involution T * ρ = cartan_involution T * (harmonic_op T * ρ) :=
      congrArg (fun x => cartan_involution T * x) h_harmonic.symm
    _ = (cartan_involution T * harmonic_op T) * ρ := by rw [mul_assoc]
    _ = harmonic_op T * ρ := by rw [cartan_symmetric_harmonic T hT]
    _ = ρ := h_harmonic

end Basic

section WithHalf

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- If `ρ` is fixed by the exact operator, then the Cartan involution
acts by negation. -/
theorem exact_annihilation (T : R) (hT : T ^ 3 = T) (ρ : R)
    (h_exact : exact_op T * ρ = ρ) :
    cartan_involution T * ρ = -ρ := by
  calc
    cartan_involution T * ρ = cartan_involution T * (exact_op T * ρ) :=
      congrArg (fun x => cartan_involution T * x) h_exact.symm
    _ = (cartan_involution T * exact_op T) * ρ := by rw [mul_assoc]
    _ = (- exact_op T) * ρ := by rw [cartan_antisymmetric_exact T hT]
    _ = - (exact_op T * ρ) := by ring
    _ = -ρ := by rw [h_exact]

/-- If `ρ` is fixed by the coexact operator, then the Cartan involution
acts by negation. -/
theorem coexact_annihilation (T : R) (hT : T ^ 3 = T) (ρ : R)
    (h_coexact : coexact_op T * ρ = ρ) :
    cartan_involution T * ρ = -ρ := by
  calc
    cartan_involution T * ρ = cartan_involution T * (coexact_op T * ρ) :=
      congrArg (fun x => cartan_involution T * x) h_coexact.symm
    _ = (cartan_involution T * coexact_op T) * ρ := by rw [mul_assoc]
    _ = (- coexact_op T) * ρ := by rw [cartan_antisymmetric_coexact T hT]
    _ = - (coexact_op T * ρ) := by ring
    _ = -ρ := by rw [h_coexact]

end WithHalf

end InfoGeometry.GrandUnification.UVSymmetry
