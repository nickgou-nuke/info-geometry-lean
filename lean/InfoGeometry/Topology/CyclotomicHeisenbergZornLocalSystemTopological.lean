/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological
import InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

/-!
# Cyclotomic Heisenberg–Zorn Local-System Readout

This module defines the joint observable readout `cyclotomicLocalSystemReadout`
sending `(q, (a, b)) : SixthRootParameter × (ℕ × ℕ)` to
`(effectiveCubeRoot q, topologicalQutritWeyl a b)`, and proves coordinate
projections, product continuity, local constancy, cube-root order three, and
mod-3 periodicity in the clock and shift exponents.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.ZornSixthRootCubicChargeTopological`:
    `effectiveCubeRoot`, `effectiveCubeRoot_cube`, `continuous_effectiveCubeRoot`.
  * `InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological`:
    `topologicalQutritWeyl`, `continuous_topologicalQutritWeyl`,
    `topologicalQutritWeyl_clock_period`, `topologicalQutritWeyl_shift_period`.
- BUCKET 2 (Deconfabulation):
  * All coordinate projections, continuity, cube-root, and mod-3 periodicity
    identities are proved constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `WeylWord`, `cyclotomicLocalSystemReadout`.
  * `cyclotomicLocalSystemReadout_fst`, `cyclotomicLocalSystemReadout_snd`.
  * `continuous_cyclotomicLocalSystemReadout`,
    `isLocallyConstant_cyclotomicLocalSystemReadout`.
  * `cyclotomicLocalSystemReadout_effective_root_cube`,
    `cyclotomicLocalSystemReadout_clock_period`,
    `cyclotomicLocalSystemReadout_shift_period`.
-/

namespace InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological

open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological
open InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

noncomputable section

/-- Complex 3×3 matrix carrier for qutrit Weyl words. -/
abbrev WeylWord := Matrix (Fin 3) (Fin 3) ℂ

/-- Joint cyclotomic parameter and qutrit Weyl-word observable readout. -/
def cyclotomicLocalSystemReadout
    (p : SixthRootParameter × (ℕ × ℕ)) : ℂ × WeylWord :=
  (effectiveCubeRoot p.1, topologicalQutritWeyl p.2.1 p.2.2)

/-- First coordinate of `cyclotomicLocalSystemReadout p` is `effectiveCubeRoot p.1`. -/
@[simp] theorem cyclotomicLocalSystemReadout_fst
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLocalSystemReadout p).1 = effectiveCubeRoot p.1 := by
  unfold cyclotomicLocalSystemReadout
  exact Eq.refl _

/-- Second coordinate of `cyclotomicLocalSystemReadout p` is `topologicalQutritWeyl p.2.1 p.2.2`. -/
@[simp] theorem cyclotomicLocalSystemReadout_snd
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLocalSystemReadout p).2 =
      topologicalQutritWeyl p.2.1 p.2.2 := by
  unfold cyclotomicLocalSystemReadout
  exact Eq.refl _

/-- The joint readout is continuous in the product topology. -/
theorem continuous_cyclotomicLocalSystemReadout :
    Continuous cyclotomicLocalSystemReadout := by
  have hroot : Continuous (fun p : SixthRootParameter × (ℕ × ℕ) =>
      effectiveCubeRoot p.1) :=
    continuous_effectiveCubeRoot.comp continuous_fst
  have hweyl : Continuous (fun p : SixthRootParameter × (ℕ × ℕ) =>
      topologicalQutritWeyl p.2.1 p.2.2) :=
    continuous_topologicalQutritWeyl.comp continuous_snd
  exact hroot.prodMk hweyl

/-- Discrete cyclotomic parameters give a locally constant joint readout. -/
theorem isLocallyConstant_cyclotomicLocalSystemReadout :
    IsLocallyConstant cyclotomicLocalSystemReadout := by
  unfold cyclotomicLocalSystemReadout
  exact IsLocallyConstant.of_discrete

/-- The first readout coordinate is always a cube root of unity. -/
theorem cyclotomicLocalSystemReadout_effective_root_cube
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLocalSystemReadout p).1 ^ 3 = 1 := by
  rw [cyclotomicLocalSystemReadout_fst]
  exact effectiveCubeRoot_cube p.1

/-- The Weyl coordinate is periodic of period 3 in the clock exponent. -/
theorem cyclotomicLocalSystemReadout_clock_period
    (p : SixthRootParameter × (ℕ × ℕ)) :
    cyclotomicLocalSystemReadout
        (p.1, (p.2.1 + 3, p.2.2)) =
      cyclotomicLocalSystemReadout p := by
  apply Prod.ext
  · unfold cyclotomicLocalSystemReadout
    exact Eq.refl _
  · change topologicalQutritWeyl (p.2.1 + 3) p.2.2 =
      topologicalQutritWeyl p.2.1 p.2.2
    exact topologicalQutritWeyl_clock_period p.2.1 p.2.2

/-- The Weyl coordinate is periodic of period 3 in the shift exponent. -/
theorem cyclotomicLocalSystemReadout_shift_period
    (p : SixthRootParameter × (ℕ × ℕ)) :
    cyclotomicLocalSystemReadout
        (p.1, (p.2.1, p.2.2 + 3)) =
      cyclotomicLocalSystemReadout p := by
  apply Prod.ext
  · unfold cyclotomicLocalSystemReadout
    exact Eq.refl _
  · change topologicalQutritWeyl p.2.1 (p.2.2 + 3) =
      topologicalQutritWeyl p.2.1 p.2.2
    exact topologicalQutritWeyl_shift_period p.2.1 p.2.2

end
end InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological
