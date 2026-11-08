/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological
import InfoGeometry.Topology.CyclotomicQutritWeylQuotientTopological
import InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

/-!
# Finite Cyclotomic Latent Quotient Chart

This module defines the finite latent quotient chart
`LatentQuotient := CubicRootParameter × (Fin 3 × Fin 3)`, the quotient map
`cyclotomicLatentQuotientReadout`, and the observable evaluation `latentObservable`,
and proves that `cyclotomicLocalSystemReadout` factors canonically through
`cyclotomicLatentQuotientReadout`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological`:
    `cyclotomicLocalSystemReadout`.
  * `InfoGeometry.Topology.CyclotomicQutritWeylQuotientTopological`:
    `exponentResiduePair`, `qutritWeylResidue`, `topologicalQutritWeyl_factorization`.
  * `InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological`:
    `CubicRootParameter`.
- BUCKET 2 (Deconfabulation):
  * All quotient projections, continuity, and observable factorization theorems
    are proved constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `LatentQuotient`, `WeylWord`, `effectiveCubeRootParameter`,
    `cyclotomicLatentQuotientReadout`, `latentObservable`.
  * `continuous_cyclotomicLatentQuotientReadout`,
    `isLocallyConstant_cyclotomicLatentQuotientReadout`,
    `cyclotomicLatentQuotientReadout_root`,
    `cyclotomicLatentQuotientReadout_residue`,
    `continuous_latentObservable`,
    `cyclotomicLocalSystemReadout_factorization`.
-/

namespace InfoGeometry.Topology.CyclotomicLatentQuotientTopological

open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological
open InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological
open InfoGeometry.Topology.CyclotomicQutritWeylQuotientTopological
open InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological
open InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

noncomputable section

/-- Finite cyclotomic latent quotient chart `CubicRootParameter × (Fin 3 × Fin 3)`. -/
abbrev LatentQuotient :=
  CubicRootParameter × (Fin 3 × Fin 3)

/-- Complex 3×3 matrix carrier for qutrit Weyl words. -/
abbrev WeylWord := Matrix (Fin 3) (Fin 3) ℂ

/-- Effective cube root as a point of the cubic-root parameter subtype. -/
def effectiveCubeRootParameter (q : SixthRootParameter) : CubicRootParameter :=
  ⟨effectiveCubeRoot q, effectiveCubeRoot_cube q⟩

/-- Finite latent quotient chart for the sixth-root and Weyl exponent labels. -/
def cyclotomicLatentQuotientReadout
    (p : SixthRootParameter × (ℕ × ℕ)) : LatentQuotient :=
  (effectiveCubeRootParameter p.1, exponentResiduePair p.2)

/-- Continuity of `cyclotomicLatentQuotientReadout` on the discrete parameter space. -/
theorem continuous_cyclotomicLatentQuotientReadout :
    Continuous cyclotomicLatentQuotientReadout := by
  unfold cyclotomicLatentQuotientReadout
  exact continuous_of_discreteTopology

/-- Local constancy of `cyclotomicLatentQuotientReadout` on the discrete parameter space. -/
theorem isLocallyConstant_cyclotomicLatentQuotientReadout :
    IsLocallyConstant cyclotomicLatentQuotientReadout := by
  unfold cyclotomicLatentQuotientReadout
  exact IsLocallyConstant.of_discrete

/-- Effective cube-root coordinate of `cyclotomicLatentQuotientReadout p`. -/
@[simp] theorem cyclotomicLatentQuotientReadout_root
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLatentQuotientReadout p).1.1 = effectiveCubeRoot p.1 := by
  unfold cyclotomicLatentQuotientReadout effectiveCubeRootParameter
  exact Eq.refl _

/-- Weyl exponent residue pair of `cyclotomicLatentQuotientReadout p`. -/
@[simp] theorem cyclotomicLatentQuotientReadout_residue
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLatentQuotientReadout p).2 = exponentResiduePair p.2 := by
  unfold cyclotomicLatentQuotientReadout
  exact Eq.refl _

/-- Observable readout from the finite latent quotient chart. -/
def latentObservable (z : LatentQuotient) : ℂ × WeylWord :=
  (z.1.1, qutritWeylResidue z.2)

/-- Continuity of `latentObservable` on `LatentQuotient`. -/
theorem continuous_latentObservable :
    Continuous latentObservable := by
  unfold latentObservable
  exact continuous_of_discreteTopology

/-- `cyclotomicLocalSystemReadout` factors canonically through `cyclotomicLatentQuotientReadout`. -/
theorem cyclotomicLocalSystemReadout_factorization
    (p : SixthRootParameter × (ℕ × ℕ)) :
    latentObservable (cyclotomicLatentQuotientReadout p) =
      cyclotomicLocalSystemReadout p := by
  apply Prod.ext
  · unfold latentObservable cyclotomicLatentQuotientReadout effectiveCubeRootParameter
      cyclotomicLocalSystemReadout
    exact Eq.refl _
  · change qutritWeylResidue (exponentResiduePair p.2) =
      topologicalQutritWeyl p.2.1 p.2.2
    exact (topologicalQutritWeyl_factorization p.2).symm

end
end InfoGeometry.Topology.CyclotomicLatentQuotientTopological
