import Mathlib
import InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological
import InfoGeometry.Topology.CyclotomicQutritWeylQuotientTopological
import InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

/-!
# Finite cyclotomic latent quotient chart

This owner combines the effective cube-root coordinate and the finite Weyl
residue coordinate into one discrete latent chart.  The earlier paired
Heisenberg--Zorn observable is recovered by an explicit readout from this
chart; no identification of the underlying algebraic carriers is made.
-/

namespace InfoGeometry.Topology.CyclotomicLatentQuotientTopological

open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological
open InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological
open InfoGeometry.Topology.CyclotomicQutritWeylQuotientTopological
open InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological
open InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

noncomputable section

abbrev LatentQuotient :=
  CubicRootParameter × (Fin 3 × Fin 3)

abbrev WeylWord := Matrix (Fin 3) (Fin 3) ℂ

/-- Effective cube root as a point of the cubic-root parameter subtype. -/
def effectiveCubeRootParameter (q : SixthRootParameter) : CubicRootParameter :=
  ⟨effectiveCubeRoot q, effectiveCubeRoot_cube q⟩

/-- Finite latent quotient chart for the root and Weyl labels. -/
def cyclotomicLatentQuotientReadout
    (p : SixthRootParameter × (ℕ × ℕ)) : LatentQuotient :=
  (effectiveCubeRootParameter p.1, exponentResiduePair p.2)

theorem continuous_cyclotomicLatentQuotientReadout :
    Continuous cyclotomicLatentQuotientReadout := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_cyclotomicLatentQuotientReadout :
    IsLocallyConstant cyclotomicLatentQuotientReadout := by
  exact IsLocallyConstant.of_discrete
    (f := cyclotomicLatentQuotientReadout)

@[simp] theorem cyclotomicLatentQuotientReadout_root
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLatentQuotientReadout p).1.1 = effectiveCubeRoot p.1 := by
  rfl

@[simp] theorem cyclotomicLatentQuotientReadout_residue
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLatentQuotientReadout p).2 = exponentResiduePair p.2 := by
  rfl

/-- Observable readout from the finite latent quotient chart. -/
def latentObservable (z : LatentQuotient) : ℂ × WeylWord :=
  (z.1.1, qutritWeylResidue z.2)

theorem continuous_latentObservable :
    Continuous latentObservable := by
  exact continuous_of_discreteTopology

/-- The previous paired observable factors through the finite latent chart. -/
theorem cyclotomicLocalSystemReadout_factorization
    (p : SixthRootParameter × (ℕ × ℕ)) :
    latentObservable (cyclotomicLatentQuotientReadout p) =
      cyclotomicLocalSystemReadout p := by
  apply Prod.ext
  · change effectiveCubeRoot p.1 = effectiveCubeRoot p.1
    rfl
  · change qutritWeylResidue (exponentResiduePair p.2) =
      topologicalQutritWeyl p.2.1 p.2.2
    exact (topologicalQutritWeyl_factorization p.2).symm

end
end InfoGeometry.Topology.CyclotomicLatentQuotientTopological
