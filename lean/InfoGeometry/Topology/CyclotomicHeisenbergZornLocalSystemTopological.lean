import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological
import InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

/-!
# Cyclotomic Heisenberg--Zorn local-system readout

This is the first genuine product-topology node joining the three finite
lanes: a sixth-root parameter, a qutrit Weyl word, and the effective Zorn
cube root.  The output is only a paired observable readout; no algebraic
identification of the carriers is asserted.
-/

namespace InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological

open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological
open InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

noncomputable section

abbrev WeylWord := InfoGeometry.Algebra.FiniteSpin.Mat3C

/-- Joint cyclotomic parameter/Weyl-word observable. -/
def cyclotomicLocalSystemReadout
    (p : SixthRootParameter × (ℕ × ℕ)) : ℂ × WeylWord :=
  (effectiveCubeRoot p.1, topologicalQutritWeyl p.2.1 p.2.2)

@[simp] theorem cyclotomicLocalSystemReadout_fst
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLocalSystemReadout p).1 = effectiveCubeRoot p.1 := by
  rfl

@[simp] theorem cyclotomicLocalSystemReadout_snd
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLocalSystemReadout p).2 =
      topologicalQutritWeyl p.2.1 p.2.2 := by
  rfl

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
  exact IsLocallyConstant.of_discrete (f := cyclotomicLocalSystemReadout)

/-- The first readout coordinate is always a cube root of unity. -/
theorem cyclotomicLocalSystemReadout_effective_root_cube
    (p : SixthRootParameter × (ℕ × ℕ)) :
    (cyclotomicLocalSystemReadout p).1 ^ 3 = 1 := by
  exact effectiveCubeRoot_cube p.1

/-- The Weyl coordinate is periodic in the clock direction. -/
theorem cyclotomicLocalSystemReadout_clock_period
    (p : SixthRootParameter × (ℕ × ℕ)) :
    cyclotomicLocalSystemReadout
        (p.1, (p.2.1 + 3, p.2.2)) =
      cyclotomicLocalSystemReadout p := by
  apply Prod.ext
  · rfl
  · change topologicalQutritWeyl (p.2.1 + 3) p.2.2 =
      topologicalQutritWeyl p.2.1 p.2.2
    exact topologicalQutritWeyl_clock_period p.2.1 p.2.2

/-- The Weyl coordinate is periodic in the shift direction. -/
theorem cyclotomicLocalSystemReadout_shift_period
    (p : SixthRootParameter × (ℕ × ℕ)) :
    cyclotomicLocalSystemReadout
        (p.1, (p.2.1, p.2.2 + 3)) =
      cyclotomicLocalSystemReadout p := by
  apply Prod.ext
  · rfl
  · change topologicalQutritWeyl p.2.1 (p.2.2 + 3) =
      topologicalQutritWeyl p.2.1 p.2.2
    exact topologicalQutritWeyl_shift_period p.2.1 p.2.2

end
end InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological
