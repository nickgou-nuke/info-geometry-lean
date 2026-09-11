import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological
import InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological

/-!
# Product chart for cyclotomic Heisenberg/Sugawara data

This owner forms an explicit product chart from three already constructed
pieces: a sixth-root parameter, a finite Heisenberg basis index, and the
charged-Fock scalar parameter.  The first output is the existing latent
quotient label; the second is the concrete dependent Sugawara packet.  The
product is intentionally a bookkeeping local system, not an asserted
algebraic identification between the two carriers.
-/

namespace InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological

open InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological
open InfoGeometry.Topology.HeisenbergFiniteModeLatentReadoutTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.CyclotomicLatentQuotientTopological
open InfoGeometry.Topology.SplitCliffordChargedFockSugawaraTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

abbrev CyclotomicHeisenbergSugawaraInput (𝕜 : Type*) :=
  SixthRootParameter × (𝕜 × Option ℤ)

abbrev CyclotomicHeisenbergSugawaraOutput (𝕜 : Type*)
    [Field 𝕜] [CharZero 𝕜] :=
  LatentQuotient × ChargedFockSugawaraPacket 𝕜

/-- Combined latent/operator readout for a root, scalar parameter, and mode. -/
def cyclotomicHeisenbergSugawaraReadout
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    CyclotomicHeisenbergSugawaraOutput 𝕜 :=
  (heisenbergFiniteModeLatentReadout (p.1, p.2.2),
    representedChargedFockSugawaraPacket (𝕜 := 𝕜) p.2.1)

@[simp] theorem cyclotomicHeisenbergSugawaraReadout_latent
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout p).1 =
      heisenbergFiniteModeLatentReadout (p.1, p.2.2) := by
  rfl

@[simp] theorem cyclotomicHeisenbergSugawaraReadout_sugawara
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout p).2 =
      representedChargedFockSugawaraPacket (𝕜 := 𝕜) p.2.1 := by
  rfl

@[simp] theorem cyclotomicHeisenbergSugawaraReadout_root
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout p).1.1 =
      effectiveCubeRootParameter p.1 := by
  rfl

@[simp] theorem cyclotomicHeisenbergSugawaraReadout_mode_degree
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout p).1.2.1 =
      heisenbergBasisCyclotomicDegree p.2.2 := by
  rfl

@[simp] theorem cyclotomicHeisenbergSugawaraReadout_sugawara_parameter
    (p : CyclotomicHeisenbergSugawaraInput 𝕜) :
    (cyclotomicHeisenbergSugawaraReadout p).2.1 = p.2.1 := by
  rfl

/-- The product readout is definitionally the product of its two native
components.  No equivalence between those components is asserted. -/
theorem cyclotomicHeisenbergSugawaraReadout_eq_product
    (root : SixthRootParameter) (a : 𝕜) (mode : Option ℤ) :
    cyclotomicHeisenbergSugawaraReadout
        (root, (a, mode)) =
      (heisenbergFiniteModeLatentReadout (root, mode),
       representedChargedFockSugawaraPacket (𝕜 := 𝕜) a) := by
  rfl

theorem latent_component_independent_of_sugawara_parameter
    (root : SixthRootParameter) (a₁ a₂ : 𝕜) (mode : Option ℤ) :
    (cyclotomicHeisenbergSugawaraReadout
        (root, (a₁, mode))).1 =
      (cyclotomicHeisenbergSugawaraReadout
        (root, (a₂, mode))).1 := by
  rfl

theorem sugawara_component_independent_of_root_and_mode
    (root₁ root₂ : SixthRootParameter) (a : 𝕜)
    (mode₁ mode₂ : Option ℤ) :
    (cyclotomicHeisenbergSugawaraReadout
        (root₁, (a, mode₁))).2 =
      (cyclotomicHeisenbergSugawaraReadout
        (root₂, (a, mode₂))).2 := by
  rfl

theorem continuous_cyclotomicHeisenbergSugawaraReadout :
    Continuous (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜)) := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_cyclotomicHeisenbergSugawaraReadout :
    IsLocallyConstant (cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜)) := by
  exact IsLocallyConstant.of_discrete
    (f := cyclotomicHeisenbergSugawaraReadout (𝕜 := 𝕜))

end
end InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological
