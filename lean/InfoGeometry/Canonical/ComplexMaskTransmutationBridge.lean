import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Canonical.BogoliubovProjectorTransport
import InfoGeometry.Canonical.ModularSuperchargeClosure
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ComplexMaskTransmutationBridge

Translator/coherence surface for Chapter 131 ("Transmutation of the Complex
Mask").

This file does not introduce new owner objects. It rewrites existing modular
surfaces into explicit doubled-real Lorentz-bivector language (`J ∘ ε`) and
connects them to the circularly polarized (`u₊/u₋`) sheet transport lane.
-/

namespace ComplexMaskTransmutationBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.ModularSuperchargeClosure
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.BogoliubovProjectorTransport

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Repo-native name for the modular phase axis used historically as
`modularComplexI`. The object is the same doubled-real generator.
-/
@[rep_depth transport]
noncomputable def lorentzBivectorGenerator : EndH :=
  modularComplexI (E := E)

/- The transmuted generator is exactly `J ∘ ε` on the doubled-real carrier. -/
@[rep_depth transport]
theorem lorentzBivectorGenerator_eq_modular_j_comp_spectral_epsilon :
    lorentzBivectorGenerator (E := E)
      = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
  let _ : CompleteSpace E := inferInstance
  rfl

/-- Equivalent dictionary form through the projector-equivariance `HestenesI`. -/
@[rep_depth transport]
theorem lorentzBivectorGenerator_eq_hestenesI :
    lorentzBivectorGenerator (E := E) = HestenesI (E := E) := by
  let _ : CompleteSpace E := inferInstance
  rfl

/--
Canonical-seed restatement in transmuted language:
`h_mod = -(H_D ∘ (J ∘ ε))`.
-/
@[rep_depth transport]
theorem canonicalModularSeed_eq_neg_superHamiltonian_comp_lorentzBivectorGenerator
    (CIK : CertifiedInverseKernel H₂) :
    canonicalBivectorSeed (E := E) CIK
      =
    -(DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK).comp
      (lorentzBivectorGenerator (E := E)) := by
  rfl

/--
The projected-even generator identity, stated on the transmuted seed name.
This is a translator theorem and reuses the owned closure lane.
-/
@[rep_depth transport]
theorem superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed_transmuted
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      =
    BogoliubovTransport.modularTransportGenerator (E := E)
      (lorentzBivectorSeed (E := E) CIK) := by
  simpa using
    (superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed
      (E := E) (CIK := CIK))

/--
Circularly polarized sheet transport: the transmuted bivector maps the `u₊`
sheet to `u₋` (plus to minus).
-/
@[rep_depth transport]
theorem lorentzBivectorGenerator_maps_plusSheet_to_minusSheet
    {u : H₂} (hu : u ∈ plusSheet (E := E)) :
    lorentzBivectorGenerator (E := E) u ∈ minusSheet (E := E) := by
  simpa [lorentzBivectorGenerator] using
    (modularComplexI_maps_plusSheet_to_minusSheet (u := u) hu)

/--
Circularly polarized sheet transport: the transmuted bivector maps the `u₋`
sheet to `u₊` (minus to plus).
-/
@[rep_depth transport]
theorem lorentzBivectorGenerator_maps_minusSheet_to_plusSheet
    {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    lorentzBivectorGenerator (E := E) u ∈ plusSheet (E := E) := by
  simpa [lorentzBivectorGenerator] using
    (modularComplexI_maps_minusSheet_to_plusSheet (u := u) hu)

end Core

end ComplexMaskTransmutationBridge
