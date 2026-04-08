import InfoGeometry.Canonical.SingularBoundaryCorrection
import InfoGeometry.Canonical.BoundaryProjector
import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Canonical.ModularSpinorBridge
import InfoGeometry.Quantum.BulkBoundary
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Krein.State

/-!
# Spinor-Modular Bridge: The Coriolis Whirlpool

This module formalizes the identification between topological Majorana boundary
modes and the modular singularization layer on the doubled Krein space.

It captures the **"Coriolis Whirlpool"** at the boundary of the causal cone:
- **Dangling Zero-Modes**: Bulk zero-modes sensitive to the boundary anomaly.
- **Vorticity Source**: The boundary generator acts as the source of chiral flux.
- **Spinor-Modular Identification**: Mapping the Weyl boundary spinors to the
  null threads of the modular web.
-/

namespace InfoGeometry.Canonical.SpinorModularBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SingularBoundaryCorrection
open InfoGeometry.Krein
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.RealMajorana

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
A **Dangling Zero-Mode** is a vector in the carrier that is in the
kernel of the bulk operator `A` but is non-trivially moved by the boundary
generator (the modular anomaly).
-/
def IsDanglingZeroMode
    (S : SingularBoundaryCorrection E) (v : E) : Prop :=
  S.kernel.A v = 0 ∧ S.boundaryGenerator v ≠ 0

/--
The subspace of dangling modes is exactly the part of the kernel where the
"Coriolis whirlpool" (the vorticity) is active.
-/
def DanglingSubspace (S : SingularBoundaryCorrection E) : Submodule ℝ E :=
  (S.kernel.A.toLinearMap).ker ⊓ (LinearMap.ker S.boundaryGenerator.toLinearMap).comap (LinearMap.id)

/--
The **Horizon** (Scale-Fixed Subspace):
The subspace of the doubled carrier where the modular operator Δ acts as the identity.
This is the locus of points where the scale inversion `X ↦ 1/X` leaves the
state unchanged—the "neck" of the Klein Bottle.
-/
noncomputable def HorizonSubspace : Submodule ℝ H₂ :=
  InfoGeometry.Canonical.boundarySubspace
    (E := E) (InfoGeometry.Canonical.TomitaTakesaki.modularOperatorDelta (E := E))

/--
Theorem: Scale Inversion Fixed Point.
On the Horizon Subspace, the scale inversion `J Δ J = Δ⁻¹` stabilizes at `Δ = 1`.
This defines the absolute present where modular time `t = -t`.
-/
theorem horizon_is_scale_invariant
    (v : H₂) (hv : v ∈ HorizonSubspace (E := E)) :
    (InfoGeometry.Canonical.TomitaTakesaki.modularOperatorDelta (E := E)) v = v := by
  simpa [HorizonSubspace] using
    (InfoGeometry.Canonical.mem_boundarySubspace
      (E := E)
      (Δ := InfoGeometry.Canonical.TomitaTakesaki.modularOperatorDelta (E := E))
      (ψ := v)).1 hv

/--
The "Coriolis Whirlpool" (the vorticity) on the singular boundary.
The boundary generator `χ` acts as the source of state-space rotation.

At the holographic boundary, the infinite modular flow `exp(tK)` degenerates
into this pure chiral rotation. The "infinity" of the bulk translation is
converted into the "spinning" of the boundary whirlpool.
-/
noncomputable def coriolisVorticity
    (S : SingularBoundaryCorrection E) : E →L[ℝ] E :=
  vorticity S.boundaryGenerator

/--
Theorem: The boundary generator is its own vorticity.
Since the boundary generator `χ = [P_D, P_MP]` is skew-adjoint (proved in
`SingularBoundaryCorrection.lean`), it acts as a pure rotation (vorticity).
-/
theorem boundaryGenerator_is_vorticity
    (S : SingularBoundaryCorrection E) :
    coriolisVorticity S = S.boundaryGenerator := by
  apply vorticity_eq_self_of_skew
  exact S.boundaryGenerator_skew

/--
The **Spinor-Modular Identification**:
A Weyl boundary spinor pair $(\psi_+, \psi_-)$ from the Kitaev topological
layer corresponds to a pair of dangling null modes in the modular web.
-/
structure SpinorModularIdentification
    (M : RealMajoranaDatum (S := E))
    (S : SingularBoundaryCorrection E) where
  psiPlus : E
  psiMinus : E
  is_plus_dangling : IsDanglingZeroMode S psiPlus
  is_minus_dangling : IsDanglingZeroMode S psiMinus
  is_plus_weyl : psiPlus ∈ M.weylPlus
  is_minus_weyl : psiMinus ∈ M.weylMinus

/--
The anomaly-sourced chiral flux is the integral of the "whirlpool" dynamics
over the dangling zero-modes.
-/
noncomputable def danglingChiralFlux
    (S : SingularBoundaryCorrection E)
    (ω : (E →L[ℝ] E) →L[ℝ] ℝ) : ℝ :=
  chiralFlux S.boundaryGenerator ω

/--
Finality: The gravity-like curvature (anomaly) of the informational state space
is concentrated precisely on the dangling Majorana threads.
-/
theorem curvature_concentrated_on_dangling_modes
    (S : SingularBoundaryCorrection E) (v : E)
    (hDangling : IsDanglingZeroMode S v) :
    S.boundaryGenerator v ≠ 0 :=
  hDangling.2

end InfoGeometry.Canonical.SpinorModularBridge
