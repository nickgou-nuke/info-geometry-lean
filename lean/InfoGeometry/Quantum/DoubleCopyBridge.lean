import InfoGeometry.Quantum.ModularAnomaly
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Quantum.BulkBoundary
import InfoGeometry.Canonical.ChiralAction
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Krein.DoubledSpace

/-!
# InfoGeometry.Quantum.DoubleCopyBridge

Current checked facade for the double-copy / anomaly-transport corridor.

This file keeps only theorem surfaces that are honest against the live codebase:

- doubled-space gauge fields and their modular `J`-coupled double-copy operator;
- chiral/somatic weight on the spectral-conformal side;
- the lattice fact that the block Witten index varies along the modular boost;
- the protected total parity index `det = 1` of the same boost;
- boundary zero-mode protection from the concrete bulk-boundary bridge.
-/

namespace DoubleCopyBridge

open InfoGeometry.Quantum.ModularAnomaly
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Canonical.ChiralAction
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Krein

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-! ### 1. Gauge Field (The Square Root) -/

/--
A gauge field on the doubled real-Majorana carrier.
The scalar `charge` is kept separate from the operator datum.
-/
structure GaugeField (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  field : DoubledSpace E →L[ℝ] DoubledSpace E
  charge : ℝ

/-! ### 2. Emergent Gravity (The Double Copy) -/

/--
`J`-coupled doubled-space double-copy operator.

This is the honest current operator surface: two doubled-space gauge fields are
coupled through the modular involution `J` and summed symmetrically.
-/
noncomputable def doubleCopyGravityOp (A1 A2 : GaugeField E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  A1.field.comp ((modular_j (E := E)).comp A2.field)
    + A2.field.comp ((modular_j (E := E)).comp A1.field)

/-! ### 3. The Somatic Weight (The Price of Separation) -/

/--
The somatic weight is the chiral information action.
-/
noncomputable def somaticWeight
    (IST : InfoSpectralTriple E)
    (CI : ConformalInference E)
    (g Λ : ℝ) : ℝ :=
  chiralInformationAction IST CI g Λ

/-! ### 4. Checked theorem surfaces -/

/--
Whenever the gauge charge is nonzero, the somatic weight can be written as a
square-law multiple of the charge.
-/
theorem double_copy_gravity_identity
    (A : GaugeField E)
    (IST : InfoSpectralTriple E)
    (CI : ConformalInference E)
    (g Λ : ℝ)
    (hcharge : A.charge ≠ 0) :
    ∃ k : ℝ, somaticWeight IST CI g Λ = k * (A.charge ^ 2) := by
  refine ⟨somaticWeight IST CI g Λ / (A.charge ^ 2), ?_⟩
  field_simp [pow_ne_zero 2 hcharge]

/--
Along the concrete lattice modular boost, the block Witten index is the explicit
hyperbolic weight `cosh(t)^N`.
-/
theorem witten_index_tracks_modular_flow
    (N : ℕ) (t : ℝ) :
    InfoGeometry.Quantum.ModularAnomaly.Lattice.wittenIndex
        (InfoGeometry.Quantum.ModularAnomaly.Lattice.sigmaMatrix (N := N) t)
      = Real.cosh t ^ N := by
  simpa using
    InfoGeometry.Quantum.ModularAnomaly.Lattice.wittenIndex_sigmaMatrix (N := N) t

/--
The protected topological invariant of the lattice modular boost is the total
parity determinant, not the varying block Witten index.
-/
theorem parity_index_protection
    (N : ℕ) :
    ∃ I : ℝ,
      ∀ t : ℝ,
        Matrix.det
          (InfoGeometry.Quantum.ModularAnomaly.Lattice.sigmaMatrix (N := N) t) = I := by
  refine ⟨1, ?_⟩
  intro t
  simpa using InfoGeometry.Quantum.ModularAnomaly.Lattice.det_sigmaMatrix (N := N) t

/--
Boundary zero-mode protection in the concrete bulk-boundary model.

This is the checked current surface replacing the stale chain-cocycle theorem:
under the standard particle-hole and boundary-localization hypotheses, the open
chain has a protected surface zero mode.
-/
theorem zero_mode_touch_is_protected
    {S : Type*}
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
    [FiniteDimensional ℝ S]
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := S))
    (P0 : InfoGeometry.Quantum.RealMajorana.KPolarization (S := S) M)
    (localOp : InfoGeometry.Quantum.KitaevChain.KitaevCell → EndS (S := S))
    (chain : List InfoGeometry.Quantum.KitaevChain.KitaevCell)
    (hTopo : InfoGeometry.Quantum.KitaevChain.topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : InfoGeometry.Quantum.KitaevChain.KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hLoc : BoundaryLocalizationBridge (M := M) (P0 := P0) localOp chain) :
    HasSurfaceZeroMode
      (globalChainOperator :=
        globalChainOperatorFromOpenChain (S := S) localOp)
      chain := by
  exact bulk_boundary_correspondence_concrete_of_boundaryLocalization
    (M := M) (P0 := P0) (localOp := localOp)
    (chain := chain) hTopo hPHS hLoc

end DoubleCopyBridge
