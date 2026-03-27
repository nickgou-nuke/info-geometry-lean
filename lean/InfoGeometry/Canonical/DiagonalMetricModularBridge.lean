import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.Canonical.SpectralInference

/-!
# Diagonal Metric Modular Bridge

Thin bridge identifying the diagonal Hessian metric operator with the already
owned scalar modular Hamiltonian lift on the doubled carrier.

This file does not add new modular or spectral ontology. It only packages the
currently proved lower surfaces:

- raw relative counts and their diagonal modular-potential lift,
- the scalar Tomita-Takesaki-style operator on the doubled router carrier,
- the spectral-root witness `D² = H.metricOp x₀`.

The key point is the narrow diagonal specialization:

`H.metricOp x₀ = (relative surprisal scalar) • Id`,

so that the spectral square can be rewritten to the modular Hamiltonian without
using a capstone wrapper.
-/

namespace InfoGeometry.Canonical.DiagonalMetricModularBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.RelativeSurprisalOperatorLift
open InfoGeometry.Canonical.SpectralInference

section Router

variable {n : ℕ} [Nonempty (Fin n)]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace (InfoGeometry.Canonical.KMSSinkhornBridge.RouterAmplitude n)

/-- Continuum modular data induced by the finite relative-count modular Hamiltonian. -/
noncomputable def countModularData
    (counts ref : RelativeCounts n) :
    ModularRadonNikodymData (InfoGeometry.Canonical.KMSSinkhornBridge.RouterAmplitude n) where
  rnDerivative :=
    Real.exp (-(relativeModularHamiltonian n (relativeCountDensity n counts ref)))
  rnDerivative_pos := Real.exp_pos _

/--
The modular Hamiltonian attached to `countModularData` is exactly the existing
relative Tomita-Takesaki lift on the doubled router carrier.
-/
@[simp] theorem countModularData_modularHamiltonian_eq_relativeTomitaTakesakiOp
    (counts ref : RelativeCounts n) :
    (countModularData counts ref).modularHamiltonian =
      relativeTomitaTakesakiOp n (relativeCountDensity n counts ref) := by
  rw [InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularHamiltonian_eq_neg_log_rn]
  simp [countModularData, InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp,
    InfoGeometry.Canonical.YangMillsContinuum.idEndH]

/--
Diagonal relative-count slice: the Hessian metric operator at the basepoint is
the diagonal average of the raw relative modular-potential lift times `Id`.
-/
def IsDiagonalRelativeCountMetricSlice
    (H : HessianGeometry H₂) (x₀ : H₂)
    (counts ref : RelativeCounts n) : Prop :=
  H.metricOp x₀ =
    diagonalAverage (n := n) (relativeCountModularPotentialOperator (n := n) counts ref) •
      ContinuousLinearMap.id ℝ H₂

/--
On the diagonal relative-count slice, the Hessian metric operator is exactly
the finite relative Tomita-Takesaki lift.
-/
theorem metricOp_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice
    {H : HessianGeometry H₂} {x₀ : H₂}
    {counts ref : RelativeCounts n}
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) H x₀ counts ref) :
    H.metricOp x₀ =
      relativeTomitaTakesakiOp n (relativeCountDensity n counts ref) := by
  rw [hDiag]
  exact (relativeTomitaTakesakiOp_eq_diagonalAverage_rawLift_smul_id
    (n := n) (counts := counts) (ref := ref)).symm

/--
On the diagonal relative-count slice, the Hessian metric operator is exactly
the continuum modular Hamiltonian induced by the same scalar relative surprisal.
-/
theorem metricOp_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice
    {H : HessianGeometry H₂} {x₀ : H₂}
    {counts ref : RelativeCounts n}
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) H x₀ counts ref) :
    H.metricOp x₀ =
      (countModularData counts ref).modularHamiltonian := by
  calc
    H.metricOp x₀ = relativeTomitaTakesakiOp n (relativeCountDensity n counts ref) :=
      metricOp_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice
        (n := n) hDiag
    _ = (countModularData counts ref).modularHamiltonian := by
      symm
      exact countModularData_modularHamiltonian_eq_relativeTomitaTakesakiOp counts ref

/--
Spectral-root specialization:
if the metric operator lies on the diagonal relative-count slice, then the
Dirac square is exactly the relative Tomita-Takesaki lift.
-/
theorem dirac_sq_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice
    {D : H₂ →L[ℝ] H₂} {H : HessianGeometry H₂} {x₀ : H₂}
    {counts ref : RelativeCounts n}
    (compat : DiracMetricCompatibility (E := H₂) D H x₀)
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) H x₀ counts ref) :
    D * D =
      relativeTomitaTakesakiOp n (relativeCountDensity n counts ref) := by
  calc
    D * D = H.metricOp x₀ := compat.dirac_sq_eq_metric
    _ = relativeTomitaTakesakiOp n (relativeCountDensity n counts ref) :=
      metricOp_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice
        (n := n) hDiag

/--
Spectral-root specialization:
if the metric operator lies on the diagonal relative-count slice, then the
Dirac square is exactly the induced continuum modular Hamiltonian.
-/
theorem dirac_sq_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice
    {D : H₂ →L[ℝ] H₂} {H : HessianGeometry H₂} {x₀ : H₂}
    {counts ref : RelativeCounts n}
    (compat : DiracMetricCompatibility (E := H₂) D H x₀)
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) H x₀ counts ref) :
    D * D =
      (countModularData counts ref).modularHamiltonian := by
  calc
    D * D = H.metricOp x₀ := compat.dirac_sq_eq_metric
    _ = (countModularData counts ref).modularHamiltonian :=
      metricOp_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice
        (n := n) hDiag

/--
Pointwise form of the diagonal specialization:
the Dirac square acts by scalar multiplication with the relative modular
Hamiltonian on the diagonal slice.
-/
theorem dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice
    {D : H₂ →L[ℝ] H₂} {H : HessianGeometry H₂} {x₀ : H₂}
    {counts ref : RelativeCounts n}
    (compat : DiracMetricCompatibility (E := H₂) D H x₀)
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) H x₀ counts ref)
    (v : H₂) :
    D (D v) =
      relativeModularHamiltonian n (relativeCountDensity n counts ref) • v := by
  have hv :
      (D * D) v =
        (relativeTomitaTakesakiOp n (relativeCountDensity n counts ref)) v := by
    exact congrArg
      (fun A : H₂ →L[ℝ] H₂ => A v)
      (dirac_sq_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice
        (n := n) compat hDiag)
  simpa [ContinuousLinearMap.mul_apply,
    InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp_apply] using hv

section SpectralTriple

/--
Info-spectral-triple corollary of the diagonal bridge:
on the diagonal relative-count slice, the spectral Dirac square is the
induced continuum modular Hamiltonian.
-/
theorem spectral_dirac_sq_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice
    (IST : InfoSpectralTriple H₂)
    {counts ref : RelativeCounts n}
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) IST.H IST.x₀ counts ref) :
    IST.D * IST.D =
      (countModularData counts ref).modularHamiltonian :=
  dirac_sq_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice
    (n := n) IST.compatibility hDiag

/--
Info-spectral-triple pointwise corollary of the diagonal bridge:
on the diagonal relative-count slice, the spectral Dirac square acts by the
relative modular Hamiltonian scalar.
-/
theorem spectral_dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice
    (IST : InfoSpectralTriple H₂)
    {counts ref : RelativeCounts n}
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) IST.H IST.x₀ counts ref)
    (v : H₂) :
    IST.D (IST.D v) =
      relativeModularHamiltonian n (relativeCountDensity n counts ref) • v :=
  dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice
    (n := n) IST.compatibility hDiag v

end SpectralTriple

end Router

end InfoGeometry.Canonical.DiagonalMetricModularBridge
