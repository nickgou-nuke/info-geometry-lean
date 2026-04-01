import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Convex.Euclidean
import InfoGeometry.Math.Convexity

/-!
# Diagonal Metric Modular Bridge

Thin bridge identifying the diagonal Hessian metric operator with the already
owned averaged modular Hamiltonian lift on the doubled carrier.

This file does not add new modular or spectral ontology. It only packages the
currently proved lower surfaces:

- raw relative counts and their diagonal modular-potential lift,
- the scalar Tomita-Takesaki-style operator on the doubled router carrier,
- the spectral-root witness `D² = H.metricOp x₀`.

The key point is the narrow diagonal specialization:

`H.metricOp x₀ = (averaged relative surprisal scalar) • Id`,

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

/-- Continuum modular data induced by the finite averaged relative-count modular Hamiltonian. -/
noncomputable def countModularData
    (counts ref : RelativeCounts n) :
    ModularRadonNikodymData (InfoGeometry.Canonical.KMSSinkhornBridge.RouterAmplitude n) where
  rnDerivative :=
    Real.exp (-(averagedModularHamiltonian n (relativeCountDensity n counts ref)))
  rnDerivative_pos := Real.exp_pos _

omit [Nonempty (Fin n)] in
/--
The modular Hamiltonian attached to `countModularData` is exactly the existing
averaged Tomita-Takesaki lift on the doubled router carrier.
-/
@[simp] theorem countModularData_modularHamiltonian_eq_relativeTomitaTakesakiOp
    (counts ref : RelativeCounts n) :
    (countModularData counts ref).modularHamiltonian =
      averagedTomitaTakesakiOp n (relativeCountDensity n counts ref) := by
  rw [InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularHamiltonian_eq_neg_log_rn]
  simp [countModularData,
    InfoGeometry.Canonical.RelativePotentialCountBridge.averagedTomitaTakesakiOp,
    InfoGeometry.Canonical.RelativePotentialCountBridge.averagedModularHamiltonian,
    InfoGeometry.Canonical.RelativePotentialCountBridge.meanLogDeltaProfile,
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

omit [Nonempty (Fin n)] in
/--
On the diagonal relative-count slice, the Hessian metric operator is exactly
the finite averaged Tomita-Takesaki lift.
-/
theorem metricOp_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice
    {H : HessianGeometry H₂} {x₀ : H₂}
    {counts ref : RelativeCounts n}
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) H x₀ counts ref) :
    H.metricOp x₀ =
      averagedTomitaTakesakiOp n (relativeCountDensity n counts ref) := by
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
    H.metricOp x₀ = averagedTomitaTakesakiOp n (relativeCountDensity n counts ref) :=
      metricOp_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice
        (n := n) hDiag
    _ = (countModularData counts ref).modularHamiltonian := by
      symm
      exact countModularData_modularHamiltonian_eq_relativeTomitaTakesakiOp counts ref

/-- Scalar diagonal weight carried by the raw count-side modular Hamiltonian. -/
noncomputable def countDiagonalScalar
    (counts ref : RelativeCounts n) : ℝ :=
  averagedModularHamiltonian n (relativeCountDensity n counts ref)

/--
Count-side arithmetic-mean criterion ensuring that the diagonal scalar lies on
the positive Hessian side rather than the signed/Krein side.
-/
theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (hsum : ∑ i : Fin n, relativeCountDensity n counts ref i ≤ (n : ℝ)) :
    0 ≤ countDiagonalScalar (n := n) counts ref := by
  let ρ : Fin n → ℝ := relativeCountDensity n counts ref
  have hcard_pos : 0 < n := by
    simpa using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin n)›)
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hcard_pos
  have hn_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hweight_pos : 0 < (n : ℝ)⁻¹ := by positivity
  have hρ_pos : ∀ i : Fin n, 0 < ρ i := by
    intro i
    dsimp [ρ, relativeCountDensity]
    exact div_pos (hcounts i) (href i)
  have hw_sum : (∑ i : Fin n, (n : ℝ)⁻¹) = 1 := by
    simp [hcard_pos.ne']
  have havg_pos : 0 < ∑ i : Fin n, (n : ℝ)⁻¹ * ρ i := by
    refine Finset.sum_pos ?_ Finset.univ_nonempty
    intro i hi
    exact mul_pos hweight_pos (hρ_pos i)
  have havg_le_one : (∑ i : Fin n, (n : ℝ)⁻¹ * ρ i) ≤ 1 := by
    calc
      ∑ i : Fin n, (n : ℝ)⁻¹ * ρ i = (n : ℝ)⁻¹ * ∑ i : Fin n, ρ i := by
        rw [Finset.mul_sum]
      _ ≤ (n : ℝ)⁻¹ * (n : ℝ) := by
        exact mul_le_mul_of_nonneg_left hsum hn_nonneg
      _ = 1 := by
        field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hcard_pos)]
  have hlog_le_zero : Real.log (∑ i : Fin n, (n : ℝ)⁻¹ * ρ i) ≤ 0 := by
    exact Real.log_nonpos havg_pos.le havg_le_one
  have hneglog_nonneg : 0 ≤ -Real.log (∑ i : Fin n, (n : ℝ)⁻¹ * ρ i) := by
    linarith
  have hjensen := InfoGeometry.Math.Convexity.neg_log_jensen_sum
      (w := fun _ : Fin n => (n : ℝ)⁻¹)
      (hw_nonneg := fun _ => hn_nonneg)
      (hw_sum := hw_sum)
      (x := ρ)
      (hx_pos := hρ_pos)
  have hrhs :
      (∑ i : Fin n, (n : ℝ)⁻¹ * -Real.log (ρ i)) = countDiagonalScalar (n := n) counts ref := by
    unfold countDiagonalScalar averagedModularHamiltonian meanLogDeltaProfile ρ
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    ring_nf
  have hbound_sum :
      -Real.log (∑ i : Fin n, (n : ℝ)⁻¹ * ρ i) ≤ ∑ i : Fin n, (n : ℝ)⁻¹ * -Real.log (ρ i) := by
    simpa using hjensen
  have hbound : -Real.log (∑ i : Fin n, (n : ℝ)⁻¹ * ρ i) ≤ countDiagonalScalar (n := n) counts ref := by
    rw [← hrhs]
    exact hbound_sum
  exact le_trans hneglog_nonneg hbound

/--
Concrete doubled-carrier Hessian geometry obtained directly from the count-side
arithmetic-mean bound.
-/
noncomputable def countDiagonalHessianGeometryOfRelativeCountDensitySumBound
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (hsum : ∑ i : Fin n, relativeCountDensity n counts ref i ≤ (n : ℝ)) : HessianGeometry H₂ :=
  InfoGeometry.Convex.Euclidean.scaledHessianGeometry
    (E := H₂)
    (countDiagonalScalar (n := n) counts ref)
    (countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card
      (n := n) counts ref hcounts href hsum)

/--
Concrete doubled-carrier Hessian geometry whose metric operator is the count-side
modular Hamiltonian scalar times the identity.
-/
noncomputable def countDiagonalHessianGeometry
    (counts ref : RelativeCounts n)
    (hNonneg : 0 ≤ countDiagonalScalar (n := n) counts ref) : HessianGeometry H₂ :=
  InfoGeometry.Convex.Euclidean.scaledHessianGeometry
    (E := H₂) (countDiagonalScalar (n := n) counts ref) hNonneg

-- theorem-class: bridge
omit [Nonempty (Fin n)] in
/--
The concrete count-driven diagonal Hessian geometry realizes the diagonal raw
count operator slice without any extra metric witness.
-/
theorem countDiagonalHessianGeometry_isDiagonalRelativeCountMetricSlice
    (counts ref : RelativeCounts n)
    (hNonneg : 0 ≤ countDiagonalScalar (n := n) counts ref)
    (x₀ : H₂) :
    IsDiagonalRelativeCountMetricSlice (n := n)
      (countDiagonalHessianGeometry (n := n) counts ref hNonneg) x₀ counts ref := by
  unfold IsDiagonalRelativeCountMetricSlice countDiagonalHessianGeometry countDiagonalScalar
  rw [InfoGeometry.Convex.Euclidean.scaledHessianGeometry_metricOp_eq_smul_id
    (E := H₂) (c := averagedModularHamiltonian n (relativeCountDensity n counts ref))
    (hc := hNonneg) (x := x₀)]
  rw [relativeModularHamiltonian_eq_diagonalAverage_rawLift (n := n) (counts := counts) (ref := ref)]

-- theorem-class: bridge
/--
The concrete count-driven diagonal Hessian geometry identifies its metric
operator with the raw averaged Tomita-Takesaki lift.
-/
theorem countDiagonalHessianGeometry_metricOp_eq_relativeTomitaTakesakiOp
    (counts ref : RelativeCounts n)
    (hNonneg : 0 ≤ countDiagonalScalar (n := n) counts ref)
    (x₀ : H₂) :
    (countDiagonalHessianGeometry (n := n) counts ref hNonneg).metricOp x₀ =
      averagedTomitaTakesakiOp n (relativeCountDensity n counts ref) := by
  rw [metricOp_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice
    (n := n)
    (H := countDiagonalHessianGeometry (n := n) counts ref hNonneg)
    (x₀ := x₀)
    (counts := counts)
    (ref := ref)]
  exact countDiagonalHessianGeometry_isDiagonalRelativeCountMetricSlice
    (n := n) counts ref hNonneg x₀

-- theorem-class: bridge
/--
The same concrete diagonal Hessian geometry identifies its metric operator with
induced continuum modular Hamiltonian.
-/
theorem countDiagonalHessianGeometry_metricOp_eq_countModularHamiltonian
    (counts ref : RelativeCounts n)
    (hNonneg : 0 ≤ countDiagonalScalar (n := n) counts ref)
    (x₀ : H₂) :
    (countDiagonalHessianGeometry (n := n) counts ref hNonneg).metricOp x₀ =
      (countModularData counts ref).modularHamiltonian := by
  calc
    (countDiagonalHessianGeometry (n := n) counts ref hNonneg).metricOp x₀
        = averagedTomitaTakesakiOp n (relativeCountDensity n counts ref) :=
          countDiagonalHessianGeometry_metricOp_eq_relativeTomitaTakesakiOp
            (n := n) counts ref hNonneg x₀
    _ = (countModularData counts ref).modularHamiltonian := by
      symm
      exact countModularData_modularHamiltonian_eq_relativeTomitaTakesakiOp counts ref

/--
The arithmetic-mean criterion produces a concrete diagonal Hessian geometry whose
metric operator is the raw averaged Tomita-Takesaki lift.
-/
theorem countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_relativeTomitaTakesakiOp
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (hsum : ∑ i : Fin n, relativeCountDensity n counts ref i ≤ (n : ℝ))
    (x₀ : H₂) :
    (countDiagonalHessianGeometryOfRelativeCountDensitySumBound
        (n := n) counts ref hcounts href hsum).metricOp x₀ =
      averagedTomitaTakesakiOp n (relativeCountDensity n counts ref) := by
  simpa [countDiagonalHessianGeometryOfRelativeCountDensitySumBound, countDiagonalHessianGeometry] using
    countDiagonalHessianGeometry_metricOp_eq_relativeTomitaTakesakiOp
      (n := n)
      counts ref
      (countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card
        (n := n) counts ref hcounts href hsum)
      x₀

/--
The arithmetic-mean criterion produces a concrete diagonal Hessian geometry whose
metric operator is the induced continuum modular Hamiltonian.
-/
theorem countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_countModularHamiltonian
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (hsum : ∑ i : Fin n, relativeCountDensity n counts ref i ≤ (n : ℝ))
    (x₀ : H₂) :
    (countDiagonalHessianGeometryOfRelativeCountDensitySumBound
        (n := n) counts ref hcounts href hsum).metricOp x₀ =
      (countModularData counts ref).modularHamiltonian := by
  simpa [countDiagonalHessianGeometryOfRelativeCountDensitySumBound, countDiagonalHessianGeometry] using
    countDiagonalHessianGeometry_metricOp_eq_countModularHamiltonian
      (n := n)
      counts ref
      (countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card
        (n := n) counts ref hcounts href hsum)
      x₀

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
      averagedTomitaTakesakiOp n (relativeCountDensity n counts ref) := by
  calc
    D * D = H.metricOp x₀ := compat.dirac_sq_eq_metric
    _ = averagedTomitaTakesakiOp n (relativeCountDensity n counts ref) :=
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
the Dirac square acts by scalar multiplication with the averaged modular
Hamiltonian on the diagonal slice.
-/
theorem dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice
    {D : H₂ →L[ℝ] H₂} {H : HessianGeometry H₂} {x₀ : H₂}
    {counts ref : RelativeCounts n}
    (compat : DiracMetricCompatibility (E := H₂) D H x₀)
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) H x₀ counts ref)
    (v : H₂) :
    D (D v) =
      averagedModularHamiltonian n (relativeCountDensity n counts ref) • v := by
  have hv :
      (D * D) v =
        (averagedTomitaTakesakiOp n (relativeCountDensity n counts ref)) v := by
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
averaged modular Hamiltonian scalar.
-/
theorem spectral_dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice
    (IST : InfoSpectralTriple H₂)
    {counts ref : RelativeCounts n}
    (hDiag : IsDiagonalRelativeCountMetricSlice (n := n) IST.H IST.x₀ counts ref)
    (v : H₂) :
    IST.D (IST.D v) =
      averagedModularHamiltonian n (relativeCountDensity n counts ref) • v :=
  dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice
    (n := n) IST.compatibility hDiag v

end SpectralTriple

end Router

end InfoGeometry.Canonical.DiagonalMetricModularBridge
