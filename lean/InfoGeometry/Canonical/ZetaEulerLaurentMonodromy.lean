import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.EulerLaurentDerivation
import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
import InfoGeometry.Arithmetic.ActualZetaPoleAsymptoticBridge
import InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy
import InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

/-!
# Euler--Laurent and zeta logarithmic-derivative readouts

This owner is the theorem-safe core of the Euler/dlog/divisor/monodromy
chain.  The formal Laurent lane supplies Euler charges and residues; the
existing divisor owner transports those charges to winding data; and the
actual zeta lane is exposed only on the half-plane where Mathlib proves the
von-Mangoldt identity.  No Hilbert--Pólya operator, global meromorphic divisor
classification, or de Rham cohomology identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZetaEulerLaurentMonodromy

open InfoGeometry.Algebra.EulerLaurentDerivation
open InfoGeometry.Algebraic.EulerLaurentHestenesDivisor
open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
open InfoGeometry.Arithmetic.ActualZetaPoleAsymptoticBridge
open InfoGeometry.Arithmetic.IndexTheorem
open InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy
open InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod
open InfoGeometry.Clifford.HestenesWindingRotor
open ArithmeticFunction
open Complex
open Filter
open scoped _root_.Topology
open scoped LSeries.notation

/-! ## Euler and formal logarithmic differential -/

theorem euler_charge_of_monomial (n : ℤ) (a : ℂ) :
    euler (monomial n a) = monomial n ((n : ℂ) * a) := by
  exact euler_monomial n a

theorem formal_logarithmic_residue_of_local_divisor
    (F : LocalDivisorData ℂ) :
    residue (chargeForm F) = F.order := by
  exact residue_dlog_equals_divisor_order F

theorem formal_normal_form_residue_of_local_divisor
    (F : LocalLaurentNormalForm (R := ℂ)) :
    residue (chargeForm (localDivisorDataOfNormalForm F)) = F.order := by
  exact residue_normalForm_charge F

/-! ## Finite monodromy readout -/

theorem finite_divisor_charge_transports_to_winding
    {G : Type*} [CommGroup G]
    {ι : Type*} [Fintype ι]
    (r : G) (order : ι → ℤ) :
    winding r (finiteKernelIndex (divisorKernelComplex order)) =
      ∏ a : ι, winding r (order a) := by
  exact winding_of_divisor_kernel_index r order

theorem finite_residue_charge_transports_to_winding
    {G : Type*} [CommGroup G]
    {ι : Type*} [Fintype ι]
    (r : G) (data : ι → LocalDivisorData ℤ) :
    winding r (finiteKernelIndex
      (divisorKernelComplex (fun a => (data a).order))) =
      winding r (∑ a : ι, residue (chargeForm (data a))) := by
  exact winding_of_residue_kernel_index r data

/-! ## Actual zeta logarithmic derivative and pole normalization -/

theorem actual_zeta_logDerivative_eq_vonMangoldt
    {s : ℂ} (hs : 1 < s.re) :
    actualRiemannZetaLogDerivative s = L ↗Λ s := by
  exact actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries hs

theorem actual_zeta_rescaled_pole_tendsto :
    Tendsto
      (fun β : ℝ => ((β - 1 : ℝ) : ℂ) * riemannZeta (β : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (1 : ℂ)) := by
  exact actualRiemannZeta_rescaled_pole_tendsto

theorem normalized_formal_pole_period
    (rho : ℂ) (m : ℤ) {R : ℝ} (hR : 0 < R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    (∮ z in C(rho, R), logarithmicPole rho m z) =
      - (m : ℂ) := by
  exact normalized_logarithmicPole_circleIntegral rho m hR

end InfoGeometry.Canonical.ZetaEulerLaurentMonodromy
