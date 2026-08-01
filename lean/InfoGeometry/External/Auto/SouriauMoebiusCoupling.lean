import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Souriau--Möbius Coupling

This module records the analytic/arithmetic closing link:
the scalar Souriau inverse-temperature slot `β` is coupled to the Möbius
parity, so the graded/Witten partition is the reciprocal zeta function.

Lean-honest point: `riemannZeta` is implemented as a meromorphic function with
a junk value at the pole.  Therefore the critical vanishing is stated on the
punctured neighbourhood `𝓝[≠] 1`, which is the exact analytic meaning of
`β → 1`.
-/

noncomputable section

open Filter Complex Topology
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.GrandUnification.SouriauMoebius

/-- The ungraded Bost--Connes/Souriau partition: `Z(β)=ζ(β)`. -/
def bosonicPartitionFunction (β : ℂ) : ℂ :=
  riemannZeta β

/-- The Möbius-graded Witten index: `Z_gr(β)=1/ζ(β)`. -/
def gradedPartitionFunction (β : ℂ) : ℂ :=
  (riemannZeta β)⁻¹

/-- The Möbius Dirichlet series model of the graded partition. -/
def moebiusLSeriesPartition (β : ℂ) : ℂ :=
  LSeries (fun n => (μ n : ℂ)) β

/-- On the half-plane of absolute convergence, the Möbius Dirichlet series is
exactly the reciprocal zeta partition. -/
theorem moebius_lseries_eq_reciprocal_zeta {β : ℂ} (hβ : 1 < β.re) :
    moebiusLSeriesPartition β = gradedPartitionFunction β := by
  unfold moebiusLSeriesPartition gradedPartitionFunction
  have hmul := LSeries_one_mul_Lseries_moebius (s := β) hβ
  rw [LSeries_one_eq_riemannZeta hβ] at hmul
  have hmul' : LSeries (fun n => (μ n : ℂ)) β * riemannZeta β = 1 := by
    simpa [mul_comm] using hmul
  exact eq_inv_of_mul_eq_one_left hmul'

/-- Equivalent product statement: ungraded partition times Möbius-graded partition is one. -/
theorem bosonic_mul_moebius_partition {β : ℂ} (hβ : 1 < β.re) :
    bosonicPartitionFunction β * moebiusLSeriesPartition β = 1 := by
  unfold bosonicPartitionFunction moebiusLSeriesPartition
  simpa [LSeries_one_eq_riemannZeta hβ] using
    (LSeries_one_mul_Lseries_moebius (s := β) hβ)

/-- Critical cancellation: as `β → 1` through punctured complex neighbourhoods,
the Möbius-graded Witten index tends to zero. -/
theorem graded_partition_vanishes_at_one_punctured :
    Tendsto gradedPartitionFunction (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
  have hnum : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 (1 - 1)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using h.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun s : ℂ => ((s - 1) * riemannZeta s)⁻¹)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
    simpa using (riemannZeta_residue_one.inv₀ one_ne_zero)
  have hquot : Tendsto (fun s : ℂ => (s - 1) * (((s - 1) * riemannZeta s)⁻¹))
      (𝓝[≠] (1 : ℂ)) (𝓝 (0 * 1)) := hnum.mul hden
  have heq : (fun s : ℂ => (s - 1) * (((s - 1) * riemannZeta s)⁻¹))
      =ᶠ[𝓝[≠] (1 : ℂ)] gradedPartitionFunction := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    simp [gradedPartitionFunction]
    field_simp [hs1]
  simpa using hquot.congr' heq

end InfoGeometry.GrandUnification.SouriauMoebius
