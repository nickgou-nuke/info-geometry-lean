import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.BostConnes.BostConnesThermofield

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

theorem riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_strip
    {s : ℂ} (hRe : 0 < s.re) (hRe' : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hRe
    simp at hRe
  have hs1 : s - 1 ≠ 0 := by
    intro hs
    have hs' : s = 1 := sub_eq_zero.mp hs
    rw [hs'] at hRe'
    norm_num at hRe'
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hRe
  have hcompleted : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have h := riemannZeta_def_of_ne_zero hs0
    exact (eq_div_iff hGamma).mp h |>.symm
  unfold riemannXi
  rw [hcompleted]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact (hs0 h).elim
      · exact (hs1 h).elim
    · rcases mul_eq_zero.mp h with hZ | hG
      · exact hZ
      · exact (hGamma hG).elim
  · intro h
    simp [h]

noncomputable def riemannXiCayley (z : ℂ) : ℂ :=
  riemannXi (cayleyToTemperature z)

theorem cayleyToTemperature_inv_eq_one_sub
    {z : ℂ} (hz : z ≠ 0) (hz' : 1 + z ≠ 0) :
    cayleyToTemperature z⁻¹ = 1 - cayleyToTemperature z := by
  unfold cayleyToTemperature
  field_simp [hz, hz']
  have hden : z + 1 ≠ 0 := by simpa [add_comm] using hz'
  rw [show 1 + z = z + 1 by ring, div_self hden]
  ring

theorem riemannXiCayley_inv_eq
    {z : ℂ} (hz : z ≠ 0) (hz' : 1 + z ≠ 0) :
    riemannXiCayley z⁻¹ = riemannXiCayley z := by
  unfold riemannXiCayley
  rw [cayleyToTemperature_inv_eq_one_sub hz hz',
    InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi_one_sub]

/-- The Cayley-composed completed Xi zero locus is invariant under the
involution `z ↦ z⁻¹` on its domain. -/
theorem riemannXiCayley_zero_inv_iff
    {z : ℂ} (hz : z ≠ 0) (hz' : 1 + z ≠ 0) :
    riemannXiCayley z⁻¹ = 0 ↔ riemannXiCayley z = 0 := by
  rw [riemannXiCayley_inv_eq hz hz']

theorem riemannXiCayley_zero_iff_riemannZeta_zero_of_strip
    {s : ℂ} (hRe : 0 < s.re) (hRe' : s.re < 1) :
    riemannZeta s = 0 ↔
      riemannXiCayley (cayleyToFugacity s) = 0 := by
  have hs1 : 1 - s ≠ 0 := by
    intro hs
    have hs' : s = 1 := (sub_eq_zero.mp hs).symm
    rw [hs'] at hRe'
    norm_num at hRe'
  rw [riemannXiCayley, cayleyToTemperature_cayleyToFugacity s hs1]
  exact (riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_strip hRe hRe').symm

/-! ## Native centered-coordinate and arithmetic readouts -/

open BostConnesThermofield

/-! The centered coordinate is owned by `RiemannZetaEquivalences`; this is its
functional-reflection identity, kept separate from Xi symmetry. -/
theorem toSymmetryAdapted_one_sub (s : ℂ) :
    toSymmetryAdapted (1 - s) = -toSymmetryAdapted s := by
  unfold toSymmetryAdapted
  ring

/-! The completed Xi readout is even in the centered coordinate. -/
theorem symmetryAdaptedXi_reflection (z : ℂ) :
    symmetryAdaptedXi (-z) = symmetryAdaptedXi z := by
  exact (symmetryAdaptedXi_is_even z).symm

/-! The same reflection is inversion in the existing Cayley coordinate. -/
theorem cayley_reflection_eq_inverse (s : ℂ) :
    cayleyToFugacity (1 - s) = (cayleyToFugacity s)⁻¹ :=
  cayleyToFugacity_one_sub_eq_inv s

/-! The critical line is exactly the Cayley unit-circle locus. -/
theorem criticalLine_iff_cayley_unitCircle_native (s : ℂ) :
    OnCriticalLine s ↔
      OnLeeYangCircle (cayleyToFugacity s) :=
  criticalLine_iff_cayley_unitCircle s

/-! The arithmetic Bost--Connes readout is the canonical Möbius/L-series
identity, not a KMS or C*-dynamical theorem. -/
theorem moebius_readout_eq_reciprocal_riemannZeta
    (beta : ℝ) (hbeta : beta > 1) :
    (moebiusLSeriesReadout beta : ℂ) =
      (riemannZeta (beta : ℂ))⁻¹ :=
  ofReal_moebiusLSeriesReadout_eq_reciprocal_zeta beta hbeta

/-! On the open critical strip, the existing Cayley Xi bridge transfers the
zero question to the ordinary Riemann zeta zero question. -/
theorem cayleyXi_zero_iff_zeta_zero_in_strip
    {s : ℂ} (hRe : 0 < s.re) (hRe' : s.re < 1) :
    riemannXiCayley (cayleyToFugacity s) = 0 ↔
      riemannZeta s = 0 := by
  exact (riemannXiCayley_zero_iff_riemannZeta_zero_of_strip hRe hRe').symm

/-! Compact packet of the independent native closure facts. -/
theorem native_riemann_zeta_cayley_bost_connes_closure
    (s : ℂ) (beta : ℝ) (hbeta : beta > 1) :
    toSymmetryAdapted (1 - s) = -toSymmetryAdapted s ∧
    riemannXi (1 - s) = riemannXi s ∧
    cayleyToFugacity (1 - s) = (cayleyToFugacity s)⁻¹ ∧
    (moebiusLSeriesReadout beta : ℂ) =
      (riemannZeta (beta : ℂ))⁻¹ := by
  exact ⟨toSymmetryAdapted_one_sub s,
    riemannXi_one_sub s,
    cayley_reflection_eq_inverse s,
    moebius_readout_eq_reciprocal_riemannZeta beta hbeta⟩

/-! ## Homogeneous two-lane coordinates -/

abbrev HomogeneousLane : Type := ℂ × ℂ

/-- The two homogeneous lanes `(p,q) = (s,1-s)`. -/
def homogeneousLanes (s : ℂ) : HomogeneousLane :=
  (s, 1 - s)

/-- Functional reflection is the swap of the two homogeneous lanes. -/
def homogeneousSwap : HomogeneousLane → HomogeneousLane :=
  fun z => (z.2, z.1)

/-- The split Cartan involution on the two homogeneous lanes. -/
def homogeneousEpsilon : HomogeneousLane → HomogeneousLane :=
  fun z => (z.1, -z.2)

/-- The real square-minus-one quarter-turn on the two lanes. -/
def homogeneousK : HomogeneousLane → HomogeneousLane :=
  fun z => (-z.2, z.1)

theorem homogeneousLanes_one_sub (s : ℂ) :
    homogeneousLanes (1 - s) =
      homogeneousSwap (homogeneousLanes s) := by
  unfold homogeneousLanes homogeneousSwap
  congr 1 <;> ring

/-- The projective coordinate of a homogeneous pair. -/
def homogeneousTau (z : HomogeneousLane) : ℂ :=
  z.1 / z.2

theorem homogeneousTau_lanes (s : ℂ) :
    homogeneousTau (homogeneousLanes s) = cayleyToFugacity s := by
  rfl

theorem homogeneousTau_swap_eq_inv
    {p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    homogeneousTau (homogeneousSwap (p, q)) =
      (homogeneousTau (p, q))⁻¹ := by
  unfold homogeneousTau homogeneousSwap
  field_simp [hp, hq]

theorem homogeneousTau_K_eq_neg_inv
    {p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    homogeneousTau (homogeneousK (p, q)) =
      -(homogeneousTau (p, q))⁻¹ := by
  unfold homogeneousTau homogeneousK
  field_simp [hp, hq]

/-! A determinant-one diagonal action on the two lanes. -/
def diagonalLaneFlow (a : ℂˣ) : HomogeneousLane → HomogeneousLane :=
  fun z => ((a : ℂ) * z.1, (a⁻¹ : ℂ) * z.2)

theorem diagonalLaneFlow_tau
    (a : ℂˣ) {p q : ℂ} (hq : q ≠ 0) :
    homogeneousTau (diagonalLaneFlow a (p, q)) =
      (a : ℂ) ^ 2 * homogeneousTau (p, q) := by
  unfold homogeneousTau diagonalLaneFlow
  field_simp [hq, Units.ne_zero a]

theorem homogeneousSwap_diagonalLaneFlow
    (a : ℂˣ) (z : HomogeneousLane) :
    homogeneousSwap (diagonalLaneFlow a z) =
      diagonalLaneFlow a⁻¹ (homogeneousSwap z) := by
  rcases z with ⟨p, q⟩
  unfold homogeneousSwap diagonalLaneFlow
  simp [mul_comm]

def zetaDiskCoordinate (s : ℂ) : ℂ :=
  (s - 1) / s

theorem zetaDiskCoordinate_eq_neg_inv_cayley
    {s : ℂ} (hs : s ≠ 0) :
    zetaDiskCoordinate s =
      -(cayleyToFugacity s)⁻¹ := by
  unfold zetaDiskCoordinate cayleyToFugacity
  field_simp [hs]
  ring

theorem riemannXi_homogeneous_swap
    {p q : ℂ} (hpq : p + q ≠ 0) :
    riemannXi (p / (p + q)) =
      riemannXi (q / (p + q)) := by
  have hq : q / (p + q) = 1 - p / (p + q) := by
    field_simp [hpq]
    ring
  rw [hq, riemannXi_one_sub]

theorem native_homogeneous_xi_cayley_closure
    (s : ℂ) :
    homogeneousLanes (1 - s) =
        homogeneousSwap (homogeneousLanes s) ∧
    homogeneousTau (homogeneousLanes s) =
        cayleyToFugacity s ∧
    riemannXi (s / (s + (1 - s))) =
        riemannXi ((1 - s) / (s + (1 - s))) := by
  have hsum : s + (1 - s) ≠ 0 := by
    norm_num
  exact ⟨homogeneousLanes_one_sub s,
    homogeneousTau_lanes s,
    riemannXi_homogeneous_swap (p := s) (q := 1 - s) hsum⟩

end InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
