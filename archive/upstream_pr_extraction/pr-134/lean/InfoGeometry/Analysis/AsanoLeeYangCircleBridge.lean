import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Analysis.AsanoUnitDiskContractionBridge

/-!
# InfoGeometry.Analysis.AsanoLeeYangCircleBridge

Canonical Cayley Correspondence and Critical-Line Localization.

This module formalizes:
1. **Cayley Forward/Inverse Cancellation:**
   $$C^{-1}(C(s)) = s, \quad C(w) = \frac{1+w}{1-w}, \quad C^{-1}(z) = \frac{z-1}{z+1}$$
2. **Canonical Riemann Cayley Map & Inversion:**
   $$z(s) = \frac{s}{1-s}, \qquad s(z) = \frac{z}{1+z}$$
   $$s(z(s)) = s \ (\forall s \neq 1), \qquad z(s(z)) = z \ (\forall z \neq -1)$$
3. **Imaginary Axis Unit-Modulus Correspondence:**
   $$\operatorname{Re}(s) = 0 \implies \left\|\frac{1+s}{1-s}\right\| = 1$$
4. **Composed Centered Critical Parameterization:**
   $$s(E) = \frac{1}{2} + i E \implies \left\|C\left(s(E) - \frac{1}{2}\right)\right\| = 1$$
5. **Canonical Riemann Equivalence:**
   $$\forall s \neq 1, \quad \left\|\frac{s}{1-s}\right\| = 1 \iff \operatorname{Re}(s) = \frac{1}{2}$$
6. **Unit Circle Inverse Critical Line Localization:**
   $$\forall z \in S^1 \setminus \{-1\}, \quad \operatorname{Re}\left(\frac{z}{1+z}\right) = \frac{1}{2}$$
7. **Compositional Partition Root Transport:**
   $$Z_{\text{LY}}(z) = 0 \implies \|z\| = 1 \wedge z \neq -1 \implies \operatorname{Re}\left(\frac{z}{1+z}\right) = \frac{1}{2}$$

**Explicit Firewall:**
Lee--Yang zeros of a finite partition function $Z_{\text{LY}}(z) = 0$ map to $\operatorname{Re}(s) = 1/2$
under the canonical Cayley inverse $s = z/(1+z)$. This does NOT equate Lee--Yang zeros with
Riemann $\xi$-zeros until an explicit zero-set divisor identity $Z_{\text{prime}}(s/(1-s)) = G(s) \xi(s)$
($G(s) \neq 0$) is proven.
-/

noncomputable section

namespace InfoGeometry.Analysis.AsanoLeeYangCircle

open Complex
open InfoGeometry.Analysis.AsanoContractionNative
open InfoGeometry.Analysis.AsanoUnitDiskContraction

/-- Cayley transform w(s) = (1 + s) / (1 - s) -/
def cayleyForward (s : ℂ) : ℂ :=
  (1 + s) / (1 - s)

/-- Inverse Cayley transform s(w) = (w - 1) / (w + 1) -/
def cayleyInverse (w : ℂ) : ℂ :=
  (w - 1) / (w + 1)

/-- Canonical Riemann Cayley map z(s) = s / (1 - s) -/
def riemannCayleyForward (s : ℂ) : ℂ :=
  s / (1 - s)

/-- Canonical Riemann Cayley inverse s(z) = z / (1 + z) -/
def riemannCayleyInverse (z : ℂ) : ℂ :=
  z / (1 + z)

/-- Critical line coordinate s(E) = 1/2 + i E -/
def criticalLineCoord (E : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (E : ℂ)

/-- 🏆 THEOREM 1: Forward/Inverse cancellation for Cayley map -/
theorem cayley_inverse_forward (s : ℂ) (hs : s ≠ 1) :
    cayleyInverse (cayleyForward s) = s := by
  dsimp [cayleyForward, cayleyInverse]
  have h1 : 1 - s ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hs)
  have h_num : (1 + s) / (1 - s) - 1 = (2 * s) / (1 - s) := by
    field_simp [h1]
    ring
  have h_den : (1 + s) / (1 - s) + 1 = 2 / (1 - s) := by
    field_simp [h1]
    ring
  rw [h_num, h_den]
  field_simp [h1]

/-- 🏆 THEOREM 2: Canonical Riemann Cayley Forward/Inverse Cancellation:
    s(z(s)) = s for s ≠ 1 -/
theorem riemann_cayley_inverse_forward (s : ℂ) (hs : s ≠ 1) :
    riemannCayleyInverse (riemannCayleyForward s) = s := by
  dsimp [riemannCayleyForward, riemannCayleyInverse]
  have h1 : 1 - s ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hs)
  have h_den : 1 + s / (1 - s) = 1 / (1 - s) := by
    field_simp [h1]
    ring
  rw [h_den]
  field_simp [h1]

/-- 🏆 THEOREM 3: Canonical Riemann Cayley Inverse/Forward Cancellation:
    z(s(z)) = z for z ≠ -1 -/
theorem riemann_cayley_forward_inverse (z : ℂ) (hz : z ≠ -1) :
    riemannCayleyForward (riemannCayleyInverse z) = z := by
  dsimp [riemannCayleyForward, riemannCayleyInverse]
  have h1 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := by
      calc z = (1 + z) - 1 := by ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by ring
    exact hz this
  have h_den : 1 - z / (1 + z) = 1 / (1 + z) := by
    field_simp [h1]
    ring
  rw [h_den]
  field_simp [h1]

/-! The ordinary Cayley chart has the same two-sided cancellation API. -/

theorem cayley_forward_inverse (w : ℂ) (hw : w ≠ -1) :
    cayleyForward (cayleyInverse w) = w := by
  dsimp [cayleyForward, cayleyInverse]
  have h1 : 1 + w ≠ 0 := by
    intro h
    have hw' : w = (1 + w) - 1 := by ring
    rw [h] at hw'
    apply hw
    simpa using hw'
  have h1' : w + 1 ≠ 0 := by
    simpa [add_comm] using h1
  have h_num : 1 + (w - 1) / (w + 1) = 2 * w / (w + 1) := by
    field_simp [h1'] <;> ring_nf
  have h_den : 1 - (w - 1) / (w + 1) = 2 / (w + 1) := by
    field_simp [h1'] <;> ring_nf
  rw [h_num, h_den]
  field_simp [h1'] <;> ring_nf

/-- 🏆 THEOREM 4: Imaginary Axis Unit-Modulus Correspondence under Cayley Transform -/
theorem norm_cayley_eq_one_of_re_eq_zero (s : ℂ) (hre : s.re = 0) (hs : s ≠ 1) :
    ‖cayleyForward s‖ = 1 := by
  dsimp [cayleyForward]
  rw [norm_div]
  have h_sq_num : ‖1 + s‖^2 = 1 + s.im^2 := by
    have h1 : (1 + s).re = 1 := by simp [hre]
    have h2 : (1 + s).im = s.im := by simp
    calc ‖1 + s‖^2 = Complex.normSq (1 + s) := by rw [Complex.normSq_eq_norm_sq]
    _ = (1 + s).re * (1 + s).re + (1 + s).im * (1 + s).im := Complex.normSq_apply (1 + s)
    _ = 1 * 1 + s.im * s.im := by rw [h1, h2]
    _ = 1 + s.im^2 := by ring
  have h_sq_den : ‖1 - s‖^2 = 1 + s.im^2 := by
    have h1 : (1 - s).re = 1 := by simp [hre]
    have h2 : (1 - s).im = -s.im := by simp
    calc ‖1 - s‖^2 = Complex.normSq (1 - s) := by rw [Complex.normSq_eq_norm_sq]
    _ = (1 - s).re * (1 - s).re + (1 - s).im * (1 - s).im := Complex.normSq_apply (1 - s)
    _ = 1 * 1 + (-s.im) * (-s.im) := by rw [h1, h2]
    _ = 1 + s.im^2 := by ring
  have h_eq_sq : ‖1 + s‖^2 = ‖1 - s‖^2 := by rw [h_sq_num, h_sq_den]
  have h_den_pos : 0 < ‖1 - s‖ := by
    have h_ne : 1 - s ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hs)
    exact norm_pos_iff.mpr h_ne
  have h_eq_norm : ‖1 + s‖ = ‖1 - s‖ := by
    nlinarith [norm_nonneg (1 + s), h_den_pos, h_eq_sq]
  rw [h_eq_norm]
  exact div_self (ne_of_gt h_den_pos)

/-- 🏆 THEOREM 5: Composed Centered Critical Line to Unit Circle -/
theorem norm_cayley_centered_critical_eq_one (E : ℝ) :
    ‖cayleyForward (criticalLineCoord E - 1 / 2)‖ = 1 := by
  have hre : (criticalLineCoord E - 1 / 2).re = 0 := by
    dsimp [criticalLineCoord]
    simp
  have hs : criticalLineCoord E - 1 / 2 ≠ 1 := by
    intro h
    have : (criticalLineCoord E - 1 / 2).re = 1 := by rw [h, Complex.one_re]
    linarith
  exact norm_cayley_eq_one_of_re_eq_zero (criticalLineCoord E - 1 / 2) hre hs

/-- 🏆 THEOREM 6: Canonical Equivalence: ‖s / (1 - s)‖ = 1 ↔ Re(s) = 1/2 for s ≠ 1 -/
theorem norm_riemannCayley_eq_one_iff (s : ℂ) (hs : s ≠ 1) :
    ‖riemannCayleyForward s‖ = 1 ↔ s.re = 1 / 2 := by
  dsimp [riemannCayleyForward]
  have h_den_ne : 1 - s ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hs)
  have h_den_pos : 0 < ‖1 - s‖ := norm_pos_iff.mpr h_den_ne
  rw [norm_div]
  constructor
  · intro h_div
    have h_norm_eq : ‖s‖ = ‖1 - s‖ := by
      exact (div_eq_one_iff_eq (ne_of_gt h_den_pos)).mp h_div
    have h_sq_eq : ‖s‖^2 = ‖1 - s‖^2 := by rw [h_norm_eq]
    have h_s_sq : ‖s‖^2 = s.re^2 + s.im^2 := by
      calc ‖s‖^2 = Complex.normSq s := by rw [Complex.normSq_eq_norm_sq]
      _ = s.re * s.re + s.im * s.im := Complex.normSq_apply s
      _ = s.re^2 + s.im^2 := by ring
    have h_1s_sq : ‖1 - s‖^2 = (1 - s.re)^2 + s.im^2 := by
      have h1 : (1 - s).re = 1 - s.re := by simp
      have h2 : (1 - s).im = -s.im := by simp
      calc ‖1 - s‖^2 = Complex.normSq (1 - s) := by rw [Complex.normSq_eq_norm_sq]
      _ = (1 - s).re * (1 - s).re + (1 - s).im * (1 - s).im := Complex.normSq_apply (1 - s)
      _ = (1 - s.re) * (1 - s.re) + (-s.im) * (-s.im) := by rw [h1, h2]
      _ = (1 - s.re)^2 + s.im^2 := by ring
    rw [h_s_sq, h_1s_sq] at h_sq_eq
    have : s.re^2 = (1 - s.re)^2 := by linarith
    have : s.re^2 = 1 - 2 * s.re + s.re^2 := by
      calc s.re^2 = (1 - s.re)^2 := this
      _ = 1 - 2 * s.re + s.re^2 := by ring
    linarith
  · intro hre
    have h_s_sq : ‖s‖^2 = (1 / 2)^2 + s.im^2 := by
      calc ‖s‖^2 = Complex.normSq s := by rw [Complex.normSq_eq_norm_sq]
      _ = s.re * s.re + s.im * s.im := Complex.normSq_apply s
      _ = (1 / 2) * (1 / 2) + s.im * s.im := by rw [hre]
      _ = (1 / 2)^2 + s.im^2 := by ring
    have h_1s_sq : ‖1 - s‖^2 = (1 / 2)^2 + s.im^2 := by
      have h1 : (1 - s).re = 1 / 2 := by simp [hre]; ring
      have h2 : (1 - s).im = -s.im := by simp
      calc ‖1 - s‖^2 = Complex.normSq (1 - s) := by rw [Complex.normSq_eq_norm_sq]
      _ = (1 - s).re * (1 - s).re + (1 - s).im * (1 - s).im := Complex.normSq_apply (1 - s)
      _ = (1 / 2) * (1 / 2) + (-s.im) * (-s.im) := by rw [h1, h2]
      _ = (1 / 2)^2 + s.im^2 := by ring
    have h_eq_sq : ‖s‖^2 = ‖1 - s‖^2 := by rw [h_s_sq, h_1s_sq]
    have h_norm_eq : ‖s‖ = ‖1 - s‖ := by
      nlinarith [norm_nonneg s, h_den_pos, h_eq_sq]
    rw [h_norm_eq]
    exact div_self (ne_of_gt h_den_pos)

/-- 🏆 THEOREM 7: Unit Circle Inverse Maps to Critical Line:
    |z| = 1 ∧ z ≠ -1 ==> Re(z / (1 + z)) = 1/2 -/
theorem re_riemannCayleyInverse_eq_half_of_norm_eq_one {z : ℂ} (hz_norm : ‖z‖ = 1) (hz_ne : z ≠ -1) :
    (riemannCayleyInverse z).re = 1 / 2 := by
  dsimp [riemannCayleyInverse]
  have h1 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := by
      calc z = (1 + z) - 1 := by ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by ring
    exact hz_ne this
  have h_norm_sq : ‖z‖^2 = 1 := by rw [hz_norm, one_pow]
  have h_z_sq : z.re^2 + z.im^2 = 1 := by
    have : ‖z‖^2 = z.re^2 + z.im^2 := by
      calc ‖z‖^2 = Complex.normSq z := by rw [Complex.normSq_eq_norm_sq]
      _ = z.re * z.re + z.im * z.im := Complex.normSq_apply z
      _ = z.re^2 + z.im^2 := by ring
    rw [← this, h_norm_sq]
  have h_div_re : (z / (1 + z)).re = (z.re * (1 + z).re + z.im * (1 + z).im) / Complex.normSq (1 + z) := by
    rw [Complex.div_re]
    ring
  have h_den_normSq : Complex.normSq (1 + z) = (1 + z.re)^2 + z.im^2 := by
    have h1_re : (1 + z).re = 1 + z.re := by simp
    have h1_im : (1 + z).im = z.im := by simp
    calc Complex.normSq (1 + z) = (1 + z).re * (1 + z).re + (1 + z).im * (1 + z).im := Complex.normSq_apply (1 + z)
    _ = (1 + z.re) * (1 + z.re) + z.im * z.im := by rw [h1_re, h1_im]
    _ = (1 + z.re)^2 + z.im^2 := by ring
  have h1_re : (1 + z).re = 1 + z.re := by simp
  have h1_im : (1 + z).im = z.im := by simp
  rw [h_div_re, h_den_normSq, h1_re, h1_im]
  have h_num_simp : z.re * (1 + z.re) + z.im * z.im = 1 + z.re := by
    calc z.re * (1 + z.re) + z.im * z.im = z.re + (z.re^2 + z.im^2) := by ring
    _ = z.re + 1 := by rw [h_z_sq]
    _ = 1 + z.re := by ring
  have h_den_simp : (1 + z.re)^2 + z.im^2 = 2 * (1 + z.re) := by
    calc (1 + z.re)^2 + z.im^2 = 1 + 2 * z.re + (z.re^2 + z.im^2) := by ring
    _ = 1 + 2 * z.re + 1 := by rw [h_z_sq]
    _ = 2 * (1 + z.re) := by ring
  rw [h_num_simp, h_den_simp]
  have h_1z_re_ne : 1 + z.re ≠ 0 := by
    intro h
    have hz_re : z.re = -1 := by linarith
    have hz_im_sq : z.im^2 = 0 := by
      have : (-1 : ℝ)^2 + z.im^2 = 1 := by rw [← hz_re]; exact h_z_sq
      linarith
    have hz_im : z.im = 0 := sq_eq_zero_iff.mp hz_im_sq
    have hz_eq : z = -1 := by
      apply Complex.ext
      · simp [hz_re]
      · simp [hz_im]
    exact hz_ne hz_eq
  calc (1 + z.re) / (2 * (1 + z.re)) = (1 * (1 + z.re)) / (2 * (1 + z.re)) := by ring
  _ = 1 / 2 := by rw [mul_div_mul_right 1 2 h_1z_re_ne]

/-- 🏆 THEOREM 8: Compositional Partition Root Transport:
    If a partition root lies on the unit circle (|z| = 1, z ≠ -1),
    its canonical Cayley preimage lies on the critical line Re(s) = 1/2 -/
theorem unitCircle_point_to_critical_line
    {z : ℂ} (hz_circle : ‖z‖ = 1) (hz_ne : z ≠ -1) :
    (riemannCayleyInverse z).re = 1 / 2 :=
  re_riemannCayleyInverse_eq_half_of_norm_eq_one hz_circle hz_ne

@[deprecated unitCircle_point_to_critical_line (since := "2026-08-16")]
theorem partition_root_on_unitCircle_to_critical_line
    {z : ℂ} (hz_circle : ‖z‖ = 1) (hz_ne : z ≠ -1) :
    (riemannCayleyInverse z).re = 1 / 2 :=
  unitCircle_point_to_critical_line hz_circle hz_ne

/--
Conditional Lee--Yang composition.  The root-localization premise is kept
explicit because the native Asano owners do not provide an unconditional
partition-specific unit-circle theorem for an arbitrary `Z`.
-/
theorem partition_root_to_critical_line_of_unitCircle_localization
    {Z : ℂ → ℂ} {z : ℂ}
    (hroot : Z z = 0)
    (hLeeYang : ∀ w, Z w = 0 → ‖w‖ = 1)
    (hz_ne : z ≠ -1) :
    (riemannCayleyInverse z).re = 1 / 2 := by
  exact re_riemannCayleyInverse_eq_half_of_norm_eq_one
    (hLeeYang z hroot) hz_ne

/--
Reusable root-to-critical-line transport under intrinsic geometric hypotheses:
zero-freeness on the open unit disk and reciprocal symmetry of the zero set.

This removes the answer-shaped Lee--Yang premise `∀ w, Z w = 0 → ‖w‖ = 1` in
favor of two structural hypotheses from which unit-circle localization follows.
-/
theorem partition_root_to_critical_line_of_disk_free_reciprocal_symmetry
    {Z : ℂ → ℂ} {z : ℂ}
    (h_disk_free : ∀ w : ℂ, ‖w‖ < 1 → Z w ≠ 0)
    (h_symm : ∀ w : ℂ, w ≠ 0 → (Z w = 0 ↔ Z w⁻¹ = 0))
    (hroot : Z z = 0)
    (hz_ne : z ≠ -1) :
    (riemannCayleyInverse z).re = 1 / 2 := by
  have h_norm_one : ‖z‖ = 1 := by
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · exfalso
      exact h_disk_free z hlt hroot
    · exact heq
    · exfalso
      have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0] at hgt
        norm_num at hgt
      have hroot_inv : Z z⁻¹ = 0 := (h_symm z hz0).mp hroot
      have h_inv_lt : ‖z⁻¹‖ < 1 := by
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hgt
      exact h_disk_free z⁻¹ h_inv_lt hroot_inv
  exact re_riemannCayleyInverse_eq_half_of_norm_eq_one h_norm_one hz_ne

end InfoGeometry.Analysis.AsanoLeeYangCircle
