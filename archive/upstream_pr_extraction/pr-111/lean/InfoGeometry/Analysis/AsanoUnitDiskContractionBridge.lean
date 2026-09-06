import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Analysis.AsanoContractionNative

/-!
# InfoGeometry.Analysis.AsanoUnitDiskContractionBridge

Asano Contraction on Closed and Open Unit Disks, Product Radius Bounds,
and Lee-Yang Unit Circle Root Localization.

This module formalizes:
1. **Product Radius Inclusion for Disks:**
   $$- \overline{\mathbb{D}}_{r_1} \cdot \overline{\mathbb{D}}_{r_2} \subseteq \overline{\mathbb{D}}_{r_1 r_2}$$
2. **Unit Disk Invariance:**
   $$- \overline{\mathbb{D}} \cdot \overline{\mathbb{D}} \subseteq \overline{\mathbb{D}}$$
3. **Contracted Root Modulus Bound:**
   $$z \in \text{signedProductSet}(\overline{\mathbb{D}}, \overline{\mathbb{D}}) \implies \|z\| \le 1$$
4. **Exterior Points are not in the Closed Unit Disk:**
   $$\|z\| > 1 \implies z \notin \overline{\mathbb{D}}$$
5. **Inversion Symmetry Forces Zeros to the Unit Circle:**
   $$\|z\| \le 1 \wedge \|z^{-1}\| \le 1 \implies \|z\| = 1$$
-/

noncomputable section

namespace InfoGeometry.Analysis.AsanoUnitDiskContraction

open InfoGeometry.Analysis.AsanoContractionNative

/-- Closed disk of radius r in the complex plane -/
def closedDisk (r : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ ≤ r}

/-- Open disk of radius r in the complex plane -/
def openDisk (r : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ < r}

/-- The origin is in the closed unit disk; it must not be supplied as an
    `outside` hypothesis for the unit-disk specialization. -/
theorem zero_mem_closedDisk_one : (0 : ℂ) ∈ closedDisk 1 := by
  simp [closedDisk]

/-- 🏆 THEOREM 1: Product of Closed Disks is Contained in the Product-Radius Disk -/
theorem signedProduct_closedDisks_subset (r₁ r₂ : ℝ) (hr₁ : 0 ≤ r₁) :
    signedProductSet (closedDisk r₁) (closedDisk r₂) ⊆ closedDisk (r₁ * r₂) := by
  intro z hz
  rcases hz with ⟨u, hu, v, hv, hz_eq⟩
  dsimp [closedDisk] at hu hv ⊢
  rw [hz_eq]
  simp only [norm_neg, norm_mul]
  exact mul_le_mul hu hv (norm_nonneg v) hr₁

/-- 🏆 THEOREM 2: Unit Disk Stability Under Signed Product Obstruction -/
theorem signedProduct_unitDisks_subset :
    signedProductSet (closedDisk 1) (closedDisk 1) ⊆ closedDisk 1 := by
  have h := signedProduct_closedDisks_subset 1 1 (by norm_num)
  simpa only [mul_one] using h

/-- 🏆 THEOREM 3: Contracted Zero Modulus Bound from Asano Disk Obstruction -/
theorem contracted_zero_norm_le_one_of_mem_signedProduct
    {z : ℂ} (hz : z ∈ signedProductSet (closedDisk 1) (closedDisk 1)) :
    ‖z‖ ≤ 1 := by
  exact signedProduct_unitDisks_subset hz

/-- 🏆 THEOREM 4: Exterior points avoid the closed unit disk.

This is the geometric fact used before any Asano non-vanishing theorem.  It
does not assert polynomial non-vanishing: that requires a genuine zero-free
outside hypothesis for the concrete polynomial. -/
theorem not_mem_closedDisk_one_of_norm_gt_one {z : ℂ} (hz_outside : 1 < ‖z‖) :
    z ∉ closedDisk 1 := by
  intro hz_mem
  dsimp [closedDisk] at hz_mem
  linarith

/-- 🏆 THEOREM 5: Inversion Symmetry Forces Roots to the Unit Circle:
    If ‖z‖ ≤ 1 and ‖1/z‖ ≤ 1, then ‖z‖ = 1 -/
theorem unitCircle_of_inversion_symmetric_roots {z : ℂ} (hz_ne : z ≠ 0)
    (h_le : ‖z‖ ≤ 1) (h_inv_le : ‖z⁻¹‖ ≤ 1) :
    ‖z‖ = 1 := by
  have h_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
  rw [norm_inv] at h_inv_le
  have h_ge : 1 ≤ ‖z‖ := by
    have h_inv : 1 / ‖z‖ ≤ 1 := by simpa only [one_div] using h_inv_le
    exact (div_le_one₀ h_norm_pos).mp h_inv
  exact le_antisymm h_le h_ge

end InfoGeometry.Analysis.AsanoUnitDiskContraction
