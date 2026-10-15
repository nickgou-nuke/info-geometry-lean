import InfoGeometry.Canonical.HarmonicWeakHorizonBridge
import InfoGeometry.Canonical.ParaHyperkahlerHodgeDecompositionBridge
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Tactic.Abel

/-!
# Weak-Value Mass Parameter and Bogoliubov–de Gennes Doublet Condensation

This module formalizes:
1. The scalar AAV quotient mass parameter on harmonic Hodge doublets.
2. The categorical condensation of massless lightcone rays into massive
   Bogoliubov–de Gennes (BdG) doublets via horizon weak-value amplification in an
   ambient preadditive category `C`.

All properties are established via standalone definitions, lemmas, and theorems
with complete proofs.
-/

namespace InfoGeometry.Physics.HarmonicWeakHorizonBdG

open InfoGeometry.Canonical.HarmonicWeakHorizon
open InfoGeometry.Canonical.ParaHyperkahlerHodgeDecompositionBridge

/-! ### 1. Scalar Weak-Value Mass Parameter on Harmonic Doublets -/

/-- The scalar weak-value mass parameter is well-defined on the nonzero
overlap chart. -/
theorem weakValueMass_denominator_identity (num den : ℝ) (hden : den ≠ 0) :
    den * horizonWeakValue num den = num := by
  exact InfoGeometry.Canonical.ZornModularAAV.weak_value_amplification_scaling
    num den den rfl hden

/-- A small overlap yields a large absolute weak-value mass when the numerator
does not cancel. This is a finite scalar estimate. -/
theorem weakValueMass_abs_gt (num den threshold : ℝ) (hden : den ≠ 0)
    (hlarge : threshold * |den| < |num|) :
    threshold < |horizonWeakValue num den| := by
  rw [horizonWeakValue, InfoGeometry.Canonical.ZornModularAAV.aharonovWeakValue,
    abs_div]
  exact (lt_div_iff₀ (abs_pos.mpr hden)).2 (by simpa [mul_comm] using hlarge)

/-- Consequently, the square of the weak-value mass parameter exceeds the
square of any nonnegative threshold satisfying the noncancellation bound. -/
theorem weakValueMass_sq_gt (num den threshold : ℝ) (hden : den ≠ 0)
    (hthreshold : 0 ≤ threshold)
    (hlarge : threshold * |den| < |num|) :
    threshold ^ 2 < (horizonWeakValue num den) ^ 2 := by
  have h := weakValueMass_abs_gt num den threshold hden hlarge
  have habs : |horizonWeakValue num den| ^ 2 =
      (horizonWeakValue num den) ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|horizonWeakValue num den| - threshold)]

/-- On harmonic doublets, using the weak value as the BdG mass parameter
produces the existing mass-square action in both components. The kinetic
Hodge-Laplacian terms vanish by the harmonic projection theorem. -/
theorem weakValueMass_harmonic_doublet_square (num den : ℝ) (hden : den ≠ 0)
    (γ₁ γ₂ : PolarizedHodgeForm ℝ) :
    den * horizonWeakValue num den = num ∧
      let m := horizonWeakValue num den
      PolarizedHodgeForm.bdgZorn m (PolarizedHodgeForm.bdgZorn m
        (PolarizedHodgeForm.projHarmonic γ₁,
         PolarizedHodgeForm.projHarmonic γ₂)) =
        ((m * m) • PolarizedHodgeForm.projHarmonic γ₁,
         (m * m) • PolarizedHodgeForm.projHarmonic γ₂) := by
  constructor
  · exact weakValueMass_denominator_identity num den hden
  · dsimp
    rw [PolarizedHodgeForm.bdgZorn_sq_eq_klein_gordon]
    rw [hodgeLaplacian_on_harmonic γ₁, hodgeLaplacian_on_harmonic γ₂]
    simp

end InfoGeometry.Physics.HarmonicWeakHorizonBdG

namespace InfoGeometry.Physics.BdGCondensation

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 2. Horizon Weak-Value Amplification -/

/-- Transition overlap between pre-selected incoming and post-selected outgoing horizon sheets. -/
@[inline]
def horizonTransitionOverlap {Ω₀ Ω : C} (i_in : Ω₀ ⟶ Ω) (p_out : Ω ⟶ Ω₀) : Ω₀ ⟶ Ω₀ :=
  i_in ≫ p_out

/-- The AAV weak value of a cross-seam horizon operator `V` under near-orthogonal post-selection. -/
@[inline]
def weakValueObservable {Ω₀ Ω : C} (i_in : Ω₀ ⟶ Ω) (p_out : Ω ⟶ Ω₀)
    (V : Ω ⟶ Ω) (sigma_inv : Ω₀ ⟶ Ω₀) : Ω₀ ⟶ Ω₀ :=
  (i_in ≫ V ≫ p_out) ≫ sigma_inv

/-- Weak-value reconstruction: `A_w ≫ σ = i_in ≫ V ≫ p_out`. -/
theorem weak_value_amplification_relation {Ω₀ Ω : C}
    (i_in : Ω₀ ⟶ Ω) (p_out : Ω ⟶ Ω₀) (V : Ω ⟶ Ω) (sigma_inv : Ω₀ ⟶ Ω₀)
    (h_inv : sigma_inv ≫ horizonTransitionOverlap i_in p_out = 𝟙 Ω₀) :
    weakValueObservable i_in p_out V sigma_inv ≫ horizonTransitionOverlap i_in p_out =
    i_in ≫ V ≫ p_out := by
  dsimp [weakValueObservable]
  rw [Category.assoc, h_inv, Category.comp_id]

/-! ### 3. Nambu Biproduct Doublet Framework -/

/-- Endomorphism reconstruction from 2x2 biproduct blocks. -/
theorem biproduct_endomorphism_reconstruct {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E) (T : E ⟶ E) :
    T = p1 ≫ (i1 ≫ T ≫ p1) ≫ i1 +
        p1 ≫ (i1 ≫ T ≫ p2) ≫ i2 +
        p2 ≫ (i2 ≫ T ≫ p1) ≫ i1 +
        p2 ≫ (i2 ≫ T ≫ p2) ≫ i2 := by
  calc
    T = 𝟙 E ≫ T ≫ 𝟙 E := by simp only [Category.id_comp, Category.comp_id]
    _ = (p1 ≫ i1 + p2 ≫ i2) ≫ T ≫ (p1 ≫ i1 + p2 ≫ i2) := by rw [h_decomp]
    _ = ((p1 ≫ i1 + p2 ≫ i2) ≫ T) ≫ (p1 ≫ i1 + p2 ≫ i2) := by simp only [Category.assoc]
    _ = ((p1 ≫ i1) ≫ T + (p2 ≫ i2) ≫ T) ≫ (p1 ≫ i1 + p2 ≫ i2) := by rw [Preadditive.add_comp]
    _ = ((p1 ≫ i1) ≫ T) ≫ (p1 ≫ i1) + ((p1 ≫ i1) ≫ T) ≫ (p2 ≫ i2) +
        ((p2 ≫ i2) ≫ T) ≫ (p1 ≫ i1) + ((p2 ≫ i2) ≫ T) ≫ (p2 ≫ i2) := by
        rw [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_add]; abel
    _ = p1 ≫ (i1 ≫ T ≫ p1) ≫ i1 +
        p1 ≫ (i1 ≫ T ≫ p2) ≫ i2 +
        p2 ≫ (i2 ≫ T ≫ p1) ≫ i1 +
        p2 ≫ (i2 ≫ T ≫ p2) ≫ i2 := by simp only [Category.assoc]

/-- Matrix multiplication identity for block compositions `S ≫ T` on the biproduct. -/
theorem biproduct_block_composition {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (S T : E ⟶ E) (a : Ω ⟶ E) (d : E ⟶ Ω) :
    a ≫ (S ≫ T) ≫ d =
    (a ≫ S ≫ p1) ≫ (i1 ≫ T ≫ d) + (a ≫ S ≫ p2) ≫ (i2 ≫ T ≫ d) := by
  calc
    a ≫ (S ≫ T) ≫ d
      = (a ≫ S) ≫ 𝟙 E ≫ (T ≫ d) := by simp only [Category.id_comp, Category.assoc]
    _ = (a ≫ S) ≫ (p1 ≫ i1 + p2 ≫ i2) ≫ (T ≫ d) := by rw [h_decomp]
    _ = (a ≫ S) ≫ ((p1 ≫ i1) ≫ (T ≫ d) + (p2 ≫ i2) ≫ (T ≫ d)) := by rw [Preadditive.add_comp]
    _ = (a ≫ S) ≫ (p1 ≫ i1) ≫ (T ≫ d) + (a ≫ S) ≫ (p2 ≫ i2) ≫ (T ≫ d) := by rw [Preadditive.comp_add]
    _ = (a ≫ S ≫ p1) ≫ (i1 ≫ T ≫ d) + (a ≫ S ≫ p2) ≫ (i2 ≫ T ≫ d) := by simp only [Category.assoc]

/-! ### 4. The Bogoliubov–de Gennes Hamiltonian -/

/-- The Bogoliubov–de Gennes Hamiltonian `ℋ_BdG = [𝒟, M; M, -𝒟]`. -/
@[inline]
def bdgHamiltonian {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω) : E ⟶ E :=
  p1 ≫ D ≫ i1 + p1 ≫ M ≫ i2 + p2 ≫ M ≫ i1 - p2 ≫ D ≫ i2

/-- Massive BdG doublet dispersion operator `(𝒟² + M²) ⊗ 𝟙_E`. -/
@[inline]
def massiveDoubletDispersion {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω) : E ⟶ E :=
  p1 ≫ (D ≫ D + M ≫ M) ≫ i1 + p2 ≫ (D ≫ D + M ≫ M) ≫ i2

/-! ### 5. Block Projection Lemmas for ℋ_BdG -/

theorem bdg_block_11 {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0) :
    i1 ≫ bdgHamiltonian p1 i1 p2 i2 D M ≫ p1 = D := by
  dsimp [bdgHamiltonian]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_add, Preadditive.add_comp]
  have h1 : i1 ≫ (p1 ≫ D ≫ i1) ≫ p1 = D := by
    calc
      i1 ≫ (p1 ≫ D ≫ i1) ≫ p1 = (i1 ≫ p1) ≫ D ≫ (i1 ≫ p1) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ D ≫ 𝟙 Ω := by rw [hid1]
      _ = D := by simp only [Category.id_comp, Category.comp_id]
  have h2 : i1 ≫ (p1 ≫ M ≫ i2) ≫ p1 = 0 := by
    calc
      i1 ≫ (p1 ≫ M ≫ i2) ≫ p1 = (i1 ≫ p1) ≫ M ≫ (i2 ≫ p1) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ M ≫ 0 := by rw [hid1, horth21]
      _ = 0 := by simp only [comp_zero, zero_comp]
  have h3 : i1 ≫ (p2 ≫ M ≫ i1) ≫ p1 = 0 := by
    calc
      i1 ≫ (p2 ≫ M ≫ i1) ≫ p1 = (i1 ≫ p2) ≫ M ≫ (i1 ≫ p1) := by simp only [Category.assoc]
      _ = 0 ≫ M ≫ 𝟙 Ω := by rw [horth12, hid1]
      _ = 0 := by simp only [comp_zero, zero_comp]
  have h4 : i1 ≫ (p2 ≫ D ≫ i2) ≫ p1 = 0 := by
    calc
      i1 ≫ (p2 ≫ D ≫ i2) ≫ p1 = (i1 ≫ p2) ≫ D ≫ (i2 ≫ p1) := by simp only [Category.assoc]
      _ = 0 ≫ D ≫ 0 := by rw [horth12, horth21]
      _ = 0 := by simp only [comp_zero, zero_comp]
  rw [h1, h2, h3, h4]
  abel

theorem bdg_block_12 {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) :
    i1 ≫ bdgHamiltonian p1 i1 p2 i2 D M ≫ p2 = M := by
  dsimp [bdgHamiltonian]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_add, Preadditive.add_comp]
  have h1 : i1 ≫ (p1 ≫ D ≫ i1) ≫ p2 = 0 := by
    calc
      i1 ≫ (p1 ≫ D ≫ i1) ≫ p2 = (i1 ≫ p1) ≫ D ≫ (i1 ≫ p2) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ D ≫ 0 := by rw [hid1, horth12]
      _ = 0 := by simp only [comp_zero, zero_comp]
  have h2 : i1 ≫ (p1 ≫ M ≫ i2) ≫ p2 = M := by
    calc
      i1 ≫ (p1 ≫ M ≫ i2) ≫ p2 = (i1 ≫ p1) ≫ M ≫ (i2 ≫ p2) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ M ≫ 𝟙 Ω := by rw [hid1, hid2]
      _ = M := by simp only [Category.id_comp, Category.comp_id]
  have h3 : i1 ≫ (p2 ≫ M ≫ i1) ≫ p2 = 0 := by
    calc
      i1 ≫ (p2 ≫ M ≫ i1) ≫ p2 = (i1 ≫ p2) ≫ M ≫ (i1 ≫ p2) := by simp only [Category.assoc]
      _ = 0 ≫ M ≫ 0 := by rw [horth12]
      _ = 0 := by simp only [comp_zero, zero_comp]
  have h4 : i1 ≫ (p2 ≫ D ≫ i2) ≫ p2 = 0 := by
    calc
      i1 ≫ (p2 ≫ D ≫ i2) ≫ p2 = (i1 ≫ p2) ≫ D ≫ (i2 ≫ p2) := by simp only [Category.assoc]
      _ = 0 ≫ D ≫ 𝟙 Ω := by rw [horth12, hid2]
      _ = 0 := by simp only [comp_zero, zero_comp]
  rw [h1, h2, h3, h4]
  abel

theorem bdg_block_21 {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth21 : i2 ≫ p1 = 0) :
    i2 ≫ bdgHamiltonian p1 i1 p2 i2 D M ≫ p1 = M := by
  dsimp [bdgHamiltonian]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_add, Preadditive.add_comp]
  have h1 : i2 ≫ (p1 ≫ D ≫ i1) ≫ p1 = 0 := by
    calc
      i2 ≫ (p1 ≫ D ≫ i1) ≫ p1 = (i2 ≫ p1) ≫ D ≫ (i1 ≫ p1) := by simp only [Category.assoc]
      _ = 0 ≫ D ≫ 𝟙 Ω := by rw [horth21, hid1]
      _ = 0 := by simp only [comp_zero, zero_comp]
  have h2 : i2 ≫ (p1 ≫ M ≫ i2) ≫ p1 = 0 := by
    calc
      i2 ≫ (p1 ≫ M ≫ i2) ≫ p1 = (i2 ≫ p1) ≫ M ≫ (i2 ≫ p1) := by simp only [Category.assoc]
      _ = 0 ≫ M ≫ 0 := by rw [horth21]
      _ = 0 := by simp only [comp_zero, zero_comp]
  have h3 : i2 ≫ (p2 ≫ M ≫ i1) ≫ p1 = M := by
    calc
      i2 ≫ (p2 ≫ M ≫ i1) ≫ p1 = (i2 ≫ p2) ≫ M ≫ (i1 ≫ p1) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ M ≫ 𝟙 Ω := by rw [hid2, hid1]
      _ = M := by simp only [Category.id_comp, Category.comp_id]
  have h4 : i2 ≫ (p2 ≫ D ≫ i2) ≫ p1 = 0 := by
    calc
      i2 ≫ (p2 ≫ D ≫ i2) ≫ p1 = (i2 ≫ p2) ≫ D ≫ (i2 ≫ p1) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ D ≫ 0 := by rw [hid2, horth21]
      _ = 0 := by simp only [comp_zero, zero_comp]
  rw [h1, h2, h3, h4]
  abel

theorem bdg_block_22 {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid2 : i2 ≫ p2 = 𝟙 Ω) (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0) :
    i2 ≫ bdgHamiltonian p1 i1 p2 i2 D M ≫ p2 = - D := by
  dsimp [bdgHamiltonian]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_add, Preadditive.add_comp]
  have h1 : i2 ≫ (p1 ≫ D ≫ i1) ≫ p2 = 0 := by
    calc
      i2 ≫ (p1 ≫ D ≫ i1) ≫ p2 = (i2 ≫ p1) ≫ D ≫ (i1 ≫ p2) := by simp only [Category.assoc]
      _ = 0 ≫ D ≫ 0 := by rw [horth21, horth12]
      _ = 0 := by simp only [comp_zero, zero_comp]
  have h2 : i2 ≫ (p1 ≫ M ≫ i2) ≫ p2 = 0 := by
    calc
      i2 ≫ (p1 ≫ M ≫ i2) ≫ p2 = (i2 ≫ p1) ≫ M ≫ (i2 ≫ p2) := by simp only [Category.assoc]
      _ = 0 ≫ M ≫ 𝟙 Ω := by rw [horth21, hid2]
      _ = 0 := by simp only [comp_zero, zero_comp]
  have h3 : i2 ≫ (p2 ≫ M ≫ i1) ≫ p2 = 0 := by
    calc
      i2 ≫ (p2 ≫ M ≫ i1) ≫ p2 = (i2 ≫ p2) ≫ M ≫ (i1 ≫ p2) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ M ≫ 0 := by rw [hid2, horth12]
      _ = 0 := by simp only [comp_zero, zero_comp]
  have h4 : i2 ≫ (p2 ≫ D ≫ i2) ≫ p2 = D := by
    calc
      i2 ≫ (p2 ≫ D ≫ i2) ≫ p2 = (i2 ≫ p2) ≫ D ≫ (i2 ≫ p2) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ D ≫ 𝟙 Ω := by rw [hid2]
      _ = D := by simp only [Category.id_comp, Category.comp_id]
  rw [h1, h2, h3, h4]
  abel

/-! ### 6. Mass Condensation Theorem: Squaring ℋ_BdG -/

/-- The square of the BdG Hamiltonian condenses the massless Hodge Laplacian `𝒟²`
into the massive doublet dispersion `𝒟² + M²`. -/
theorem bdg_hamiltonian_squared {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (h_comm : D ≫ M = M ≫ D) :
    bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M =
    massiveDoubletDispersion p1 i1 p2 i2 D M := by
  let H := bdgHamiltonian p1 i1 p2 i2 D M
  have h_rec := biproduct_endomorphism_reconstruct p1 i1 p2 i2 h_decomp (H ≫ H)
  rw [h_rec]
  have hb11 : i1 ≫ (H ≫ H) ≫ p1 = D ≫ D + M ≫ M := by
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H H i1 p1]
    rw [bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21]
    rw [bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21]
    rw [bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12]
  have hb12 : i1 ≫ (H ≫ H) ≫ p2 = 0 := by
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H H i1 p2]
    rw [bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21]
    rw [bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12]
    rw [bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21]
    rw [Preadditive.comp_neg, h_comm]
    abel
  have hb21 : i2 ≫ (H ≫ H) ≫ p1 = 0 := by
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H H i2 p1]
    rw [bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21]
    rw [bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21]
    rw [bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21]
    rw [Preadditive.neg_comp, h_comm]
    abel
  have hb22 : i2 ≫ (H ≫ H) ≫ p2 = D ≫ D + M ≫ M := by
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H H i2 p2]
    rw [bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21]
    rw [bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12]
    rw [bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21]
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
    abel
  rw [hb11, hb12, hb21, hb22]
  simp only [Category.assoc, zero_comp, comp_zero, add_zero]
  dsimp [massiveDoubletDispersion]

/-- Massless condensation: when the kinetic operator is null (`𝒟² = 0`), the square
of the BdG Hamiltonian reduces to the pure mass condensate in both chiral sectors,
`p₁ ≫ M² ≫ i₁ + p₂ ≫ M² ≫ i₂`. -/
theorem bdg_hamiltonian_squared_of_kinetic_null {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (h_comm : D ≫ M = M ≫ D)
    (h_kinetic_null : D ≫ D = 0) :
    bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M =
      p1 ≫ (M ≫ M) ≫ i1 + p2 ≫ (M ≫ M) ≫ i2 := by
  rw [bdg_hamiltonian_squared p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp h_comm]
  dsimp [massiveDoubletDispersion]
  have hm : D ≫ D + M ≫ M = M ≫ M := by
    rw [h_kinetic_null]
    simp
  rw [hm]

/-! ### 7. Condensation of Lightcone Null Rays into Massive Doublets -/

/-- A massless lightcone ray (null eigenstate `u ≫ 𝒟² = 0`) is condensed into a
massive BdG doublet state whose rest energy squared is precisely `M²`. -/
theorem massless_null_ray_condenses_to_massive_doublet {X E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (h_comm : D ≫ M = M ≫ D)
    (u : X ⟶ Ω)
    (h_null : u ≫ (D ≫ D) = 0) :
    (u ≫ i1) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M) =
    (u ≫ (M ≫ M)) ≫ i1 := by
  rw [bdg_hamiltonian_squared p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp h_comm]
  dsimp [massiveDoubletDispersion]
  rw [Preadditive.comp_add]
  have h1 : (u ≫ i1) ≫ (p1 ≫ (D ≫ D + M ≫ M) ≫ i1) = (u ≫ (M ≫ M)) ≫ i1 := by
    calc
      (u ≫ i1) ≫ (p1 ≫ (D ≫ D + M ≫ M) ≫ i1)
        = (u ≫ (i1 ≫ p1)) ≫ (D ≫ D + M ≫ M) ≫ i1 := by simp only [Category.assoc]
      _ = (u ≫ 𝟙 Ω) ≫ (D ≫ D + M ≫ M) ≫ i1 := by rw [hid1]
      _ = u ≫ (D ≫ D + M ≫ M) ≫ i1 := by simp only [Category.comp_id]
      _ = (u ≫ (D ≫ D)) ≫ i1 + (u ≫ (M ≫ M)) ≫ i1 := by
          simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
      _ = (0 : X ⟶ Ω) ≫ i1 + (u ≫ (M ≫ M)) ≫ i1 := by rw [h_null]
      _ = (u ≫ (M ≫ M)) ≫ i1 := by simp only [zero_comp, zero_add]
  have h2 : (u ≫ i1) ≫ (p2 ≫ (D ≫ D + M ≫ M) ≫ i2) = 0 := by
    calc
      (u ≫ i1) ≫ (p2 ≫ (D ≫ D + M ≫ M) ≫ i2)
        = (u ≫ (i1 ≫ p2)) ≫ (D ≫ D + M ≫ M) ≫ i2 := by simp only [Category.assoc]
      _ = (u ≫ 0) ≫ (D ≫ D + M ≫ M) ≫ i2 := by rw [horth12]
      _ = 0 := by simp only [comp_zero, zero_comp]
  rw [h1, h2, add_zero]

/-! ### 8. Anticommutation with Symplectic Pairing Operator -/

/-- The symplectic pairing operator `𝒥_BdG = [0, 𝟙; -𝟙, 0]`. -/
@[inline]
def symplecticPairing {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E) : E ⟶ E :=
  p1 ≫ i2 - p2 ≫ i1

/-- The BdG Hamiltonian strictly anticommutes with the symplectic pairing operator:
`𝒥_BdG ≫ ℋ_BdG + ℋ_BdG ≫ 𝒥_BdG = 0`. -/
theorem bdg_anticommutes_pairing {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E) :
    symplecticPairing p1 i1 p2 i2 ≫ bdgHamiltonian p1 i1 p2 i2 D M +
    bdgHamiltonian p1 i1 p2 i2 D M ≫ symplecticPairing p1 i1 p2 i2 = 0 := by
  let J := symplecticPairing p1 i1 p2 i2
  let H := bdgHamiltonian p1 i1 p2 i2 D M
  have h_rec := biproduct_endomorphism_reconstruct p1 i1 p2 i2 h_decomp (J ≫ H + H ≫ J)
  rw [h_rec]
  have hj11 : i1 ≫ J ≫ p1 = 0 := by
    dsimp only [J, symplecticPairing]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    simp only [Category.assoc, hid1, hid2, horth12, horth21, Category.id_comp, Category.comp_id,
      zero_comp, comp_zero, sub_self]
  have hj12 : i1 ≫ J ≫ p2 = 𝟙 Ω := by
    dsimp only [J, symplecticPairing]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    simp only [Category.assoc, hid1, hid2, horth12, horth21, Category.id_comp, Category.comp_id,
      zero_comp, comp_zero, sub_zero]
  have hj21 : i2 ≫ J ≫ p1 = - 𝟙 Ω := by
    dsimp only [J, symplecticPairing]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    simp only [Category.assoc, hid1, hid2, horth12, horth21, Category.id_comp, Category.comp_id,
      zero_comp, comp_zero, zero_sub]
  have hj22 : i2 ≫ J ≫ p2 = 0 := by
    dsimp only [J, symplecticPairing]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    simp only [Category.assoc, hid1, hid2, horth12, horth21, Category.id_comp, Category.comp_id,
      zero_comp, comp_zero, sub_self]
  have hb11 : i1 ≫ (J ≫ H + H ≫ J) ≫ p1 = 0 := by
    rw [Preadditive.add_comp, Preadditive.comp_add]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp J H i1 p1]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H J i1 p1]
    rw [hj11, hj12, hj21, bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21]
    rw [bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21]
    rw [bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12]
    simp only [zero_comp, comp_zero, zero_add, add_zero, Category.id_comp, Category.comp_id,
      Preadditive.comp_neg, Preadditive.neg_comp]
    abel
  have hb12 : i1 ≫ (J ≫ H + H ≫ J) ≫ p2 = 0 := by
    rw [Preadditive.add_comp, Preadditive.comp_add]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp J H i1 p2]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H J i1 p2]
    rw [hj11, hj12, hj22, bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21]
    rw [bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21]
    simp only [zero_comp, comp_zero, zero_add, add_zero, Category.id_comp, Category.comp_id,
      Preadditive.comp_neg, Preadditive.neg_comp]
    abel
  have hb21 : i2 ≫ (J ≫ H + H ≫ J) ≫ p1 = 0 := by
    rw [Preadditive.add_comp, Preadditive.comp_add]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp J H i2 p1]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H J i2 p1]
    rw [hj21, hj22, hj11, bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21]
    rw [bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21]
    simp only [zero_comp, comp_zero, zero_add, add_zero, Category.id_comp, Category.comp_id,
      Preadditive.comp_neg, Preadditive.neg_comp]
    abel
  have hb22 : i2 ≫ (J ≫ H + H ≫ J) ≫ p2 = 0 := by
    rw [Preadditive.add_comp, Preadditive.comp_add]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp J H i2 p2]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H J i2 p2]
    rw [hj21, hj22, hj12, bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12]
    rw [bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21]
    simp only [zero_comp, comp_zero, zero_add, add_zero, Category.id_comp, Category.comp_id,
      Preadditive.comp_neg, Preadditive.neg_comp]
    abel
  rw [hb11, hb12, hb21, hb22]
  simp only [zero_comp, comp_zero, add_zero]

end InfoGeometry.Physics.BdGCondensation
