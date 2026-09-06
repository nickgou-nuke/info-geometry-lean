import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic
import InfoGeometry.Analysis.AsanoLeeYangCircleBridge

/-!
# Reciprocal Zero Localization and Cayley Transport

This module formalizes:
1. **The Open Unit Disk $\mathbb{D}$ and Exterior $\mathbb{E}$**:
   $$\mathbb{D} = \{z \in \mathbb{C} \mid \|z\| < 1\}, \qquad \mathbb{E} = \{z \in \mathbb{C} \mid \|z\| > 1\}$$
2. **Elementary Reciprocal Boundary Localization**:
   If a function is zero-free on both $\mathbb{D}$ and $\mathbb{E}$, then every zero lies on $S^1$.
   Reciprocal zero symmetry is used below only to derive exterior zero-freeness:
   $$\forall z_0 \in \mathbb{C}, \quad Z_\infty(z_0) = 0 \implies \|z_0\| = 1$$
3. **Transport to the Critical Line $\operatorname{Re}(s) = 1/2$**:
   Every root $z_0 \in S^1 \setminus \{-1\}$ satisfying these hypotheses maps via the Cayley map $s(z) = \frac{z}{1+z}$
   to a point on the critical line:
   $$\operatorname{Re}\left(\frac{z_0}{1+z_0}\right) = \frac{1}{2}$$
-/

noncomputable section

namespace InfoGeometry.Analysis.HurwitzAsano

open Complex
open InfoGeometry.Analysis.AsanoLeeYangCircle

/-- The open unit disk $\mathbb{D} \subset \mathbb{C}$ -/
def openUnitDisk : Set ℂ := {z : ℂ | ‖z‖ < 1}

/-- The open exterior $\mathbb{E} \subset \mathbb{C}$ -/
def openExterior : Set ℂ := {z : ℂ | 1 < ‖z‖}

/-- The unit circle $S^1 \subset \mathbb{C}$ -/
def unitCircle : Set ℂ := {z : ℂ | ‖z‖ = 1}

/-- A function is zero-free in the open unit disk. -/
def ZeroFreeInUnitDisk (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ openUnitDisk, f z ≠ 0

/-- The zero set is invariant under inversion away from the origin. -/
def ReciprocalZeroSymmetric (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, z ≠ 0 → (f z = 0 ↔ f z⁻¹ = 0)

/-- 🏆 THEOREM 1: Trichotomy of the Complex Plane with respect to $S^1$ -/
theorem complex_trichotomy_unit_circle (z : ℂ) :
    ‖z‖ < 1 ∨ ‖z‖ = 1 ∨ 1 < ‖z‖ := by
  rcases lt_trichotomy ‖z‖ 1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Inversion on ℂ \ {0} maps the exterior strictly into the open unit disk -/
theorem norm_inv_lt_one_of_one_lt_norm {z : ℂ} (hz : 1 < ‖z‖) :
    ‖z⁻¹‖ < 1 := by
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ hz

/-- Inversion on ℂ \ {0} maps the open unit disk strictly into the exterior -/
theorem one_lt_norm_inv_of_norm_lt_one {z : ℂ} (hz_pos : 0 < ‖z‖) (hz : ‖z‖ < 1) :
    1 < ‖z⁻¹‖ := by
  rw [norm_inv]
  exact (one_lt_inv₀ hz_pos).mpr hz

/-- Two-region zero localization:
    If $f : \mathbb{C} \to \mathbb{C}$ is zero-free on the open unit disk $\mathbb{D}$,
    and satisfies reciprocal zero-freeness on the exterior $\mathbb{E}$,
    then any zero $z_0$ of $f$ must lie exactly on the unit circle $S^1$. -/
theorem reciprocal_root_on_unit_circle_of_two_region_free
    {f : ℂ → ℂ}
    (h_disk_free : ∀ z ∈ openUnitDisk, f z ≠ 0)
    (h_ext_free  : ∀ z ∈ openExterior, f z ≠ 0)
    {z0 : ℂ} (hz0_root : f z0 = 0) :
    ‖z0‖ = 1 := by
  rcases complex_trichotomy_unit_circle z0 with h_lt | h_eq | h_gt
  · exfalso
    exact h_disk_free z0 h_lt hz0_root
  · exact h_eq
  · exfalso
    exact h_ext_free z0 h_gt hz0_root

/-- 🏆 THEOREM 3: Inversion-Symmetric Zero-Freeness Transfer:
    If $f$ is zero-free on the unit disk $\mathbb{D}$ and satisfies the self-reciprocal
    zero relation $f(z) = 0 \iff f(z^{-1}) = 0$ for $z \neq 0$,
    then $f$ is automatically zero-free on the exterior $\mathbb{E}$. -/
theorem exterior_zero_free_of_reciprocal_symmetry
    {f : ℂ → ℂ}
    (h_disk_free : ∀ z ∈ openUnitDisk, f z ≠ 0)
    (h_symm : ∀ z : ℂ, z ≠ 0 → (f z = 0 ↔ f z⁻¹ = 0)) :
    ∀ z ∈ openExterior, f z ≠ 0 := by
  intro z hz_ext
  have hz_ne : z ≠ 0 := by
    intro hz_zero
    have h_contra : 1 < (0 : ℝ) := by
      calc 1 < ‖z‖ := hz_ext
      _ = ‖(0 : ℂ)‖ := by rw [hz_zero]
      _ = 0 := norm_zero
    linarith
  intro hz_zero
  have hz_inv_zero : f z⁻¹ = 0 := (h_symm z hz_ne).mp hz_zero
  have hz_inv_in_disk : z⁻¹ ∈ openUnitDisk := norm_inv_lt_one_of_one_lt_norm hz_ext
  exact h_disk_free z⁻¹ hz_inv_in_disk hz_inv_zero

/-- Master reciprocal zero-localization theorem:
    Under disk zero-freeness and self-reciprocity, every root $z_0$ satisfies $\|z_0\| = 1$. -/
theorem root_modulus_one_of_disk_free_reciprocal_symmetry
    {f : ℂ → ℂ}
    (h_disk_free : ∀ z ∈ openUnitDisk, f z ≠ 0)
    (h_symm : ∀ z : ℂ, z ≠ 0 → (f z = 0 ↔ f z⁻¹ = 0))
    {z0 : ℂ} (hz0_root : f z0 = 0) :
    ‖z0‖ = 1 := by
  have h_ext_free := exterior_zero_free_of_reciprocal_symmetry h_disk_free h_symm
  exact reciprocal_root_on_unit_circle_of_two_region_free h_disk_free h_ext_free hz0_root

/-- The same localization packaged as membership in the unit-circle set. -/
theorem root_mem_unitCircle
    {f : ℂ → ℂ}
    (h_disk_free : ZeroFreeInUnitDisk f)
    (h_symm : ReciprocalZeroSymmetric f)
    {z0 : ℂ} (hz0_root : f z0 = 0) :
    z0 ∈ unitCircle := by
  exact root_modulus_one_of_disk_free_reciprocal_symmetry
    h_disk_free h_symm hz0_root

/-- Full geometric root transport to Critical Line $\operatorname{Re}(s) = 1/2$:
    Any non-exceptional root $z_0 \in S^1 \setminus \{-1\}$ satisfying these hypotheses
    transports via the Riemann Cayley map $s(z) = \frac{z}{1+z}$ to the critical line. -/
theorem reciprocal_root_to_critical_line
    {f : ℂ → ℂ}
    (h_disk_free : ∀ z ∈ openUnitDisk, f z ≠ 0)
    (h_symm : ∀ z : ℂ, z ≠ 0 → (f z = 0 ↔ f z⁻¹ = 0))
    {z0 : ℂ} (hz0_root : f z0 = 0) (hz0_ne_neg_one : z0 ≠ -1) :
    (riemannCayleyInverse z0).re = 1 / 2 := by
  have h_norm_one : ‖z0‖ = 1 :=
    root_modulus_one_of_disk_free_reciprocal_symmetry h_disk_free h_symm hz0_root
  exact re_riemannCayleyInverse_eq_half_of_norm_eq_one h_norm_one hz0_ne_neg_one

end InfoGeometry.Analysis.HurwitzAsano
