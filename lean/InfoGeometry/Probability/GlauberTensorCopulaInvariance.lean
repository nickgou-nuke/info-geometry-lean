import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

/-!
# Finite Separable-Kernel Factorization and Scale-Invariant Ratio

This module uses counting sums on a finite detector index type. It proves
Fubini factorization for a separable scalar kernel and the resulting algebraic
scale invariance of a ratio. It does not formalize a continuous Glauber field
correlator, detector-volume cancellation, a copula in the probabilistic sense,
or any identity between transformer attention and quantum-optics observables.
-/

namespace InfoGeometry.Probability.GlauberTensorCopula

variable {α : Type*} [Fintype α]

/-- Counting sum on a finite detector index type. -/
def integrate1 (f : α → ℝ) : ℝ := ∑ x, f x

/-- Iterated counting sum on the product of two finite detector index types. -/
def integrate2 (F : α → α → ℝ) : ℝ := ∑ x, ∑ y, F x y

/-- Scalar homogeneity of the finite counting sum. -/
theorem integrate1_smul (c : ℝ) (f : α → ℝ) :
    integrate1 (fun x => c * f x) = c * integrate1 f := by
  simp [integrate1, Finset.mul_sum]

/-- Scalar homogeneity of the iterated finite counting sum. -/
theorem integrate2_smul (c : ℝ) (F : α → α → ℝ) :
    integrate2 (fun x y => c * F x y) = c * integrate2 F := by
  simp [integrate2, Finset.mul_sum]

/-- Fubini factorization for a separable kernel over finite counting measure. -/
theorem integrate2_tensor_factorization (f g : α → ℝ) :
    integrate2 (fun x y => f x * g y) = integrate1 f * integrate1 g := by
  simp [integrate1, integrate2, Fintype.sum_mul_sum]

/-- Finite scalar model with a separable cross-kernel. The name is historical:
these fields are scalar functions, not quantum field operators or expectation
values. -/
structure SeparableKernelModel (α : Type*) [Fintype α] where
  /-- Positive scalar amplitude. -/
  A0 : ℝ
  /-- Positive scalar kernel factor. -/
  kappa : ℝ
  hA0_pos : 0 < A0
  hkappa_pos : 0 < kappa
  /-- First real-valued factor in the separable kernel. -/
  G1 : α → ℝ
  /-- Second real-valued factor in the separable kernel. -/
  G2 : α → ℝ
  /-- Positivity of the first finite counting sum. -/
  hI1_pos : 0 < integrate1 (α := α) G1
  /-- Positivity of the second finite counting sum. -/
  hI2_pos : 0 < integrate1 (α := α) G2

namespace SeparableKernelModel

variable {α : Type*} [Fintype α] (sys : SeparableKernelModel α)

/-- The first scalar total `A₀ * ∑ x, G₁ x`. -/
def L1 : ℝ :=
  sys.A0 * integrate1 sys.G1

/-- The second scalar total `A₀ * ∑ x, G₂ x`. -/
def L2 : ℝ :=
  sys.A0 * integrate1 sys.G2

/-- Separable scalar kernel `κ * G₁(x) * G₂(y)`. It is not a quantum-optics
field correlator. -/
def crossKernel : α → α → ℝ :=
  fun x y => sys.kappa * (sys.G1 x * sys.G2 y)

/-- Finite total `A₀ * ∑ x, ∑ y, crossKernel x y`. -/
def integratedKernel : ℝ :=
  sys.A0 * integrate2 sys.crossKernel

/-- The finite separable-kernel identity
`Q = (κ / A₀) * (L₁ * L₂)`. -/
theorem integratedKernel_factorization :
    sys.integratedKernel = (sys.kappa / sys.A0) * (sys.L1 * sys.L2) := by
  change sys.A0 * integrate2
      (fun x y => sys.kappa * (sys.G1 x * sys.G2 y)) =
    (sys.kappa / sys.A0) *
      ((sys.A0 * integrate1 sys.G1) * (sys.A0 * integrate1 sys.G2))
  rw [integrate2_smul, integrate2_tensor_factorization]
  have hA0_ne : sys.A0 ≠ 0 := ne_of_gt sys.hA0_pos
  field_simp [hA0_ne]

theorem L1_pos : 0 < sys.L1 :=
  mul_pos sys.hA0_pos sys.hI1_pos

theorem L2_pos : 0 < sys.L2 :=
  mul_pos sys.hA0_pos sys.hI2_pos

theorem integratedKernel_pos : 0 < sys.integratedKernel := by
  rw [sys.integratedKernel_factorization]
  have h_frac : 0 < sys.kappa / sys.A0 := div_pos sys.hkappa_pos sys.hA0_pos
  have h_prod : 0 < sys.L1 * sys.L2 := mul_pos sys.L1_pos sys.L2_pos
  exact mul_pos h_frac h_prod

/-- Scalar ratio `(L₁ * L₂) / Q`; it is not a copula distribution. -/
def separableKernelRatio : ℝ :=
  (sys.L1 * sys.L2) / sys.integratedKernel

/-- The ratio reduces to `A₀ / κ` in this finite separable-kernel model. -/
theorem separableKernelRatio_eq_amplitude_div_factor :
    sys.separableKernelRatio = sys.A0 / sys.kappa := by
  dsimp only [separableKernelRatio]
  rw [sys.integratedKernel_factorization]
  have hA0_ne : sys.A0 ≠ 0 := ne_of_gt sys.hA0_pos
  have hkappa_ne : sys.kappa ≠ 0 := ne_of_gt sys.hkappa_pos
  have hL1_ne : sys.L1 ≠ 0 := ne_of_gt sys.L1_pos
  have hL2_ne : sys.L2 ≠ 0 := ne_of_gt sys.L2_pos
  have hprod_ne : sys.L1 * sys.L2 ≠ 0 := mul_ne_zero hL1_ne hL2_ne
  field_simp [hA0_ne, hkappa_ne, hprod_ne]

/-- Multiplying the finite-model ratio by `κ` gives `A₀`. -/
theorem factor_mul_ratio_eq_amplitude :
    sys.kappa * sys.separableKernelRatio = sys.A0 := by
  rw [sys.separableKernelRatio_eq_amplitude_div_factor]
  have hkappa_ne : sys.kappa ≠ 0 := ne_of_gt sys.hkappa_pos
  exact mul_div_cancel₀ sys.A0 hkappa_ne

/-- Rescale both scalar response functions by the same positive constant. -/
def rescaleGeometry (alpha : ℝ) (halpha_pos : 0 < alpha) :
    SeparableKernelModel α where
  A0 := sys.A0
  kappa := sys.kappa
  hA0_pos := sys.hA0_pos
  hkappa_pos := sys.hkappa_pos
  G1 := fun x => alpha * sys.G1 x
  G2 := fun x => alpha * sys.G2 x
  hI1_pos := by
    rw [integrate1_smul]
    exact mul_pos halpha_pos sys.hI1_pos
  hI2_pos := by
    rw [integrate1_smul]
    exact mul_pos halpha_pos sys.hI2_pos

/-- The scalar ratio is unchanged by common positive rescaling of its two
separable response factors. -/
theorem separableKernelRatio_scale_invariance (alpha : ℝ) (halpha_pos : 0 < alpha) :
    (sys.rescaleGeometry alpha halpha_pos).separableKernelRatio = sys.separableKernelRatio := by
  rw [separableKernelRatio_eq_amplitude_div_factor, separableKernelRatio_eq_amplitude_div_factor]
  rfl

/-- Rescale the two scalar response functions independently by positive factors. -/
def rescaleAsymmetric (alpha1 alpha2 : ℝ) (h1_pos : 0 < alpha1) (h2_pos : 0 < alpha2)
    : SeparableKernelModel α where
  A0 := sys.A0
  kappa := sys.kappa
  hA0_pos := sys.hA0_pos
  hkappa_pos := sys.hkappa_pos
  G1 := fun x => alpha1 * sys.G1 x
  G2 := fun x => alpha2 * sys.G2 x
  hI1_pos := by
    rw [integrate1_smul]
    exact mul_pos h1_pos sys.hI1_pos
  hI2_pos := by
    rw [integrate1_smul]
    exact mul_pos h2_pos sys.hI2_pos

/-- The ratio is invariant under independent positive rescaling of its two
separable factors. -/
theorem separableKernelRatio_asymmetric_scale_invariance
    (alpha1 alpha2 : ℝ) (h1_pos : 0 < alpha1) (h2_pos : 0 < alpha2)
    :
    ((sys.rescaleAsymmetric alpha1 alpha2 h1_pos h2_pos).separableKernelRatio) =
    sys.separableKernelRatio := by
  rw [separableKernelRatio_eq_amplitude_div_factor, separableKernelRatio_eq_amplitude_div_factor]
  rfl

end SeparableKernelModel

end InfoGeometry.Probability.GlauberTensorCopula
