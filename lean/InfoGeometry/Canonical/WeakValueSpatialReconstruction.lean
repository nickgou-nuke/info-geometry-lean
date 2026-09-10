import Mathlib
import InfoGeometry.Projective.TwinRankOneWeakRatio

/-!
# Spatial weak-value reconstruction

Three-dimensional current/density reconstruction with actual coordinate
derivatives. A complex overlap is converted to a real nonnegative weight by
normSq; its real part is never substituted for a probability density.

These are identities for a supplied current and overlap. No Schrödinger--Pauli
equation, Navier--Stokes existence theorem, or colimit-to-spacetime identification
is assumed or asserted.
-/

noncomputable section
namespace InfoGeometry.Canonical.WeakValueSpatialReconstruction

open scoped BigOperators

abbrev Space := Fin 3 → ℝ
abbrev Field := Space → Fin 3 → ℝ

/-- Positive readout weight; zero exactly at zero complex overlap. -/
def overlapWeight (d : ℂ) : ℝ := Complex.normSq d

/-- The real current in Re(n/d), including the denominator's phase. -/
def realCurrent (n d : ℂ) : ℝ := n.re * d.re + n.im * d.im

theorem real_weak_value_eq_current_density (n d : ℂ) :
    (n / d).re = realCurrent n d / overlapWeight d := by
  rw [Complex.div_re]
  simp [realCurrent, overlapWeight, add_div]

theorem overlapWeight_pos {d : ℂ} (hd : d ≠ 0) :
    0 < overlapWeight d := by
  have hn := Complex.normSq_nonneg d
  have hz : Complex.normSq d ≠ 0 := fun h => hd (Complex.normSq_eq_zero.mp h)
  exact lt_of_le_of_ne hn (Ne.symm hz)

section OperatorReadout
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Compatibility with the existing guarded operator weak ratio. -/
theorem operator_readout (Q : H →L[ℂ] H) (pre post : H)
    (hd : inner (𝕜 := ℂ) post pre ≠ 0) :
    (InfoGeometry.Projective.TwinRankOneWeakRatio.weakRatio Q pre post).map
        Complex.re =
      some (realCurrent (inner (𝕜 := ℂ) post (Q pre))
        (inner (𝕜 := ℂ) post pre) /
        overlapWeight (inner (𝕜 := ℂ) post pre)) := by
  simp only [InfoGeometry.Projective.TwinRankOneWeakRatio.weakRatio,
    hd, if_false, Option.map_some]
  rw [real_weak_value_eq_current_density]
end OperatorReadout

/-- Scalar component readout. The physical domain requires rho x ≠ 0. -/
def reconstruct (j : Field) (rho : Space → ℝ) : Field :=
  fun x i => j x i / rho x

def coordinate (i : Fin 3) : Space := Pi.single i 1

/-- Ordinary partial derivative through a coordinate line. -/
def partial (f : Space → ℝ) (x : Space) (i : Fin 3) : ℝ :=
  deriv (fun s : ℝ => f (x + s • coordinate i)) 0

def SpatiallyDifferentiable (f : Space → ℝ) : Prop :=
  ∀ x i, DifferentiableAt ℝ (fun s : ℝ => f (x + s • coordinate i)) 0

def divergence (u : Field) (x : Space) : ℝ :=
  ∑ i, partial (fun y => u y i) x i

def curl (u : Field) (x : Space) : Fin 3 → ℝ :=
  ![partial (fun y => u y 2) x 1 - partial (fun y => u y 1) x 2,
    partial (fun y => u y 0) x 2 - partial (fun y => u y 2) x 0,
    partial (fun y => u y 1) x 0 - partial (fun y => u y 0) x 1]

def laplacian (f : Space → ℝ) (x : Space) : ℝ :=
  ∑ i, partial (fun y => partial f y i) x i

theorem partial_quotient (f rho : Space → ℝ) (x : Space) (i : Fin 3)
    (hf : SpatiallyDifferentiable f) (hr : SpatiallyDifferentiable rho)
    (h0 : rho x ≠ 0) :
    partial (fun y => f y / rho y) x i =
      (partial f x i * rho x - f x * partial rho x i) / rho x ^ 2 := by
  have hd := (hf x i).hasDerivAt.div (hr x i).hasDerivAt (by simpa using h0)
  simpa [partial] using hd.deriv

theorem partial_div_const (f : Space → ℝ) (d : ℝ) (x : Space) (i : Fin 3) :
    partial (fun y => f y / d) x i = partial f x i / d := by
  simp [partial]

theorem divergence_reconstruct (j : Field) (rho : Space → ℝ) (x : Space)
    (hj : ∀ i, SpatiallyDifferentiable (fun y => j y i))
    (hr : SpatiallyDifferentiable rho) (h0 : rho x ≠ 0) :
    divergence (reconstruct j rho) x =
      (divergence j x * rho x - ∑ i, j x i * partial rho x i) / rho x ^ 2 := by
  simp only [divergence, reconstruct]
  have hq (i : Fin 3) := partial_quotient (fun y => j y i) rho x i (hj i) hr h0
  simp_rw [hq]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul]

theorem partial_projection (x : Space) (a b : Fin 3) :
    partial (fun y => y a) x b = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst b
    simp [partial, coordinate]
  · simp [partial, coordinate, h, Ne.symm h]

/-- The exact weighted-current criterion for incompressibility. -/
theorem incompressible_iff (j : Field) (rho : Space → ℝ) (x : Space)
    (hj : ∀ i, SpatiallyDifferentiable (fun y => j y i))
    (hr : SpatiallyDifferentiable rho) (h0 : rho x ≠ 0) :
    divergence (reconstruct j rho) x = 0 ↔
      divergence j x * rho x = ∑ i, j x i * partial rho x i := by
  rw [divergence_reconstruct j rho x hj hr h0]
  simp [div_eq_zero_iff, pow_ne_zero 2 h0, sub_eq_zero]

theorem reconstruct_clears_density (j : Field) (rho : Space → ℝ)
    (h0 : ∀ x, rho x ≠ 0) :
    (fun x i => rho x * reconstruct j rho x i) = j := by
  funext x i
  dsimp [reconstruct]
  field_simp [h0 x]

/-- A current continuity equation transports to the reconstructed mass flux. -/
theorem continuity_reconstruct (j : ℝ → Field) (rho : ℝ → Space → ℝ)
    (t : ℝ) (x : Space) (h0 : ∀ y, rho t y ≠ 0)
    (h : deriv (fun s => rho s x) t + divergence (j t) x = 0) :
    deriv (fun s => rho s x) t +
      divergence (fun y i => rho t y * reconstruct (j t) (rho t) y i) x = 0 := by
  rw [reconstruct_clears_density (j t) (rho t) h0]
  exact h

/-- Spatially uniform overlap scales the actual curl, not just a proxy. -/
theorem curl_reconstruct_uniform (j : Field) (d : ℝ) (x : Space) :
    curl (reconstruct j (fun _ => d)) x = fun i => curl j x i / d := by
  funext i
  fin_cases i <;>
    simp [curl, reconstruct, partial_div_const, sub_div]

/-- Actual forced incompressible momentum residual in coordinate derivatives. -/
def nsResidual (nu : ℝ) (u : ℝ → Field) (p : ℝ → Space → ℝ)
    (forcing : ℝ → Field) (t : ℝ) (x : Space) (i : Fin 3) : ℝ :=
  deriv (fun s => u s x i) t +
    (∑ k, u t x k * partial (fun y => u t y i) x k) +
    partial (p t) x i - nu * laplacian (fun y => u t y i) x - forcing t x i

/-- Minimal classical derivative regularity, kept explicit because deriv is total. -/
def ClassicalRegularityOn (times : Set ℝ) (u : ℝ → Field)
    (p : ℝ → Space → ℝ) : Prop :=
  (∀ t ∈ times, ∀ x i, DifferentiableAt ℝ (fun s => u s x i) t) ∧
  (∀ t ∈ times, ContDiff ℝ 2 (u t)) ∧
  (∀ t ∈ times, ContDiff ℝ 1 (p t))

/-- PDE satisfaction includes regularity; reconstruction alone does not imply it. -/
def SolvesNavierStokesOn (times : Set ℝ) (nu : ℝ) (u : ℝ → Field)
    (p : ℝ → Space → ℝ) (forcing : ℝ → Field) : Prop :=
  ClassicalRegularityOn times u p ∧
  (∀ t ∈ times, ∀ x, divergence (u t) x = 0) ∧
  (∀ t ∈ times, ∀ x i, nsResidual nu u p forcing t x i = 0)

end InfoGeometry.Canonical.WeakValueSpatialReconstruction
