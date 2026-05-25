import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib

/-!
# InfoGeometry.Projective.SplitOctonions.SplitOctonionsBarrier

Coordinate-level logarithmic barrier on a real diagonal Zorn slice.
This file proves:

- positivity/incompatibility of isotropic vacuum with the open cone,
- first derivative of the barrier in the `a`-coordinate,
- second derivative (`1 / a^2`) as the Hessian entry,
- divergence of the barrier along sequences with determinant tending to `0+`.

Boundary note:
this is a local diagonal slice model (`X = diag(a,b)`), not a full
nonassociative split-octonion multiplication formalization.
-/

noncomputable section

namespace InfoGeometry.Projective.SplitOctonions.SplitOctonionsBarrier

/-- Diagonal coordinate slice `diag(a,b)`. -/
structure ZornSlice where
  a : Real
  b : Real

namespace ZornSlice

/-- Determinant on the diagonal slice. -/
def det (X : ZornSlice) : Real :=
  X.a * X.b

/-- Open cone interior (strict positivity of both diagonal coordinates). -/
def InCone (X : ZornSlice) : Prop :=
  0 < X.a ∧ 0 < X.b

/-- Isotropic vacuum marker on the slice. -/
def IsIsotropicVacuum (X : ZornSlice) : Prop :=
  X.a ≠ 0 ∧ X.b ≠ 0 ∧ X.det = 0

@[simp] theorem det_mk (a b : Real) : det ⟨a, b⟩ = a * b := rfl

theorem inCone_det_pos (X : ZornSlice) (hC : X.InCone) : 0 < X.det := by
  dsimp [det]
  exact mul_pos hC.1 hC.2

theorem isotropic_vacuum_empty_cone (X : ZornSlice) (hC : X.InCone) :
    ¬ X.IsIsotropicVacuum := by
  intro hI
  have hdetpos : 0 < X.det := inCone_det_pos X hC
  exact (ne_of_gt hdetpos) hI.2.2

/-- Logarithmic barrier `F(X) = -log(a) - log(b)`. -/
def barrier (X : ZornSlice) : Real :=
  -Real.log X.a - Real.log X.b

/-- First derivative in the `a` direction. -/
theorem barrier_deriv_a (X : ZornSlice) (hC : X.InCone) :
    HasDerivAt (fun x : Real => -Real.log x - Real.log X.b) (-(X.a)⁻¹) X.a := by
  have hneg : HasDerivAt (fun x : Real => -Real.log x) (-(X.a)⁻¹) X.a :=
    (Real.hasDerivAt_log hC.1.ne').neg
  have hconst : HasDerivAt (fun _ : Real => (-Real.log X.b)) 0 X.a :=
    hasDerivAt_const X.a (-Real.log X.b)
  have hsum : HasDerivAt (fun x : Real => (-Real.log x) + (-Real.log X.b)) (-(X.a)⁻¹ + 0) X.a :=
    hneg.add hconst
  simpa [sub_eq_add_neg] using hsum

/-- Second derivative in the `a` direction. -/
theorem barrier_hessian_a (X : ZornSlice) (hC : X.InCone) :
    HasDerivAt (fun x : Real => -x⁻¹) ((X.a ^ 2)⁻¹) X.a := by
  have hinv : HasDerivAt (fun x : Real => x⁻¹) (-(X.a ^ 2)⁻¹) X.a :=
    hasDerivAt_inv hC.1.ne'
  have hneg : HasDerivAt (fun x : Real => -x⁻¹) ((X.a ^ 2)⁻¹) X.a := by
    simpa using hinv.neg
  simpa [one_div, pow_two] using hneg

/-- First derivative in the `b` direction. -/
theorem barrier_deriv_b (X : ZornSlice) (hC : X.InCone) :
    HasDerivAt (fun y : Real => -Real.log X.a - Real.log y) (-(X.b)⁻¹) X.b := by
  have hconst : HasDerivAt (fun _ : Real => (-Real.log X.a)) 0 X.b :=
    hasDerivAt_const X.b (-Real.log X.a)
  have hneg : HasDerivAt (fun y : Real => -Real.log y) (-(X.b)⁻¹) X.b :=
    (Real.hasDerivAt_log hC.2.ne').neg
  have hsum : HasDerivAt (fun y : Real => (-Real.log X.a) + (-Real.log y)) (0 + (-(X.b)⁻¹)) X.b :=
    hconst.add hneg
  simpa [sub_eq_add_neg, add_comm] using hsum

/-- Second derivative in the `b` direction. -/
theorem barrier_hessian_b (X : ZornSlice) (hC : X.InCone) :
    HasDerivAt (fun y : Real => -y⁻¹) ((X.b ^ 2)⁻¹) X.b := by
  have hinv : HasDerivAt (fun y : Real => y⁻¹) (-(X.b ^ 2)⁻¹) X.b :=
    hasDerivAt_inv hC.2.ne'
  have hneg : HasDerivAt (fun y : Real => -y⁻¹) ((X.b ^ 2)⁻¹) X.b := by
    simpa using hinv.neg
  simpa [one_div, pow_two] using hneg

/-- Diagonal Hessian metric entries for the slice barrier. -/
def barrierMetric (X : ZornSlice) : Fin 2 → Fin 2 → Real
  | ⟨0, _⟩, ⟨0, _⟩ => (X.a ^ 2)⁻¹
  | ⟨1, _⟩, ⟨1, _⟩ => (X.b ^ 2)⁻¹
  | _, _ => 0

theorem barrierMetric_diag00 (X : ZornSlice) : barrierMetric X ⟨0, by decide⟩ ⟨0, by decide⟩ = (X.a ^ 2)⁻¹ := rfl

theorem barrierMetric_diag11 (X : ZornSlice) : barrierMetric X ⟨1, by decide⟩ ⟨1, by decide⟩ = (X.b ^ 2)⁻¹ := rfl

theorem barrierMetric_pos_diag (X : ZornSlice) (hC : X.InCone) :
    0 < barrierMetric X ⟨0, by decide⟩ ⟨0, by decide⟩ ∧
    0 < barrierMetric X ⟨1, by decide⟩ ⟨1, by decide⟩ := by
  constructor
  · simpa [barrierMetric, pow_two] using inv_pos.mpr (sq_pos_of_pos hC.1)
  · simpa [barrierMetric, pow_two] using inv_pos.mpr (sq_pos_of_pos hC.2)

/-- Barrier identity against determinant on the cone. -/
theorem barrier_eq_negLog_det (X : ZornSlice) (hC : X.InCone) :
    barrier X = -Real.log X.det := by
  dsimp [barrier, det]
  rw [Real.log_mul hC.1.ne' hC.2.ne']
  ring

/--
Divergence of the barrier to `+∞` when `det(X_n) → 0` through positive values.
-/
theorem barrier_diverges_at_vacuum
    (Xseq : Nat → ZornSlice)
    (h_in : ∀ n, (Xseq n).InCone)
    (h_lim : Filter.Tendsto (fun n => (Xseq n).det) Filter.atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Filter.Tendsto (fun n => barrier (Xseq n)) Filter.atTop Filter.atTop := by
  have hsplit : (fun n => barrier (Xseq n)) = (fun n => -Real.log ((Xseq n).det)) := by
    funext n
    exact barrier_eq_negLog_det (Xseq n) (h_in n)
  rw [hsplit]
  have h_log_bot : Filter.Tendsto (fun n => Real.log ((Xseq n).det)) Filter.atTop Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero.comp (by simpa using h_lim)
  refine Filter.tendsto_atTop.2 ?_
  intro b
  have h_eventually : ∀ᶠ n in Filter.atTop, Real.log ((Xseq n).det) ≤ -b :=
    (Filter.tendsto_atBot.1 h_log_bot) (-b)
  filter_upwards [h_eventually] with n hn
  linarith

end ZornSlice

end InfoGeometry.Projective.SplitOctonions.SplitOctonionsBarrier
