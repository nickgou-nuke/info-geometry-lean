import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Tactic

/-!
# Quadratic potentials and their exact differential forms

For a continuous symmetric real bilinear form `g`, `potential g x = g x x / 2`.
The first and second Fréchet derivatives are proved, rather than defined to be
the expected answers. Nondegeneracy is needed only for uniqueness of the metric
gradient. For a `g`-skew endomorphism `A`, the normalized twisted differential
`-dK ∘ A / 2` is a primitive of `g(A·,·)`. These are affine-space results; a
curved cone additionally needs a connection and the equation `∇E = id`.
-/

noncomputable section

namespace InfoGeometry.Geometry.QuadraticPotentialCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def potential (g : E →L[ℝ] E →L[ℝ] ℝ) (x : E) : ℝ := g x x / 2

theorem hasFDerivAt_potential (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, g u v = g v u) (x : E) :
    HasFDerivAt (potential g) (g x) x := by
  convert (g.hasFDerivAt_of_bilinear (hasFDerivAt_id x)
    (hasFDerivAt_id x)).const_smul (1 / 2 : ℝ) using 1
  · funext y
    simp [potential, div_eq_mul_inv, mul_comm]
  · ext v
    simp [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, hs]
    ring

theorem fderiv_potential (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, g u v = g v u) : fderiv ℝ (potential g) = g := by
  funext x
  exact (hasFDerivAt_potential g hs x).fderiv

theorem hessian_potential (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, g u v = g v u) (x : E) :
    fderiv ℝ (fderiv ℝ (potential g)) x = g := by
  rw [fderiv_potential g hs]
  exact g.fderiv

theorem potential_smul (g : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) (x : E) :
    potential g (r • x) = r ^ 2 * potential g x := by
  simp [potential, pow_two]; ring

theorem euler_identity (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, g u v = g v u) (x : E) :
    fderiv ℝ (potential g) x x = 2 * potential g x := by
  rw [fderiv_potential g hs]
  simp only [potential]
  ring

/-- The metric gradient is `x`. A Hilbert/Riesz gradient uses a different metric. -/
theorem metric_gradient_unique (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, g u v = g v u)
    (hn : ∀ u, (∀ v, g u v = 0) → u = 0) (x y : E)
    (hy : ∀ v, g y v = fderiv ℝ (potential g) x v) : y = x := by
  apply sub_eq_zero.mp
  apply hn
  intro v
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hy, fderiv_potential g hs]
  exact sub_self _

theorem hessian_add_affine (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, g u v = g v u) (ell : E →L[ℝ] ℝ) (c : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => potential g y + ell y + c)) x = g := by
  have hfirst : fderiv ℝ (fun y => potential g y + ell y + c) =
      fun y => g y + ell := by
    funext y
    exact (((hasFDerivAt_potential g hs y).add ell.hasFDerivAt).add_const c).fderiv
  rw [hfirst]
  exact (g.hasFDerivAt.add_const ell).fderiv

theorem shift_changes_zero (g : E →L[ℝ] E →L[ℝ] ℝ) :
    potential g 0 = 0 ∧ potential g 0 + 1 ≠ 0 := by simp [potential]

/-- Linear one-form field with the convention `omega(u,v) = g(Au,v)`. -/
def twistedPrimitive (g : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] ℝ := (1 / 2 : ℝ) • (g.comp A)

theorem twistedPrimitive_eq_differential (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, g u v = g v u) (A : E →L[ℝ] E)
    (ha : ∀ u v, g (A u) v = -g u (A v)) (x v : E) :
    twistedPrimitive g A x v = -(1 / 2 : ℝ) *
      fderiv ℝ (potential g) x (A v) := by
  rw [fderiv_potential g hs]
  simp [twistedPrimitive, ha]

/-- Native Mathlib alternating one-form corresponding to `-dK ∘ A / 2`. -/
def potentialOneForm (g : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toLinearIsometry.toContinuousLinearMap.comp
    (twistedPrimitive g A)

/-- A native exterior derivative, with its sign and factor checked explicitly. -/
theorem extDeriv_potentialOneForm (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, g u v = g v u) (A : E →L[ℝ] E)
    (ha : ∀ u v, g (A u) v = -g u (A v)) (x u v : E) :
    extDeriv (potentialOneForm g A) x ![u, v] = g (A u) v := by
  rw [extDeriv, (potentialOneForm g A).fderiv]
  have hremove : Fin.removeNth (1 : Fin 2) ![u, v] (0 : Fin 1) = u := rfl
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two, potentialOneForm, twistedPrimitive, hs, ha, hremove]
  have h := ha v u
  rw [hs (A v) u] at h
  linarith

theorem potentialTwoForm_closed (g : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    extDeriv (extDeriv (potentialOneForm g A)) = 0 := by
  exact extDeriv_extDeriv ((potentialOneForm g A).contDiff (n := ⊤)) (by simp)

end InfoGeometry.Geometry.QuadraticPotentialCalculus
