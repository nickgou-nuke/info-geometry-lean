import Mathlib

open scoped BigOperators
open scoped Real

namespace InfoGeometry

/-! ---------------------------------------------------------------------------
## 1) Finite probability vectors (ℝ-valued)
---------------------------------------------------------------------------- -/
namespace Prob

variable {α : Type*} [Fintype α]

/-- A probability vector on a finite type, valued in `ℝ`. -/
abbrev FinProb (α : Type*) [Fintype α] := InfoGeometry.FinProb α

@[simp] lemma sum_eq_one (p : FinProb α) : (∑ a, p a) = 1 := p.sum_one

/-- Dirac / point-mass probability vector. -/
def dirac [DecidableEq α] (a0 : α) : FinProb α :=
  InfoGeometry.dirac (a0 := a0)

/-- Normalize nonnegative weights into a probability vector. -/
noncomputable def normalize (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hZ : 0 < (∑ a, w a)) : FinProb α :=
  InfoGeometry.normalize (w := w) (hw := hw) (hZ := hZ)

end Prob


/-! ---------------------------------------------------------------------------
## 2) Transformation groups: invariance + transitivity ⇒ uniform distribution
---------------------------------------------------------------------------- -/
namespace TransformationGroups

open Prob

section Discrete

variable {α : Type*} [Fintype α]

/-- Invariance of a finite probability vector under a group action. -/
def InvariantUnder {G : Type*} [Group G] [MulAction G α] (p : FinProb α) : Prop :=
  ∀ g a, p (g • a) = p a

/-- Transitivity of a group action. -/
def IsTransitive {G : Type*} [Group G] [MulAction G α] : Prop :=
  ∀ a b, ∃ g : G, g • a = b

lemma eq_of_invariant_transitive
  {G : Type*} [Group G] [MulAction G α]
  (p : FinProb α)
  (hinv : InvariantUnder (α := α) p)
  (htrans : IsTransitive (G := G) (α := α)) :
  ∀ a b : α, p a = p b := by
  intro a b
  rcases htrans a b with ⟨g, rfl⟩
  simpa using (hinv g a).symm

lemma uniform_of_all_eq
  [Nonempty α]
  (p : FinProb α)
  (hall : ∀ a b : α, p a = p b) :
  ∀ a : α, p a = 1 / (Fintype.card α : ℝ) := by
  classical
  let a0 : α := Classical.choice (by infer_instance : Nonempty α)
  let c : ℝ := p a0
  have hc : ∀ a : α, p a = c := by
    intro a
    simpa [c] using hall a a0

  have hsum :
      (∑ a : α, p a) = (Fintype.card α : ℝ) * c := by
    calc
      (∑ a : α, p a) = ∑ a : α, c := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        simp [hc a]
      _ = (Fintype.card α : ℝ) * c := by
        simpa [Finset.card_univ] using (Finset.sum_const c : (∑ _a : α, c) = _)

  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero)

  have hcval : c = 1 / (Fintype.card α : ℝ) := by
    have hEq : (Fintype.card α : ℝ) * c = 1 := by
      simpa [hsum] using p.sum_one
    have hEq' : c * (Fintype.card α : ℝ) = 1 := by
      simpa [mul_comm] using hEq
    exact (eq_div_iff hcard).2 hEq'

  intro a
  calc
    p a = c := hc a
    _ = 1 / (Fintype.card α : ℝ) := hcval

theorem uniform_of_transformation_group
  {G : Type*} [Group G] [MulAction G α]
  [Nonempty α]
  (p : FinProb α)
  (hinv : InvariantUnder (α := α) p)
  (htrans : IsTransitive (G := G) (α := α)) :
  ∀ a : α, p a = 1 / (Fintype.card α : ℝ) := by
  apply uniform_of_all_eq (p := p)
  exact eq_of_invariant_transitive (α := α) p hinv htrans

end Discrete

end TransformationGroups


/-! ---------------------------------------------------------------------------
## 3) Determinant functoriality: GL(V), Units(Matrix), log|det|, Jacobian chain rule
---------------------------------------------------------------------------- -/
namespace Determinant

/-! ## Route A: `GL(V) := V ≃ₗ[𝕜] V` -/
namespace LinearRoute

variable {𝕜 : Type*} [Field 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- `GL(V)` as linear automorphisms. -/
abbrev GL : Type* := V ≃ₗ[𝕜] V

/-- Determinant as a group hom to units. -/
noncomputable def detHom : GL (𝕜 := 𝕜) (V := V) →* 𝕜ˣ :=
  LinearEquiv.det

@[simp] lemma detHom_apply (g : GL (𝕜 := 𝕜) (V := V)) :
    detHom (𝕜 := 𝕜) (V := V) g = g.det := rfl

/-- Special linear subgroup as kernel of determinant. -/
def SL : Subgroup (GL (𝕜 := 𝕜) (V := V)) :=
  (detHom (𝕜 := 𝕜) (V := V)).ker

@[simp] lemma mem_SL_iff (g : GL (𝕜 := 𝕜) (V := V)) :
    g ∈ SL (𝕜 := 𝕜) (V := V) ↔ detHom (𝕜 := 𝕜) (V := V) g = 1 := Iff.rfl

@[simp] lemma det_mul (g h : GL (𝕜 := 𝕜) (V := V)) :
    (g * h).det = g.det * h.det := by
  simpa using (detHom (𝕜 := 𝕜) (V := V)).map_mul g h

@[simp] lemma det_inv (g : GL (𝕜 := 𝕜) (V := V)) :
    (g⁻¹).det = (g.det)⁻¹ := by
  simpa using (detHom (𝕜 := 𝕜) (V := V)).map_inv g

end LinearRoute


/-! ## Route B: `Units (Matrix n n R)` -/
namespace MatrixRoute

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- “Matrix GL”: invertible matrices are units of the matrix ring. -/
abbrev GLm : Type* := Units (Matrix n n R)

/-- Determinant as a multiplicative monoid hom on matrices. -/
noncomputable def detMonoidHom : Matrix n n R →* R :=
{ toFun := Matrix.det
  map_one' := Matrix.det_one
  map_mul' := Matrix.det_mul }

/-- Determinant on units via `Units.map`. -/
noncomputable def detUnitHom : GLm (n := n) (R := R) →* Rˣ :=
  Units.map (detMonoidHom (n := n) (R := R))

@[simp] lemma detUnitHom_val (A : GLm (n := n) (R := R)) :
    ((detUnitHom (n := n) (R := R) A : Rˣ) : R) = Matrix.det (A : Matrix n n R) := rfl

/-- “Matrix SL”: kernel of `det : Units(Matrix) →* Units R`. -/
def SLm : Subgroup (GLm (n := n) (R := R)) :=
  (detUnitHom (n := n) (R := R)).ker

@[simp] lemma mem_SLm_iff (A : GLm (n := n) (R := R)) :
    A ∈ SLm (n := n) (R := R) ↔ detUnitHom (n := n) (R := R) A = 1 := Iff.rfl

@[simp] lemma det_mul (A B : GLm (n := n) (R := R)) :
    Matrix.det ((A * B : GLm (n := n) (R := R)) : Matrix n n R)
      =
    Matrix.det (A : Matrix n n R) * Matrix.det (B : Matrix n n R) :=
by
  simpa using (Matrix.det_mul (A : Matrix n n R) (B : Matrix n n R))

end MatrixRoute


/-! ## `log ∘ |det|` additivity (ℝ-case) -/
namespace Characters

open LinearRoute

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

noncomputable def logAbsDet (g : GL (𝕜 := ℝ) (V := V)) : ℝ :=
  Real.log (Real.abs ((detHom (𝕜 := ℝ) (V := V) g : ℝ)))

theorem logAbsDet_mul (g h : GL (𝕜 := ℝ) (V := V)) :
    logAbsDet (V := V) (g * h) = logAbsDet (V := V) g + logAbsDet (V := V) h := by
  set dg : ℝ := (detHom (𝕜 := ℝ) (V := V) g : ℝ)
  set dh : ℝ := (detHom (𝕜 := ℝ) (V := V) h : ℝ)
  have hg : dg ≠ 0 := (detHom (𝕜 := ℝ) (V := V) g).ne_zero
  have hh : dh ≠ 0 := (detHom (𝕜 := ℝ) (V := V) h).ne_zero
  have hg_abs : 0 < |dg| := abs_pos.mpr hg
  have hh_abs : 0 < |dh| := abs_pos.mpr hh
  -- `Real.log_mul` requires strict positivity of both factors.
  simp [logAbsDet, dg, dh, Real.abs_mul, Real.log_mul hg_abs hh_abs,
        detHom, Units.val_mul, mul_assoc, add_comm, add_left_comm, add_assoc]

end Characters


/-! ## Jacobian chain rule as determinant multiplicativity of derivatives -/
namespace Jacobian

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Jacobian determinant of a continuous linear map (via its linear part). -/
noncomputable def jacDet (L : E →L[𝕜] E) : 𝕜 :=
  LinearMap.det L.toLinearMap

theorem jacDet_comp
  {f g : E → E} {x : E} {f' g' : E →L[𝕜] E}
  (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' (f x)) :
  jacDet (𝕜 := 𝕜) (E := E) (g'.comp f') =
    jacDet (𝕜 := 𝕜) (E := E) g' * jacDet (𝕜 := 𝕜) (E := E) f' := by
  -- purely algebraic: `det (A ∘ B) = det A * det B`
  simpa [jacDet] using (LinearMap.det_comp (g'.toLinearMap) (f'.toLinearMap))

end Jacobian

end Determinant


/-! ---------------------------------------------------------------------------
## 4) Projective gauge fixing (canonical normalization) as a proved lemma
---------------------------------------------------------------------------- -/
namespace GaugeFixing

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]
variable (ν : Measure α)

noncomputable def Z (f : α → ENNReal) : ENNReal := ∫⁻ x, f x ∂ν

noncomputable def canonical (f : α → ENNReal) : Measure α :=
  (Z (ν := ν) f)⁻¹ • (ν.withDensity f)

/-- Projective invariance: scaling the density cancels after normalization. -/
theorem canonical_invariant_smul
    (f : α → ENNReal) (hf : Measurable f)
    (r : ENNReal) (hr0 : r ≠ 0) (hrtop : r ≠ ⊤) :
    canonical (ν := ν) (r • f) = canonical (ν := ν) f := by
  -- expand and push scalars through withDensity and lintegral
  dsimp [canonical, Z]
  -- withDensity scaling
  have hwd : ν.withDensity (r • f) = r • ν.withDensity f := by
    simpa using (withDensity_smul (ν := ν) (r := r) hf)
  -- lintegral scaling
  have hZ : (∫⁻ x, (r • f) x ∂ν) = r * ∫⁻ x, f x ∂ν := by
    -- `Pi.smul_apply` + `smul_eq_mul` for `ENNReal`
    simp [Pi.smul_apply, smul_eq_mul, hf, lintegral_const_mul]
  -- now cancel the scalar in front
  -- (r * Z)⁻¹ • (r • μ) = Z⁻¹ • μ
  -- using `smul_smul` and `ENNReal.mul_inv_cancel`.
  rw [hZ, hwd]
  -- reassociate scalars on measures
  -- ( (r * Zf)⁻¹ * r ) • μ = (Zf)⁻¹ • μ
  -- use commutativity in `ENNReal`
  simp [smul_smul, mul_assoc, mul_left_comm, mul_comm, ENNReal.mul_inv_cancel hr0 hrtop]

end GaugeFixing

end InfoGeometry
