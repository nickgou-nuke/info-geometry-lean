import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Complex quantum geometric tensor for pure states

This is the generic complex-valued owner complementary to the repository's
real doubled/Krein QGT.  A pure state is supplied as a unit vector and the
tangent vectors are explicit data; no manifold or differentiability claim is
smuggled into the definition.  The projective (horizontal) part is therefore
available for arbitrary complex Hilbert spaces, while Mathlib's native
`inner_re_symm` and `inner_im_symm` provide the real/imaginary decomposition.
-/

noncomputable section

namespace InfoGeometry.Quantum

open scoped InnerProductSpace

/-- A normalized pure state in a complex inner-product space. -/
structure UnitPureState (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  vector : E
  norm_eq_one : ‖vector‖ = 1

instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Coe (UnitPureState E) E := ⟨UnitPureState.vector⟩

@[simp] theorem UnitPureState.coe_vector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) : (ψ : E) = ψ.vector := rfl

@[simp] theorem UnitPureState.norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) : ‖(ψ : E)‖ = 1 := ψ.norm_eq_one

/-- The horizontal/projective component of a tangent vector at a pure state. -/
def pureStateHorizontal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (dψ : E) : E :=
  dψ - ⟪(ψ : E), dψ⟫_ℂ • (ψ : E)

theorem pureStateHorizontal_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (dψ : E) :
    ⟪(ψ : E), pureStateHorizontal ψ dψ⟫_ℂ = 0 := by
  unfold pureStateHorizontal
  rw [inner_sub_right, inner_smul_right]
  have hnorm : ⟪(ψ : E), (ψ : E)⟫_ℂ = 1 := by
    apply Complex.ext
    · simpa [real_inner_self_eq_norm_sq] using congrArg (fun x : ℝ => (x : ℂ))
        (show ‖(ψ : E)‖ ^ 2 = (1 : ℝ) by simp [ψ.norm_eq_one])
    · simp
  rw [hnorm, mul_one, sub_self]

theorem pureStateHorizontal_idempotent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (dψ : E) :
    pureStateHorizontal ψ (pureStateHorizontal ψ dψ) =
      pureStateHorizontal ψ dψ := by
  change pureStateHorizontal ψ dψ -
      ⟪(ψ : E), pureStateHorizontal ψ dψ⟫_ℂ • (ψ : E) =
    pureStateHorizontal ψ dψ
  rw [pureStateHorizontal_orthogonal]
  simp

/-- The complex QGT, with the state-direction removed projectively. -/
def complexPureQGT
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u v : U) : ℂ :=
  ⟪pureStateHorizontal ψ (D u), pureStateHorizontal ψ (D v)⟫_ℂ

/-- Real (metric/Fisher) component of the complex pure-state QGT. -/
def complexPureQGTRe
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u v : U) : ℝ :=
  (complexPureQGT ψ D u v).re

/-- Imaginary (Berry-curvature) component of the complex pure-state QGT. -/
def complexPureQGTIm
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u v : U) : ℝ :=
  (complexPureQGT ψ D u v).im

@[simp] theorem complexPureQGT_conj_symm
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u v : U) :
    complexPureQGT ψ D u v = star (complexPureQGT ψ D v u) := by
  unfold complexPureQGT
  simpa only [starRingEnd_apply] using
    (inner_conj_symm
      (pureStateHorizontal ψ (D u)) (pureStateHorizontal ψ (D v))).symm

@[simp] theorem complexPureQGTRe_symm
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u v : U) :
    complexPureQGTRe ψ D u v = complexPureQGTRe ψ D v u := by
  unfold complexPureQGTRe complexPureQGT
  simpa using
    (inner_re_symm (𝕜 := ℂ)
      (pureStateHorizontal ψ (D u)) (pureStateHorizontal ψ (D v)))

@[simp] theorem complexPureQGTIm_skew
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u v : U) :
    complexPureQGTIm ψ D u v = -complexPureQGTIm ψ D v u := by
  unfold complexPureQGTIm complexPureQGT
  simpa using
    (inner_im_symm (𝕜 := ℂ)
      (pureStateHorizontal ψ (D u)) (pureStateHorizontal ψ (D v)))

@[simp] theorem complexPureQGTIm_diag
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u : U) :
    complexPureQGTIm ψ D u u = 0 := by
  have h := complexPureQGTIm_skew ψ D u u
  linarith

theorem complexPureQGTRe_diag_nonneg
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u : U) :
    0 ≤ complexPureQGTRe ψ D u u := by
  unfold complexPureQGTRe complexPureQGT
  let z : E := pureStateHorizontal ψ (D u)
  have h := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) z
  change 0 ≤ RCLike.re (inner ℂ z z)
  rw [← h]
  exact sq_nonneg _

theorem complexPureQGT_re_im_decomposition
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : UnitPureState E) (D : U → E) (u v : U) :
    (complexPureQGTRe ψ D u v : ℂ) +
        (complexPureQGTIm ψ D u v : ℂ) * Complex.I =
      complexPureQGT ψ D u v := by
  exact Complex.re_add_im (complexPureQGT ψ D u v)

end InfoGeometry.Quantum
