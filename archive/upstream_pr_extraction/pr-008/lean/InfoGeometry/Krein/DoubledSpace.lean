import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import InfoGeometry.Krein.KreinSpace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra.Basic

/-!
# InfoGeometry.Krein.DoubledSpace

Canonical diagonal (Pontryagin) model of the doubled information state space.
The carrier is `WithLp 2 (E × E)`, and the fundamental symmetry is the sign flip
`J(x, ξ) = (x, -ξ)`.
-/

namespace InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The doubled space E ⊕ E as the canonical L² carrier. -/
abbrev DoubledSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  WithLp 2 (E × E)

-- Projection and constructor API for DoubledSpace
def toDoubled (x ξ : E) : DoubledSpace E := WithLp.toLp 2 (x, ξ)
def DoubledSpace.fst (u : DoubledSpace E) : E := (WithLp.ofLp u).1
def DoubledSpace.snd (u : DoubledSpace E) : E := (WithLp.ofLp u).2

@[simp] lemma fst_toDoubled (x ξ : E) : (toDoubled x ξ).fst = x := rfl
@[simp] lemma snd_toDoubled (x ξ : E) : (toDoubled x ξ).snd = ξ := rfl
@[simp] lemma toDoubled_fst_snd (u : DoubledSpace E) : toDoubled u.fst u.snd = u := by
  simp [toDoubled, DoubledSpace.fst, DoubledSpace.snd, WithLp.toLp_ofLp]

/-- The Hessian indefinite form on DoubledSpace.
In the diagonal basis, this is exactly the Krein inner product: [x, ξ]·[y, η] = ⟪x, y⟫ - ⟪ξ, η⟫. -/
noncomputable def hessianIndefiniteForm (u v : DoubledSpace E) : ℝ :=
  KreinSpace.kreinInner u v

/-- Characterization of Krein skew-adjointness as infinitesimal Hessian invariance. -/
def IsKreinSkewAdjoint (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  KreinSpace.IsKreinSkewAdjoint A

theorem IsKreinSkewAdjoint.hessian_infinitesimal
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsKreinSkewAdjoint A)
    (x y : DoubledSpace E) :
    hessianIndefiniteForm (A x) y + hessianIndefiniteForm x (A y) = 0 :=
  (KreinSpace.isKreinSkewAdjoint_iff A).mp hA x y

/-- The Lie algebra of the information state space (Information Killing Fields). -/
noncomputable def informationLieAlgebra (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    LieSubalgebra ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) where
  carrier := {A | IsKreinSkewAdjoint A}
  zero_mem' := by simp [IsKreinSkewAdjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg]
  add_mem' hA hB := by
    simp [IsKreinSkewAdjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at *
    rw [KreinSpace.kreinAdjoint_add, hA, hB, neg_add]
  smul_mem' c A hA := by
    simp [IsKreinSkewAdjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at *
    rw [KreinSpace.kreinAdjoint_smul, hA, smul_neg]
  lie_mem' hA hB := by
    simp [IsKreinSkewAdjoint, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at *
    rw [KreinSpace.kreinAdjoint_lie, hA, hB]
    simp [Ring.lie_def, neg_mul, mul_neg, neg_neg]
    rw [neg_sub, add_comm]

end InfoGeometry.Krein
