import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# CBO-001: complex bounded operators

This file is the native Lean adapter for the Isabelle/AFP `cblinfun` base
surface from `Complex_Bounded_Operators`.

The AFP donor surface is:

* `('a, 'b) cblinfun`;
* `cblinfun_apply`;
* `cblinfun_eqI`;
* `id_cblinfun`;
* `cblinfun_compose`;
* `norm_cblinfun`.

The Lean owner surface is mathlib's `ContinuousLinearMap` over `ℂ`.
No proof object is transported from Isabelle; all declarations below are
thin, theorem-backed adapters around mathlib.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace Basic

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- CBO-001 carrier: complex bounded linear operators. -/
abbrev CBO (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] : Type _ :=
  E →L[ℂ] F

/-- AFP `cblinfun_apply`, exposed as a named adapter. -/
def apply (T : CBO E F) (x : E) : F :=
  T x

@[simp]
theorem apply_eq (T : CBO E F) (x : E) :
    apply T x = T x :=
  rfl

/-- AFP `cblinfun_eqI`: bounded operators are equal if they agree pointwise. -/
theorem ext {S T : CBO E F} (h : ∀ x : E, S x = T x) : S = T := by
  ext x
  exact h x

/-- AFP `id_cblinfun`, as mathlib's continuous linear identity. -/
def id (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : CBO E E :=
  ContinuousLinearMap.id ℂ E

@[simp]
theorem id_apply (x : E) :
    id E x = x :=
  rfl

/-- AFP `cblinfun_compose`, as mathlib composition. -/
def comp (S : CBO F G) (T : CBO E F) : CBO E G :=
  S.comp T

@[simp]
theorem comp_apply (S : CBO F G) (T : CBO E F) (x : E) :
    comp S T x = S (T x) :=
  rfl

@[simp]
theorem comp_id (T : CBO E F) :
    comp T (id E) = T := by
  ext x
  rfl

@[simp]
theorem id_comp (T : CBO E F) :
    comp (id F) T = T := by
  ext x
  rfl

theorem comp_assoc (R : CBO G G) (S : CBO F G) (T : CBO E F) :
    comp (comp R S) T = comp R (comp S T) := by
  ext x
  rfl

/-! ## Algebraic operation adapters from AFP `Complex_Bounded_Linear_Function0` -/

@[simp]
theorem zero_apply (x : E) :
    (0 : CBO E F) x = 0 :=
  rfl

@[simp]
theorem add_apply (S T : CBO E F) (x : E) :
    (S + T) x = S x + T x :=
  rfl

@[simp]
theorem neg_apply (T : CBO E F) (x : E) :
    (-T) x = -T x :=
  rfl

@[simp]
theorem sub_apply (S T : CBO E F) (x : E) :
    (S - T) x = S x - T x :=
  rfl

@[simp]
theorem smul_apply (c : ℂ) (T : CBO E F) (x : E) :
    (c • T) x = c • T x :=
  rfl

/-- AFP `norm_cblinfun`: operator application is bounded by the operator norm. -/
theorem norm_apply_le (T : CBO E F) (x : E) :
    ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  T.le_opNorm x

/-- AFP `norm_cblinfun_bound`: a pointwise operator bound controls the norm. -/
theorem norm_le_bound (T : CBO E F) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ x : E, ‖T x‖ ≤ b * ‖x‖) :
    ‖T‖ ≤ b :=
  ContinuousLinearMap.opNorm_le_bound T hb h

/-! ## Identity and composition norm adapters -/

theorem norm_id_le :
    ‖id E‖ ≤ (1 : ℝ) :=
  ContinuousLinearMap.norm_id_le

theorem norm_id [NontrivialTopology E] :
    ‖id E‖ = (1 : ℝ) :=
  ContinuousLinearMap.norm_id

theorem norm_comp_le (S : CBO F G) (T : CBO E F) :
    ‖comp S T‖ ≤ ‖S‖ * ‖T‖ :=
  S.opNorm_comp_le T

@[simp]
theorem comp_zero (S : CBO F G) :
    comp S (0 : CBO E F) = 0 := by
  ext x
  rfl

@[simp]
theorem zero_comp (T : CBO E F) :
    comp (0 : CBO F G) T = 0 := by
  ext x
  rfl

end Basic
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
