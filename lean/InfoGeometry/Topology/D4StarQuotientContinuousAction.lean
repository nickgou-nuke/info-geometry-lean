import InfoGeometry.Topology.D4StarGraphQuotient
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Continuity of the induced finite color action on the orbit quotient. -/

theorem continuous_starQuotientMap :
    Continuous starQuotientMap := by
  exact continuous_quotient_mk'

theorem continuous_quotientColorAction
    (σ : Equiv.Perm ColorChannel) :
    Continuous (quotientColorAction σ) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp (continuous_vertexPermutation σ)

theorem continuous_quotientColorAction_inverse
    (σ : Equiv.Perm ColorChannel) :
    Continuous (quotientColorAction σ.symm) := by
  exact continuous_quotientColorAction σ.symm

theorem quotientColorAction_comp
    (σ τ : Equiv.Perm ColorChannel) (q : D4StarQuotient) :
    quotientColorAction σ (quotientColorAction τ q) =
      quotientColorAction (σ * τ) q := by
  induction q using Quotient.inductionOn with
  | _ v =>
      cases v <;> rfl

theorem quotientColorAction_identity (q : D4StarQuotient) :
    quotientColorAction (1 : Equiv.Perm ColorChannel) q = q := by
  induction q using Quotient.inductionOn with
  | _ v =>
      cases v <;> rfl

def quotientColorHomeomorph (σ : Equiv.Perm ColorChannel) :
    D4StarQuotient ≃ₜ D4StarQuotient :=
  { toEquiv :=
      { toFun := quotientColorAction σ
        invFun := quotientColorAction σ.symm
        left_inv := by
          intro q
          rw [quotientColorAction_comp]
          simpa using quotientColorAction_identity q
        right_inv := by
          intro q
          rw [quotientColorAction_comp]
          simpa using quotientColorAction_identity q }
    continuous_toFun := continuous_quotientColorAction σ
    continuous_invFun := continuous_quotientColorAction_inverse σ }

@[simp] theorem quotientColorHomeomorph_centre
    (σ : Equiv.Perm ColorChannel) :
    quotientColorHomeomorph σ (starQuotientMap centralVertex) =
      starQuotientMap centralVertex := by
  exact quotientColorAction_centre σ

@[simp] theorem quotientColorHomeomorph_outer
    (σ : Equiv.Perm ColorChannel) (c : ColorChannel) :
    quotientColorHomeomorph σ (starQuotientMap (outerVertex c)) =
      starQuotientMap (outerVertex c) := by
  change quotientColorAction σ
      (starQuotientMap (outerVertex c)) =
    starQuotientMap (outerVertex c)
  rw [quotientColorAction_outer_moved, outer_vertices_same_class]

@[simp] theorem quotientColorAction_eq_id
    (σ : Equiv.Perm ColorChannel) :
    quotientColorAction σ = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro v
  cases v with
  | inl c =>
      change quotientColorAction σ
          (starQuotientMap (outerVertex c)) =
        starQuotientMap (outerVertex c)
      rw [quotientColorAction_outer_moved, outer_vertices_same_class]
  | inr centre =>
      cases centre
      change quotientColorAction σ (starQuotientMap centralVertex) =
        starQuotientMap centralVertex
      exact quotientColorAction_centre σ

@[simp] theorem quotientColorHomeomorph_eq_refl
    (σ : Equiv.Perm ColorChannel) :
    quotientColorHomeomorph σ =
      Homeomorph.refl D4StarQuotient := by
  ext q
  exact congrFun (quotientColorAction_eq_id σ) q

end InfoGeometry.Topology.PauliJungD4Star
