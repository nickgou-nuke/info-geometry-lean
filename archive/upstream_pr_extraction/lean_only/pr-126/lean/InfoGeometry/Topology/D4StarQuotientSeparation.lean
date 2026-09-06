import InfoGeometry.Topology.D4StarQuotientContinuousAction

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! The orbit quotient has exactly two points: centre and outer orbit. -/

def quotientToBool : D4StarQuotient → Bool :=
  Quotient.lift
    (fun v => match v with
      | Sum.inr _ => true
      | Sum.inl _ => false)
    (by
      intro v w h
      cases v with
      | inl c =>
          cases w with
          | inl d => rfl
          | inr u => exact False.elim h
      | inr u =>
          cases w with
          | inl c => exact False.elim h
          | inr v => rfl)

def boolToQuotient : Bool → D4StarQuotient
  | true => starQuotientMap centralVertex
  | false => starQuotientMap (outerVertex ColorChannel.red)

theorem quotientToBool_boolToQuotient (b : Bool) :
    quotientToBool (boolToQuotient b) = b := by
  cases b <;> rfl

theorem boolToQuotient_quotientToBool (q : D4StarQuotient) :
    boolToQuotient (quotientToBool q) = q := by
  induction q using Quotient.inductionOn with
  | _ v =>
      cases v with
      | inr u => rfl
      | inl c =>
          simpa [boolToQuotient, quotientToBool] using
            (outer_vertices_same_class c ColorChannel.red).symm

noncomputable def d4StarQuotientEquivBool : D4StarQuotient ≃ Bool :=
  { toFun := quotientToBool
    invFun := boolToQuotient
    left_inv := boolToQuotient_quotientToBool
    right_inv := quotientToBool_boolToQuotient }

theorem continuous_quotientToBool :
    Continuous quotientToBool := by
  apply Continuous.quotient_lift
  exact continuous_of_discreteTopology

theorem continuous_boolToQuotient :
    Continuous boolToQuotient := by
  exact continuous_of_discreteTopology

noncomputable def d4StarQuotientHomeomorphBool :
    D4StarQuotient ≃ₜ Bool :=
  { toEquiv := d4StarQuotientEquivBool
    continuous_toFun := continuous_quotientToBool
    continuous_invFun := continuous_boolToQuotient }

@[simp] theorem quotientToBool_centre :
    quotientToBool (starQuotientMap centralVertex) = true := rfl

@[simp] theorem quotientToBool_outer (c : ColorChannel) :
    quotientToBool (starQuotientMap (outerVertex c)) = false := rfl

theorem quotient_has_exactly_two_classes :
    ∃ e : D4StarQuotient ≃ Bool, e = d4StarQuotientEquivBool :=
  ⟨d4StarQuotientEquivBool, rfl⟩

end InfoGeometry.Topology.PauliJungD4Star
