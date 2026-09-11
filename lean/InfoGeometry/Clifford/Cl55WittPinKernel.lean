import InfoGeometry.Clifford.Cl55WittPinCoverBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittPinNativeTwistedAction

namespace InfoGeometry.Clifford.Clifford55

/-!
# Central-kernel theorem for the native Pin action

The scalar `-1` is constructed inside `Pin55` as the square of one negative
Witt reflection vector.  Its action is the identity.  The converse kernel
classification is intentionally not asserted here.
-/

noncomputable def negOnePin : Pin55 := fNegPin 0 * fNegPin 0

theorem negOnePin_coe : (negOnePin : Cl55) = -1 := by
  change (fNegPin 0 : Cl55) * (fNegPin 0 : Cl55) = -1
  rw [fNegPin_coe, ← pow_two, f_neg_sq]

theorem pinTwistedOrthogonalAction_negOnePin :
    pinTwistedOrthogonalAction negOnePin = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change pinTwistedActionEquiv negOnePin v = v
  rw [negOnePin, pinTwistedActionEquiv_mul_all,
    pinTwistedActionEquiv_fNegPin_eq_negativeReflection]
  change negativeReflectionLinearEquiv 0
      (negativeReflectionLinearEquiv 0 v) = v
  simpa only [negativeReflectionLinearEquiv_apply] using
    negativeReflection_involutive 0 v

theorem negOnePin_mem_kernel :
    negOnePin ∈ (pinTwistedOrthogonalAction).ker := by
  change pinTwistedOrthogonalAction negOnePin = 1
  exact pinTwistedOrthogonalAction_negOnePin

theorem negOnePin_ne_one : negOnePin ≠ 1 := by
  intro h
  have hcoe : (negOnePin : Cl55) = (1 : Cl55) := by
    exact congrArg (fun g : Pin55 => (g : Cl55)) h
  rw [negOnePin_coe] at hcoe
  have htwo : (2 : Cl55) = 0 := by
    calc
      (2 : Cl55) = 1 - (-1 : Cl55) := by norm_num
      _ = 1 - 1 := by rw [hcoe]
      _ = 0 := sub_self _
  have htwo' : (2 : Cl55) ≠ 0 := by
    intro hzero
    have hsmul : (2 : ℝ) • (1 : Cl55) = 0 := by
      rw [Algebra.smul_def, mul_one]
      exact hzero
    rcases smul_eq_zero.mp hsmul with h2 | h1
    · norm_num at h2
    · exact one_ne_zero h1
  exact htwo' htwo

theorem negOnePin_sq : negOnePin * negOnePin = 1 := by
  apply Subtype.ext
  change (negOnePin : Cl55) * (negOnePin : Cl55) = (1 : Cl55)
  rw [negOnePin_coe]
  simp

@[simp] theorem negOnePin_inv : negOnePin⁻¹ = negOnePin := by
  calc
    negOnePin⁻¹ = negOnePin⁻¹ * 1 := by simp
    _ = negOnePin⁻¹ * (negOnePin * negOnePin) := by
      rw [negOnePin_sq]
    _ = (negOnePin⁻¹ * negOnePin) * negOnePin := by
      rw [mul_assoc]
    _ = negOnePin := by
      rw [inv_mul_cancel, one_mul]

theorem negOnePin_commute (g : Pin55) :
    negOnePin * g = g * negOnePin := by
  apply Subtype.ext
  change (negOnePin : Cl55) * (g : Cl55) =
    (g : Cl55) * (negOnePin : Cl55)
  rw [negOnePin_coe]
  simp

def pinSignSubgroup : Subgroup Pin55 :=
  Subgroup.closure ({1, negOnePin} : Set Pin55)

theorem mem_pinSignSubgroup_iff (g : Pin55) :
    g ∈ pinSignSubgroup ↔ g = 1 ∨ g = negOnePin := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
        rcases hg with rfl | hg
        · exact Or.inl rfl
        · exact Or.inr (Set.mem_singleton_iff.mp hg)
    | one =>
        exact Or.inl rfl
    | mul g h hg hh hG hH =>
        rcases hG with rfl | rfl <;> rcases hH with rfl | rfl
        · simp
        · simp
        · simp
        · exact Or.inl negOnePin_sq
    | inv_mem g hg =>
        rcases hg with rfl | rfl
        · simp
        · right
          calc
            negOnePin⁻¹ = negOnePin⁻¹ * 1 := by simp
            _ = negOnePin⁻¹ * (negOnePin * negOnePin) := by
              rw [negOnePin_sq]
            _ = (negOnePin⁻¹ * negOnePin) * negOnePin := by
              rw [mul_assoc]
            _ = negOnePin := by
              rw [inv_mul_cancel, one_mul]
  · intro hg
    rcases hg with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl))

theorem pinSignSubgroup_le_center :
    pinSignSubgroup ≤ Subgroup.center Pin55 := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  rcases hg with rfl | hg
  · change (1 : Pin55) ∈ Subgroup.center Pin55
    rw [Subgroup.mem_center_iff]
    intro h
    simp
  · rw [Set.mem_singleton_iff] at hg
    subst g
    change negOnePin ∈ Subgroup.center Pin55
    rw [Subgroup.mem_center_iff]
    intro h
    exact (negOnePin_commute h).symm

instance pinSignSubgroup_normal : pinSignSubgroup.Normal where
  conj_mem g hg h := by
    rcases (mem_pinSignSubgroup_iff g).mp hg with rfl | rfl
    · exact (mem_pinSignSubgroup_iff (h * 1 * h⁻¹)).mpr (Or.inl (by simp))
    · apply (mem_pinSignSubgroup_iff _).mpr
      right
      calc
        h * negOnePin * h⁻¹ = negOnePin * h * h⁻¹ := by
          exact congrArg (fun x => x * h⁻¹) (negOnePin_commute h).symm
        _ = negOnePin := by simp

theorem pinSignSubgroup_le_kernel :
    pinSignSubgroup ≤ (pinTwistedOrthogonalAction).ker := by
  refine (Subgroup.closure_le (pinTwistedOrthogonalAction).ker).2 ?_
  intro g hg
  rcases hg with rfl | rfl
  · simp
  · exact negOnePin_mem_kernel

noncomputable def pinSignQuotientAction :
    (Pin55 ⧸ pinSignSubgroup) →* orthogonalGroup55 :=
  QuotientGroup.lift pinSignSubgroup pinTwistedOrthogonalAction
    pinSignSubgroup_le_kernel

@[simp] theorem pinSignQuotientAction_mk (g : Pin55) :
    pinSignQuotientAction (QuotientGroup.mk' pinSignSubgroup g) =
      pinTwistedOrthogonalAction g := by
  rfl

theorem pinSignQuotientAction_mk_eq_one_iff (g : Pin55) :
    pinSignQuotientAction (QuotientGroup.mk' pinSignSubgroup g) = 1 ↔
      g ∈ (pinTwistedOrthogonalAction).ker := by
  rw [pinSignQuotientAction_mk]
  exact MonoidHom.mem_ker.symm

theorem pinSignQuotientAction_mk_eq_mk_iff (g h : Pin55) :
    pinSignQuotientAction (QuotientGroup.mk' pinSignSubgroup g) =
        pinSignQuotientAction (QuotientGroup.mk' pinSignSubgroup h) ↔
      h⁻¹ * g ∈ (pinTwistedOrthogonalAction).ker := by
  constructor
  · intro heq
    apply (pinSignQuotientAction_mk_eq_one_iff (h⁻¹ * g)).mp
    rw [pinSignQuotientAction_mk]
    rw [map_mul, map_inv]
    rw [← pinSignQuotientAction_mk g,
      ← pinSignQuotientAction_mk h, heq]
    simp
  · intro hker
    have hker' :
        pinTwistedOrthogonalAction (h⁻¹ * g) = 1 :=
      (MonoidHom.mem_ker).mp hker
    have hq :
        pinSignQuotientAction
            (QuotientGroup.mk' pinSignSubgroup (h⁻¹ * g)) = 1 := by
      rw [pinSignQuotientAction_mk]
      exact hker'
    calc
      pinSignQuotientAction (QuotientGroup.mk' pinSignSubgroup g) =
          pinSignQuotientAction
            (QuotientGroup.mk' pinSignSubgroup (h * (h⁻¹ * g))) := by
              simp
      _ = pinSignQuotientAction (QuotientGroup.mk' pinSignSubgroup h) *
          pinSignQuotientAction
            (QuotientGroup.mk' pinSignSubgroup (h⁻¹ * g)) := by
              exact map_mul pinSignQuotientAction
                (QuotientGroup.mk' pinSignSubgroup h)
                (QuotientGroup.mk' pinSignSubgroup (h⁻¹ * g))
      _ = pinSignQuotientAction (QuotientGroup.mk' pinSignSubgroup h) := by
            rw [hq, mul_one]

theorem pinSignSubgroup_le_native_kernel :
    pinSignSubgroup ≤ (pinTwistedNativeOrthogonalAction).ker := by
  refine (Subgroup.closure_le (pinTwistedNativeOrthogonalAction).ker).2 ?_
  intro g hg
  rcases hg with rfl | rfl
  · exact (pinTwistedNativeOrthogonalAction).ker.one_mem
  · change pinTwistedNativeOrthogonalAction negOnePin = 1
    rw [pinTwistedNativeOrthogonalAction_apply,
      pinTwistedOrthogonalAction_negOnePin]
    rfl

noncomputable def pinSignNativeQuotientAction :
    (Pin55 ⧸ pinSignSubgroup) →* Q55.IsometryEquiv Q55 :=
  QuotientGroup.lift pinSignSubgroup pinTwistedNativeOrthogonalAction
    pinSignSubgroup_le_native_kernel

@[simp] theorem pinSignNativeQuotientAction_mk (g : Pin55) :
    pinSignNativeQuotientAction
        (QuotientGroup.mk' pinSignSubgroup g) =
      pinTwistedNativeOrthogonalAction g := by
  rfl

theorem pinSignNativeQuotientAction_mk_eq_one_iff (g : Pin55) :
    pinSignNativeQuotientAction
        (QuotientGroup.mk' pinSignSubgroup g) = 1 ↔
      g ∈ (pinTwistedNativeOrthogonalAction).ker := by
  rw [pinSignNativeQuotientAction_mk]
  exact MonoidHom.mem_ker.symm

theorem pinSignNativeQuotientAction_mk_eq_mk_iff (g h : Pin55) :
    pinSignNativeQuotientAction
        (QuotientGroup.mk' pinSignSubgroup g) =
        pinSignNativeQuotientAction
          (QuotientGroup.mk' pinSignSubgroup h) ↔
      h⁻¹ * g ∈ (pinTwistedNativeOrthogonalAction).ker := by
  constructor
  · intro heq
    apply (pinSignNativeQuotientAction_mk_eq_one_iff (h⁻¹ * g)).mp
    rw [pinSignNativeQuotientAction_mk]
    rw [map_mul, map_inv]
    rw [← pinSignNativeQuotientAction_mk g,
      ← pinSignNativeQuotientAction_mk h, heq]
    simp
  · intro hker
    have hker' :
        pinTwistedNativeOrthogonalAction (h⁻¹ * g) = 1 :=
      (MonoidHom.mem_ker).mp hker
    have hq :
        pinSignNativeQuotientAction
            (QuotientGroup.mk' pinSignSubgroup (h⁻¹ * g)) = 1 := by
      rw [pinSignNativeQuotientAction_mk]
      exact hker'
    calc
      pinSignNativeQuotientAction
          (QuotientGroup.mk' pinSignSubgroup g) =
          pinSignNativeQuotientAction
            (QuotientGroup.mk' pinSignSubgroup (h * (h⁻¹ * g))) := by
              simp
      _ = pinSignNativeQuotientAction
            (QuotientGroup.mk' pinSignSubgroup h) *
          pinSignNativeQuotientAction
            (QuotientGroup.mk' pinSignSubgroup (h⁻¹ * g)) := by
              exact map_mul pinSignNativeQuotientAction
                (QuotientGroup.mk' pinSignSubgroup h)
                (QuotientGroup.mk' pinSignSubgroup (h⁻¹ * g))
      _ = pinSignNativeQuotientAction
            (QuotientGroup.mk' pinSignSubgroup h) := by
            rw [hq, mul_one]

theorem pinSignNativeQuotientAction_mk_readback (g : Pin55) :
    pinSignNativeQuotientAction
        (QuotientGroup.mk' pinSignSubgroup g) =
      orthogonalGroup55IsometryEquiv
        (pinSignQuotientAction (QuotientGroup.mk' pinSignSubgroup g)) := by
  rw [pinSignNativeQuotientAction_mk, pinSignQuotientAction_mk]
  exact pinTwistedNativeOrthogonalAction_apply g

end InfoGeometry.Clifford.Clifford55

