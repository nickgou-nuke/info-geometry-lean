import InfoGeometry.Clifford.Cl55WittPinKernel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Spin55NativeOrthogonalKernelReduction

namespace InfoGeometry.Clifford.Clifford55

/-!
# Central sign kernel for the native `Spin(5,5)` action

The square of a negative Witt reflection is the scalar `-1`.  Since this
scalar is even, it has a native `Spin55` representative.  Its orthogonal
action is trivial and it is nontrivial as a group element.  This owner proves
the central kernel subgroup and its quotient action; it does not classify the
full native kernel.
-/

noncomputable def negOneSpin : Spin55 :=
  ⟨pinToUnits negOnePin, by
    change (pinToUnits negOnePin : Cl55) ∈ spinGroup Q55
    rw [spinGroup.mem_iff]
    constructor
    · change (pinToUnits negOnePin : Cl55) ∈ pinGroup Q55
      exact negOnePin.property
    · have hcoe : (pinToUnits negOnePin : Cl55) = (-1 : Cl55) := by
        change (negOnePin : Cl55) = -1
        exact negOnePin_coe
      rw [hcoe]
      change (-1 : Cl55) ∈ CliffordAlgebra.even Q55
      convert (CliffordAlgebra.even Q55).algebraMap_mem (-1 : ℝ) using 1
      all_goals simp⟩

theorem spinToPin_negOneSpin :
    spinToPin negOneSpin = negOnePin := by
  apply Subtype.ext
  rfl

theorem negOneSpin_action :
    spinActionIsometryEquiv negOneSpin = 1 := by
  apply DFunLike.ext _ _
  intro v
  change spinAction negOneSpin v = v
  change pinTwistedAction (spinToPin negOneSpin) v = v
  rw [spinToPin_negOneSpin, negOnePin, pinTwistedAction_mul]
  change pinTwistedAction (fNegPin 0)
      (pinTwistedAction (fNegPin 0) v) = v
  rw [pinTwistedAction_f_neg_eq_negativeReflection]
  change negativeReflectionLinearEquiv 0
      (negativeReflectionLinearEquiv 0 v) = v
  exact negativeReflection_involutive 0 v

theorem negOneSpin_mem_kernel :
    negOneSpin ∈ (spinNativeOrthogonalAction).ker := by
  rw [MonoidHom.mem_ker]
  change spinActionIsometryEquiv negOneSpin = 1
  exact negOneSpin_action

theorem negOneSpin_ne_one :
    negOneSpin ≠ 1 := by
  intro h
  have hpin : spinToPin negOneSpin = spinToPin (1 : Spin55) :=
    congrArg spinToPin h
  rw [spinToPin_negOneSpin] at hpin
  have hneg : negOnePin = 1 := by
    simpa using hpin
  exact negOnePin_ne_one hneg

theorem negOneSpin_sq : negOneSpin * negOneSpin = 1 := by
  apply Subtype.ext
  change (pinToUnits negOnePin : Cl55) *
      (pinToUnits negOnePin : Cl55) = (1 : Cl55)
  change (negOnePin : Cl55) * (negOnePin : Cl55) = (1 : Cl55)
  rw [negOnePin_coe]
  simp

theorem negOneSpin_commute (g : Spin55) :
    negOneSpin * g = g * negOneSpin := by
  apply Subtype.ext
  change (pinToUnits negOnePin : Cl55) * (g : Cl55) =
    (g : Cl55) * (pinToUnits negOnePin : Cl55)
  change (negOnePin : Cl55) * (g : Cl55) =
    (g : Cl55) * (negOnePin : Cl55)
  rw [negOnePin_coe]
  simp

def spinSignSubgroup : Subgroup Spin55 :=
  Subgroup.closure ({1, negOneSpin} : Set Spin55)

theorem mem_spinSignSubgroup_iff (g : Spin55) :
    g ∈ spinSignSubgroup ↔ g = 1 ∨ g = negOneSpin := by
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
        · exact Or.inl negOneSpin_sq
    | inv_mem g hg =>
        rcases hg with rfl | rfl
        · simp
        · right
          calc
            negOneSpin⁻¹ = negOneSpin⁻¹ * 1 := by simp
            _ = negOneSpin⁻¹ * (negOneSpin * negOneSpin) := by
              rw [negOneSpin_sq]
            _ = (negOneSpin⁻¹ * negOneSpin) * negOneSpin := by
              rw [mul_assoc]
            _ = negOneSpin := by simp
  · intro hg
    rcases hg with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure
        (Set.mem_insert_iff.mpr (Or.inr rfl))

theorem spinSignSubgroup_le_center :
    spinSignSubgroup ≤ Subgroup.center Spin55 := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  rcases hg with rfl | hg
  · change (1 : Spin55) ∈ Subgroup.center Spin55
    rw [Subgroup.mem_center_iff]
    intro h
    simp
  · rw [Set.mem_singleton_iff] at hg
    subst g
    change negOneSpin ∈ Subgroup.center Spin55
    rw [Subgroup.mem_center_iff]
    intro h
    exact (negOneSpin_commute h).symm

instance spinSignSubgroup_normal : spinSignSubgroup.Normal where
  conj_mem g hg h := by
    rcases (mem_spinSignSubgroup_iff g).mp hg with rfl | rfl
    · exact (mem_spinSignSubgroup_iff (h * 1 * h⁻¹)).mpr (Or.inl (by simp))
    · apply (mem_spinSignSubgroup_iff _).mpr
      right
      calc
        h * negOneSpin * h⁻¹ = negOneSpin * h * h⁻¹ := by
          exact congrArg (fun x => x * h⁻¹) (negOneSpin_commute h).symm
        _ = negOneSpin := by simp

theorem spinSignSubgroup_le_nativeSpinKernel :
    spinSignSubgroup ≤ (spinNativeOrthogonalAction).ker := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  rcases hg with rfl | hg
  · exact (spinNativeOrthogonalAction).ker.one_mem
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact negOneSpin_mem_kernel

theorem spinToPinHom_map_spinSignSubgroup :
    Subgroup.map spinToPinHom spinSignSubgroup = pinSignSubgroup := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨g, hg, rfl⟩
    rcases (mem_spinSignSubgroup_iff g).mp hg with rfl | rfl
    · exact (mem_pinSignSubgroup_iff (1 : Pin55)).mpr (Or.inl rfl)
    · change spinToPin negOneSpin ∈ pinSignSubgroup
      rw [spinToPin_negOneSpin]
      exact (mem_pinSignSubgroup_iff negOnePin).mpr (Or.inr rfl)
  · intro hp
    rcases (mem_pinSignSubgroup_iff p).mp hp with rfl | rfl
    · refine ⟨1, (mem_spinSignSubgroup_iff (1 : Spin55)).mpr (Or.inl rfl), ?_⟩
      rfl
    · refine ⟨negOneSpin,
        (mem_spinSignSubgroup_iff negOneSpin).mpr (Or.inr rfl), ?_⟩
      exact spinToPin_negOneSpin

noncomputable def spinSignQuotientAction :
    (Spin55 ⧸ spinSignSubgroup) →* Q55.IsometryEquiv Q55 :=
  QuotientGroup.lift spinSignSubgroup spinNativeOrthogonalAction
    spinSignSubgroup_le_nativeSpinKernel

@[simp] theorem spinSignQuotientAction_mk (g : Spin55) :
    spinSignQuotientAction (QuotientGroup.mk' spinSignSubgroup g) =
      spinNativeOrthogonalAction g := by
  rfl

theorem spinSignQuotientAction_mk_eq_one_iff (g : Spin55) :
    spinSignQuotientAction (QuotientGroup.mk' spinSignSubgroup g) = 1 ↔
      g ∈ (spinNativeOrthogonalAction).ker := by
  rw [spinSignQuotientAction_mk]
  exact MonoidHom.mem_ker.symm

theorem spinSignQuotientAction_mk_eq_mk_iff (g h : Spin55) :
    spinSignQuotientAction (QuotientGroup.mk' spinSignSubgroup g) =
        spinSignQuotientAction (QuotientGroup.mk' spinSignSubgroup h) ↔
      h⁻¹ * g ∈ (spinNativeOrthogonalAction).ker := by
  constructor
  · intro heq
    apply (spinSignQuotientAction_mk_eq_one_iff (h⁻¹ * g)).mp
    rw [spinSignQuotientAction_mk]
    rw [map_mul, map_inv]
    rw [← spinSignQuotientAction_mk g,
      ← spinSignQuotientAction_mk h, heq]
    simp
  · intro hk
    have hker :
        spinNativeOrthogonalAction (h⁻¹ * g) = 1 :=
      MonoidHom.mem_ker.mpr hk
    have hq :
        spinSignQuotientAction
            (QuotientGroup.mk' spinSignSubgroup (h⁻¹ * g)) = 1 := by
      rw [spinSignQuotientAction_mk]
      exact hker
    calc
      spinSignQuotientAction (QuotientGroup.mk' spinSignSubgroup g) =
          spinSignQuotientAction
            (QuotientGroup.mk' spinSignSubgroup (h * (h⁻¹ * g))) := by
        simp
      _ = spinSignQuotientAction (QuotientGroup.mk' spinSignSubgroup h) *
          spinSignQuotientAction
            (QuotientGroup.mk' spinSignSubgroup (h⁻¹ * g)) := by
        exact map_mul spinSignQuotientAction
          (QuotientGroup.mk' spinSignSubgroup h)
          (QuotientGroup.mk' spinSignSubgroup (h⁻¹ * g))
      _ = spinSignQuotientAction (QuotientGroup.mk' spinSignSubgroup h) := by
        rw [hq, mul_one]

theorem nativeSpinKernel_nontrivial :
    Nontrivial ((spinNativeOrthogonalAction).ker : Subgroup Spin55) := by
  exact ⟨⟨1, (spinNativeOrthogonalAction).ker.one_mem⟩,
    ⟨negOneSpin, negOneSpin_mem_kernel⟩, by
      intro h
      have hval : (1 : Spin55) = negOneSpin := congrArg Subtype.val h
      exact negOneSpin_ne_one hval.symm⟩

end InfoGeometry.Clifford.Clifford55
