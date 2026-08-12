import InfoGeometry.Clifford.Cl55RealSplitPinKernelExact
import InfoGeometry.Clifford.Cl55RealSplitPinProjectiveQuotient
import InfoGeometry.Clifford.RealQuadraticReflection
import InfoGeometry.Clifford.Cl55WittNativeCartanDieudonne

namespace InfoGeometry.Clifford.Clifford55

/-!
# Native group structure and split-Pin action on the quadratic isometry group

 Mathlib provides composition and inversion for `QuadraticMap.IsometryEquiv`,
but not a `Group` instance for the endomorphism case.  The generic lawful
instance is supplied by `RealQuadraticReflection`; this file transports the
already verified split-Pin action to the native `Q55` group.
-/

noncomputable def realSplitPinNativeOrthogonalAction :
    realSplitPin55 →* Q55.IsometryEquiv Q55 :=
  orthogonalGroup55MulEquiv.toMonoidHom.comp realSplitPinOrthogonalAction

@[simp] theorem realSplitPinNativeOrthogonalAction_apply
    (g : realSplitPin55) :
    realSplitPinNativeOrthogonalAction g =
      orthogonalGroup55IsometryEquiv (realSplitPinOrthogonalAction g) :=
  rfl

theorem nativeQuadraticReflection_mem_realSplitPinNativeImage
    (v : V55) (hv : Q55 v ≠ 0) :
    realQuadraticReflectionIsometry Q55 v hv ∈
      Subgroup.map realSplitPinNativeOrthogonalAction ⊤ := by
  rcases quadraticReflection_mem_realSplitPin_image v hv with ⟨g, -, hg⟩
  refine ⟨g, trivial, ?_⟩
  change orthogonalGroup55IsometryEquiv
      (realSplitPinOrthogonalAction g) =
    realQuadraticReflectionIsometry Q55 v hv
  rw [hg]
  exact orthogonalGroup55IsometryEquiv.apply_symm_apply _

theorem nativeQuadraticReflectionSubgroup_le_realSplitPinNativeImage :
    nativeQuadraticReflectionSubgroup ≤
      Subgroup.map realSplitPinNativeOrthogonalAction ⊤ := by
  change Subgroup.closure nativeQuadraticReflectionSet ≤ _
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨v, hv, rfl⟩
  exact nativeQuadraticReflection_mem_realSplitPinNativeImage v hv

theorem realSplitPinNativeOrthogonalAction_map_top_eq_top :
    Subgroup.map realSplitPinNativeOrthogonalAction ⊤ =
      (⊤ : Subgroup (Q55.IsometryEquiv Q55)) := by
  apply le_antisymm le_top
  rw [← nativeQuadraticReflectionSubgroup_eq_top]
  exact nativeQuadraticReflectionSubgroup_le_realSplitPinNativeImage

theorem realSplitPinNativeOrthogonalAction_surjective :
    Function.Surjective realSplitPinNativeOrthogonalAction := by
  intro h
  have hh : h ∈ Subgroup.map realSplitPinNativeOrthogonalAction ⊤ := by
    rw [realSplitPinNativeOrthogonalAction_map_top_eq_top]
    trivial
  rcases hh with ⟨g, -, hgh⟩
  exact ⟨g, hgh⟩

theorem realSplitPinNative_reflection_factorization
    (f : Q55.IsometryEquiv Q55) :
    ∃ l : List realSplitPin55,
      realSplitPinNativeOrthogonalAction
          (l.foldr (· * ·) 1) = f ∧
        (∀ g ∈ l, ∃ v : V55, ∃ hv : Q55 v ≠ 0,
          realSplitPinNativeOrthogonalAction g =
            realQuadraticReflectionIsometry Q55 v hv) := by
  classical
  rcases nativeQuadraticReflection_factorization f with
    ⟨lr, hlr, hprod⟩
  have hlift : ∀ (lr : List (Q55.IsometryEquiv Q55)),
      (∀ r ∈ lr, r ∈ nativeQuadraticReflectionSet) →
      ∃ lp : List realSplitPin55,
        realSplitPinNativeOrthogonalAction
            (lp.foldr (· * ·) 1) =
          nativeQuadraticReflectionProduct lr ∧
        (∀ g ∈ lp, ∃ v : V55, ∃ hv : Q55 v ≠ 0,
          realSplitPinNativeOrthogonalAction g =
            realQuadraticReflectionIsometry Q55 v hv) := by
    intro lr
    induction lr with
    | nil =>
        intro _
        exact ⟨[], by
          simp [realSplitPinNativeOrthogonalAction,
            nativeQuadraticReflectionProduct], by simp⟩
    | cons r rs ih =>
        intro hlr
        have hr : r ∈ nativeQuadraticReflectionSet := hlr r (by simp)
        have hrs : ∀ s ∈ rs, s ∈ nativeQuadraticReflectionSet := by
          intro s hs
          exact hlr s (by simp [hs])
        rcases hr with ⟨v, hv, rfl⟩
        rcases nativeQuadraticReflection_mem_realSplitPinNativeImage v hv with
          ⟨g, -, hg⟩
        rcases ih hrs with ⟨lp, hlp, hlpmem⟩
        refine ⟨g :: lp, ?_, ?_⟩
        · simp only [List.foldr_cons, map_mul, hg, hlp,
            nativeQuadraticReflectionProduct]
        · intro h hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact ⟨v, hv, hg⟩
          · exact hlpmem h hmem
  rcases hlift lr hlr with ⟨lp, hlp, hlpmem⟩
  exact ⟨lp, by rw [hlp, hprod], hlpmem⟩

theorem realSplitPinNativeOrthogonalAction_mem_kernel_iff :
    ∀ g : realSplitPin55,
      g ∈ (realSplitPinNativeOrthogonalAction).ker ↔
      g ∈ realSplitPinSignSubgroup := by
  intro g
  have heone : orthogonalGroup55IsometryEquiv (1 : orthogonalGroup55) =
      (1 : Q55.IsometryEquiv Q55) := by
    apply DFunLike.ext _ _
    intro x
    rfl
  constructor
  · intro hg
    have hold : realSplitPinOrthogonalAction g = 1 := by
      apply orthogonalGroup55IsometryEquiv.injective
      calc
        orthogonalGroup55IsometryEquiv
            (realSplitPinOrthogonalAction g) =
            realSplitPinNativeOrthogonalAction g := rfl
        _ = 1 := hg
        _ = orthogonalGroup55IsometryEquiv (1 : orthogonalGroup55) :=
          heone.symm
    exact (realSplitPinOrthogonalAction_kernel_eq_signSubgroup).symm ▸ hold
  · intro hg
    have hold : realSplitPinOrthogonalAction g = 1 :=
      (realSplitPinOrthogonalAction_mem_kernel_iff_pm_one g).mpr
        (show (g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1 from hg)
    calc
      realSplitPinNativeOrthogonalAction g =
          orthogonalGroup55IsometryEquiv
            (realSplitPinOrthogonalAction g) := rfl
      _ = orthogonalGroup55IsometryEquiv (1 : orthogonalGroup55) :=
        congrArg orthogonalGroup55IsometryEquiv hold
      _ = 1 := heone

theorem realSplitPinNativeOrthogonalAction_mem_kernel_iff_pm_one
    (g : realSplitPin55) :
    g ∈ (realSplitPinNativeOrthogonalAction).ker ↔
      (g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1 := by
  rw [realSplitPinNativeOrthogonalAction_mem_kernel_iff]
  rfl

theorem realSplitPinNativeOrthogonalAction_kernel_eq_signSubgroup :
    (realSplitPinNativeOrthogonalAction).ker = realSplitPinSignSubgroup := by
  ext g
  exact realSplitPinNativeOrthogonalAction_mem_kernel_iff g

theorem realSplitPinSignSubgroup_native_inclusion_mulExact :
    Function.MulExact
      (realSplitPinSignSubgroup.subtype :
        realSplitPinSignSubgroup →* realSplitPin55)
      realSplitPinNativeOrthogonalAction := by
  intro g
  constructor
  · intro hg
    exact ⟨⟨g, (realSplitPinNativeOrthogonalAction_mem_kernel_iff g).mp hg⟩, rfl⟩
  · intro hg
    rcases hg with ⟨h, hh⟩
    rw [← hh]
    exact (realSplitPinNativeOrthogonalAction_mem_kernel_iff h).mpr h.property

noncomputable def realSplitPinNativeSignQuotientEquiv :
    (realSplitPin55 ⧸
      (realSplitPinSignSubgroup : Subgroup realSplitPin55)) ≃*
      Q55.IsometryEquiv Q55 := by
  exact
    (QuotientGroup.quotientMulEquivOfEq
      realSplitPinNativeOrthogonalAction_kernel_eq_signSubgroup).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective
        realSplitPinNativeOrthogonalAction
        realSplitPinNativeOrthogonalAction_surjective)

theorem realSplitPinNativeSignQuotientEquiv_mk
    (g : realSplitPin55) :
    realSplitPinNativeSignQuotientEquiv (QuotientGroup.mk g) =
      realSplitPinNativeOrthogonalAction g := by
  rfl

theorem realSplitPinNativeSignQuotientEquiv_eq_transport
    : realSplitPinNativeSignQuotientEquiv =
      realSplitPinSignQuotientEquiv.trans orthogonalGroup55MulEquiv := by
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro g
  change realSplitPinNativeOrthogonalAction g =
    orthogonalGroup55MulEquiv
      (realSplitPinSignQuotientEquiv (QuotientGroup.mk g))
  have hsign :
      realSplitPinSignQuotientEquiv (QuotientGroup.mk g) =
        realSplitPinOrthogonalAction g := by
    rfl
  rw [hsign]
  rfl

end InfoGeometry.Clifford.Clifford55
