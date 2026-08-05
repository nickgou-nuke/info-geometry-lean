import InfoGeometry.Clifford.Cl55RealSplitPin

namespace InfoGeometry.Clifford.Clifford55

/-!
# Twisted action of the real split Pin generator subgroup

`pinGroup Q55` is Mathlib's unitary Pin subgroup and excludes positive
normalized Witt vectors for the present Clifford star convention.  The
generator-level split subgroup `realSplitPin55` retains both signatures.  Its
Lipschitz membership is enough for the native twisted action to preserve the
Clifford vector range; the parity lemma then proves preservation of `Q55`.
-/

noncomputable def realSplitPinTwistedAdj
    (g : realSplitPin55) (v : V55) : Cl55 :=
  CliffordAlgebra.involute (Q := Q55) ((g : Cl55ˣ) : Cl55) * ι55 v *
    (↑((g : Cl55ˣ)⁻¹) : Cl55)

noncomputable def globalSheetRealSplitPin : realSplitPin55 :=
  ⟨globalSheetUnit, globalSheetUnit_mem_realSplitPin⟩

theorem realSplitPinTwistedAdj_globalSheet (v : V55) :
    realSplitPinTwistedAdj globalSheetRealSplitPin v =
      ι55 (globalSheetReflection v) := by
  have hu :
      ((globalSheetRealSplitPin : realSplitPin55) : Cl55ˣ) =
        pinToUnits globalSheetPin := by
    apply Units.ext
    exact globalSheetUnit_coe
  rw [realSplitPinTwistedAdj, hu]
  exact pinTwistedAdj_globalSheetPin v

theorem realSplitPinTwistedAdj_mem_ι_range
    (g : realSplitPin55) (v : V55) :
    realSplitPinTwistedAdj g v ∈ LinearMap.range (ι55) := by
  exact lipschitzGroup.involute_act_ι_mem_range_ι
    (realSplitPin_mem_lipschitz (g : Cl55ˣ) g.property) v

noncomputable def realSplitPinTwistedAmbientLinear
    (g : realSplitPin55) : Cl55 →ₗ[ℝ] Cl55 where
  toFun x := CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55) * x *
    (↑((g : Cl55ˣ)⁻¹) : Cl55)
  map_add' x y := by
    rw [mul_add, add_mul]
  map_smul' r x := by
    simp only [Algebra.smul_def]
    calc
      CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55) *
          (algebraMap ℝ Cl55 r * x) *
            (↑((g : Cl55ˣ)⁻¹) : Cl55) =
        algebraMap ℝ Cl55 r *
          (CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55) * x *
            (↑((g : Cl55ˣ)⁻¹) : Cl55)) := by
          have hcomm :
              CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55) *
                  algebraMap ℝ Cl55 r =
                algebraMap ℝ Cl55 r *
                  CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55) :=
            (Algebra.commutes r
              (CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55))).symm
          rw [← mul_assoc, hcomm]
          ac_rfl
      _ = r •
          (CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55) * x *
            (↑((g : Cl55ˣ)⁻¹) : Cl55)) := by
          rw [Algebra.smul_def]

noncomputable def realSplitPinTwistedRangeEndomorphism
    (g : realSplitPin55) :
    LinearMap.range (ι55) →ₗ[ℝ] LinearMap.range (ι55) :=
  LinearMap.codRestrict (LinearMap.range (ι55))
    ((realSplitPinTwistedAmbientLinear g).comp
      (LinearMap.range (ι55)).subtype)
    (by
      intro z
      rcases z.property with ⟨v, hv⟩
      change realSplitPinTwistedAmbientLinear g (z : Cl55) ∈
        LinearMap.range (ι55)
      rw [← hv]
      exact realSplitPinTwistedAdj_mem_ι_range g v)

noncomputable def realSplitPinTwistedAction
    (g : realSplitPin55) : V55 →ₗ[ℝ] V55 :=
  ι55RangeEquiv.symm.toLinearMap.comp
    ((realSplitPinTwistedRangeEndomorphism g).comp
      ι55RangeEquiv.toLinearMap)

theorem realSplitPinTwistedAction_apply_ι
    (g : realSplitPin55) (v : V55) :
    ι55 (realSplitPinTwistedAction g v) =
      realSplitPinTwistedAdj g v := by
  have h := congrArg
      (fun z : LinearMap.range (ι55) => (z : Cl55))
      (show ι55RangeEquiv (realSplitPinTwistedAction g v) =
          realSplitPinTwistedRangeEndomorphism g (ι55RangeEquiv v) by
        change ι55RangeEquiv
            (ι55RangeEquiv.symm
              (realSplitPinTwistedRangeEndomorphism g (ι55RangeEquiv v))) = _
        exact ι55RangeEquiv.apply_symm_apply _)
  exact h

theorem realSplitPinTwistedAction_globalSheet_eq_globalSheetReflection :
    realSplitPinTwistedAction globalSheetRealSplitPin =
      globalSheetReflectionLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  rw [realSplitPinTwistedAction_apply_ι,
    realSplitPinTwistedAdj_globalSheet]
  rfl

theorem realSplitPinTwistedAction_mul
    (g h : realSplitPin55) :
    realSplitPinTwistedAction (g * h) =
      (realSplitPinTwistedAction g).comp
        (realSplitPinTwistedAction h) := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  change ι55 (realSplitPinTwistedAction (g * h) v) =
    ι55 (realSplitPinTwistedAction g
      (realSplitPinTwistedAction h v))
  rw [realSplitPinTwistedAction_apply_ι (g * h) v]
  simp [realSplitPinTwistedAdj, Subgroup.coe_mul, Units.val_mul,
    map_mul, mul_inv_rev, mul_assoc,
    realSplitPinTwistedAction_apply_ι]

theorem realSplitPinTwistedAction_one :
    realSplitPinTwistedAction (1 : realSplitPin55) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  rw [realSplitPinTwistedAction_apply_ι]
  simp [realSplitPinTwistedAdj]

noncomputable def realSplitPinTwistedActionEquiv
    (g : realSplitPin55) : V55 ≃ₗ[ℝ] V55 :=
  LinearEquiv.ofLinear
    (realSplitPinTwistedAction g)
    (realSplitPinTwistedAction g⁻¹)
    (by
      rw [← realSplitPinTwistedAction_mul, mul_inv_cancel,
        realSplitPinTwistedAction_one])
    (by
      rw [← realSplitPinTwistedAction_mul, inv_mul_cancel,
        realSplitPinTwistedAction_one])

theorem realSplitPinTwistedActionEquiv_mul (g h : realSplitPin55) :
    realSplitPinTwistedActionEquiv (g * h) =
      realSplitPinTwistedActionEquiv g *
        realSplitPinTwistedActionEquiv h := by
  apply LinearEquiv.ext
  intro v
  change realSplitPinTwistedAction (g * h) v =
    realSplitPinTwistedAction g (realSplitPinTwistedAction h v)
  rw [realSplitPinTwistedAction_mul]
  rfl

theorem realSplitPinTwistedAction_preserves_Q55
    (g : realSplitPin55) (v : V55) :
    Q55 (realSplitPinTwistedAction g v) = Q55 v := by
  have hparity := lipschitzUnit_involute_eq_or_neg
    (g : Cl55ˣ) (realSplitPin_mem_lipschitz (g : Cl55ˣ) g.property)
  have hunit :
      (↑((g : Cl55ˣ)⁻¹) : Cl55) * ((g : Cl55ˣ) : Cl55) = 1 := by
    exact Units.inv_mul (g : Cl55ˣ)
  have hunitRight :
      ((g : Cl55ˣ) : Cl55) * (↑((g : Cl55ˣ)⁻¹) : Cl55) = 1 := by
    exact Units.mul_inv (g : Cl55ˣ)
  have hconjSquare :
      (((g : Cl55ˣ) : Cl55) * ι55 v *
          (↑((g : Cl55ˣ)⁻¹) : Cl55)) *
        (((g : Cl55ˣ) : Cl55) * ι55 v *
          (↑((g : Cl55ˣ)⁻¹) : Cl55)) =
      ι55 v * ι55 v := by
    calc
      _ = ((g : Cl55ˣ) : Cl55) * ι55 v *
          (((↑((g : Cl55ˣ)⁻¹) : Cl55) *
            ((g : Cl55ˣ) : Cl55))) * ι55 v *
          (↑((g : Cl55ˣ)⁻¹) : Cl55) := by noncomm_ring
      _ = ((g : Cl55ˣ) : Cl55) * ι55 v * 1 * ι55 v *
          (↑((g : Cl55ˣ)⁻¹) : Cl55) := by rw [hunit]
      _ = ((g : Cl55ˣ) : Cl55) * (ι55 v * ι55 v) *
          (↑((g : Cl55ˣ)⁻¹) : Cl55) := by noncomm_ring
      _ = ((g : Cl55ˣ) : Cl55) * algebraMap ℝ Cl55 (Q55 v) *
          (↑((g : Cl55ˣ)⁻¹) : Cl55) := by
            rw [CliffordAlgebra.ι_sq_scalar]
      _ = algebraMap ℝ Cl55 (Q55 v) *
          (((g : Cl55ˣ) : Cl55) *
            (↑((g : Cl55ˣ)⁻¹) : Cl55)) := by
            have hcomm :
                ((g : Cl55ˣ) : Cl55) * algebraMap ℝ Cl55 (Q55 v) =
                  algebraMap ℝ Cl55 (Q55 v) * ((g : Cl55ˣ) : Cl55) :=
              (Algebra.commutes (Q55 v) ((g : Cl55ˣ) : Cl55)).symm
            rw [hcomm, mul_assoc]
      _ = algebraMap ℝ Cl55 (Q55 v) := by
            rw [hunitRight]
            simp
      _ = ι55 v * ι55 v := by rw [CliffordAlgebra.ι_sq_scalar]
  have htwistedSquare :
      (CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55) * ι55 v *
          (↑((g : Cl55ˣ)⁻¹) : Cl55)) *
        (CliffordAlgebra.involute ((g : Cl55ˣ) : Cl55) * ι55 v *
          (↑((g : Cl55ˣ)⁻¹) : Cl55)) =
      ι55 v * ι55 v := by
    rcases hparity with hplus | hminus
    · rw [hplus]
      exact hconjSquare
    · rw [hminus]
      simpa only [neg_mul, mul_neg, neg_neg] using hconjSquare
  have hq :
      ι55 (realSplitPinTwistedAction g v) *
          ι55 (realSplitPinTwistedAction g v) =
        ι55 v * ι55 v := by
    rw [realSplitPinTwistedAction_apply_ι]
    exact htwistedSquare
  rw [CliffordAlgebra.ι_sq_scalar, CliffordAlgebra.ι_sq_scalar] at hq
  exact (algebraMap ℝ Cl55).injective hq

noncomputable def realSplitPinOrthogonalAction :
    realSplitPin55 →* orthogonalGroup55 where
  toFun g :=
    ⟨realSplitPinTwistedActionEquiv g,
      realSplitPinTwistedAction_preserves_Q55 g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change realSplitPinTwistedActionEquiv (1 : realSplitPin55) v = v
    change realSplitPinTwistedAction (1 : realSplitPin55) v = v
    rw [realSplitPinTwistedAction_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    exact realSplitPinTwistedActionEquiv_mul g h

end InfoGeometry.Clifford.Clifford55
