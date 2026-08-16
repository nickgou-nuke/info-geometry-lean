import InfoGeometry.Clifford.Cl55WittPinReflections

/-!
# Native Pin twisted action on the `Cl(5,5)` Witt vector range

This owner uses Mathlib's native `pinGroup` and `involute_act_ι_mem_range_ι`
theorem.  It deliberately stops at the Clifford vector range: no arbitrary
choice of a preimage in `V55`, and no Pin-cover or surjectivity claim, is
introduced here.
-/

namespace InfoGeometry.Clifford.Clifford55

open CliffordAlgebra

noncomputable def pinTwistedAdj (g : Pin55) (v : V55) : Cl55 :=
  involute (Q := Q55) (pinToUnits g : Cl55) * ι55 v *
    (↑((pinToUnits g)⁻¹) : Cl55)

noncomputable def pinTwistedAdjLinear (g : Pin55) : V55 →ₗ[ℝ] Cl55 where
  toFun v := pinTwistedAdj g v
  map_add' x y := by
    dsimp [pinTwistedAdj]
    rw [map_add]
    noncomm_ring
  map_smul' r x := by
    dsimp [pinTwistedAdj]
    rw [map_smul]
    simp [smul_mul_assoc, mul_smul_comm]

theorem pinTwistedAdj_mul (g h : Pin55) (v : V55) :
    pinTwistedAdj (g * h) v =
      CliffordAlgebra.involute (pinToUnits g : Cl55) *
        pinTwistedAdj h v * (↑((pinToUnits g)⁻¹) : Cl55) := by
  simp [pinTwistedAdj]
  noncomm_ring

theorem pinTwistedAdj_mem_ι_range (g : Pin55) (v : V55) :
    pinTwistedAdj g v ∈ LinearMap.range (ι55) := by
  exact pinGroup.involute_act_ι_mem_range_ι g.2 v

noncomputable def pinTwistedAmbientLinear (g : Pin55) :
    Cl55 →ₗ[ℝ] Cl55 where
  toFun x := CliffordAlgebra.involute (pinToUnits g : Cl55) * x *
    (↑((pinToUnits g)⁻¹) : Cl55)
  map_add' x y := by
    noncomm_ring
  map_smul' r x := by
    simp [smul_mul_assoc, mul_smul_comm]

theorem pinTwistedAmbientLinear_mem_range
    (g : Pin55) (x : LinearMap.range (ι55)) :
    pinTwistedAmbientLinear g x ∈ LinearMap.range (ι55) := by
  rcases x.property with ⟨v, hv⟩
  rw [← hv]
  exact pinGroup.involute_act_ι_mem_range_ι g.2 v

noncomputable def pinTwistedRangeEndomorphism (g : Pin55) :
    LinearMap.range (ι55) →ₗ[ℝ] LinearMap.range (ι55) :=
  LinearMap.codRestrict (LinearMap.range (ι55))
    ((pinTwistedAmbientLinear g).domRestrict (LinearMap.range (ι55)))
    (pinTwistedAmbientLinear_mem_range g)

theorem pinTwistedAmbientLinear_mul (g h : Pin55) (x : Cl55) :
    pinTwistedAmbientLinear (g * h) x =
      pinTwistedAmbientLinear g (pinTwistedAmbientLinear h x) := by
  simp [pinTwistedAmbientLinear, pinToUnits]
  noncomm_ring

theorem pinTwistedRangeEndomorphism_mul (g h : Pin55) :
    pinTwistedRangeEndomorphism (g * h) =
      (pinTwistedRangeEndomorphism g).comp
        (pinTwistedRangeEndomorphism h) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change pinTwistedAmbientLinear (g * h) (x : Cl55) =
    pinTwistedAmbientLinear g
      (pinTwistedAmbientLinear h (x : Cl55))
  exact pinTwistedAmbientLinear_mul g h (x : Cl55)

noncomputable def pinTwistedAction (g : Pin55) : V55 →ₗ[ℝ] V55 :=
  ι55RangeEquiv.symm.toLinearMap.comp
    ((pinTwistedRangeEndomorphism g).comp ι55RangeEquiv.toLinearMap)

theorem pinTwistedAction_mul (g h : Pin55) :
    pinTwistedAction (g * h) =
      (pinTwistedAction g).comp (pinTwistedAction h) := by
  apply LinearMap.ext
  intro v
  simp [pinTwistedAction, pinTwistedRangeEndomorphism_mul]

theorem pinTwistedAction_apply_ι (g : Pin55) (v : V55) :
    ι55 (pinTwistedAction g v) = pinTwistedAdj g v := by
  have heq :
      ι55RangeEquiv (pinTwistedAction g v) =
        pinTwistedRangeEndomorphism g (ι55RangeEquiv v) := by
    change ι55RangeEquiv
        (ι55RangeEquiv.symm
          (pinTwistedRangeEndomorphism g (ι55RangeEquiv v))) = _
    exact ι55RangeEquiv.apply_symm_apply _
  have hval := congrArg
      (fun z : LinearMap.range (ι55) => (z : Cl55)) heq
  exact hval

theorem pinTwistedAction_one :
    pinTwistedAction (1 : Pin55) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  rw [pinTwistedAction_apply_ι]
  simp [pinTwistedAdj, pinToUnits]

noncomputable def pinTwistedActionEquiv (g : Pin55) : V55 ≃ₗ[ℝ] V55 :=
  LinearEquiv.ofLinear
    (pinTwistedAction g)
    (pinTwistedAction g⁻¹)
    (by
      rw [← pinTwistedAction_mul, mul_inv_cancel, pinTwistedAction_one])
    (by
      rw [← pinTwistedAction_mul, inv_mul_cancel, pinTwistedAction_one])

theorem pinTwistedActionEquiv_mul_apply (g h : Pin55) (v : V55) :
    pinTwistedActionEquiv (g * h) v =
      pinTwistedActionEquiv g (pinTwistedActionEquiv h v) := by
  change pinTwistedAction (g * h) v =
    pinTwistedAction g (pinTwistedAction h v)
  rw [pinTwistedAction_mul]
  rfl

theorem pinTwistedActionEquiv_mul (g h : Pin55) :
    pinTwistedActionEquiv (g * h) =
      pinTwistedActionEquiv g * pinTwistedActionEquiv h := by
  apply LinearEquiv.ext
  intro v
  exact pinTwistedActionEquiv_mul_apply g h v

noncomputable def pinTwistedVectorRangeLinear (g : Pin55) :
    V55 →ₗ[ℝ] LinearMap.range (ι55) :=
  LinearMap.codRestrict (LinearMap.range (ι55))
    (pinTwistedAdjLinear g) (pinTwistedAdj_mem_ι_range g)

@[simp] theorem pinTwistedVectorRangeLinear_coe (g : Pin55) (v : V55) :
    (pinTwistedVectorRangeLinear g v : Cl55) = pinTwistedAdj g v :=
  rfl

noncomputable def pinTwistedVectorRangeAction (g : Pin55) (v : V55) :
    LinearMap.range (ι55) :=
  ⟨pinTwistedAdj g v, pinTwistedAdj_mem_ι_range g v⟩

noncomputable def pinTwistedAdjRangeLinear (g : Pin55) :
    V55 →ₗ[ℝ] LinearMap.range (ι55) where
  toFun v := pinTwistedVectorRangeAction g v
  map_add' x y := by
    apply Subtype.ext
    exact (pinTwistedAdjLinear g).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact (pinTwistedAdjLinear g).map_smul r x

@[simp] theorem pinTwistedVectorRangeAction_coe (g : Pin55) (v : V55) :
    (pinTwistedVectorRangeAction g v : Cl55) = pinTwistedAdj g v :=
  rfl

theorem pinTwistedAdj_mem_ι_range_of_unit (i : Fin 5) (v : V55) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ v ∈
      LinearMap.range (ι55) := by
  exact pinTwistedAdj_mem_ι_range ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ v

theorem pinToUnits_f_neg (i : Fin 5) :
    pinToUnits ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ = fNegUnit i := by
  apply Units.ext
  exact fNegUnit_coe i

theorem pinTwistedAdj_f_neg_eq (i : Fin 5) (v : V55) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ v =
      involute (fNegUnit i : Cl55) * ι55 v *
        (↑((fNegUnit i)⁻¹) : Cl55) := by
  rw [pinTwistedAdj, pinToUnits_f_neg]

theorem pinTwistedAdj_f_neg_apply_e_pos (i : Fin 5) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ (e_pos i) =
      ι55 (e_pos i) := by
  rw [pinTwistedAdj_f_neg_eq]
  exact f_neg_pin_twisted_action_e_pos i

theorem pinTwistedAdj_f_neg_apply_f_neg (i : Fin 5) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ (f_neg i) =
      -ι55 (f_neg i) := by
  rw [pinTwistedAdj_f_neg_eq]
  exact f_neg_pin_twisted_action_f_neg i

theorem pinTwistedAdj_f_neg_apply_e_pos_reflection (i : Fin 5) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ (e_pos i) =
      ι55 (negativeReflection i (e_pos i)) := by
  rw [negativeReflection_apply_e_pos]
  exact pinTwistedAdj_f_neg_apply_e_pos i

theorem pinTwistedAdj_f_neg_apply_f_neg_reflection (i : Fin 5) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ (f_neg i) =
      ι55 (negativeReflection i (f_neg i)) := by
  rw [negativeReflection_apply_f_neg]
  simpa using pinTwistedAdj_f_neg_apply_f_neg i

theorem f_neg_isOrtho_of_ne {i j : Fin 5} (hij : i ≠ j) :
    Q55.IsOrtho (f_neg i) (f_neg j) := by
  classical
  simp only [QuadraticMap.isOrtho_def, Q55_apply, f_neg,
    Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply]
  have hzero : ∑ x : Fin 5, (0 : ℝ) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    norm_num
  rw [hzero]
  have hzero_add : ∑ x : Fin 5, ((0 : ℝ) + 0) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    norm_num
  rw [hzero_add]
  simp only [zero_sub, add_zero]
  change
    -(∑ x : Fin 5, ((if x = i then (1 : ℝ) else 0) +
      (if x = j then 1 else 0)) ^ 2) =
      -(∑ x : Fin 5, (if x = i then (1 : ℝ) else 0) ^ 2) -
        ∑ x : Fin 5, (if x = j then (1 : ℝ) else 0) ^ 2
  have hcross :
      ∑ x : Fin 5, (if x = i then (1 : ℝ) else 0) *
        (if x = j then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxi : x = i
    · subst x
      simp [hij]
    · simp [hxi]
  have hi :
      ∑ x : Fin 5, (if x = i then (1 : ℝ) else 0) ^ 2 = 1 := by
    simp
  have hj :
      ∑ x : Fin 5, (if x = j then (1 : ℝ) else 0) ^ 2 = 1 := by
    simp
  have hsum :
      ∑ x : Fin 5, ((if x = i then (1 : ℝ) else 0) +
        (if x = j then 1 else 0)) ^ 2 = 2 := by
    calc
      _ = ∑ x : Fin 5,
          ((if x = i then (1 : ℝ) else 0) ^ 2 +
            (if x = j then (1 : ℝ) else 0) ^ 2 +
            2 * ((if x = i then (1 : ℝ) else 0) *
            (if x = j then 1 else 0))) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = (∑ x : Fin 5, (if x = i then (1 : ℝ) else 0) ^ 2) +
          (∑ x : Fin 5, (if x = j then (1 : ℝ) else 0) ^ 2) +
          2 * (∑ x : Fin 5, (if x = i then (1 : ℝ) else 0) *
            (if x = j then 1 else 0)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum]
      _ = 2 := by rw [hi, hj, hcross]; norm_num
  rw [hsum, hi, hj]
  norm_num

theorem pinTwistedAdj_f_neg_apply_e_pos_all (i j : Fin 5) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ (e_pos j) =
      ι55 (e_pos j) := by
  rw [pinTwistedAdj_f_neg_eq, fNegUnit_coe,
    CliffordAlgebra.involute_ι, fNegUnit_inv_coe]
  apply neg_sq_twisted_fix_of_anticomm
  · exact f_neg_mul_self i
  · have h := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (Q := Q55) (e_pos_ortho_f_neg j i)
    simpa [add_comm] using h

theorem pinTwistedAdj_f_neg_apply_e_pos_reflection_all (i j : Fin 5) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ (e_pos j) =
      ι55 (negativeReflection i (e_pos j)) := by
  have hneg : negativeReflection i (e_pos j) = e_pos j := by
    apply Prod.ext
    · rfl
    · funext k
      simp [negativeReflection, e_pos]
  rw [hneg]
  exact pinTwistedAdj_f_neg_apply_e_pos_all i j

theorem pinTwistedAdj_f_neg_apply_f_neg_ne (i j : Fin 5) (hji : j ≠ i) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ (f_neg j) =
      ι55 (f_neg j) := by
  rw [pinTwistedAdj_f_neg_eq, fNegUnit_coe,
    CliffordAlgebra.involute_ι, fNegUnit_inv_coe]
  apply neg_sq_twisted_fix_of_anticomm
  · exact f_neg_mul_self i
  · apply (add_eq_zero_iff_eq_neg).mpr
    have h := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (Q := Q55) (f_neg_isOrtho_of_ne (Ne.symm hji))
    simpa [add_comm] using h

theorem pinTwistedAdj_f_neg_apply_f_neg_all (i j : Fin 5) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ (f_neg j) =
      ι55 (negativeReflection i (f_neg j)) := by
  by_cases hji : j = i
  · subst j
    exact pinTwistedAdj_f_neg_apply_f_neg_reflection i
  · have hneg : negativeReflection i (f_neg j) = f_neg j := by
      apply Prod.ext
      · rfl
      · funext k
        by_cases hki : k = i
        · subst k
          simp [negativeReflection, f_neg, hji, Ne.symm hji]
        · simp [negativeReflection, f_neg, hki]
    rw [hneg]
    exact pinTwistedAdj_f_neg_apply_f_neg_ne i j hji

theorem pinTwistedAdjLinear_f_neg_eq_negativeReflection (i : Fin 5) :
    pinTwistedAdjLinear ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ =
      ι55.comp (negativeReflectionLinearEquiv i).toLinearMap := by
  apply Module.Basis.ext
    ((Pi.basisFun ℝ (Fin 5)).prod (Pi.basisFun ℝ (Fin 5)))
  intro k
  cases k with
  | inl j =>
      have hs : Pi.single j (1 : ℝ) =
          (fun k => if j = k then (1 : ℝ) else 0) := by
        funext k
        by_cases h : k = j
        · subst k
          simp
        · have h' : j ≠ k := Ne.symm h
          simp [Pi.single_apply, h, h']
      convert pinTwistedAdj_f_neg_apply_e_pos_reflection_all i j using 1 <;>
        simp [pinTwistedAdjLinear, e_pos, negativeReflection,
          Pi.basisFun_apply, Pi.single_apply, eq_comm, hs]
  | inr j =>
      have hs : Pi.single j (1 : ℝ) =
          (fun k => if j = k then (1 : ℝ) else 0) := by
        funext k
        by_cases h : k = j
        · subst k
          simp
        · have h' : j ≠ k := Ne.symm h
          simp [Pi.single_apply, h, h']
      convert pinTwistedAdj_f_neg_apply_f_neg_all i j using 1 <;>
        simp [pinTwistedAdjLinear, f_neg, negativeReflection,
          Pi.basisFun_apply, Pi.single_apply, eq_comm, hs]

theorem pinTwistedAdj_f_neg_eq_negativeReflectionAlg (i : Fin 5) (v : V55) :
    pinTwistedAdj ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ v =
      negativeReflectionAlg i (ι55 v) := by
  have h := congrArg
      (fun T : V55 →ₗ[ℝ] Cl55 => T v)
      (pinTwistedAdjLinear_f_neg_eq_negativeReflection i)
  simpa [pinTwistedAdjLinear, negativeReflectionAlg_apply_ι] using h

theorem pinTwistedAction_f_neg_eq_negativeReflection (i : Fin 5) :
    pinTwistedAction (fNegPin i) =
      (negativeReflectionLinearEquiv i).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  rw [pinTwistedAction_apply_ι]
  have hi : pinTwistedAdj (fNegPin i) v =
      negativeReflectionAlg i (ι55 v) := by
    simpa [fNegPin] using pinTwistedAdj_f_neg_eq_negativeReflectionAlg i v
  rw [hi, negativeReflectionAlg_apply_ι]
  rfl

theorem pinTwistedAction_f_neg_preserves_Q55 (i : Fin 5) (v : V55) :
    Q55 (pinTwistedAction (fNegPin i) v) = Q55 v := by
  rw [pinTwistedAction_f_neg_eq_negativeReflection]
  exact negativeReflection_preserves_Q55 i v

noncomputable def negativeReflectionRangeLinear (i : Fin 5) :
    V55 →ₗ[ℝ] LinearMap.range (ι55) :=
  LinearMap.codRestrict (LinearMap.range (ι55))
    (ι55.comp (negativeReflectionLinearEquiv i).toLinearMap)
    (fun v => LinearMap.mem_range_self (ι55) (negativeReflection i v))

theorem pinTwistedVectorRangeLinear_f_neg_eq_negativeReflectionRangeLinear
    (i : Fin 5) :
    pinTwistedVectorRangeLinear
        ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ =
      negativeReflectionRangeLinear i := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have h := congrArg
      (fun T : V55 →ₗ[ℝ] Cl55 => T v)
      (pinTwistedAdjLinear_f_neg_eq_negativeReflection i)
  simpa [pinTwistedVectorRangeLinear, negativeReflectionRangeLinear,
    pinTwistedAdjLinear] using h

theorem pinTwistedAdj_fNegPin_mul (i j : Fin 5) (v : V55) :
    pinTwistedAdj (fNegPin i * fNegPin j) v =
      negativeReflectionAlg i
        (negativeReflectionAlg j (ι55 v)) := by
  change pinTwistedAdj
      ((⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ : Pin55) *
        ⟨ι55 (f_neg j), f_neg_mem_pinGroup j⟩) v = _
  rw [pinTwistedAdj_mul, pinTwistedAdj_f_neg_eq_negativeReflectionAlg]
  rw [pinToUnits_f_neg]
  rw [negativeReflectionAlg_apply_ι]
  rw [← pinTwistedAdj_f_neg_eq]
  exact pinTwistedAdj_f_neg_eq_negativeReflectionAlg i
    (negativeReflection j v)

theorem pinTwistedAdj_mul_fNegPin (g : Pin55) (i : Fin 5) (v : V55) :
    pinTwistedAdj (g * fNegPin i) v =
      pinTwistedAdj g (negativeReflection i v) := by
  rw [pinTwistedAdj_mul]
  have hi :
      pinTwistedAdj (fNegPin i) v =
        negativeReflectionAlg i (ι55 v) := by
    simpa [fNegPin] using pinTwistedAdj_f_neg_eq_negativeReflectionAlg i v
  simpa [pinTwistedAdj, negativeReflectionAlg_apply_ι] using
    congrArg (fun z : Cl55 =>
      CliffordAlgebra.involute (pinToUnits g : Cl55) * z *
        (↑((pinToUnits g)⁻¹) : Cl55)) hi

theorem pinTwistedAdj_fNegPin_mul_three (i j k : Fin 5) (v : V55) :
    pinTwistedAdj ((fNegPin i * fNegPin j) * fNegPin k) v =
      negativeReflectionAlg i
        (negativeReflectionAlg j
          (negativeReflectionAlg k (ι55 v))) := by
  change pinTwistedAdj
      (((⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ : Pin55) *
          ⟨ι55 (f_neg j), f_neg_mem_pinGroup j⟩) *
        ⟨ι55 (f_neg k), f_neg_mem_pinGroup k⟩) v = _
  calc
    pinTwistedAdj
        (((⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ : Pin55) *
            ⟨ι55 (f_neg j), f_neg_mem_pinGroup j⟩) *
          ⟨ι55 (f_neg k), f_neg_mem_pinGroup k⟩) v =
        involute (Q := Q55)
            (pinToUnits (fNegPin i * fNegPin j) : Cl55) *
          pinTwistedAdj (fNegPin k) v *
          (↑((pinToUnits (fNegPin i * fNegPin j))⁻¹) : Cl55) := by
            exact pinTwistedAdj_mul (fNegPin i * fNegPin j) (fNegPin k) v
    _ = pinTwistedAdj (fNegPin i * fNegPin j)
          (negativeReflection k v) := by
            have hk' :
                pinTwistedAdj (fNegPin k) v =
                  negativeReflectionAlg k (ι55 v) := by
              simpa [fNegPin] using
                pinTwistedAdj_f_neg_eq_negativeReflectionAlg k v
            simpa [pinTwistedAdj, fNegPin,
              negativeReflectionAlg_apply_ι] using
              congrArg (fun z : Cl55 =>
                involute (Q := Q55)
                    (pinToUnits (fNegPin i * fNegPin j) : Cl55) * z *
                  (↑((pinToUnits (fNegPin i * fNegPin j))⁻¹) : Cl55)) hk'
    _ = negativeReflectionAlg i
          (negativeReflectionAlg j
            (ι55 (negativeReflection k v))) := by
            exact pinTwistedAdj_fNegPin_mul i j (negativeReflection k v)
    _ = negativeReflectionAlg i
          (negativeReflectionAlg j
            (negativeReflectionAlg k (ι55 v))) := by
            simp only [negativeReflectionAlg_apply_ι]

theorem pinTwistedAdj_globalSheetPin (v : V55) :
    pinTwistedAdj globalSheetPin v =
      ι55 (globalSheetReflection v) := by
  rw [globalSheetPin]
  rw [pinTwistedAdj_mul_fNegPin]
  rw [pinTwistedAdj_mul_fNegPin]
  rw [pinTwistedAdj_mul_fNegPin]
  rw [pinTwistedAdj_mul_fNegPin]
  have h0 :
      pinTwistedAdj (fNegPin 0)
          (negativeReflection 1
            (negativeReflection 2
              (negativeReflection 3
                (negativeReflection 4 v)))) =
        negativeReflectionAlg 0
          (ι55 (negativeReflection 1
            (negativeReflection 2
              (negativeReflection 3
                (negativeReflection 4 v))))) := by
    simpa [fNegPin] using
      pinTwistedAdj_f_neg_eq_negativeReflectionAlg 0
        (negativeReflection 1
          (negativeReflection 2
            (negativeReflection 3
              (negativeReflection 4 v))))
  rw [h0]
  have h1 := negativeReflectionAlg_apply_ι 0
    (negativeReflection 1
      (negativeReflection 2
        (negativeReflection 3
          (negativeReflection 4 v))))
  rw [h1]
  apply congrArg ι55
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;>
      simp [globalSheetReflection, negativeReflection]

theorem pinTwistedAdj_globalSheetPin_involutive (v : V55) :
    pinTwistedAdj globalSheetPin (globalSheetReflection v) = ι55 v := by
  rw [pinTwistedAdj_globalSheetPin]
  simp only [globalSheetReflection_involutive]

theorem pinTwistedAction_globalSheetPin_eq_globalSheetReflection :
    pinTwistedAction globalSheetPin =
      globalSheetReflectionLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  rw [pinTwistedAction_apply_ι, pinTwistedAdj_globalSheetPin]
  rfl

theorem pinTwistedAction_globalSheetPin_preserves_Q55 (v : V55) :
    Q55 (pinTwistedAction globalSheetPin v) = Q55 v := by
  rw [pinTwistedAction_globalSheetPin_eq_globalSheetReflection]
  exact globalSheetReflection_preserves_Q55 v

theorem pinTwistedAction_globalSheetPin_involutive (v : V55) :
    pinTwistedAction globalSheetPin
        (pinTwistedAction globalSheetPin v) = v := by
  rw [pinTwistedAction_globalSheetPin_eq_globalSheetReflection]
  change globalSheetReflection (globalSheetReflection v) = v
  exact globalSheetReflection_involutive v

theorem pinTwistedActionEquiv_fNegPin_eq_negativeReflection (i : Fin 5) :
    pinTwistedActionEquiv (fNegPin i) = negativeReflectionLinearEquiv i := by
  apply LinearEquiv.ext
  intro v
  change pinTwistedAction (fNegPin i) v = _
  rw [pinTwistedAction_f_neg_eq_negativeReflection]
  rfl

theorem pinTwistedActionEquiv_globalSheetPin_eq_globalSheetReflection :
    pinTwistedActionEquiv globalSheetPin = globalSheetReflectionLinearEquiv := by
  apply LinearEquiv.ext
  intro v
  change pinTwistedAction globalSheetPin v = _
  rw [pinTwistedAction_globalSheetPin_eq_globalSheetReflection]
  rfl

noncomputable def spinToPin (g : Spin55) : Pin55 :=
  ⟨g, spinGroup.mem_pin g.property⟩

noncomputable def spinToPinHom : Spin55 →* Pin55 where
  toFun := spinToPin
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def spinAction (g : Spin55) : V55 →ₗ[ℝ] V55 :=
  pinTwistedAction (spinToPin g)

noncomputable def pinTwistedActionIsometryEquiv
    (g : Pin55)
    (hQ : ∀ v : V55, Q55 (pinTwistedAction g v) = Q55 v) :
    Q55.IsometryEquiv Q55 :=
  { pinTwistedActionEquiv g with
    map_app' := hQ }

theorem spinAction_preserves_Q55 (g : Spin55) (v : V55) :
    Q55 (spinAction g v) = Q55 v := by
  change Q55 (pinTwistedAction (spinToPin g) v) = Q55 v
  have hι := pinTwistedAction_apply_ι (spinToPin g) v
  have hu : pinToUnits (spinToPin g) = spinGroup.toUnits g := by
    apply Units.ext
    rfl
  have hinv :
      CliffordAlgebra.involute (spinGroup.toUnits g : Cl55) =
        (spinGroup.toUnits g : Cl55) := by
    simpa using (spinGroup.involute_eq g.property)
  have hι' :
      ι55 (spinAction g v) =
        (spinGroup.toUnits g : Cl55) * ι55 v *
          (↑((spinGroup.toUnits g)⁻¹) : Cl55) := by
    simpa only [pinTwistedAdj, hu, hinv] using hι
  have hunit :
      (↑((spinGroup.toUnits g)⁻¹) : Cl55) *
          (spinGroup.toUnits g : Cl55) = 1 := by
    simpa using Units.inv_mul (spinGroup.toUnits g)
  have hunitRight :
      (spinGroup.toUnits g : Cl55) *
          (↑((spinGroup.toUnits g)⁻¹) : Cl55) = 1 := by
    simpa using Units.mul_inv (spinGroup.toUnits g)
  have hsquare :
      (spinGroup.toUnits g : Cl55) * ι55 v *
          (↑((spinGroup.toUnits g)⁻¹) : Cl55) *
        ((spinGroup.toUnits g : Cl55) * ι55 v *
          (↑((spinGroup.toUnits g)⁻¹) : Cl55)) =
        (ι55 v) * (ι55 v) := by
    calc
      (spinGroup.toUnits g : Cl55) * ι55 v *
          (↑((spinGroup.toUnits g)⁻¹) : Cl55) *
        ((spinGroup.toUnits g : Cl55) * ι55 v *
          (↑((spinGroup.toUnits g)⁻¹) : Cl55)) =
          (spinGroup.toUnits g : Cl55) *
            (ι55 v * ι55 v) *
            (↑((spinGroup.toUnits g)⁻¹) : Cl55) := by
              calc
                (spinGroup.toUnits g : Cl55) * ι55 v *
                    (↑((spinGroup.toUnits g)⁻¹) : Cl55) *
                    ((spinGroup.toUnits g : Cl55) * ι55 v *
                      (↑((spinGroup.toUnits g)⁻¹) : Cl55)) =
                    (spinGroup.toUnits g : Cl55) * ι55 v *
                      ((↑((spinGroup.toUnits g)⁻¹) : Cl55) *
                        (spinGroup.toUnits g : Cl55)) * ι55 v *
                      (↑((spinGroup.toUnits g)⁻¹) : Cl55) := by
                        simp only [mul_assoc]
                _ = (spinGroup.toUnits g : Cl55) * ι55 v *
                      1 * ι55 v *
                      (↑((spinGroup.toUnits g)⁻¹) : Cl55) := by
                        rw [hunit]
                _ = (spinGroup.toUnits g : Cl55) *
                      (ι55 v * ι55 v) *
                      (↑((spinGroup.toUnits g)⁻¹) : Cl55) := by
                        simp only [one_mul, mul_assoc]
      _ = (spinGroup.toUnits g : Cl55) *
            (algebraMap ℝ Cl55 (Q55 v)) *
            (↑((spinGroup.toUnits g)⁻¹) : Cl55) := by
              rw [CliffordAlgebra.ι_sq_scalar]
      _ = (algebraMap ℝ Cl55 (Q55 v)) *
            ((spinGroup.toUnits g : Cl55) *
              (↑((spinGroup.toUnits g)⁻¹) : Cl55)) := by
              have hcomm :
                  (spinGroup.toUnits g : Cl55) *
                      algebraMap ℝ Cl55 (Q55 v) =
                    algebraMap ℝ Cl55 (Q55 v) *
                      (spinGroup.toUnits g : Cl55) :=
                (Algebra.commutes (Q55 v)
                  (spinGroup.toUnits g : Cl55)).symm
              rw [hcomm, mul_assoc]
      _ = algebraMap ℝ Cl55 (Q55 v) := by
              rw [hunitRight]
              simp
      _ = ι55 v * ι55 v := by
              rw [CliffordAlgebra.ι_sq_scalar]
  have hq :
      ι55 (spinAction g v) * ι55 (spinAction g v) =
        ι55 v * ι55 v := by
    change ι55 (spinAction g v) * ι55 (spinAction g v) =
      ι55 v * ι55 v
    rw [hι', hsquare]
  rw [CliffordAlgebra.ι_sq_scalar, CliffordAlgebra.ι_sq_scalar] at hq
  exact (algebraMap ℝ Cl55).injective hq

noncomputable def spinActionIsometryEquiv (g : Spin55) :
    Q55.IsometryEquiv Q55 :=
  pinTwistedActionIsometryEquiv (spinToPin g) (by
    intro v
    exact spinAction_preserves_Q55 g v)

@[simp] theorem spinActionIsometryEquiv_apply (g : Spin55) (v : V55) :
    spinActionIsometryEquiv g v = spinAction g v := rfl

theorem spinActionIsometryEquiv_mul_apply (g h : Spin55) (v : V55) :
    spinActionIsometryEquiv (g * h) v =
      spinActionIsometryEquiv g (spinActionIsometryEquiv h v) := by
  change spinAction (g * h) v = spinAction g (spinAction h v)
  have hpin : spinToPin (g * h) = spinToPin g * spinToPin h := by
    rfl
  rw [spinAction, hpin, pinTwistedAction_mul]
  rfl

noncomputable def fNegPinIsometryEquiv (i : Fin 5) :
    Q55.IsometryEquiv Q55 :=
  pinTwistedActionIsometryEquiv (fNegPin i)
    (fun v => pinTwistedAction_f_neg_preserves_Q55 i v)

theorem fNegPinIsometryEquiv_eq_negativeReflectionIsometry (i : Fin 5) :
    fNegPinIsometryEquiv i = negativeReflectionIsometry i := by
  apply DFunLike.ext
  intro v
  change pinTwistedAction (fNegPin i) v = _
  rw [pinTwistedAction_f_neg_eq_negativeReflection]
  rfl

noncomputable def globalSheetPinIsometryEquiv :
    Q55.IsometryEquiv Q55 :=
  pinTwistedActionIsometryEquiv globalSheetPin
    (fun v => pinTwistedAction_globalSheetPin_preserves_Q55 v)

theorem globalSheetPinIsometryEquiv_eq_globalSheetReflectionIsometry :
    globalSheetPinIsometryEquiv = globalSheetReflectionIsometry := by
  apply DFunLike.ext
  intro v
  change pinTwistedAction globalSheetPin v = _
  rw [pinTwistedAction_globalSheetPin_eq_globalSheetReflection]
  rfl

theorem pinTwistedAction_f_neg_involutive (i : Fin 5) (v : V55) :
    pinTwistedAction (fNegPin i)
        (pinTwistedAction (fNegPin i) v) = v := by
  rw [pinTwistedAction_f_neg_eq_negativeReflection]
  exact negativeReflection_involutive i v

theorem pinTwistedAction_f_neg_commute (i j : Fin 5) (v : V55) :
    pinTwistedAction (fNegPin i)
        (pinTwistedAction (fNegPin j) v) =
      pinTwistedAction (fNegPin j)
        (pinTwistedAction (fNegPin i) v) := by
  rw [pinTwistedAction_f_neg_eq_negativeReflection,
    pinTwistedAction_f_neg_eq_negativeReflection]
  exact negativeReflection_commute i j v

theorem pinTwistedAction_globalSheetPin_commute_f_neg
    (i : Fin 5) (v : V55) :
    pinTwistedAction globalSheetPin
        (pinTwistedAction (fNegPin i) v) =
      pinTwistedAction (fNegPin i)
        (pinTwistedAction globalSheetPin v) := by
  rw [pinTwistedAction_globalSheetPin_eq_globalSheetReflection,
    pinTwistedAction_f_neg_eq_negativeReflection]
  exact globalSheetReflection_commute_negativeReflection i v

end InfoGeometry.Clifford.Clifford55
