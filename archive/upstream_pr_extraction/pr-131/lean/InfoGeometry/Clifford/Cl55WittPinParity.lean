import InfoGeometry.Clifford.Cl55WittPinOrthogonalAction

namespace InfoGeometry.Clifford.Clifford55

/-!
# Parity of the Clifford grade involution on Lipschitz units

Every unit in the native Lipschitz subgroup is a product of vector units.
Consequently its grade involution is either itself or its negative.  This is
the parity fact needed to compare ordinary and twisted Pin actions.
-/

theorem lipschitzUnit_involute_eq_or_neg
    (x : Cl55ˣ) (hx : x ∈ LipschitzGroup55) :
    CliffordAlgebra.involute (x : Cl55) = (x : Cl55) ∨
      CliffordAlgebra.involute (x : Cl55) = -(x : Cl55) := by
  change x ∈ lipschitzGroup Q55 at hx
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
      obtain ⟨a, ha⟩ := hx
      right
      simpa [ha] using (CliffordAlgebra.involute_ι (Q := Q55) a)
  | inv_mem x hx =>
      obtain ⟨a, ha⟩ := hx
      right
      change CliffordAlgebra.involute (↑(x⁻¹) : Cl55) =
        -(↑(x⁻¹) : Cl55)
      have hinv_mul :
          CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
              CliffordAlgebra.involute (x : Cl55) = 1 := by
        have h := congrArg (CliffordAlgebra.involute (Q := Q55))
          (Units.inv_mul x : (↑(x⁻¹) : Cl55) * (x : Cl55) = 1)
        simpa only [map_mul, map_one] using h
      have hright :
          (x : Cl55) * (↑(x⁻¹) : Cl55) = 1 :=
        Units.mul_inv x
      have hprod :
          CliffordAlgebra.involute (↑(x⁻¹) : Cl55) * (x : Cl55) = -1 := by
        have hinv_mul' :
            CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
                (-(x : Cl55)) = 1 := by
          simpa [← ha, CliffordAlgebra.involute_ι] using hinv_mul
        calc
          CliffordAlgebra.involute (↑(x⁻¹) : Cl55) * (x : Cl55) =
              -(CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
                (-(x : Cl55))) := by
                  noncomm_ring
          _ = -1 := by rw [hinv_mul']
      calc
        CliffordAlgebra.involute (↑(x⁻¹) : Cl55) =
            CliffordAlgebra.involute (↑(x⁻¹) : Cl55) * 1 := by simp
        _ = CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
            ((x : Cl55) * (↑(x⁻¹) : Cl55)) := by rw [hright]
        _ = (CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
            (x : Cl55)) * (↑(x⁻¹) : Cl55) := by noncomm_ring
        _ = (-1) * (↑(x⁻¹) : Cl55) := by rw [hprod]
        _ = -(↑(x⁻¹) : Cl55) := by simp
  | one =>
      left
      simp
  | mul y z _ _ hy hz =>
      rcases hy with hy | hy <;> rcases hz with hz | hz
      · left
        simpa [map_mul, Units.val_mul, hy, hz]
      · right
        simpa [map_mul, Units.val_mul, hy, hz]
      · right
        simpa [map_mul, Units.val_mul, hy, hz]
      · left
        simpa [map_mul, Units.val_mul, hy, hz]

theorem pinTwistedAction_eq_pinConjAction_of_involute_eq
    (g : Pin55)
    (hg : CliffordAlgebra.involute (pinToUnits g : Cl55) =
      (pinToUnits g : Cl55)) :
    pinTwistedAction g = pinConjAction g := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  rw [pinTwistedAction_apply_ι, pinConjAction_apply_ι]
  simp only [pinTwistedAdj, hg]

theorem pinTwistedAction_eq_neg_pinConjAction_of_involute_eq_neg
    (g : Pin55)
    (hg : CliffordAlgebra.involute (pinToUnits g : Cl55) =
      -(pinToUnits g : Cl55)) :
    pinTwistedAction g = -(pinConjAction g) := by
  apply LinearMap.ext
  intro v
  apply ι55_injective
  rw [pinTwistedAction_apply_ι]
  simp only [LinearMap.neg_apply, map_neg]
  rw [pinConjAction_apply_ι]
  simp only [pinTwistedAdj, hg]
  noncomm_ring

theorem pinTwistedAction_preserves_Q55 (g : Pin55) (v : V55) :
    Q55 (pinTwistedAction g v) = Q55 v := by
  have hparity := lipschitzUnit_involute_eq_or_neg
    (pinToUnits g) (pin_units_mem_lipschitz g)
  rcases hparity with hplus | hminus
  · rw [pinTwistedAction_eq_pinConjAction_of_involute_eq g hplus]
    exact pinConjAction_preserves_Q55 g v
  · rw [pinTwistedAction_eq_neg_pinConjAction_of_involute_eq_neg g hminus]
    simpa using pinConjAction_preserves_Q55 g v

theorem pinTwistedActionEquiv_mul_all (g h : Pin55) :
    pinTwistedActionEquiv (g * h) =
      pinTwistedActionEquiv g * pinTwistedActionEquiv h :=
  pinTwistedActionEquiv_mul g h

noncomputable def pinTwistedOrthogonalAction : Pin55 →* orthogonalGroup55 where
  toFun g :=
    ⟨pinTwistedActionEquiv g, pinTwistedAction_preserves_Q55 g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change pinTwistedActionEquiv (1 : Pin55) v = v
    change pinTwistedAction (1 : Pin55) v = v
    rw [pinTwistedAction_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change pinTwistedActionEquiv (g * h) v =
      (pinTwistedActionEquiv g * pinTwistedActionEquiv h) v
    change pinTwistedAction (g * h) v =
      pinTwistedAction g (pinTwistedAction h v)
    rw [pinTwistedAction_mul]
    rfl

theorem pinTwistedOrthogonalAction_spinToPin_eq_pinOrthogonalAction
    (g : Spin55) :
    pinTwistedOrthogonalAction (spinToPin g) =
      pinOrthogonalAction (spinToPin g) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply ι55_injective
  change ι55 (pinTwistedAction (spinToPin g) v) =
    ι55 (pinConjAction (spinToPin g) v)
  rw [pinTwistedAction_apply_ι, pinConjAction_apply_ι]
  have hu : pinToUnits (spinToPin g) = spinGroup.toUnits g := by
    apply Units.ext
    rfl
  have hinv : CliffordAlgebra.involute (spinGroup.toUnits g : Cl55) =
      (spinGroup.toUnits g : Cl55) := by
    simpa using (spinGroup.involute_eq g.property)
  have hinv' : CliffordAlgebra.involute (g : Cl55) = (g : Cl55) :=
    spinGroup.involute_eq g.property
  simp [pinTwistedAdj, hu, hinv, hinv']

end InfoGeometry.Clifford.Clifford55
