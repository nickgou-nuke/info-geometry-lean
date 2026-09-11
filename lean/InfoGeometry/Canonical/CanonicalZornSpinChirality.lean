import InfoGeometry.Canonical.CanonicalZornSpinRelatedFiber
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Chirality preservation of the canonical Zorn spin representation

The Zorn gamma operators exchange the two typed semispinor summands.  Hence
the Dirac grading operator anticommutes with Clifford generators and
intertwines the full Clifford action with the grade involution.  Elements of
Mathlib's spin group are even, so their Dirac operators preserve both
semispinor summands.
-/

noncomputable section

namespace CanonicalZornSpinChirality

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornOuterTrialityGroup
open CanonicalZornSpinRelatedFiber

/-- Dirac chirality: `+1` on `8s` and `-1` on `8c`. -/
def diracChirality : DiracSpinor16 ≃ₗ[ℂ] DiracSpinor16 where
  toFun Ψ := (Ψ.1, -Ψ.2)
  invFun Ψ := (Ψ.1, -Ψ.2)
  left_inv Ψ := by
    apply Prod.ext
    · rfl
    · exact neg_neg Ψ.2
  right_inv Ψ := by
    apply Prod.ext
    · rfl
    · exact neg_neg Ψ.2
  map_add' Ψ Φ := by
    apply Prod.ext <;> simp [add_comm]
  map_smul' c Ψ := by
    apply Prod.ext
    · rfl
    · exact (smul_neg c Ψ.2).symm

@[simp] theorem diracChirality_apply (S : SpinorPlus8) (C : SpinorMinus8) :
    diracChirality (S, C) = (S, -C) := rfl

@[simp] theorem diracChirality_sq (Ψ : DiracSpinor16) :
    diracChirality (diracChirality Ψ) = Ψ := by
  simp [diracChirality]

theorem cliffordPlus_neg (V : Vector8) (S : SpinorPlus8) :
    cliffordPlus V (-S) = -cliffordPlus V S := by
  have h := map_neg (diracGamma V) (S, 0)
  exact congrArg Prod.snd h

theorem cliffordMinus_neg (V : Vector8) (C : SpinorMinus8) :
    cliffordMinus V (-C) = -cliffordMinus V C := by
  have h := map_neg (diracGamma V) (0, C)
  exact congrArg Prod.fst h

/-- The grading operator anticommutes with every Clifford generator. -/
theorem diracChirality_gamma (V : Vector8) (Ψ : DiracSpinor16) :
    diracChirality (diracGamma V Ψ) =
      -diracGamma V (diracChirality Ψ) := by
  rcases Ψ with ⟨S, C⟩
  apply Prod.ext
  · change cliffordMinus V C = -cliffordMinus V (-C)
    rw [cliffordMinus_neg, neg_neg]
  · change -cliffordPlus V S = -cliffordPlus V S
    rfl

/-- Chirality implements the Clifford grade involution in the canonical
Zorn representation. -/
theorem diracChirality_clifford_involute
    (a : CliffordAlgebra vectorQuadratic) (Ψ : DiracSpinor16) :
    diracChirality (zornCliffordRepresentation a Ψ) =
      zornCliffordRepresentation (CliffordAlgebra.involute a)
        (diracChirality Ψ) := by
  induction a using CliffordAlgebra.induction generalizing Ψ with
  | algebraMap r =>
      simp
  | ι V =>
      rw [zornCliffordRepresentation_ι, CliffordAlgebra.involute_ι,
        map_neg, zornCliffordRepresentation_ι]
      exact diracChirality_gamma V Ψ
  | mul a b ha hb =>
      rw [map_mul, map_mul, map_mul]
      change diracChirality
          (zornCliffordRepresentation a (zornCliffordRepresentation b Ψ)) = _
      rw [ha, hb]
      rfl
  | add a b ha hb =>
      rw [map_add, map_add, map_add]
      change diracChirality
          (zornCliffordRepresentation a Ψ + zornCliffordRepresentation b Ψ) = _
      rw [map_add, ha, hb]
      rfl

/-- Every spin operator commutes with chirality because spin elements lie in
the even Clifford subalgebra. -/
theorem complexSpinDirac_commutes_chirality
    (g : ComplexSpin44) (Ψ : DiracSpinor16) :
    diracChirality
        (((complexSpinDiracRepresentation g : DiracGL) :
          Module.End ℂ DiracSpinor16) Ψ) =
      ((complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) (diracChirality Ψ) := by
  rw [complexSpinDiracRepresentation_val]
  rw [diracChirality_clifford_involute]
  rw [spinGroup.involute_eq g.2]

/-- A spin operator sends the positive semispinor summand into itself. -/
theorem complexSpinDirac_preserves_plus
    (g : ComplexSpin44) (S : SpinorPlus8) :
    (((complexSpinDiracRepresentation g : DiracGL) :
      Module.End ℂ DiracSpinor16) (S, 0)).2 = 0 := by
  have h := complexSpinDirac_commutes_chirality g (S, 0)
  have h2 := congrArg Prod.snd h
  have hsum :
      (((complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) (S, 0)).2 +
      (((complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) (S, 0)).2 = 0 :=
    neg_eq_iff_add_eq_zero.mp (by simpa [diracChirality] using h2)
  have hsmul : (2 : ℂ) •
      (((complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) (S, 0)).2 = 0 := by
    simpa [two_smul] using hsum
  exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)

/-- A spin operator sends the negative semispinor summand into itself. -/
theorem complexSpinDirac_preserves_minus
    (g : ComplexSpin44) (C : SpinorMinus8) :
    (((complexSpinDiracRepresentation g : DiracGL) :
      Module.End ℂ DiracSpinor16) (0, C)).1 = 0 := by
  have h := complexSpinDirac_commutes_chirality g (0, C)
  have h1 := congrArg Prod.fst h
  let A := ((complexSpinDiracRepresentation g : DiracGL) :
    Module.End ℂ DiracSpinor16)
  have hneg : (A (0, -C)).1 = -(A (0, C)).1 := by
    have hm := map_neg A (0, C)
    simpa using congrArg Prod.fst hm
  have hself : (A (0, C)).1 = -(A (0, C)).1 := by
    have hcomm : (A (0, C)).1 = (A (0, -C)).1 := by
      simpa [A, diracChirality] using h1
    exact hcomm.trans hneg
  have hsum : (A (0, C)).1 + (A (0, C)).1 = 0 :=
    eq_neg_iff_add_eq_zero.mp hself
  have hsmul : (2 : ℂ) • (A (0, C)).1 = 0 := by
    simpa [two_smul] using hsum
  exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)

/-! ## Restricted half-spin representations -/

/-- Positive-semispinor block of the Dirac spin action. -/
def spinPlusLinear (g : ComplexSpin44) : Module.End ℂ SpinorPlus8 :=
  (LinearMap.fst ℂ SpinorPlus8 SpinorMinus8).comp
    ((((complexSpinDiracRepresentation g : DiracGL) :
      Module.End ℂ DiracSpinor16)).comp
        (LinearMap.inl ℂ SpinorPlus8 SpinorMinus8))

@[simp] theorem spinPlusLinear_apply (g : ComplexSpin44) (S : SpinorPlus8) :
    spinPlusLinear g S =
      (((complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) (S, 0)).1 := rfl

/-- Negative-semispinor block of the Dirac spin action. -/
def spinMinusLinear (g : ComplexSpin44) : Module.End ℂ SpinorMinus8 :=
  (LinearMap.snd ℂ SpinorPlus8 SpinorMinus8).comp
    ((((complexSpinDiracRepresentation g : DiracGL) :
      Module.End ℂ DiracSpinor16)).comp
        (LinearMap.inr ℂ SpinorPlus8 SpinorMinus8))

@[simp] theorem spinMinusLinear_apply (g : ComplexSpin44)
    (C : SpinorMinus8) :
    spinMinusLinear g C =
      (((complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) (0, C)).2 := rfl

theorem spinPlusLinear_one : spinPlusLinear 1 = 1 := by
  apply LinearMap.ext
  intro S
  simp [spinPlusLinear]

theorem spinMinusLinear_one : spinMinusLinear 1 = 1 := by
  apply LinearMap.ext
  intro C
  simp [spinMinusLinear]

theorem spinPlusLinear_mul (g h : ComplexSpin44) :
    spinPlusLinear (g * h) = spinPlusLinear g * spinPlusLinear h := by
  apply LinearMap.ext
  intro S
  let A := ((complexSpinDiracRepresentation h : DiracGL) :
    Module.End ℂ DiracSpinor16)
  have hz : (A (S, 0)).2 = 0 := complexSpinDirac_preserves_plus h S
  change
    (((complexSpinDiracRepresentation (g * h) : DiracGL) :
      Module.End ℂ DiracSpinor16) (S, 0)).1 =
      (((complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) ((A (S, 0)).1, 0)).1
  rw [map_mul]
  change
    (((complexSpinDiracRepresentation g : DiracGL) :
      Module.End ℂ DiracSpinor16) (A (S, 0))).1 = _
  rw [show A (S, 0) = ((A (S, 0)).1, 0) by
    apply Prod.ext <;> simp [hz]]

theorem spinMinusLinear_mul (g h : ComplexSpin44) :
    spinMinusLinear (g * h) = spinMinusLinear g * spinMinusLinear h := by
  apply LinearMap.ext
  intro C
  let A := ((complexSpinDiracRepresentation h : DiracGL) :
    Module.End ℂ DiracSpinor16)
  have hz : (A (0, C)).1 = 0 := complexSpinDirac_preserves_minus h C
  change
    (((complexSpinDiracRepresentation (g * h) : DiracGL) :
      Module.End ℂ DiracSpinor16) (0, C)).2 =
      (((complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) (0, (A (0, C)).2)).2
  rw [map_mul]
  change
    (((complexSpinDiracRepresentation g : DiracGL) :
      Module.End ℂ DiracSpinor16) (A (0, C))).2 = _
  rw [show A (0, C) = (0, (A (0, C)).2) by
    apply Prod.ext <;> simp [hz]]

/-- Genuine positive half-spin representation extracted from the even Dirac
action. -/
def complexSpinPlusRepresentation : ComplexSpin44 →* SpinorPlusGL where
  toFun g :=
    { val := spinPlusLinear g
      inv := spinPlusLinear g⁻¹
      val_inv := by
        rw [← spinPlusLinear_mul, mul_inv_cancel, spinPlusLinear_one]
      inv_val := by
        rw [← spinPlusLinear_mul, inv_mul_cancel, spinPlusLinear_one] }
  map_one' := by
    apply Units.ext
    exact spinPlusLinear_one
  map_mul' g h := by
    apply Units.ext
    exact spinPlusLinear_mul g h

/-- Genuine negative half-spin representation extracted from the even Dirac
action. -/
def complexSpinMinusRepresentation : ComplexSpin44 →* SpinorMinusGL where
  toFun g :=
    { val := spinMinusLinear g
      inv := spinMinusLinear g⁻¹
      val_inv := by
        rw [← spinMinusLinear_mul, mul_inv_cancel, spinMinusLinear_one]
      inv_val := by
        rw [← spinMinusLinear_mul, inv_mul_cancel, spinMinusLinear_one] }
  map_one' := by
    apply Units.ext
    exact spinMinusLinear_one
  map_mul' g h := by
    apply Units.ext
    exact spinMinusLinear_mul g h

theorem complexSpinDirac_blocks (g : ComplexSpin44)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    (((complexSpinDiracRepresentation g : DiracGL) :
      Module.End ℂ DiracSpinor16) (S, C)) =
      (spinorPlusAct (complexSpinPlusRepresentation g) S,
        spinorMinusAct (complexSpinMinusRepresentation g) C) := by
  have hsplit : (S, C) = (S, 0) + (0, C) := by
    apply Prod.ext
    · exact (add_zero S).symm
    · exact (zero_add C).symm
  rw [hsplit, map_add]
  apply Prod.ext
  · simp [spinorPlusAct, complexSpinPlusRepresentation,
      spinPlusLinear, complexSpinDirac_preserves_minus]
  · simp [spinorMinusAct, complexSpinMinusRepresentation,
      spinMinusLinear, complexSpinDirac_preserves_plus]

end CanonicalZornSpinChirality

end noncomputable section
