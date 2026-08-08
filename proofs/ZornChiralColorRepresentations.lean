import proofs.ZornColorChargeConjugation
import proofs.ZornColorLieRepresentation

/-!
# Bundled chiral color representations

The two supported matrix-unit families are extended to arbitrary `3 × 3`
matrices.  A shared induction theorem proves the commutator law, and explicit
coordinate probes prove faithfulness of both chiral actions.
-/

noncomputable section

namespace ZornChiralColorRepresentations

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open SplitOctonionBraidSU3
open ZornThreeChannelCAR ZornColorLieAction
open ZornColorLieRepresentation ZornChiralColorActions
open ZornColorChargeConjugation

/-- Linear extension of an arbitrary family indexed by matrix units. -/
def matrixUnitAction (op : Fin 3 → Fin 3 → Module.End ℂ DiracSpinor16) :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ DiracSpinor16 where
  toFun A := ∑ r : Fin 3, ∑ s : Fin 3, A r s • op r s
  map_add' A B := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp [Matrix.smul_apply, Finset.smul_sum, smul_smul]

@[simp] theorem matrixUnitAction_apply
    (op : Fin 3 → Fin 3 → Module.End ℂ DiracSpinor16)
    (A : Matrix (Fin 3) (Fin 3) ℂ) :
    matrixUnitAction op A = ∑ r : Fin 3, ∑ s : Fin 3, A r s • op r s := rfl

@[simp] theorem matrixUnitAction_single
    (op : Fin 3 → Fin 3 → Module.End ℂ DiracSpinor16)
    (r s : Fin 3) (c : ℂ) :
    matrixUnitAction op (Matrix.single r s c) = c • op r s := by
  fin_cases r <;> fin_cases s <;>
    simp [matrixUnitAction, Fin.sum_univ_three]

private theorem matrixSingle_mul (r s t u : Fin 3) (a b : ℂ) :
    Matrix.single r s a * Matrix.single t u b =
      colorDelta s t • Matrix.single r u (a * b) := by
  classical
  by_cases hst : s = t
  · subst t
    simp [colorDelta]
  · simp [colorDelta, hst]

/-- A matrix-unit commutator packet extends to arbitrary matrices. -/
theorem matrixUnitAction_commutator
    (op : Fin 3 → Fin 3 → Module.End ℂ DiracSpinor16)
    (hop : ∀ r s t u,
      op r s * op t u - op t u * op r s =
        colorDelta s t • op r u - colorDelta u r • op t s)
    (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    matrixUnitAction op (A * B - B * A) =
      matrixUnitAction op A * matrixUnitAction op B -
        matrixUnitAction op B * matrixUnitAction op A := by
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A₁ A₂ h₁ h₂ =>
      calc
        matrixUnitAction op ((A₁ + A₂) * B - B * (A₁ + A₂)) =
            matrixUnitAction op
              ((A₁ * B - B * A₁) + (A₂ * B - B * A₂)) := by
                congr 1; noncomm_ring
        _ = matrixUnitAction op (A₁ * B - B * A₁) +
              matrixUnitAction op (A₂ * B - B * A₂) := map_add _ _ _
        _ = _ := by
          rw [h₁, h₂, map_add]
          noncomm_ring
  | h_std_basis r s a =>
      induction B using Matrix.induction_on' with
      | h_zero => simp
      | h_add B₁ B₂ h₁ h₂ =>
          calc
            matrixUnitAction op
                (Matrix.single r s a * (B₁ + B₂) -
                  (B₁ + B₂) * Matrix.single r s a) =
                matrixUnitAction op
                  ((Matrix.single r s a * B₁ - B₁ * Matrix.single r s a) +
                   (Matrix.single r s a * B₂ - B₂ * Matrix.single r s a)) := by
                    congr 1; noncomm_ring
            _ = matrixUnitAction op
                  (Matrix.single r s a * B₁ - B₁ * Matrix.single r s a) +
                matrixUnitAction op
                  (Matrix.single r s a * B₂ - B₂ * Matrix.single r s a) :=
                    map_add _ _ _
            _ = _ := by
              rw [h₁, h₂, map_add]
              noncomm_ring
      | h_std_basis t u b =>
          rw [matrixSingle_mul, matrixSingle_mul, map_sub, map_smul, map_smul,
            matrixUnitAction_single, matrixUnitAction_single,
            matrixUnitAction_single, matrixUnitAction_single]
          calc
            colorDelta s t • (a * b) • op r u -
                colorDelta u r • (b * a) • op t s =
              (a * b) •
                (colorDelta s t • op r u - colorDelta u r • op t s) := by
                  rw [mul_comm b a]
                  module
            _ = (a * b) • (op r s * op t u - op t u * op r s) := by
                  rw [hop]
            _ = a • op r s * b • op t u - b • op t u * a • op r s := by
                  simp only [smul_sub, smul_mul_smul]
                  module

/-- Faithful positive chiral action. -/
def positiveColorAction :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ DiracSpinor16 :=
  matrixUnitAction positiveColorOp

/-- Faithful negative chiral action. -/
def negativeColorAction :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ DiracSpinor16 :=
  matrixUnitAction negativeColorOp

@[simp] theorem positiveColorAction_apply (A : Matrix (Fin 3) (Fin 3) ℂ) :
    positiveColorAction A = matrixUnitAction positiveColorOp A := rfl

@[simp] theorem negativeColorAction_apply (A : Matrix (Fin 3) (Fin 3) ℂ) :
    negativeColorAction A = matrixUnitAction negativeColorOp A := rfl

theorem positiveColorAction_commutator (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    matrixUnitAction positiveColorOp (A * B - B * A) =
    matrixUnitAction positiveColorOp A * matrixUnitAction positiveColorOp B -
      matrixUnitAction positiveColorOp B * matrixUnitAction positiveColorOp A :=
  matrixUnitAction_commutator
    (op := positiveColorOp) positiveColorOp_commutator A B

theorem negativeColorAction_commutator (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    matrixUnitAction negativeColorOp (A * B - B * A) =
    matrixUnitAction negativeColorOp A * matrixUnitAction negativeColorOp B -
      matrixUnitAction negativeColorOp B * matrixUnitAction negativeColorOp A :=
  matrixUnitAction_commutator
    (op := negativeColorOp) negativeColorOp_commutator A B

theorem positiveColorOp_probe_u (r s i j : Fin 3) :
    (positiveColorOp r s (positiveUProbe j)).1.val.u i =
      colorDelta i r * colorDelta s j := by
  rw [positiveColorOp_apply]
  by_cases hsj : s = j <;> by_cases hir : i = r <;>
    simp [positiveUProbe, colorPlusZorn, mixedPlusZorn, colorDelta,
      hsj, hir, zornSmul]

theorem positiveColorAction_probe_u (A : Matrix (Fin 3) (Fin 3) ℂ)
    (r s : Fin 3) :
    ((positiveColorAction A) (positiveUProbe s)).1.val.u r = A r s := by
  change positiveUCoord r ((matrixUnitAction positiveColorOp A) (positiveUProbe s)) = A r s
  rw [matrixUnitAction_apply, LinearMap.sum_apply, map_sum]
  change (∑ x : Fin 3, positiveUCoord r
    (∑ y : Fin 3, A x y • positiveColorOp x y (positiveUProbe s))) = A r s
  simp_rw [map_sum, map_smul, positiveUCoord_apply, positiveColorOp_probe_u]
  simp [colorDelta]

theorem positiveColorAction_injective : Function.Injective positiveColorAction := by
  intro A B hAB
  apply Matrix.ext
  intro r s
  have h := congrArg
    (fun F : Module.End ℂ DiracSpinor16 =>
      positiveUCoord r (F (positiveUProbe s))) hAB
  change ((positiveColorAction A) (positiveUProbe s)).1.val.u r =
    ((positiveColorAction B) (positiveUProbe s)).1.val.u r at h
  rw [positiveColorAction_probe_u, positiveColorAction_probe_u] at h
  exact h

/-- Negative-`v` probe carrying the `r`th standard color vector. -/
def negativeVProbe (r : Fin 3) : DiracSpinor16 :=
  (0, ⟨{ a := 0, u := 0, v := Pi.single r 1, b := 0 }⟩)

/-- Linear extraction of one negative-`v` coordinate. -/
def negativeVCoord (s : Fin 3) : DiracSpinor16 →ₗ[ℂ] ℂ where
  toFun X := X.2.val.v s
  map_add' X Y := by rw [Prod.snd_add, copy_add_val]; rfl
  map_smul' c X := by rw [Prod.smul_snd, copy_smul_val]; rfl

@[simp] theorem negativeVCoord_apply (s : Fin 3) (X : DiracSpinor16) :
    negativeVCoord s X = X.2.val.v s := rfl

theorem negativeColorOp_probe_v (r s i j : Fin 3) :
    (negativeColorOp r s (negativeVProbe j)).2.val.v i =
      -(colorDelta i s * colorDelta r j) := by
  rw [negativeColorOp_apply]
  by_cases his : i = s <;> by_cases hrj : r = j <;>
    simp [negativeVProbe, colorMinusZorn, mixedMinusZorn, colorDelta,
      his, hrj]

theorem negativeColorAction_probe_v (A : Matrix (Fin 3) (Fin 3) ℂ)
    (r s : Fin 3) :
    ((negativeColorAction A) (negativeVProbe r)).2.val.v s = -A r s := by
  change negativeVCoord s
    ((matrixUnitAction negativeColorOp A) (negativeVProbe r)) = -A r s
  rw [matrixUnitAction_apply, LinearMap.sum_apply, map_sum]
  change (∑ x : Fin 3, negativeVCoord s
    (∑ y : Fin 3, A x y • negativeColorOp x y (negativeVProbe r))) = -A r s
  simp_rw [map_sum, map_smul, negativeVCoord_apply, negativeColorOp_probe_v]
  simp [colorDelta]

theorem negativeColorAction_injective : Function.Injective negativeColorAction := by
  intro A B hAB
  apply Matrix.ext
  intro r s
  have h := congrArg
    (fun F : Module.End ℂ DiracSpinor16 =>
      negativeVCoord s (F (negativeVProbe r))) hAB
  have hneg : -A r s = -B r s := by
    change ((negativeColorAction A) (negativeVProbe r)).2.val.v s =
      ((negativeColorAction B) (negativeVProbe r)).2.val.v s at h
    rw [negativeColorAction_probe_v, negativeColorAction_probe_v] at h
    exact h
  exact neg_injective hneg

/-- Disjoint support persists after arbitrary linear combination. -/
theorem positive_negativeColorAction_mul_zero
    (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    positiveColorAction A * negativeColorAction B = 0 := by
  rw [positiveColorAction, negativeColorAction,
    matrixUnitAction_apply, matrixUnitAction_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul,
    positive_negative_mul_eq_zero, smul_zero]
  simp

theorem negative_positiveColorAction_mul_zero
    (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    negativeColorAction A * positiveColorAction B = 0 := by
  rw [positiveColorAction, negativeColorAction,
    matrixUnitAction_apply, matrixUnitAction_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul,
    negative_positive_mul_eq_zero, smul_zero]
  simp

theorem positive_negativeColorAction_commute
    (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    positiveColorAction A * negativeColorAction B =
      negativeColorAction B * positiveColorAction A := by
  rw [positive_negativeColorAction_mul_zero,
    negative_positiveColorAction_mul_zero]

/-- A single negative color matrix unit annihilates the positive `u` probe. -/
theorem negativeColorOp_positiveUProbe_zero
    (r t s : Fin 3) :
    negativeColorOp r t (positiveUProbe s) = 0 := by
  rw [negativeColorOp_apply]
  apply Prod.ext <;> apply ZornCopy.ext <;> apply zorn_ext
  · simp
  · funext i; simp
  · funext i; simp
  · simp
  · simp [positiveUProbe, colorMinusZorn, mixedMinusZorn]
  · funext i; simp [positiveUProbe, colorMinusZorn, mixedMinusZorn]
  · funext i; simp [positiveUProbe, colorMinusZorn, mixedMinusZorn]
  · simp [positiveUProbe, colorMinusZorn, mixedMinusZorn]

/-- A single positive color matrix unit annihilates the negative `v` probe. -/
theorem positiveColorOp_negativeVProbe_zero
    (s t r : Fin 3) :
    positiveColorOp s t (negativeVProbe r) = 0 := by
  rw [positiveColorOp_apply]
  apply Prod.ext <;> apply ZornCopy.ext <;> apply zorn_ext
  · simp [negativeVProbe, colorPlusZorn, mixedPlusZorn, zornSmul]
  · funext i; simp [negativeVProbe, colorPlusZorn, mixedPlusZorn, zornSmul]
  · funext i; simp [negativeVProbe, colorPlusZorn, mixedPlusZorn, zornSmul]
  · simp [negativeVProbe, colorPlusZorn, mixedPlusZorn, zornSmul]
  · simp
  · funext i; simp
  · funext i; simp
  · simp

theorem negativeColorAction_positiveUProbe_zero
    (A : Matrix (Fin 3) (Fin 3) ℂ) (s : Fin 3) :
    negativeColorAction A (positiveUProbe s) = 0 := by
  rw [negativeColorAction, matrixUnitAction_apply, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro r _
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [LinearMap.smul_apply, negativeColorOp_positiveUProbe_zero, smul_zero]

theorem positiveColorAction_negativeVProbe_zero
    (A : Matrix (Fin 3) (Fin 3) ℂ) (r : Fin 3) :
    positiveColorAction A (negativeVProbe r) = 0 := by
  rw [positiveColorAction, matrixUnitAction_apply, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro s _
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [LinearMap.smul_apply, positiveColorOp_negativeVProbe_zero, smul_zero]

/-- Direct-sum action of the two commuting chiral color copies. -/
def chiralColorAction :
    (Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 3) (Fin 3) ℂ) →ₗ[ℂ]
      Module.End ℂ DiracSpinor16 where
  toFun AB := positiveColorAction AB.1 + negativeColorAction AB.2
  map_add' AB CD := by
    rw [Prod.fst_add, Prod.snd_add, map_add, map_add]
    abel
  map_smul' c AB := by
    rw [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, smul_add]
    simp

@[simp] theorem chiralColorAction_apply
    (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    chiralColorAction (A, B) = positiveColorAction A + negativeColorAction B := rfl

/-- The direct-sum color action is faithful on the Dirac carrier. -/
theorem chiralColorAction_injective : Function.Injective chiralColorAction := by
  rintro ⟨A, B⟩ ⟨C, D⟩ h
  rw [chiralColorAction_apply, chiralColorAction_apply] at h
  have hA : A = C := by
    apply Matrix.ext
    intro r s
    have hp := congrArg
      (fun F : Module.End ℂ DiracSpinor16 =>
        positiveUCoord r (F (positiveUProbe s))) h
    change positiveUCoord r
        ((positiveColorAction A + negativeColorAction B) (positiveUProbe s)) =
      positiveUCoord r
        ((positiveColorAction C + negativeColorAction D) (positiveUProbe s)) at hp
    rw [LinearMap.add_apply, LinearMap.add_apply,
      negativeColorAction_positiveUProbe_zero,
      negativeColorAction_positiveUProbe_zero, add_zero, add_zero] at hp
    change ((positiveColorAction A) (positiveUProbe s)).1.val.u r =
      ((positiveColorAction C) (positiveUProbe s)).1.val.u r at hp
    rw [positiveColorAction_probe_u, positiveColorAction_probe_u] at hp
    exact hp
  have hB : B = D := by
    apply Matrix.ext
    intro r s
    have hn := congrArg
      (fun F : Module.End ℂ DiracSpinor16 =>
        negativeVCoord s (F (negativeVProbe r))) h
    change negativeVCoord s
        ((positiveColorAction A + negativeColorAction B) (negativeVProbe r)) =
      negativeVCoord s
        ((positiveColorAction C + negativeColorAction D) (negativeVProbe r)) at hn
    rw [LinearMap.add_apply, LinearMap.add_apply,
      positiveColorAction_negativeVProbe_zero,
      positiveColorAction_negativeVProbe_zero, zero_add, zero_add] at hn
    change ((negativeColorAction B) (negativeVProbe r)).2.val.v s =
      ((negativeColorAction D) (negativeVProbe r)).2.val.v s at hn
    have hneg : -B r s = -D r s := by
      rw [negativeColorAction_probe_v, negativeColorAction_probe_v] at hn
      exact hn
    exact neg_injective hneg
  exact Prod.ext hA hB

/-- Bracket preservation for the faithful direct-sum action. -/
theorem chiralColorAction_commutator
    (A B C D : Matrix (Fin 3) (Fin 3) ℂ) :
    chiralColorAction (A * B - B * A, C * D - D * C) =
      chiralColorAction (A, C) * chiralColorAction (B, D) -
        chiralColorAction (B, D) * chiralColorAction (A, C) := by
  rw [chiralColorAction_apply, chiralColorAction_apply,
    chiralColorAction_apply]
  simp only [mul_add, add_mul]
  rw [positive_negativeColorAction_mul_zero,
    negative_positiveColorAction_mul_zero,
    positive_negativeColorAction_mul_zero,
    negative_positiveColorAction_mul_zero]
  simp only [positiveColorAction_apply, negativeColorAction_apply]
  rw [positiveColorAction_commutator, negativeColorAction_commutator]
  noncomm_ring

/-- The conjugate negative transpose forced by the normalization of `J`. -/
def conjNegTranspose (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun r s => -complexConjHom (A s r)

@[simp] theorem conjNegTranspose_apply
    (A : Matrix (Fin 3) (Fin 3) ℂ) (r s : Fin 3) :
    conjNegTranspose A r s = -complexConjHom (A s r) := rfl

/-- The conjugate-linear involution transports the complete positive matrix
action to the negative action, not only its nine basis operators. -/
theorem chargeConjugation_positiveColorAction
    (A : Matrix (Fin 3) (Fin 3) ℂ) (X : DiracSpinor16) :
    chargeConjugation (positiveColorAction A X) =
      negativeColorAction (conjNegTranspose A) (chargeConjugation X) := by
  simp only [positiveColorAction, negativeColorAction, matrixUnitAction,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply]
  conv_rhs => rw [Finset.sum_comm]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    chargeConjugation_positiveColorOp]
  simp only [conjNegTranspose_apply]
  rw [LinearMap.smul_apply]
  module

/-- The converse transport of the complete negative action. -/
theorem chargeConjugation_negativeColorAction
    (A : Matrix (Fin 3) (Fin 3) ℂ) (X : DiracSpinor16) :
    chargeConjugation (negativeColorAction A X) =
      positiveColorAction (conjNegTranspose A) (chargeConjugation X) := by
  simp only [positiveColorAction, negativeColorAction, matrixUnitAction,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply]
  conv_rhs => rw [Finset.sum_comm]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    chargeConjugation_negativeColorOp]
  simp only [conjNegTranspose_apply]
  rw [LinearMap.smul_apply]
  module

end ZornChiralColorRepresentations

end noncomputable section
