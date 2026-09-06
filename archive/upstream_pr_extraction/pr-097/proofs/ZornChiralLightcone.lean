import InfoGeometry.Canonical.CanonicalZornCliffordRepresentation
import InfoGeometry.Canonical.CanonicalZornCompositionFiveGradeBridge
import InfoGeometry.Canonical.CanonicalZornSpinChirality

/-!
# Canonical Zorn chiral lightcone operators

The upper and lower Zorn nilpotents give null vectors in the canonical vector
copy.  Their gamma actions are cut into directed chiral blocks by the genuine
Dirac grading projectors `(1 ± χ)/2`.
-/

noncomputable section

namespace ZornChiralLightcone

open InfoGeometry.Physics.SplitOctonionBraidSU3
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation

/-- The chiral grading on the canonical Dirac carrier. -/
def chiralityOperator : Module.End ℂ DiracSpinor16 :=
  CanonicalZornSpinChirality.diracChirality.toLinearMap

@[simp] theorem chiralityOperator_apply (S : SpinorPlus8) (C : SpinorMinus8) :
    chiralityOperator (S, C) = (S, -C) := rfl

theorem chiralityOperator_sq :
    chiralityOperator * chiralityOperator = 1 := by
  apply LinearMap.ext
  intro Ψ
  change CanonicalZornSpinChirality.diracChirality
      (CanonicalZornSpinChirality.diracChirality Ψ) = Ψ
  exact CanonicalZornSpinChirality.diracChirality_sq Ψ

@[ext] lemma Zorn.ext_chiral (X Y : Zorn) (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hb : X.b = Y.b) : X = Y := by
  cases X
  cases Y
  dsimp only at ha hu hv hb
  rw [ha, hu, hv, hb]

/-- Positive Dirac/Peirce projector. -/
def peirceProjectorPlus : Module.End ℂ DiracSpinor16 :=
  (1 / 2 : ℂ) • (1 + chiralityOperator)

/-- Negative Dirac/Peirce projector. -/
def peirceProjectorMinus : Module.End ℂ DiracSpinor16 :=
  (1 / 2 : ℂ) • (1 - chiralityOperator)

@[simp] theorem peirceProjectorPlus_apply (S : SpinorPlus8) (C : SpinorMinus8) :
  peirceProjectorPlus (S, C) = (S, 0) := by
  apply Prod.ext
  · simp [peirceProjectorPlus, chiralityOperator]
    module
  · simp [peirceProjectorPlus, chiralityOperator]

@[simp] theorem peirceProjectorMinus_apply (S : SpinorPlus8) (C : SpinorMinus8) :
  peirceProjectorMinus (S, C) = (0, C) := by
  apply Prod.ext
  · simp [peirceProjectorMinus, chiralityOperator]
  · simp [peirceProjectorMinus, chiralityOperator]
    module

theorem peirceProjectorPlus_sq :
    peirceProjectorPlus * peirceProjectorPlus = peirceProjectorPlus := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  simp

theorem peirceProjectorMinus_sq :
    peirceProjectorMinus * peirceProjectorMinus = peirceProjectorMinus := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  simp

theorem peirceProjectorMinus_mul_plus :
    peirceProjectorMinus * peirceProjectorPlus = 0 := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  simp

theorem peirceProjectorPlus_mul_minus :
    peirceProjectorPlus * peirceProjectorMinus = 0 := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  simp

theorem peirceProjectorPlus_add_minus :
    peirceProjectorPlus + peirceProjectorMinus = 1 := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  apply Prod.ext <;> simp

/-- Upper and lower null vectors on the typed vector carrier. -/
def upperLightconeVector (r : Fin 3) : Vector8 := ⟨E_k r⟩
def lowerLightconeVector (r : Fin 3) : Vector8 := ⟨F_k r⟩

theorem upperLightconeVector_null (r : Fin 3) :
    vectorQuadratic (upperLightconeVector r) = 0 := by
  rw [vectorQuadratic_apply]
  simp [upperLightconeVector, vectorNorm, zornNorm, E_k, dot3]

theorem lowerLightconeVector_null (r : Fin 3) :
    vectorQuadratic (lowerLightconeVector r) = 0 := by
  rw [vectorQuadratic_apply]
  simp [lowerLightconeVector, vectorNorm, zornNorm, F_k, dot3]

theorem upperLightconeGamma_sq (r : Fin 3) :
    diracGamma (upperLightconeVector r) * diracGamma (upperLightconeVector r) = 0 := by
  rw [diracGamma_sq, upperLightconeVector_null]
  simp

theorem lowerLightconeGamma_sq (r : Fin 3) :
    diracGamma (lowerLightconeVector r) * diracGamma (lowerLightconeVector r) = 0 := by
  rw [diracGamma_sq, lowerLightconeVector_null]
  simp

/-- Exact block-diagonal representation of the gamma action. -/
def lightconeSigmaPlus (r : Fin 3) : Module.End ℂ DiracSpinor16 :=
  peirceProjectorPlus * diracGamma (upperLightconeVector r) * peirceProjectorMinus

def lightconeSigmaMinus (r : Fin 3) : Module.End ℂ DiracSpinor16 :=
  peirceProjectorMinus * diracGamma (lowerLightconeVector r) * peirceProjectorPlus

@[simp] lemma ZornCopy_val_a_zero (s : TrialitySector) : (0 : ZornCopy s).val.a = 0 := rfl
@[simp] lemma ZornCopy_val_u_zero (s : TrialitySector) : (0 : ZornCopy s).val.u = 0 := by ext i; fin_cases i <;> rfl
@[simp] lemma ZornCopy_val_v_zero (s : TrialitySector) : (0 : ZornCopy s).val.v = 0 := by ext i; fin_cases i <;> rfl
@[simp] lemma ZornCopy_val_b_zero (s : TrialitySector) : (0 : ZornCopy s).val.b = 0 := rfl

/-- Linearity of `diracGamma V` gives the zero law on the positive semispinor input. -/
@[simp] theorem cliffordPlus_zero (V : Vector8) :
    cliffordPlus V (0 : SpinorPlus8) = (0 : SpinorMinus8) := by
  have h := (diracGamma V).map_zero
  exact congrArg Prod.snd h

/-- Linearity of `diracGamma V` gives the zero law on the negative semispinor input. -/
@[simp] theorem cliffordMinus_zero (V : Vector8) :
    cliffordMinus V (0 : SpinorMinus8) = (0 : SpinorPlus8) := by
  have h := (diracGamma V).map_zero
  exact congrArg Prod.fst h

@[simp] theorem lightconeSigmaPlus_apply (r : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeSigmaPlus r (S, C) =
      (cliffordMinus (upperLightconeVector r) C, 0) := by
  change peirceProjectorPlus (diracGamma (upperLightconeVector r) (peirceProjectorMinus (S, C))) = _
  rw [peirceProjectorMinus_apply S C]
  change peirceProjectorPlus
    (cliffordMinus (upperLightconeVector r) C,
      cliffordPlus (upperLightconeVector r) 0) = _
  rw [cliffordPlus_zero, peirceProjectorPlus_apply]

@[simp] theorem lightconeSigmaMinus_apply (r : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeSigmaMinus r (S, C) =
      (0, cliffordPlus (lowerLightconeVector r) S) := by
  change peirceProjectorMinus (diracGamma (lowerLightconeVector r) (peirceProjectorPlus (S, C))) = _
  rw [peirceProjectorPlus_apply S C]
  change peirceProjectorMinus
    (cliffordMinus (lowerLightconeVector r) 0,
      cliffordPlus (lowerLightconeVector r) S) = _
  rw [cliffordMinus_zero, peirceProjectorMinus_apply]

/-- Canonical unit witnesses in the two typed semispinor copies. -/
def spinorPlusOne : SpinorPlus8 := ⟨I_zorn⟩
def spinorMinusOne : SpinorMinus8 := ⟨I_zorn⟩

theorem lightconeSigmaPlus_ne_zero (r : Fin 3) :
    lightconeSigmaPlus r ≠ 0 := by
  intro h
  have h_eval : lightconeSigmaPlus r (0, spinorMinusOne) = 0 := by rw [h]; rfl
  have h_apply : lightconeSigmaPlus r (0, spinorMinusOne) = (cliffordMinus (upperLightconeVector r) spinorMinusOne, 0) :=
    lightconeSigmaPlus_apply r 0 spinorMinusOne
  rw [h_apply] at h_eval
  injection h_eval with h1 _
  have h_u : (cliffordMinus (upperLightconeVector r) spinorMinusOne).val.u r = 0 := by
    have h1_u := congrArg (fun Z => Z.val.u r) h1
    change _ = (0 : SpinorPlus8).val.u r at h1_u
    rw [ZornCopy_val_u_zero] at h1_u
    exact h1_u
  fin_cases r
  · revert h_u; simp [cliffordMinus, upperLightconeVector, spinorMinusOne, zornConj, zornMul, E_k, I_zorn, e_k, cross3]
  · revert h_u; simp [cliffordMinus, upperLightconeVector, spinorMinusOne, zornConj, zornMul, E_k, I_zorn, e_k, cross3]
  · revert h_u; simp [cliffordMinus, upperLightconeVector, spinorMinusOne, zornConj, zornMul, E_k, I_zorn, e_k, cross3]

theorem lightconeSigmaMinus_ne_zero (r : Fin 3) :
    lightconeSigmaMinus r ≠ 0 := by
  intro h
  have h_eval : lightconeSigmaMinus r (spinorPlusOne, 0) = 0 := by rw [h]; rfl
  have h_apply : lightconeSigmaMinus r (spinorPlusOne, 0) = (0, cliffordPlus (lowerLightconeVector r) spinorPlusOne) :=
    lightconeSigmaMinus_apply r spinorPlusOne 0
  rw [h_apply] at h_eval
  injection h_eval with _ h2
  have h_v : (cliffordPlus (lowerLightconeVector r) spinorPlusOne).val.v r = 0 := by
    have h2_v := congrArg (fun Z => Z.val.v r) h2
    change _ = (0 : SpinorMinus8).val.v r at h2_v
    rw [ZornCopy_val_v_zero] at h2_v
    exact h2_v
  fin_cases r
  · revert h_v; simp [cliffordPlus, lowerLightconeVector, spinorPlusOne, zornMul, F_k, I_zorn, e_k, cross3]
  · revert h_v; simp [cliffordPlus, lowerLightconeVector, spinorPlusOne, zornMul, F_k, I_zorn, e_k, cross3]
  · revert h_v; simp [cliffordPlus, lowerLightconeVector, spinorPlusOne, zornMul, F_k, I_zorn, e_k, cross3]

/-! ## Exact mixed products

The mixed products preserve chirality, but they are color-resolved Zorn
actions rather than the identity on the full Dirac carrier.
-/

@[simp] theorem lightconeSigmaPlus_mul_minus_apply (r : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeSigmaPlus r (lightconeSigmaMinus r (S, C)) =
      (cliffordMinus (upperLightconeVector r)
        (cliffordPlus (lowerLightconeVector r) S), 0) := by
  calc
    _ = lightconeSigmaPlus r
        (0, cliffordPlus (lowerLightconeVector r) S) :=
      congrArg (lightconeSigmaPlus r)
        (lightconeSigmaMinus_apply r S C)
    _ = _ := lightconeSigmaPlus_apply r 0
      (cliffordPlus (lowerLightconeVector r) S)

@[simp] theorem lightconeSigmaMinus_mul_plus_apply (r : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeSigmaMinus r (lightconeSigmaPlus r (S, C)) =
      (0, cliffordPlus (lowerLightconeVector r)
        (cliffordMinus (upperLightconeVector r) C)) := by
  calc
    _ = lightconeSigmaMinus r
        (cliffordMinus (upperLightconeVector r) C, 0) :=
      congrArg (lightconeSigmaMinus r)
        (lightconeSigmaPlus_apply r S C)
    _ = _ := lightconeSigmaMinus_apply r
      (cliffordMinus (upperLightconeVector r) C) 0

/-- Exact color-resolved anticommutator on the two chiral blocks. -/
theorem lightconeSigma_anticommutator_apply (r : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeSigmaPlus r (lightconeSigmaMinus r (S, C)) +
        lightconeSigmaMinus r (lightconeSigmaPlus r (S, C)) =
      (cliffordMinus (upperLightconeVector r)
          (cliffordPlus (lowerLightconeVector r) S),
        cliffordPlus (lowerLightconeVector r)
          (cliffordMinus (upperLightconeVector r) C)) := by
  rw [lightconeSigmaPlus_mul_minus_apply,
    lightconeSigmaMinus_mul_plus_apply]
  apply Prod.ext <;> simp

/-- Exact color-resolved commutator on the two chiral blocks. -/
theorem lightconeSigma_commutator_apply (r : Fin 3)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    lightconeSigmaPlus r (lightconeSigmaMinus r (S, C)) -
        lightconeSigmaMinus r (lightconeSigmaPlus r (S, C)) =
      (cliffordMinus (upperLightconeVector r)
          (cliffordPlus (lowerLightconeVector r) S),
        -cliffordPlus (lowerLightconeVector r)
          (cliffordMinus (upperLightconeVector r) C)) := by
  rw [lightconeSigmaPlus_mul_minus_apply,
    lightconeSigmaMinus_mul_plus_apply]
  apply Prod.ext <;> simp

theorem lightconeSigmaPlus_nilpotent (r : Fin 3) :
    lightconeSigmaPlus r * lightconeSigmaPlus r = 0 := by
  calc lightconeSigmaPlus r * lightconeSigmaPlus r
    _ = peirceProjectorPlus * diracGamma (upperLightconeVector r) * (peirceProjectorMinus * peirceProjectorPlus) * diracGamma (upperLightconeVector r) * peirceProjectorMinus := by
      simp only [lightconeSigmaPlus, mul_assoc]
    _ = 0 := by
      rw [peirceProjectorMinus_mul_plus]
      simp

theorem lightconeSigmaMinus_nilpotent (r : Fin 3) :
    lightconeSigmaMinus r * lightconeSigmaMinus r = 0 := by
  calc lightconeSigmaMinus r * lightconeSigmaMinus r
    _ = peirceProjectorMinus * diracGamma (lowerLightconeVector r) * (peirceProjectorPlus * peirceProjectorMinus) * diracGamma (lowerLightconeVector r) * peirceProjectorPlus := by
      simp only [lightconeSigmaMinus, mul_assoc]
    _ = 0 := by
      rw [peirceProjectorPlus_mul_minus]
      simp

theorem peirce_causal_closure_plus (r : Fin 3) :
    peirceProjectorPlus * lightconeSigmaPlus r * peirceProjectorMinus =
      lightconeSigmaPlus r := by
  calc peirceProjectorPlus * lightconeSigmaPlus r * peirceProjectorMinus
    _ = (peirceProjectorPlus * peirceProjectorPlus) * diracGamma (upperLightconeVector r) * (peirceProjectorMinus * peirceProjectorMinus) := by
      simp only [lightconeSigmaPlus]
      simp only [mul_assoc]
    _ = peirceProjectorPlus * diracGamma (upperLightconeVector r) * peirceProjectorMinus := by
      rw [peirceProjectorPlus_sq, peirceProjectorMinus_sq]
    _ = lightconeSigmaPlus r := rfl

theorem peirce_causal_closure_minus (r : Fin 3) :
    peirceProjectorMinus * lightconeSigmaMinus r * peirceProjectorPlus =
      lightconeSigmaMinus r := by
  calc peirceProjectorMinus * lightconeSigmaMinus r * peirceProjectorPlus
    _ = (peirceProjectorMinus * peirceProjectorMinus) * diracGamma (lowerLightconeVector r) * (peirceProjectorPlus * peirceProjectorPlus) := by
      simp only [lightconeSigmaMinus]
      simp only [mul_assoc]
    _ = peirceProjectorMinus * diracGamma (lowerLightconeVector r) * peirceProjectorPlus := by
      rw [peirceProjectorMinus_sq, peirceProjectorPlus_sq]
    _ = lightconeSigmaMinus r := rfl

/-- The canonical chirality grading is an involutive tripotent. -/
theorem chiralityOperator_tripotent :
    chiralityOperator * chiralityOperator * chiralityOperator = chiralityOperator := by
  rw [chiralityOperator_sq, one_mul]

/-- Each Peirce projector is also tripotent (indeed idempotent). -/
theorem peirceProjectorPlus_tripotent :
    peirceProjectorPlus * peirceProjectorPlus * peirceProjectorPlus =
      peirceProjectorPlus := by
  rw [peirceProjectorPlus_sq, peirceProjectorPlus_sq]

theorem peirceProjectorMinus_tripotent :
    peirceProjectorMinus * peirceProjectorMinus * peirceProjectorMinus =
      peirceProjectorMinus := by
  rw [peirceProjectorMinus_sq, peirceProjectorMinus_sq]

end ZornChiralLightcone

end noncomputable section
