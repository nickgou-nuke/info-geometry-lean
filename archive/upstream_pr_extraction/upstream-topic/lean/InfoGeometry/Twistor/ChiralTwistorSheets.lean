import Mathlib.Tactic
import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-! Chiral sheets and their chosen real coordinate readouts. -/

noncomputable section

namespace InfoGeometry.Twistor.ChiralTwistorSheets

open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

local notation "TwistorPlus" => Fin 2 → ℂ
local notation "TwistorMinus" => Fin 2 → ℂ
local notation "PeircePlus4" => ℝ × (Fin 3 → ℝ)
local notation "PeirceMinus4" => (Fin 3 → ℝ) × ℝ

/-! The two twistor owners use isomorphic but non-definitional carriers.
This explicit equivalence is the sole carrier bridge between them. -/

noncomputable def penroseTwistor4CarrierEquiv :
    PenroseIncidence.Twistor4 ≃ₗ[ℂ] PenroseTwistor.TwistorCarrier where
  toFun p := fun i =>
    if h : i.val < 2 then p.1 ⟨i.val, h⟩
    else p.2 ⟨i.val - 2, by omega⟩
  invFun z :=
    (fun i => z ⟨i.val, by omega⟩,
      fun i => z ⟨i.val + 2, by omega⟩)
  left_inv := by
    intro p
    apply Prod.ext <;> funext i <;> simp
  right_inv := by
    intro z
    funext i
    fin_cases i <;> rfl
  map_add' := by
    intro p q
    funext i
    by_cases h : i.val < 2 <;> simp [h]
  map_smul' := by
    intro c p
    funext i
    by_cases h : i.val < 2 <;> simp [h]

@[simp] theorem penroseTwistor4CarrierEquiv_apply (p : PenroseIncidence.Twistor4) :
    penroseTwistor4CarrierEquiv p = fun i =>
      if h : i.val < 2 then p.1 ⟨i.val, h⟩
      else p.2 ⟨i.val - 2, by omega⟩ := rfl

noncomputable def twistorChiralDecomposition :
    TwistorCarrier ≃ₗ[ℂ] TwistorPlus × TwistorMinus where
  toFun z :=
    (fun i => z ⟨i.val, by omega⟩,
      fun i => z ⟨i.val + 2, by omega⟩)
  invFun p := fun i =>
    if h : i.val < 2 then p.1 ⟨i.val, h⟩
    else p.2 ⟨i.val - 2, by omega⟩
  left_inv := by
    intro z
    funext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨p, q⟩
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  map_add' := by
    intro z w
    apply Prod.ext <;> funext i <;> rfl
  map_smul' := by
    intro c z
    apply Prod.ext <;> funext i <;> rfl

@[simp] theorem twistorChiralDecomposition_apply (z : TwistorCarrier) :
    twistorChiralDecomposition z =
      (fun i => z ⟨i.val, by omega⟩,
        fun i => z ⟨i.val + 2, by omega⟩) := rfl

theorem twistorChiralDecomposition_carrierBridge (p : PenroseIncidence.Twistor4) :
    twistorChiralDecomposition (penroseTwistor4CarrierEquiv p) =
      (p.1, p.2) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

noncomputable def twistorChiralRealDecomposition :
    TwistorCarrier ≃ₗ[ℝ] TwistorPlus × TwistorMinus where
  toFun z :=
    (fun i => z ⟨i.val, by omega⟩,
      fun i => z ⟨i.val + 2, by omega⟩)
  invFun p := fun i =>
    if h : i.val < 2 then p.1 ⟨i.val, h⟩
    else p.2 ⟨i.val - 2, by omega⟩
  left_inv := by
    intro z
    funext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨p, q⟩
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  map_add' := by
    intro z w
    apply Prod.ext <;> funext i <;> rfl
  map_smul' := by
    intro r z
    apply Prod.ext <;> funext i <;> simp

@[simp] theorem twistorChiralRealDecomposition_apply (z : TwistorCarrier) :
    twistorChiralRealDecomposition z =
      (fun i => z ⟨i.val, by omega⟩,
        fun i => z ⟨i.val + 2, by omega⟩) := rfl

theorem twistorPlus_finrank_real :
    Module.finrank ℝ TwistorPlus = 4 := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]

theorem twistorMinus_finrank_real :
    Module.finrank ℝ TwistorMinus = 4 := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]

theorem twistorChiral_real_dimension :
    Module.finrank ℝ (TwistorPlus × TwistorMinus) = 8 := by
  calc
    Module.finrank ℝ (TwistorPlus × TwistorMinus) =
        Module.finrank ℝ TwistorPlus + Module.finrank ℝ TwistorMinus :=
      Module.finrank_prod
    _ = 4 + 4 := by
      norm_num [twistorPlus_finrank_real, twistorMinus_finrank_real]
    _ = 8 := by norm_num

noncomputable def twistorPlusRealEquiv :
    TwistorPlus ≃ₗ[ℝ] PeircePlus4 where
  toFun z := ((z 0).re, ![(z 0).im, (z 1).re, (z 1).im])
  invFun p := fun i => if i = 0 then ⟨p.1, p.2 0⟩ else ⟨p.2 1, p.2 2⟩
  left_inv := by
    intro z
    funext i
    fin_cases i <;> apply Complex.ext <;> simp
  right_inv := by
    rintro ⟨a, v⟩
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
  map_add' := by
    intro z w
    apply Prod.ext
    · simp
    · funext i
      fin_cases i <;> simp
  map_smul' := by
    intro r z
    apply Prod.ext
    · simp
    · funext i
      fin_cases i <;> simp

noncomputable def twistorMinusRealEquiv :
    TwistorMinus ≃ₗ[ℝ] PeirceMinus4 where
  toFun z := (![(z 0).re, (z 0).im, (z 1).re], (z 1).im)
  invFun p := fun i => if i = 0 then ⟨p.1 0, p.1 1⟩ else ⟨p.1 2, p.2⟩
  left_inv := by
    intro z
    funext i
    fin_cases i <;> apply Complex.ext <;> simp
  right_inv := by
    rintro ⟨v, b⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_add' := by
    intro z w
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · simp
  map_smul' := by
    intro r z
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · simp

noncomputable def twistorChiralPeirceEquiv :
    TwistorCarrier ≃ₗ[ℝ] PeircePlus4 × PeirceMinus4 :=
  twistorChiralRealDecomposition.trans
    { toFun := fun p => (twistorPlusRealEquiv p.1, twistorMinusRealEquiv p.2)
      invFun := fun p => (twistorPlusRealEquiv.symm p.1, twistorMinusRealEquiv.symm p.2)
      left_inv := by
        intro p
        exact Prod.ext (twistorPlusRealEquiv.left_inv p.1)
          (twistorMinusRealEquiv.left_inv p.2)
      right_inv := by
        intro p
        exact Prod.ext (twistorPlusRealEquiv.right_inv p.1)
          (twistorMinusRealEquiv.right_inv p.2)
      map_add' := by
        intro p q
        exact Prod.ext (twistorPlusRealEquiv.map_add p.1 q.1)
          (twistorMinusRealEquiv.map_add p.2 q.2)
      map_smul' := by
        intro r p
        exact Prod.ext (twistorPlusRealEquiv.map_smul r p.1)
          (twistorMinusRealEquiv.map_smul r p.2) }

@[simp] theorem twistorChiralPeirceEquiv_apply (z : TwistorCarrier) :
    twistorChiralPeirceEquiv z =
      (twistorPlusRealEquiv (fun i => z ⟨i.val, by omega⟩),
        twistorMinusRealEquiv (fun i => z ⟨i.val + 2, by omega⟩)) := by
  rfl

theorem twistorChiralPeirceEquiv_carrierBridge
    (p : PenroseIncidence.Twistor4) :
    twistorChiralPeirceEquiv (penroseTwistor4CarrierEquiv p) =
      (twistorPlusRealEquiv p.1, twistorMinusRealEquiv p.2) := by
  rw [twistorChiralPeirceEquiv_apply]
  rfl

noncomputable def chiralPeirceCoordinateEquiv :
    (PeircePlus4 × PeirceMinus4) ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun p := ![p.1.1, p.1.2 0, p.1.2 1, p.1.2 2,
    p.2.2, p.2.1 0, p.2.1 1, p.2.1 2]
  invFun x := ((x 0, ![x 1, x 2, x 3]), (![x 5, x 6, x 7], x 4))
  left_inv := by
    rintro ⟨⟨a, v⟩, ⟨w, b⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;> rfl
    · apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · rfl
  right_inv := by
    intro x
    funext i
    fin_cases i <;> rfl
  map_add' := by
    intro p q
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro r p
    funext i
    fin_cases i <;> simp

noncomputable def twistorChiralZornEquiv :
    TwistorCarrier ≃ₗ[ℝ] CZ :=
  twistorChiralPeirceEquiv.trans
    (chiralPeirceCoordinateEquiv.trans circularPeirceBasis.equivFun.symm)

theorem twistorChiralZornEquiv_circularCoordinates (z : TwistorCarrier) :
    circularPeirceBasis.equivFun (twistorChiralZornEquiv z) =
      chiralPeirceCoordinateEquiv (twistorChiralPeirceEquiv z) := by
  unfold twistorChiralZornEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    circularPeirceBasis.equivFun.apply_symm_apply]

/-- The twistor vector whose chosen real chiral coordinates are the `j`-th
Peirce coordinate axis.  This is a basis-level readout, not a new carrier. -/
noncomputable def twistorChiralCoordinateAxis (j : Fin 8) : TwistorCarrier :=
  twistorChiralPeirceEquiv.symm
    (chiralPeirceCoordinateEquiv.symm (Pi.single j 1))

@[simp] theorem twistorChiralCoordinateAxis_readback (j : Fin 8) :
    chiralPeirceCoordinateEquiv
        (twistorChiralPeirceEquiv (twistorChiralCoordinateAxis j)) =
      Pi.single j 1 := by
  simp [twistorChiralCoordinateAxis]

@[simp] theorem twistorChiralCoordinateAxis_zorn (j : Fin 8) :
    twistorChiralZornEquiv (twistorChiralCoordinateAxis j) =
      circularPeirceBasis j := by
  apply circularPeirceBasis.equivFun.injective
  rw [twistorChiralZornEquiv_circularCoordinates]
  unfold twistorChiralCoordinateAxis
  simp only [LinearEquiv.apply_symm_apply]
  ext k
  have h := Module.Basis.equivFun_self circularPeirceBasis j k
  rw [Pi.single_apply, h]
  by_cases hkj : k = j
  · subst k
    simp
  · have hjk : j ≠ k := Ne.symm hkj
    simp [hkj, hjk]

end InfoGeometry.Twistor.ChiralTwistorSheets
