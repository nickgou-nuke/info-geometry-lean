import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalFiveGradedCarrierModule
import InfoGeometry.Exceptional.FreudenthalSymplecticAction
import InfoGeometry.Exceptional.FreudenthalSymplecticMixedTripleCounterexample

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

abbrev SymplecticContactModule := ℝ × (FreudenthalCharge J × ℝ)
abbrev SymplecticContactEnd := Module.End ℝ (SymplecticContactModule (J := J))

def symplecticContactBracket
    (u v : FiveGradedCarrier D) : FiveGradedCarrier D where
  minus2 :=
    (-2 * u.zero_scale * v.minus2 + 2 * v.zero_scale * u.minus2) -
      2 * FreudenthalCharge.symplecticForm D u.minus1 v.minus1
  minus1 :=
    (-u.zero_scale • v.minus1 + v.zero_scale • u.minus1) +
      ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) v.minus1 -
        (v.zero_symp : Module.End ℝ (FreudenthalCharge J)) u.minus1) +
      (-u.minus2 • v.plus1 + v.minus2 • u.plus1)
  zero_symp :=
    ⁅u.zero_symp, v.zero_symp⁆ +
      mixedSymplecticBracket D u.minus1 v.plus1 -
      mixedSymplecticBracket D v.minus1 u.plus1
  zero_scale :=
    (u.plus2 * v.minus2 - v.plus2 * u.minus2) +
      (FreudenthalCharge.symplecticForm D u.minus1 v.plus1 -
        FreudenthalCharge.symplecticForm D v.minus1 u.plus1)
  plus1 :=
    (u.zero_scale • v.plus1 - v.zero_scale • u.plus1) +
      ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) v.plus1 -
        (v.zero_symp : Module.End ℝ (FreudenthalCharge J)) u.plus1) +
      (-u.plus2 • v.minus1 + v.plus2 • u.minus1)
  plus2 :=
    (2 * u.zero_scale * v.plus2 - 2 * v.zero_scale * u.plus2) +
      2 * FreudenthalCharge.symplecticForm D u.plus1 v.plus1

def symplecticContactRepresentation :
    FiveGradedCarrier D →ₗ[ℝ] SymplecticContactEnd (J := J) where
  toFun u :=
    { toFun := fun q =>
        (u.zero_scale * q.1 +
            FreudenthalCharge.symplecticForm D u.plus1 q.2.1 +
            u.plus2 * q.2.2,
          (q.1 • u.minus1 +
              (u.zero_symp : Module.End ℝ (FreudenthalCharge J)) q.2.1 +
              q.2.2 • u.plus1,
            u.minus2 * q.1 -
              FreudenthalCharge.symplecticForm D u.minus1 q.2.1 -
              u.zero_scale * q.2.2))
      map_add' := by
        rintro ⟨a, ⟨x, b⟩⟩ ⟨c, ⟨y, d⟩⟩
        apply Prod.ext
        · simp [symplecticForm_add_right]
          ring
        · apply Prod.ext
          · simp
            module
          · simp [symplecticForm_add_right]
            ring
      map_smul' := by
        rintro c ⟨a, ⟨x, b⟩⟩
        apply Prod.ext
        · simp [symplecticForm_smul_right]
          ring
        · apply Prod.ext
          · simp
            module
          · simp [symplecticForm_smul_right]
            ring }
  map_add' u v := by
    apply LinearMap.ext
    rintro ⟨a, ⟨x, b⟩⟩
    apply Prod.ext
    · simp [symplecticForm_add_left]
      ring
    · apply Prod.ext
      · simp
        module
      · simp [symplecticForm_add_left]
        ring
  map_smul' c u := by
    apply LinearMap.ext
    rintro ⟨a, ⟨x, b⟩⟩
    apply Prod.ext
    · simp [symplecticForm_smul_left]
      ring
    · apply Prod.ext
      · simp
        module
      · simp [symplecticForm_smul_left]
        ring

@[simp] theorem symplecticContactRepresentation_apply
    (u : FiveGradedCarrier D) (r : ℝ)
    (z : FreudenthalCharge J) (s : ℝ) :
    symplecticContactRepresentation D u (r, (z, s)) =
      (u.zero_scale * r +
          FreudenthalCharge.symplecticForm D u.plus1 z + u.plus2 * s,
        (r • u.minus1 +
            (u.zero_symp : Module.End ℝ (FreudenthalCharge J)) z +
            s • u.plus1,
          u.minus2 * r -
            FreudenthalCharge.symplecticForm D u.minus1 z -
            u.zero_scale * s)) := rfl

theorem symplecticOperator_move_right
    (T : SymplecticTKKZero D) (x y : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D x
        ((T : Module.End ℝ (FreudenthalCharge J)) y) =
      -FreudenthalCharge.symplecticForm D
        ((T : Module.End ℝ (FreudenthalCharge J)) x) y := by
  linarith [T.property x y]

theorem symplecticContactRepresentation_bracket
    (u v : FiveGradedCarrier D) :
    symplecticContactRepresentation D (symplecticContactBracket D u v) =
      symplecticContactRepresentation D u *
          symplecticContactRepresentation D v -
        symplecticContactRepresentation D v *
          symplecticContactRepresentation D u := by
  apply LinearMap.ext
  rintro ⟨r, ⟨z, s⟩⟩
  apply Prod.ext
  · simp [symplecticContactBracket, Module.End.mul_apply,
      Ring.lie_def, mixedSymplecticBracket_val,
      symplecticRankTwo_apply, symplecticForm_add_left,
      symplecticForm_add_right, symplecticForm_sub_left,
      symplecticForm_smul_left, symplecticForm_smul_right,
      symplecticForm_neg_left]
    rw [symplecticOperator_move_right D v.zero_symp u.plus1 z,
      symplecticOperator_move_right D u.zero_symp v.plus1 z]
    rw [FreudenthalCharge.symplectic_form_skew D v.minus1 u.plus1,
      FreudenthalCharge.symplectic_form_skew D v.plus1 u.minus1,
      FreudenthalCharge.symplectic_form_skew D v.plus1 u.plus1]
    ring
  · apply Prod.ext
    · simp [symplecticContactBracket, Module.End.mul_apply,
        Ring.lie_def, mixedSymplecticBracket_val,
        symplecticRankTwo_apply]
      module
    · simp [symplecticContactBracket, Module.End.mul_apply,
        Ring.lie_def, mixedSymplecticBracket_val,
        symplecticRankTwo_apply, symplecticForm_add_left,
        symplecticForm_add_right, symplecticForm_sub_left,
        symplecticForm_smul_left, symplecticForm_smul_right,
        symplecticForm_neg_left]
      rw [symplecticOperator_move_right D v.zero_symp u.minus1 z,
        symplecticOperator_move_right D u.zero_symp v.minus1 z]
      rw [FreudenthalCharge.symplectic_form_skew D v.minus1 u.minus1]
      ring

theorem symplecticContactRepresentation_injective :
    Function.Injective (symplecticContactRepresentation D) := by
  intro u v huv
  have hminus := congrArg
    (fun F : SymplecticContactEnd (J := J) =>
      F ((1 : ℝ), ((0 : FreudenthalCharge J), (0 : ℝ)))) huv
  have hplus := congrArg
    (fun F : SymplecticContactEnd (J := J) =>
      F ((0 : ℝ), ((0 : FreudenthalCharge J), (1 : ℝ)))) huv
  have hm2 : u.minus2 = v.minus2 := by
    simpa using congrArg (fun q => q.2.2) hminus
  have hm1 : u.minus1 = v.minus1 := by
    simpa using congrArg (fun q => q.2.1) hminus
  have hscale : u.zero_scale = v.zero_scale := by
    simpa using congrArg (fun q => q.1) hminus
  have hp1 : u.plus1 = v.plus1 := by
    simpa using congrArg (fun q => q.2.1) hplus
  have hp2 : u.plus2 = v.plus2 := by
    simpa using congrArg (fun q => q.1) hplus
  have hsymp : u.zero_symp = v.zero_symp := by
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    have hz := congrArg
      (fun F : SymplecticContactEnd (J := J) =>
        F ((0 : ℝ), (z, (0 : ℝ)))) huv
    simpa using congrArg (fun q => q.2.1) hz
  apply FiveGradedCarrier.ext D u v
  · exact hm2
  · exact hm1
  · exact hsymp
  · exact hscale
  · exact hp1
  · exact hp2

theorem corrected_minus1_minus1_bracket
    (x y : FreudenthalCharge J) :
    symplecticContactBracket D (injChargeMinus D x) (injChargeMinus D y) =
      genEminus D
        (-2 * FreudenthalCharge.symplecticForm D x y) := by
  apply FiveGradedCarrier.ext <;>
    simp [symplecticContactBracket, injChargeMinus, genEminus]

end InfoGeometry.Exceptional.Freudenthal
