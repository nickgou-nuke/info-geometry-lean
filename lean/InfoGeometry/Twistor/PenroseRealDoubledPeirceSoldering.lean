import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.SplitQuadraticSheets
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

/-!
# Penrose real-doubled/Peirce soldering

This file records the carrier-level soldering between the complex Penrose
twistor carrier and the canonical real doubled carrier.  It deliberately
does not transport the Penrose quadratic form or octonionic multiplication:
the result here is a real-linear carrier equivalence together with its
canonical doubled Peirce decomposition.
-/

namespace InfoGeometry.Twistor.PenroseRealDoubledPeirceSoldering

open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

local notation "Real4" => Fin 4 → ℝ
local notation "Peirce8" => PeirceCarrier

noncomputable def twistorRealification :
    TwistorCarrier ≃ₗ[ℝ] (Real4 × Real4) where
  toFun z := (fun i => (z i).re, fun i => (z i).im)
  invFun p := fun i => ⟨p.1 i, p.2 i⟩
  left_inv z := by
    funext i
    apply Complex.ext <;> rfl
  right_inv p := by
    rcases p with ⟨x, y⟩
    rfl
  map_add' z w := by
    ext i <;> simp
  map_smul' r z := by
    ext i <;> simp [smul_eq_mul]

@[simp] theorem twistorRealification_apply (z : TwistorCarrier) :
    twistorRealification z =
      (fun i => (z i).re, fun i => (z i).im) := rfl

@[simp] theorem twistorRealification_symm_apply (x y : Real4) (i : Fin 4) :
    (twistorRealification.symm (x, y)) i = ⟨x i, y i⟩ := rfl

noncomputable def penroseRealDoubledEquiv :
    TwistorCarrier ≃ₗ[ℝ] DoubledSpace Real4 :=
  { toFun := fun z => to_doubled (fun i => (z i).re) (fun i => (z i).im)
    invFun := fun u => fun i =>
      ⟨(WithLp.fst u) i, (WithLp.snd u) i⟩
    left_inv := by
      intro z
      funext i
      apply Complex.ext <;> simp
    right_inv := by
      intro u
      apply DoubledSpace.ext <;> simp [to_doubled]
    map_add' := by
      intro z w
      apply DoubledSpace.ext
      · funext i
        simp [to_doubled]
      · funext i
        simp [to_doubled]
    map_smul' := by
      intro r z
      apply DoubledSpace.ext
      · funext i
        simp [to_doubled]
      · funext i
        simp [to_doubled] }

@[simp] theorem penroseRealDoubledEquiv_apply (z : TwistorCarrier) :
    penroseRealDoubledEquiv z =
      to_doubled (fun i => (z i).re) (fun i => (z i).im) := by
  rfl

theorem penroseRealDoubled_peirce_decomposition (z : TwistorCarrier) :
    penroseRealDoubledEquiv z =
      plusPoint (E := Real4) (fun i => (z i).re) +
        minusPoint (E := Real4) (fun i => (z i).im) := by
  apply DoubledSpace.ext <;> simp [penroseRealDoubledEquiv, plusPoint, minusPoint,
    to_doubled]

theorem penroseRealDoubled_soldering_readback (z : TwistorCarrier) :
    (WithLp.fst (penroseRealDoubledEquiv z),
      WithLp.snd (penroseRealDoubledEquiv z)) =
      (fun i => (z i).re, fun i => (z i).im) := by
  simp [penroseRealDoubledEquiv]

noncomputable def penrosePeirceEquiv :
    TwistorCarrier ≃ₗ[ℝ] Peirce8 where
  toFun z := ![(z 0).re, (z 1).re, (z 2).re, (z 3).re,
    (z 0).im, (z 1).im, (z 2).im, (z 3).im]
  invFun x := fun i =>
    ⟨x ⟨i.val, by omega⟩, x ⟨i.val + 4, by omega⟩⟩
  left_inv := by
    intro z
    funext i
    apply Complex.ext
    · fin_cases i <;> simp
    · fin_cases i <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> rfl
  map_add' := by
    intro z w
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro r z
    funext i
    fin_cases i <;> simp

@[simp] theorem penrosePeirceEquiv_apply (z : TwistorCarrier) :
    penrosePeirceEquiv z =
      ![(z 0).re, (z 1).re, (z 2).re, (z 3).re,
        (z 0).im, (z 1).im, (z 2).im, (z 3).im] := rfl

theorem penrosePeirceEquiv_readback (z : TwistorCarrier) :
    (fun i =>
      ⟨(penrosePeirceEquiv z) ⟨i.val, by omega⟩,
        (penrosePeirceEquiv z) ⟨i.val + 4, by omega⟩⟩) = z := by
  funext i
  apply Complex.ext
  · fin_cases i <;> simp
  · fin_cases i <;> simp

end InfoGeometry.Twistor.PenroseRealDoubledPeirceSoldering
