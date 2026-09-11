import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import InfoGeometry.Physics.PenroseQuantizedTwistorSplitOctonion
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

/-!
# Penrose real bi-twistors and the real doubled Peirce carrier

The Penrose reality condition determines the lower half of a bi-twistor from
its upper half.  This owner records that fact as a native real carrier map:
the real and imaginary parts of the four upper complex coordinates are the
two real sheets.  The final map is the established Peirce coordinate readout;
no multiplication or norm equivalence is asserted here.
-/

noncomputable section

namespace InfoGeometry.Physics.PenroseTwistor

open InfoGeometry.Krein
open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

abbrev PenroseRealCarrier := InfoGeometry.Algebra.FiniteSpin.Vec4C
abbrev RealSheet := InfoGeometry.Algebra.FiniteSpin.Vec4R
abbrev PenrosePeirceCarrier := InfoGeometry.Algebra.FiniteSpin.Vec8R

def realBiTwistor (u : PenroseRealCarrier) : BiTwistor where
  up := u
  dn := fun i => star (u i)

@[simp] theorem realBiTwistor_isReal (u : PenroseRealCarrier) :
    isRealBiTwistor (realBiTwistor u) := by
  intro i
  rfl

@[simp] theorem realBiTwistor_up (u : PenroseRealCarrier) (i : Fin 4) :
    (realBiTwistor u).up i = u i := rfl

@[simp] theorem realBiTwistor_dn (u : PenroseRealCarrier) (i : Fin 4) :
    (realBiTwistor u).dn i = star (u i) := rfl

def penroseRealToDoubled :
    PenroseRealCarrier →ₗ[ℝ] DoubledSpace RealSheet where
  toFun u := to_doubled (fun i => (u i).re) (fun i => (u i).im)
  map_add' u v := by
    apply DoubledSpace.ext <;> funext i <;> simp [to_doubled]
  map_smul' c u := by
    apply DoubledSpace.ext <;> funext i <;> simp [to_doubled]

@[simp] theorem penroseRealToDoubled_fst (u : PenroseRealCarrier) :
    WithLp.fst (penroseRealToDoubled u) = fun i => (u i).re := by
  rfl

@[simp] theorem penroseRealToDoubled_snd (u : PenroseRealCarrier) :
    WithLp.snd (penroseRealToDoubled u) = fun i => (u i).im := by
  rfl

def penroseRealToPeirce :
    PenroseRealCarrier →ₗ[ℝ] PenrosePeirceCarrier where
  toFun u := ![(u 0).re, (u 1).re, (u 2).re, (u 3).re,
    (u 0).im, (u 1).im, (u 2).im, (u 3).im]
  map_add' u v := by
    ext i
    fin_cases i <;> simp
  map_smul' c u := by
    ext i
    fin_cases i <;> simp

def peirceToPenroseReal :
    PenrosePeirceCarrier →ₗ[ℝ] PenroseRealCarrier where
  toFun x := fun i =>
    ⟨x ⟨i.val, by omega⟩, x ⟨i.val + 4, by omega⟩⟩
  map_add' x y := by
    funext i
    apply Complex.ext <;> simp
  map_smul' c x := by
    funext i
    apply Complex.ext <;> simp

noncomputable def penroseRealPeirceSoldering :
    PenroseRealCarrier ≃ₗ[ℝ] PenrosePeirceCarrier :=
  { penroseRealToPeirce with
    invFun := peirceToPenroseReal
    left_inv := by
      intro u
      funext i
      fin_cases i <;> simp [penroseRealToPeirce, peirceToPenroseReal]
    right_inv := by
      intro x
      funext i
      fin_cases i <;> simp [penroseRealToPeirce, peirceToPenroseReal] }

@[simp] theorem penroseRealPeirceSoldering_apply (u : PenroseRealCarrier) :
    penroseRealPeirceSoldering u = penroseRealToPeirce u := rfl

@[simp] theorem penroseRealPeirceSoldering_realBiTwistor (u : PenroseRealCarrier) :
    isRealBiTwistor (realBiTwistor u) := realBiTwistor_isReal u

theorem penroseReal_soldering_readback (u : PenroseRealCarrier) :
    peirceToPenroseReal (penroseRealToPeirce u) = u := by
  exact penroseRealPeirceSoldering.left_inv u

theorem penroseReal_doubled_readback (u : PenroseRealCarrier) :
    (WithLp.fst (penroseRealToDoubled u) =
        (fun i => (u i).re)) ∧
      (WithLp.snd (penroseRealToDoubled u) =
        (fun i => (u i).im)) := by
  exact ⟨penroseRealToDoubled_fst u, penroseRealToDoubled_snd u⟩

end InfoGeometry.Physics.PenroseTwistor
