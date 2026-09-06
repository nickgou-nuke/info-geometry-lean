import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

/-!
# Real twistor, split-quaternion block, and split-octonion carrier readouts

This file records only real-linear carrier equivalences.  In particular, it
does not impose a bi-twistor reality involution and does not transport either
the matrix or Zorn multiplication.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealSplitOctonionCarrierBridge

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

abbrev Real8 := Fin 8 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat2Pair := Mat2 × Mat2
abbrev Exterior3 := InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev CanonicalZorn := InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.CanonicalSplitOctonion

noncomputable def twistorRealEquivReal8 :
    Twistor4 ≃ₗ[ℝ] Real8 where
  toFun z := ![(z.1 0).re, (z.1 0).im, (z.1 1).re, (z.1 1).im,
    (z.2 0).re, (z.2 0).im, (z.2 1).re, (z.2 1).im]
  invFun x :=
    (fun i => ⟨x ⟨2 * i.val, by omega⟩, x ⟨2 * i.val + 1, by omega⟩⟩,
     fun i => ⟨x ⟨2 * i.val + 4, by omega⟩, x ⟨2 * i.val + 5, by omega⟩⟩)
  left_inv := by
    intro z
    apply Prod.ext <;> funext i
    · fin_cases i <;> apply Complex.ext <;> simp
    · fin_cases i <;> apply Complex.ext <;> simp
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

@[simp] theorem twistorRealEquivReal8_apply (z : Twistor4) :
    twistorRealEquivReal8 z =
      ![(z.1 0).re, (z.1 0).im, (z.1 1).re, (z.1 1).im,
        (z.2 0).re, (z.2 0).im, (z.2 1).re, (z.2 1).im] := rfl

/-- The chosen real polarization, expressed as the inverse coordinate readout. -/
noncomputable def realCoordinatesTwistor : Real8 →ₗ[ℝ] Twistor4 :=
  twistorRealEquivReal8.symm

noncomputable def real8EquivMat2Pair : Real8 ≃ₗ[ℝ] Mat2Pair where
  toFun x :=
    (!![x 0, x 1; x 2, x 3], !![x 4, x 5; x 6, x 7])
  invFun p := ![p.1 0 0, p.1 0 1, p.1 1 0, p.1 1 1,
    p.2 0 0, p.2 0 1, p.2 1 0, p.2 1 1]
  left_inv := by
    intro x
    funext i
    fin_cases i <;> rfl
  right_inv := by
    intro p
    apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  map_add' := by
    intro x y
    apply Prod.ext <;> ext i j <;> fin_cases i <;> simp
  map_smul' := by
    intro r x
    apply Prod.ext <;> ext i j <;> fin_cases i <;> simp

noncomputable def twistorRealEquivMat2Pair :
    Twistor4 ≃ₗ[ℝ] Mat2Pair :=
  twistorRealEquivReal8.trans real8EquivMat2Pair

noncomputable def twistorRealEquivExterior3 :
    Twistor4 ≃ₗ[ℝ] Exterior3 :=
  twistorRealEquivReal8.trans
    exterior3SplitOctonionCoordinateEquiv.symm

noncomputable def twistorRealEquivZorn :
    Twistor4 ≃ₗ[ℝ] CanonicalZorn :=
  twistorRealEquivExterior3.trans exterior3CircularPeirceEquiv

theorem twistorRealEquivZorn_factorization (z : Twistor4) :
    twistorRealEquivZorn z =
      exterior3CircularPeirceEquiv (twistorRealEquivExterior3 z) := rfl

@[simp] theorem twistorRealEquivExterior3_coordinateAxis (j : Fin 8) :
    twistorRealEquivExterior3 (realCoordinatesTwistor (Pi.single j 1)) =
      exterior3PeirceBasis j := by
  simp [twistorRealEquivExterior3, realCoordinatesTwistor]
  apply exterior3SplitOctonionCoordinateEquiv.injective
  simp [exterior3SplitOctonionCoordinateEquiv_basis]

@[simp] theorem twistorRealEquivZorn_coordinateAxis (j : Fin 8) :
    twistorRealEquivZorn (realCoordinatesTwistor (Pi.single j 1)) =
    circularPeirceBasis j := by
  rw [twistorRealEquivZorn_factorization,
    twistorRealEquivExterior3_coordinateAxis]
  exact exterior3CircularPeirceEquiv_basis j

theorem twistor_real_carrier_has_block_and_zorn_readouts :
    Nonempty (Twistor4 ≃ₗ[ℝ] Mat2Pair) ∧
      Nonempty (Twistor4 ≃ₗ[ℝ] CanonicalZorn) :=
  ⟨⟨twistorRealEquivMat2Pair⟩, ⟨twistorRealEquivZorn⟩⟩

end InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
