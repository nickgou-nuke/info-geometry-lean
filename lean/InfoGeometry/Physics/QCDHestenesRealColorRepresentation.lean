import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetComplexPolarization
import InfoGeometry.Physics.QCDNativeZornColorRepresentation

/-!
# Hestenes real form of the three-colour representation

This module keeps the colour carrier real and realizes the ordinary complex
structure internally.  The complex matrix action remains only a convenient
coordinate source; the representation carrier is

`RealColorLane = Fin 3 -> (R × R)`.

The internal operator `realColorJ` is the pointwise real rotation
`(x,y) ↦ (-y,x)`.  It squares to `-I`.  The realified `gl₃(C)` action is
obtained by transporting the already-owned faithful complex colour action
through the real/imaginary coordinate equivalence.  The action commutes with
`realColorJ`.

A separate real-linear involution `realColorConj` acts by `(x,y) ↦ (x,-y)`.
It squares to the identity and anticommutes with `realColorJ`, which is the
real-linear form of `C(iψ) = -i Cψ`.

No physical charge-conjugation, Hilbert-space, or gauge-field interpretation is
asserted here.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDHestenesRealColorRepresentation

open InfoGeometry.Canonical.TwoSheetComplexPolarization
open InfoGeometry.Physics.QCDNativeZornColorRepresentation

abbrev ComplexColorLane := InfoGeometry.Algebra.FiniteSpin.Vec3C
abbrev RealPair := ℝ × ℝ
abbrev RealColorLane := Fin 3 → RealPair
abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C

/-- Real/imaginary coordinate equivalence for one complex scalar. -/
def complexPairEquiv : ℂ ≃ₗ[ℝ] RealPair where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv z := by
    apply Complex.ext <;> rfl
  right_inv p := by
    rcases p with ⟨x,y⟩
    rfl
  map_add' z w := by
    ext <;> rfl
  map_smul' r z := by
    ext <;> simp [add_comm]

/-- Pointwise realification of the three-component complex colour carrier. -/
def colorRealEquiv : ComplexColorLane ≃ₗ[ℝ] RealColorLane where
  toFun u := fun i => complexPairEquiv (u i)
  invFun u := fun i => complexPairEquiv.symm (u i)
  left_inv u := by
    funext i
    exact complexPairEquiv.symm_apply_apply (u i)
  right_inv u := by
    funext i
    exact complexPairEquiv.apply_symm_apply (u i)
  map_add' u v := by
    funext i
    exact map_add complexPairEquiv (u i) (v i)
  map_smul' r u := by
    funext i
    exact map_smul complexPairEquiv r (u i)

/-- The internal square-minus-one operator on one real two-plane. -/
def pairJ : RealPair →ₗ[ℝ] RealPair where
  toFun p := (-p.2, p.1)
  map_add' p q := by
    rcases p with ⟨x,y⟩
    rcases q with ⟨u,v⟩
    ext <;> simp [add_comm]
  map_smul' r p := by
    rcases p with ⟨x,y⟩
    ext <;> simp

/-- Real-linear conjugation on one real two-plane. -/
def pairConj : RealPair →ₗ[ℝ] RealPair where
  toFun p := (p.1, -p.2)
  map_add' p q := by
    rcases p with ⟨x,y⟩
    rcases q with ⟨u,v⟩
    ext <;> simp
    · abel
  map_smul' r p := by
    rcases p with ⟨x,y⟩
    ext <;> simp

/-- `pairJ` is exactly the finite two-sheet Hestenes complex axis. -/
theorem pairJ_eq_emergentComplexK_mulVec (p : RealPair) :
    pairJ p =
      (emergentComplexK.mulVec ![p.1, p.2] 0,
       emergentComplexK.mulVec ![p.1, p.2] 1) := by
  rcases p with ⟨x,y⟩
  rw [emergentComplexK_eq]
  simp [pairJ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem pairJ_sq : pairJ * pairJ = -(1 : Module.End ℝ RealPair) := by
  apply LinearMap.ext
  rintro ⟨x,y⟩
  ext <;> simp [pairJ, Module.End.mul_apply]

@[simp] theorem pairConj_sq :
    pairConj * pairConj = (1 : Module.End ℝ RealPair) := by
  apply LinearMap.ext
  rintro ⟨x,y⟩
  ext <;> simp [pairConj, Module.End.mul_apply]

/-- Real conjugation anticommutes with the internal complex axis. -/
theorem pairConj_anticomm_pairJ :
    pairConj * pairJ = -(pairJ * pairConj) := by
  apply LinearMap.ext
  rintro ⟨x,y⟩
  ext <;> simp [pairConj, pairJ, Module.End.mul_apply]

/-- Pointwise Hestenes complex structure on the three-colour real carrier. -/
def realColorJ : Module.End ℝ RealColorLane where
  toFun u := fun i => pairJ (u i)
  map_add' u v := by
    funext i
    exact map_add pairJ (u i) (v i)
  map_smul' r u := by
    funext i
    exact map_smul pairJ r (u i)

/-- Pointwise real conjugation on the three-colour carrier. -/
def realColorConj : Module.End ℝ RealColorLane where
  toFun u := fun i => pairConj (u i)
  map_add' u v := by
    funext i
    exact map_add pairConj (u i) (v i)
  map_smul' r u := by
    funext i
    exact map_smul pairConj r (u i)

@[simp] theorem realColorJ_sq :
    realColorJ * realColorJ = -(1 : Module.End ℝ RealColorLane) := by
  apply LinearMap.ext
  intro u
  funext i
  change pairJ (pairJ (u i)) = -(u i)
  rcases u i with ⟨x,y⟩
  change pairJ (pairJ (x, y)) = -(x, y)
  simp [pairJ]

@[simp] theorem realColorConj_sq :
    realColorConj * realColorConj = (1 : Module.End ℝ RealColorLane) := by
  apply LinearMap.ext
  intro u
  funext i
  rcases u i with ⟨x,y⟩
  simp [realColorConj, pairConj, Module.End.mul_apply]

/-- `C J = - J C` on the real three-colour carrier. -/
theorem realColorConj_anticomm_J :
    realColorConj * realColorJ = -(realColorJ * realColorConj) := by
  apply LinearMap.ext
  intro u
  funext i
  rcases u i with ⟨x,y⟩
  simp [realColorConj, realColorJ, pairConj, pairJ, Module.End.mul_apply]

/-- Transport the native complex colour action to the real Hestenes carrier. -/
def realColorAction (A : M3C) : Module.End ℝ RealColorLane :=
  colorRealEquiv.toLinearMap.comp
    (((colorAction A).restrictScalars ℝ).comp colorRealEquiv.symm.toLinearMap)

@[simp] theorem realColorAction_readback (A : M3C) (u : RealColorLane) :
    colorRealEquiv.symm (realColorAction A u) =
      colorAction A (colorRealEquiv.symm u) := by
  simp [realColorAction]

/-- Reading the internal real complex structure back gives multiplication by `i`. -/
theorem realColorJ_readback (u : RealColorLane) :
    colorRealEquiv.symm (realColorJ u) =
      fun i => Complex.I * (colorRealEquiv.symm u i) := by
  funext i
  rcases u i with ⟨x,y⟩
  apply Complex.ext <;> simp [colorRealEquiv, complexPairEquiv, realColorJ, pairJ]

/-- The realified colour action commutes with the internal Hestenes complex structure. -/
theorem realColorAction_commutes_J (A : M3C) :
    realColorAction A * realColorJ = realColorJ * realColorAction A := by
  apply LinearMap.ext
  intro u
  apply colorRealEquiv.symm.injective
  rw [Module.End.mul_apply, Module.End.mul_apply]
  rw [realColorAction_readback, realColorJ_readback]
  rw [realColorJ_readback, realColorAction_readback]
  funext i
  simp [colorAction, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc]

/-- Multiplication of complex matrices is represented after realification. -/
theorem realColorAction_mul (A B : M3C) :
    realColorAction (A * B) = realColorAction A * realColorAction B := by
  apply LinearMap.ext
  intro u
  apply colorRealEquiv.symm.injective
  rw [realColorAction_readback, Module.End.mul_apply,
      realColorAction_readback, realColorAction_readback]
  have h := LinearMap.congr_fun (colorAction_mul A B) (colorRealEquiv.symm u)
  simpa [Module.End.mul_apply] using h

/-- The realified representation preserves matrix commutators. -/
theorem realColorAction_commutator (A B : M3C) :
    realColorAction (A * B - B * A) =
      realColorAction A * realColorAction B -
        realColorAction B * realColorAction A := by
  apply LinearMap.ext
  intro u
  apply colorRealEquiv.symm.injective
  have h := LinearMap.congr_fun (colorAction_commutator A B) (colorRealEquiv.symm u)
  simpa [realColorAction, Module.End.mul_apply] using h

/-- Faithfulness survives realification. -/
theorem realColorAction_injective : Function.Injective realColorAction := by
  intro A B hAB
  apply colorAction_injective
  apply LinearMap.ext
  intro u
  have hreal := LinearMap.congr_fun hAB (colorRealEquiv u)
  have hcomplex := congrArg colorRealEquiv.symm hreal
  simpa [realColorAction] using hcomplex

/-- The complete real-colour carrier packet: internal complex structure,
conjugation, faithful action, and its commutator transport. -/
theorem hestenes_real_color_packet :
    realColorJ * realColorJ = -(1 : Module.End ℝ RealColorLane) ∧
    realColorConj * realColorConj = (1 : Module.End ℝ RealColorLane) ∧
    realColorConj * realColorJ = -(realColorJ * realColorConj) ∧
    Function.Injective realColorAction ∧
    (∀ A : M3C, realColorAction A * realColorJ = realColorJ * realColorAction A) ∧
    (∀ A B : M3C,
      realColorAction (A * B - B * A) =
        realColorAction A * realColorAction B -
          realColorAction B * realColorAction A) := by
  exact ⟨realColorJ_sq, realColorConj_sq, realColorConj_anticomm_J,
    realColorAction_injective, realColorAction_commutes_J,
    realColorAction_commutator⟩

end InfoGeometry.Physics.QCDHestenesRealColorRepresentation

end noncomputable section
