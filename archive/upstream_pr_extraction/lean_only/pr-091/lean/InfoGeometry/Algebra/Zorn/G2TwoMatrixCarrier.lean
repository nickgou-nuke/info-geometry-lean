import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2TwoCartanMixingGenerator

namespace InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2Unipotent
open InfoGeometry.Algebra.Zorn.G2TwoCartanMixingGenerator

abbrev F2 := ZMod 2

def bitToF2 (b : Bool) : F2 := if b then 1 else 0

def f2ToBit (z : F2) : Bool := z = 1

@[simp] theorem f2ToBit_bitToF2 (b : Bool) :
    f2ToBit (bitToF2 b) = b := by
  cases b <;> simp [f2ToBit, bitToF2]

theorem bitToF2_f2ToBit (z : F2) :
    bitToF2 (f2ToBit z) = z := by
  fin_cases z <;> simp [f2ToBit, bitToF2]

def carrierToVec (X : SplitOctF2) : Fin 8 → F2 :=
  fun i => bitToF2 ((splitOctF2EquivBits X) i)

def vecToCarrier (v : Fin 8 → F2) : SplitOctF2 :=
  splitOctF2EquivBits.symm (fun i => f2ToBit (v i))

theorem vecToCarrier_carrierToVec (X : SplitOctF2) :
    vecToCarrier (carrierToVec X) = X := by
  apply splitOctF2EquivBits.injective
  funext i
  simp [vecToCarrier, carrierToVec, f2ToBit_bitToF2]

theorem carrierToVec_vecToCarrier (v : Fin 8 → F2) :
    carrierToVec (vecToCarrier v) = v := by
  funext i
  simp [carrierToVec, vecToCarrier, bitToF2_f2ToBit]

def carrierVecEquiv : SplitOctF2 ≃ (Fin 8 → F2) where
  toFun := carrierToVec
  invFun := vecToCarrier
  left_inv := vecToCarrier_carrierToVec
  right_inv := carrierToVec_vecToCarrier

def matrixAction (M : Matrix (Fin 8) (Fin 8) F2) :
    SplitOctF2 → SplitOctF2 :=
  fun X => vecToCarrier (M.mulVec (carrierToVec X))

lemma bitToF2_add (a b : Bool) :
    bitToF2 a + bitToF2 b = bitToF2 (a ^^ b) := by
  cases a <;> cases b <;> rfl

theorem matrixAction_mul (M N : Matrix (Fin 8) (Fin 8) F2) (X : SplitOctF2) :
    matrixAction (M * N) X = matrixAction M (matrixAction N X) := by
  simp only [matrixAction, carrierToVec_vecToCarrier]
  rw [Matrix.mulVec_mulVec]

theorem matrixAction_one (X : SplitOctF2) :
    matrixAction (1 : Matrix (Fin 8) (Fin 8) F2) X = X := by
  rw [matrixAction]
  simp [vecToCarrier_carrierToVec]

theorem carrierToVec_add (X Y : SplitOctF2) :
    carrierToVec (add X Y) = carrierToVec X + carrierToVec Y := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  funext i
  fin_cases i <;>
    simp [carrierToVec, splitOctF2EquivBits, splitOctF2ToBits,
      add, add2, bitToF2_add]

theorem matrixAction_add (M : Matrix (Fin 8) (Fin 8) F2)
    (X Y : SplitOctF2) :
    matrixAction M (add X Y) =
      add (matrixAction M X) (matrixAction M Y) := by
  apply carrierVecEquiv.injective
  change carrierToVec (vecToCarrier (M.mulVec (carrierToVec (add X Y)))) =
    carrierToVec (add (matrixAction M X) (matrixAction M Y))
  rw [carrierToVec_vecToCarrier, carrierToVec_add]
  rw [Matrix.mulVec_add]
  simp only [matrixAction]
  rw [carrierToVec_add, carrierToVec_vecToCarrier,
    carrierToVec_vecToCarrier]

theorem matrixAction_zero (M : Matrix (Fin 8) (Fin 8) F2) :
    matrixAction M zero = zero := by
  have h := matrixAction_add M zero zero
  rw [add_self, add_self] at h
  exact h

lemma matrixAction_ite_zero (M : Matrix (Fin 8) (Fin 8) F2)
    (p : Bool) (E : SplitOctF2) :
    matrixAction M (if p then E else zero) =
      if p then matrixAction M E else zero := by
  cases p <;> simp [matrixAction_zero]

def autMatrix (f : SplitOctF2Aut) : Matrix (Fin 8) (Fin 8) F2 :=
  fun i j => carrierToVec (f.1 (basis8 j)) i

theorem autMatrix_entry (f : SplitOctF2Aut) (i j : Fin 8) :
    autMatrix f i j = carrierToVec (f.1 (basis8 j)) i := by
  rfl

theorem autMatrix_entry_x0 (f : SplitOctF2Aut) (j : Fin 8) :
    autMatrix f 2 j = bitToF2 ((f.1 (basis8 j)).x0) := by
  rfl

theorem autMatrix_entry_x1 (f : SplitOctF2Aut) (j : Fin 8) :
    autMatrix f 3 j = bitToF2 ((f.1 (basis8 j)).x1) := by
  rfl

theorem autMatrix_entry_x2 (f : SplitOctF2Aut) (j : Fin 8) :
    autMatrix f 4 j = bitToF2 ((f.1 (basis8 j)).x2) := by
  rfl

theorem autMatrix_entry_y1 (f : SplitOctF2Aut) (j : Fin 8) :
    autMatrix f 6 j = bitToF2 ((f.1 (basis8 j)).y1) := by
  rfl

theorem carrierToVec_basis8 (j : Fin 8) :
    carrierToVec (basis8 j) = fun i => if i = j then 1 else 0 := by
  fin_cases j <;> funext i <;> fin_cases i <;> rfl

theorem autMatrix_mulVec_basis (f : SplitOctF2Aut) (j : Fin 8) :
    (autMatrix f).mulVec (carrierToVec (basis8 j)) =
      carrierToVec (f.1 (basis8 j)) := by
  rw [carrierToVec_basis8]
  funext i
  simp [autMatrix, Matrix.mulVec, dotProduct]

theorem autMatrix_action_basis (f : SplitOctF2Aut) (j : Fin 8) :
    matrixAction (autMatrix f) (basis8 j) = f.1 (basis8 j) := by
  change vecToCarrier ((autMatrix f).mulVec (carrierToVec (basis8 j))) =
    f.1 (basis8 j)
  rw [autMatrix_mulVec_basis, vecToCarrier_carrierToVec]

theorem autMatrix_action (f : SplitOctF2Aut) (X : SplitOctF2) :
    matrixAction (autMatrix f) X = f.1 X := by
  rw [← basisExpansion_eq X, map_basisExpansion]
  dsimp [basisExpansion]
  simp only [matrixAction_add, matrixAction_ite_zero]
  have h0 := autMatrix_action_basis f 0
  have h1 := autMatrix_action_basis f 1
  have h2 := autMatrix_action_basis f 2
  have h3 := autMatrix_action_basis f 3
  have h4 := autMatrix_action_basis f 4
  have h5 := autMatrix_action_basis f 5
  have h6 := autMatrix_action_basis f 6
  have h7 := autMatrix_action_basis f 7
  dsimp [basis8] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

theorem autMatrix_vec_action (f : SplitOctF2Aut) (v : Fin 8 → F2) :
    vecToCarrier ((autMatrix f).mulVec v) =
      f.1 (vecToCarrier v) := by
  have h := autMatrix_action f (vecToCarrier v)
  simpa [matrixAction, carrierToVec_vecToCarrier] using h

/-- THEOREM: The matrix representation map `autMatrix : SplitOctF2Aut → Matrix (Fin 8) (Fin 8) F2`
is strictly injective. -/
theorem autMatrix_injective : Function.Injective autMatrix := by
  intro f g h
  apply Subtype.ext
  apply Equiv.ext
  intro X
  have hf : f.1 X = matrixAction (autMatrix f) X := (autMatrix_action f X).symm
  have hg : g.1 X = matrixAction (autMatrix g) X := (autMatrix_action g X).symm
  rw [hf, hg, h]

theorem autMatrix_bijective (f : SplitOctF2Aut) :
    Function.Bijective (autMatrix f).mulVec := by
  constructor
  · intro v w h
    have hv := autMatrix_vec_action f v
    have hw := autMatrix_vec_action f w
    have hc : f.1 (vecToCarrier v) = f.1 (vecToCarrier w) := by
      rw [← hv, ← hw, h]
    have hc' := f.1.injective hc
    have hvw := congrArg carrierToVec hc'
    rw [carrierToVec_vecToCarrier, carrierToVec_vecToCarrier] at hvw
    exact hvw
  · intro v
    let y : SplitOctF2 := f.1.symm (vecToCarrier v)
    refine ⟨carrierToVec y, ?_⟩
    have hvec := autMatrix_vec_action f (carrierToVec y)
    have hvec' : vecToCarrier ((autMatrix f).mulVec (carrierToVec y)) =
        f.1 y := by
      simpa only [vecToCarrier_carrierToVec] using hvec
    have hy : f.1 y = vecToCarrier v := by
      dsimp [y]
      rw [f.1.apply_symm_apply]
    have hcar : vecToCarrier ((autMatrix f).mulVec (carrierToVec y)) =
        vecToCarrier v := hvec'.trans hy
    have hv := congrArg carrierToVec hcar
    rw [carrierToVec_vecToCarrier, carrierToVec_vecToCarrier] at hv
    exact hv

noncomputable def matrixTransportEquiv (M : Matrix (Fin 8) (Fin 8) F2)
    (hM : Function.Bijective M.mulVec) : SplitOctF2 ≃ SplitOctF2 :=
  carrierVecEquiv.trans ((Equiv.ofBijective M.mulVec hM).trans carrierVecEquiv.symm)

@[simp] theorem matrixTransportEquiv_apply
    (M : Matrix (Fin 8) (Fin 8) F2) (hM : Function.Bijective M.mulVec)
    (X : SplitOctF2) :
    (matrixTransportEquiv M hM) X = matrixAction M X := rfl

noncomputable def matrixTransportAut (M : Matrix (Fin 8) (Fin 8) F2)
    (hM : Function.Bijective M.mulVec)
    (h1 : matrixAction M one = one)
    (hadd : ∀ X Y, matrixAction M (add X Y) =
      add (matrixAction M X) (matrixAction M Y))
    (hmul : ∀ X Y, matrixAction M (mul X Y) =
      mul (matrixAction M X) (matrixAction M Y)) : SplitOctF2Aut :=
  ⟨matrixTransportEquiv M hM, h1, hadd, hmul⟩

@[simp] theorem matrixTransportAut_apply
    (M : Matrix (Fin 8) (Fin 8) F2) (hM : Function.Bijective M.mulVec)
    (h1 : matrixAction M one = one)
    (hadd : ∀ X Y, matrixAction M (add X Y) =
      add (matrixAction M X) (matrixAction M Y))
    (hmul : ∀ X Y, matrixAction M (mul X Y) =
      mul (matrixAction M X) (matrixAction M Y))
    (X : SplitOctF2) :
    (matrixTransportAut M hM h1 hadd hmul).1 X = matrixAction M X := by
  rfl

noncomputable def autMatrixAut (f : SplitOctF2Aut) : SplitOctF2Aut :=
  matrixTransportAut (autMatrix f) (autMatrix_bijective f)
    (by rw [autMatrix_action]; exact f.2.1)
    (by
      intro X Y
      rw [autMatrix_action, autMatrix_action, autMatrix_action]
      exact f.2.2.1 X Y)
    (by
      intro X Y
      rw [autMatrix_action, autMatrix_action, autMatrix_action]
      exact f.2.2.2 X Y)

theorem autMatrixAut_eq (f : SplitOctF2Aut) :
    autMatrixAut f = f := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  change (matrixTransportAut (autMatrix f) (autMatrix_bijective f)
      _ _ _).1 X = f.1 X
  rw [matrixTransportAut_apply, autMatrix_action]

theorem autMatrix_mul (f g : SplitOctF2Aut) :
    autMatrix (f * g) = autMatrix g * autMatrix f := by
  apply Matrix.mulVec_injective
  funext v
  apply carrierVecEquiv.symm.injective
  calc
    vecToCarrier ((autMatrix (f * g)).mulVec v) =
        (f * g).1 (vecToCarrier v) := autMatrix_vec_action (f * g) v
    _ = g.1 (f.1 (vecToCarrier v)) := rfl
    _ = g.1 (vecToCarrier ((autMatrix f).mulVec v)) := by
      rw [autMatrix_vec_action]
    _ = vecToCarrier ((autMatrix g).mulVec ((autMatrix f).mulVec v)) :=
      (autMatrix_vec_action g ((autMatrix f).mulVec v)).symm
    _ = vecToCarrier ((autMatrix g * autMatrix f).mulVec v) := by
      rw [Matrix.mulVec_mulVec]

theorem autMatrix_one :
    autMatrix (1 : SplitOctF2Aut) =
      (1 : Matrix (Fin 8) (Fin 8) F2) := by
  apply Matrix.mulVec_injective
  funext v
  apply carrierVecEquiv.symm.injective
  calc
    vecToCarrier ((autMatrix (1 : SplitOctF2Aut)).mulVec v) =
        (1 : SplitOctF2Aut).1 (vecToCarrier v) :=
      autMatrix_vec_action (1 : SplitOctF2Aut) v
    _ = vecToCarrier v := rfl
    _ = vecToCarrier ((1 : Matrix (Fin 8) (Fin 8) F2).mulVec v) := by
      simp

theorem matrix_eq_of_action_eq
    {M N : Matrix (Fin 8) (Fin 8) F2}
    (h : ∀ X : SplitOctF2, matrixAction M X = matrixAction N X) :
    M = N := by
  apply Matrix.mulVec_injective
  funext v
  let X : SplitOctF2 := vecToCarrier v
  have hx := h X
  apply congrArg carrierToVec at hx
  simpa [matrixAction, X, carrierToVec_vecToCarrier] using hx

theorem cartanMixingAut_matrix_transport
    (h : admissibleBasis7 mixingBasis) :
    autMatrixAut (cartanMixingAut h) = cartanMixingAut h := by
  exact autMatrixAut_eq (cartanMixingAut h)

/-! The Cartan involution has a permutation matrix in the carrier coordinates. -/

def swapCartanIndex : Fin 8 → Fin 8 := ![1, 0, 5, 6, 7, 2, 3, 4]

def swapCartanMatrix : Matrix (Fin 8) (Fin 8) F2 :=
  fun i j => if j = swapCartanIndex i then 1 else 0

theorem swapCartanMatrix_mulVec (v : Fin 8 → F2) (i : Fin 8) :
    swapCartanMatrix.mulVec v i = v (swapCartanIndex i) := by
  simp [swapCartanMatrix, Matrix.mulVec, dotProduct]

theorem swapCartanMatrix_action (X : SplitOctF2) :
    matrixAction swapCartanMatrix X = swapCartanFun X := by
  apply splitOctF2EquivBits.injective
  funext i
  rw [matrixAction]
  simp only [carrierToVec, vecToCarrier, swapCartanMatrix_mulVec]
  fin_cases i <;>
    simp [swapCartanIndex, splitOctF2EquivBits, splitOctF2ToBits,
      splitOctF2OfBits, bitToF2, f2ToBit, swapCartanFun]

theorem swapCartanIndex_involutive (i : Fin 8) :
    swapCartanIndex (swapCartanIndex i) = i := by
  fin_cases i <;> rfl

theorem swapCartanMatrix_mulVec_involutive (v : Fin 8 → F2) :
    swapCartanMatrix.mulVec (swapCartanMatrix.mulVec v) = v := by
  funext i
  rw [swapCartanMatrix_mulVec, swapCartanMatrix_mulVec,
    swapCartanIndex_involutive]

theorem swapCartanMatrix_bijective :
    Function.Bijective swapCartanMatrix.mulVec := by
  constructor
  · intro v w h
    calc
      v = swapCartanMatrix.mulVec (swapCartanMatrix.mulVec v) :=
        (swapCartanMatrix_mulVec_involutive v).symm
      _ = swapCartanMatrix.mulVec (swapCartanMatrix.mulVec w) :=
        congrArg swapCartanMatrix.mulVec h
      _ = w := swapCartanMatrix_mulVec_involutive w
  · intro v
    exact ⟨swapCartanMatrix.mulVec v, swapCartanMatrix_mulVec_involutive v⟩

theorem swapCartanMatrix_unit :
    matrixAction swapCartanMatrix one = one := by
  rw [swapCartanMatrix_action]
  rfl

theorem swapCartanMatrix_add (X Y : SplitOctF2) :
    matrixAction swapCartanMatrix (add X Y) =
      add (matrixAction swapCartanMatrix X) (matrixAction swapCartanMatrix Y) := by
  rw [swapCartanMatrix_action, swapCartanMatrix_action, swapCartanMatrix_action]
  exact swapCartanAut.2.2.1 X Y

theorem swapCartanMatrix_mul (X Y : SplitOctF2) :
    matrixAction swapCartanMatrix (mul X Y) =
      mul (matrixAction swapCartanMatrix X) (matrixAction swapCartanMatrix Y) := by
  rw [swapCartanMatrix_action, swapCartanMatrix_action, swapCartanMatrix_action]
  exact swapCartanAut.2.2.2 X Y

noncomputable def swapCartanMatrixAut : SplitOctF2Aut :=
  matrixTransportAut swapCartanMatrix swapCartanMatrix_bijective
    swapCartanMatrix_unit swapCartanMatrix_add swapCartanMatrix_mul

theorem swapCartanMatrixAut_eq_native :
    swapCartanMatrixAut = swapCartanAut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  change (matrixTransportAut swapCartanMatrix swapCartanMatrix_bijective
      swapCartanMatrix_unit swapCartanMatrix_add swapCartanMatrix_mul).1 X =
    swapCartanAut.1 X
  rw [matrixTransportAut_apply, swapCartanMatrix_action]
  rfl

/-! The native long simple-root shear as an explicit matrix. -/

def longRootMatrix : Matrix (Fin 8) (Fin 8) F2 := ![
  ![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,1,0,0,0,0,0], ![0,0,0,1,1,0,0,0],
  ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,1,0,0],
  ![0,0,0,0,0,0,1,0], ![0,0,0,0,0,0,1,1]]

@[simp] lemma f2ToBit_bitToF2_add (a b : Bool) :
    f2ToBit (bitToF2 a + bitToF2 b) = (a ^^ b) := by
  cases a <;> cases b <;> rfl

@[simp] lemma f2_add_self (z : F2) : z + z = 0 := by
  fin_cases z <;> rfl

theorem longRootMatrix_mulVec (v : Fin 8 → F2) :
    longRootMatrix.mulVec v =
      ![v 0, v 1, v 2, v 3 + v 4, v 4, v 5, v 6, v 6 + v 7] := by
  funext i
  fin_cases i <;>
    simp [longRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem longRootMatrix_action (X : SplitOctF2) :
    matrixAction longRootMatrix X = unipotentLong true X := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  apply splitOctF2EquivBits.injective
  funext i
  rw [matrixAction]
  simp only [carrierToVec, vecToCarrier, longRootMatrix_mulVec]
  fin_cases i <;>
    simp [splitOctF2EquivBits, splitOctF2ToBits, splitOctF2OfBits,
      bitToF2, f2ToBit, unipotentLong, add2] <;>
    cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> rfl


theorem longRootMatrix_mulVec_involutive (v : Fin 8 → F2) :
    longRootMatrix.mulVec (longRootMatrix.mulVec v) = v := by
  rw [longRootMatrix_mulVec]
  funext i
  fin_cases i <;> simp [longRootMatrix_mulVec]
  · rw [_root_.add_assoc, f2_add_self, _root_.add_zero]
  · rw [← _root_.add_assoc, f2_add_self, _root_.zero_add]

theorem longRootMatrix_bijective :
    Function.Bijective longRootMatrix.mulVec := by
  constructor
  · intro v w h
    calc
      v = longRootMatrix.mulVec (longRootMatrix.mulVec v) :=
        (longRootMatrix_mulVec_involutive v).symm
      _ = longRootMatrix.mulVec (longRootMatrix.mulVec w) :=
        congrArg longRootMatrix.mulVec h
      _ = w := longRootMatrix_mulVec_involutive w
  · intro v
    exact ⟨longRootMatrix.mulVec v, longRootMatrix_mulVec_involutive v⟩

theorem longRootMatrix_unit :
    matrixAction longRootMatrix one = one := by
  rw [longRootMatrix_action]
  rfl

theorem longRootMatrix_add (X Y : SplitOctF2) :
    matrixAction longRootMatrix (add X Y) =
      add (matrixAction longRootMatrix X) (matrixAction longRootMatrix Y) := by
  rw [longRootMatrix_action, longRootMatrix_action, longRootMatrix_action]
  exact unipotentLong_add true X Y

theorem longRootMatrix_mul (X Y : SplitOctF2) :
    matrixAction longRootMatrix (mul X Y) =
      mul (matrixAction longRootMatrix X) (matrixAction longRootMatrix Y) := by
  rw [longRootMatrix_action, longRootMatrix_action, longRootMatrix_action]
  exact unipotentLong_mul true X Y

noncomputable def longRootMatrixAut : SplitOctF2Aut :=
  matrixTransportAut longRootMatrix longRootMatrix_bijective
    longRootMatrix_unit longRootMatrix_add longRootMatrix_mul

theorem longRootMatrixAut_eq_native :
    longRootMatrixAut = unipotentLongAut true := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  change (matrixTransportAut longRootMatrix longRootMatrix_bijective
      longRootMatrix_unit longRootMatrix_add longRootMatrix_mul).1 X =
    (unipotentLongAut true).1 X
  rw [matrixTransportAut_apply, longRootMatrix_action,
    unipotentLongAut_apply]

/-! The native short simple-root shear as an explicit matrix. -/

def shortRootMatrix : Matrix (Fin 8) (Fin 8) F2 := ![
  ![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,1,1,0,0,0,0], ![0,0,0,1,0,0,0,0],
  ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,1,0,0],
  ![0,0,0,0,0,1,1,0], ![0,0,0,0,0,0,0,1]]

theorem shortRootMatrix_mulVec (v : Fin 8 → F2) :
    shortRootMatrix.mulVec v =
      ![v 0, v 1, v 2 + v 3, v 3, v 4, v 5, v 5 + v 6, v 7] := by
  funext i
  fin_cases i <;>
    simp [shortRootMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem shortRootMatrix_action (X : SplitOctF2) :
    matrixAction shortRootMatrix X = unipotentShort true X := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  apply splitOctF2EquivBits.injective
  funext i
  rw [matrixAction]
  simp only [carrierToVec, vecToCarrier, shortRootMatrix_mulVec]
  fin_cases i <;>
    simp [splitOctF2EquivBits, splitOctF2ToBits, splitOctF2OfBits,
      bitToF2, f2ToBit, unipotentShort, add2] <;>
    cases x0 <;> cases x1 <;> cases y0 <;> cases y1 <;> rfl

theorem shortRootMatrix_mulVec_involutive (v : Fin 8 → F2) :
    shortRootMatrix.mulVec (shortRootMatrix.mulVec v) = v := by
  rw [shortRootMatrix_mulVec]
  funext i
  fin_cases i <;> simp [shortRootMatrix_mulVec]
  rw [_root_.add_assoc, f2_add_self, _root_.add_zero]
  rw [← _root_.add_assoc, f2_add_self, _root_.zero_add]

theorem shortRootMatrix_bijective :
    Function.Bijective shortRootMatrix.mulVec := by
  constructor
  · intro v w h
    calc
      v = shortRootMatrix.mulVec (shortRootMatrix.mulVec v) :=
        (shortRootMatrix_mulVec_involutive v).symm
      _ = shortRootMatrix.mulVec (shortRootMatrix.mulVec w) :=
        congrArg shortRootMatrix.mulVec h
      _ = w := shortRootMatrix_mulVec_involutive w
  · intro v
    exact ⟨shortRootMatrix.mulVec v, shortRootMatrix_mulVec_involutive v⟩

theorem shortRootMatrix_unit :
    matrixAction shortRootMatrix one = one := by
  rw [shortRootMatrix_action]
  rfl

theorem shortRootMatrix_add (X Y : SplitOctF2) :
    matrixAction shortRootMatrix (add X Y) =
      add (matrixAction shortRootMatrix X) (matrixAction shortRootMatrix Y) := by
  rw [shortRootMatrix_action, shortRootMatrix_action, shortRootMatrix_action]
  exact unipotentShort_add true X Y

theorem shortRootMatrix_mul (X Y : SplitOctF2) :
    matrixAction shortRootMatrix (mul X Y) =
      mul (matrixAction shortRootMatrix X) (matrixAction shortRootMatrix Y) := by
  rw [shortRootMatrix_action, shortRootMatrix_action, shortRootMatrix_action]
  exact unipotentShort_mul true X Y

noncomputable def shortRootMatrixAut : SplitOctF2Aut :=
  matrixTransportAut shortRootMatrix shortRootMatrix_bijective
    shortRootMatrix_unit shortRootMatrix_add shortRootMatrix_mul

theorem shortRootMatrixAut_eq_native :
    shortRootMatrixAut = unipotentShortAut true := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  change (matrixTransportAut shortRootMatrix shortRootMatrix_bijective
      shortRootMatrix_unit shortRootMatrix_add shortRootMatrix_mul).1 X =
    (unipotentShortAut true).1 X
  rw [matrixTransportAut_apply, shortRootMatrix_action,
    unipotentShortAut_apply]

/-! Matrix transport of the first simple-root word. -/

def simpleRootProductMatrix : Matrix (Fin 8) (Fin 8) F2 :=
  longRootMatrix * shortRootMatrix

theorem simpleRootProductMatrix_action (X : SplitOctF2) :
    matrixAction simpleRootProductMatrix X =
      (unipotentShortAut true * unipotentLongAut true).1 X := by
  rw [simpleRootProductMatrix, matrixAction_mul,
    longRootMatrix_action, shortRootMatrix_action]
  rfl

theorem simpleRootProductMatrix_bijective :
    Function.Bijective simpleRootProductMatrix.mulVec := by
  have h := longRootMatrix_bijective.comp shortRootMatrix_bijective
  simpa [simpleRootProductMatrix, Matrix.mulVec_mulVec] using h

theorem simpleRootProductMatrix_unit :
    matrixAction simpleRootProductMatrix one = one := by
  rw [simpleRootProductMatrix_action]
  rfl

theorem simpleRootProductMatrix_add (X Y : SplitOctF2) :
    matrixAction simpleRootProductMatrix (add X Y) =
      add (matrixAction simpleRootProductMatrix X)
        (matrixAction simpleRootProductMatrix Y) := by
  rw [simpleRootProductMatrix_action, simpleRootProductMatrix_action,
    simpleRootProductMatrix_action]
  exact (unipotentShortAut true * unipotentLongAut true).2.2.1 X Y

theorem simpleRootProductMatrix_mul (X Y : SplitOctF2) :
    matrixAction simpleRootProductMatrix (mul X Y) =
      mul (matrixAction simpleRootProductMatrix X)
        (matrixAction simpleRootProductMatrix Y) := by
  rw [simpleRootProductMatrix_action, simpleRootProductMatrix_action,
    simpleRootProductMatrix_action]
  exact (unipotentShortAut true * unipotentLongAut true).2.2.2 X Y

noncomputable def simpleRootProductMatrixAut : SplitOctF2Aut :=
  matrixTransportAut simpleRootProductMatrix simpleRootProductMatrix_bijective
    simpleRootProductMatrix_unit simpleRootProductMatrix_add
    simpleRootProductMatrix_mul

theorem simpleRootProductMatrixAut_eq_native :
    simpleRootProductMatrixAut =
      unipotentShortAut true * unipotentLongAut true := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  change (matrixTransportAut simpleRootProductMatrix
      simpleRootProductMatrix_bijective simpleRootProductMatrix_unit
      simpleRootProductMatrix_add simpleRootProductMatrix_mul).1 X =
    (unipotentShortAut true * unipotentLongAut true).1 X
  rw [matrixTransportAut_apply, simpleRootProductMatrix_action]

theorem simpleRootProductMatrixAut_pow_four :
    simpleRootProductMatrixAut ^ 4 = (1 : SplitOctF2Aut) := by
  rw [simpleRootProductMatrixAut_eq_native]
  exact simpleRootProduct_four

/-! The coordinate permutation representing the native three-cycle. -/

def cycle012Matrix : Matrix (Fin 8) (Fin 8) F2 := ![
  ![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,0,1,0,0,0,0], ![0,0,0,0,1,0,0,0],
  ![0,0,1,0,0,0,0,0], ![0,0,0,0,0,0,1,0],
  ![0,0,0,0,0,0,0,1], ![0,0,0,0,0,1,0,0]]

theorem cycle012Matrix_mulVec (v : Fin 8 → F2) :
    cycle012Matrix.mulVec v =
      ![v 0, v 1, v 3, v 4, v 2, v 6, v 7, v 5] := by
  funext i
  fin_cases i <;>
    simp [cycle012Matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem cycle012Matrix_action (X : SplitOctF2) :
    matrixAction cycle012Matrix X = cycle012Fun X := by
  apply splitOctF2EquivBits.injective
  funext i
  rw [matrixAction]
  simp only [carrierToVec, vecToCarrier, cycle012Matrix_mulVec]
  fin_cases i <;>
    simp [splitOctF2EquivBits, splitOctF2ToBits, splitOctF2OfBits,
      bitToF2, f2ToBit, cycle012Fun]

theorem cycle012Matrix_bijective :
    Function.Bijective cycle012Matrix.mulVec := by
  let inv : (Fin 8 → F2) → Fin 8 → F2 :=
    fun v => ![v 0, v 1, v 4, v 2, v 3, v 7, v 5, v 6]
  have hleft : ∀ v, cycle012Matrix.mulVec (inv v) = v := by
    intro v
    rw [cycle012Matrix_mulVec]
    funext i
    fin_cases i <;> rfl
  have hright : ∀ v, inv (cycle012Matrix.mulVec v) = v := by
    intro v
    rw [cycle012Matrix_mulVec]
    funext i
    fin_cases i <;> rfl
  exact ⟨fun v w h => by
    calc
      v = inv (cycle012Matrix.mulVec v) := (hright v).symm
      _ = inv (cycle012Matrix.mulVec w) := congrArg inv h
      _ = w := hright w,
    fun v => ⟨inv v, hleft v⟩⟩

theorem cycle012Matrix_unit :
    matrixAction cycle012Matrix one = one := by
  rw [cycle012Matrix_action]
  rfl

theorem cycle012Matrix_add (X Y : SplitOctF2) :
    matrixAction cycle012Matrix (add X Y) =
      add (matrixAction cycle012Matrix X) (matrixAction cycle012Matrix Y) := by
  rw [cycle012Matrix_action, cycle012Matrix_action, cycle012Matrix_action]
  exact cycle012_add X Y

theorem cycle012Matrix_mul (X Y : SplitOctF2) :
    matrixAction cycle012Matrix (mul X Y) =
      mul (matrixAction cycle012Matrix X) (matrixAction cycle012Matrix Y) := by
  rw [cycle012Matrix_action, cycle012Matrix_action, cycle012Matrix_action]
  exact cycle012_mul X Y

noncomputable def cycle012MatrixAut : SplitOctF2Aut :=
  matrixTransportAut cycle012Matrix cycle012Matrix_bijective
    cycle012Matrix_unit cycle012Matrix_add cycle012Matrix_mul

theorem cycle012MatrixAut_eq_native :
    cycle012MatrixAut = cycle012Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  change (matrixTransportAut cycle012Matrix cycle012Matrix_bijective
      cycle012Matrix_unit cycle012Matrix_add cycle012Matrix_mul).1 X =
    cycle012Aut.1 X
  rw [matrixTransportAut_apply, cycle012Matrix_action,
    cycle012Aut_apply]

theorem cycle012MatrixAut_cube :
    cycle012MatrixAut ^ 3 = (1 : SplitOctF2Aut) := by
  rw [cycle012MatrixAut_eq_native]
  exact cycle012Aut_cube

/-! The coordinate permutation representing the native transposition. -/

def swap01Matrix : Matrix (Fin 8) (Fin 8) F2 := ![
  ![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,0,1,0,0,0,0], ![0,0,1,0,0,0,0,0],
  ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,0,1,0],
  ![0,0,0,0,0,1,0,0], ![0,0,0,0,0,0,0,1]]

theorem swap01Matrix_mulVec (v : Fin 8 → F2) :
    swap01Matrix.mulVec v =
      ![v 0, v 1, v 3, v 2, v 4, v 6, v 5, v 7] := by
  funext i
  fin_cases i <;>
    simp [swap01Matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem swap01Matrix_action (X : SplitOctF2) :
    matrixAction swap01Matrix X = swap01Fun X := by
  apply splitOctF2EquivBits.injective
  funext i
  rw [matrixAction]
  simp only [carrierToVec, vecToCarrier, swap01Matrix_mulVec]
  fin_cases i <;>
    simp [splitOctF2EquivBits, splitOctF2ToBits, splitOctF2OfBits,
      bitToF2, f2ToBit, swap01Fun]

theorem swap01Matrix_mulVec_involutive (v : Fin 8 → F2) :
    swap01Matrix.mulVec (swap01Matrix.mulVec v) = v := by
  rw [swap01Matrix_mulVec]
  rw [swap01Matrix_mulVec]
  funext i
  fin_cases i <;> rfl

theorem swap01Matrix_bijective :
    Function.Bijective swap01Matrix.mulVec := by
  constructor
  · intro v w h
    calc
      v = swap01Matrix.mulVec (swap01Matrix.mulVec v) :=
        (swap01Matrix_mulVec_involutive v).symm
      _ = swap01Matrix.mulVec (swap01Matrix.mulVec w) :=
        congrArg swap01Matrix.mulVec h
      _ = w := swap01Matrix_mulVec_involutive w
  · intro v
    exact ⟨swap01Matrix.mulVec v, swap01Matrix_mulVec_involutive v⟩

theorem swap01Matrix_unit :
    matrixAction swap01Matrix one = one := by
  rw [swap01Matrix_action]
  rfl

theorem swap01Matrix_add (X Y : SplitOctF2) :
    matrixAction swap01Matrix (add X Y) =
      add (matrixAction swap01Matrix X) (matrixAction swap01Matrix Y) := by
  rw [swap01Matrix_action, swap01Matrix_action, swap01Matrix_action]
  exact swap01_add X Y

theorem swap01Matrix_mul (X Y : SplitOctF2) :
    matrixAction swap01Matrix (mul X Y) =
      mul (matrixAction swap01Matrix X) (matrixAction swap01Matrix Y) := by
  rw [swap01Matrix_action, swap01Matrix_action, swap01Matrix_action]
  exact swap01_mul X Y

noncomputable def swap01MatrixAut : SplitOctF2Aut :=
  matrixTransportAut swap01Matrix swap01Matrix_bijective
    swap01Matrix_unit swap01Matrix_add swap01Matrix_mul

theorem swap01MatrixAut_eq_native :
    swap01MatrixAut = swap01Aut := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  change (matrixTransportAut swap01Matrix swap01Matrix_bijective
      swap01Matrix_unit swap01Matrix_add swap01Matrix_mul).1 X =
    swap01Aut.1 X
  rw [matrixTransportAut_apply, swap01Matrix_action,
    swap01Aut_apply]

theorem swap01MatrixAut_sq :
    swap01MatrixAut * swap01MatrixAut = (1 : SplitOctF2Aut) := by
  rw [swap01MatrixAut_eq_native]
  exact swap01Aut_sq

theorem swap01Matrix_cycle012Matrix_conjugate :
    swap01MatrixAut * cycle012MatrixAut * swap01MatrixAut =
      cycle012MatrixAut * cycle012MatrixAut := by
  rw [swap01MatrixAut_eq_native, cycle012MatrixAut_eq_native]
  exact swap01_cycle012_conjugate

theorem swapCartanMatrix_cycle012Matrix_comm :
    swapCartanMatrixAut * cycle012MatrixAut =
      cycle012MatrixAut * swapCartanMatrixAut := by
  rw [swapCartanMatrixAut_eq_native, cycle012MatrixAut_eq_native]
  exact swapCartanAut_comm_cycle012

theorem swapCartanMatrix_swap01Matrix_comm :
    swapCartanMatrixAut * swap01MatrixAut =
      swap01MatrixAut * swapCartanMatrixAut := by
  rw [swapCartanMatrixAut_eq_native, swap01MatrixAut_eq_native]
  exact swapCartanAut_comm_swap01

theorem autMatrix_longRootMatrix :
    autMatrix (unipotentLongAut true) = longRootMatrix := by
  apply matrix_eq_of_action_eq
  intro X
  rw [autMatrix_action, longRootMatrix_action,
    unipotentLongAut_apply]

theorem autMatrix_shortRootMatrix :
    autMatrix (unipotentShortAut true) = shortRootMatrix := by
  apply matrix_eq_of_action_eq
  intro X
  rw [autMatrix_action, shortRootMatrix_action,
    unipotentShortAut_apply]

theorem autMatrix_cycle012Matrix :
    autMatrix cycle012Aut = cycle012Matrix := by
  apply matrix_eq_of_action_eq
  intro X
  rw [autMatrix_action, cycle012Matrix_action, cycle012Aut_apply]

theorem autMatrix_swap01Matrix :
    autMatrix swap01Aut = swap01Matrix := by
  apply matrix_eq_of_action_eq
  intro X
  rw [autMatrix_action, swap01Matrix_action, swap01Aut_apply]

theorem autMatrix_swapCartanMatrix :
    autMatrix swapCartanAut = swapCartanMatrix := by
  apply matrix_eq_of_action_eq
  intro X
  rw [autMatrix_action, swapCartanMatrix_action]
  rfl

end InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
