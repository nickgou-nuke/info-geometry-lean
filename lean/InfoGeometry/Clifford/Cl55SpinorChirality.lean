import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Clifford.ClNNBilinear
import InfoGeometry.Arithmetic.SplitCliffordRealization
import InfoGeometry.Clifford.ConformalGeneratorLemmas55
import InfoGeometry.Canonical.Herm2x2OsO55RationalBridge
import Mathlib.GroupTheory.Perm.Sign

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinorChirality

open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.GammaMatrices
open InfoGeometry.Algebra.CPT
open InfoGeometry.Arithmetic.SplitCliffordRealization
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ClNNBilinear
open InfoGeometry.Canonical.Herm2x2OsO55RationalBridge

noncomputable def q55Real (v : Fin 10 → ℝ) : ℝ :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 4 ^ 2 -
    (v 5 ^ 2 + v 6 ^ 2 + v 7 ^ 2 + v 8 ^ 2 + v 9 ^ 2)

noncomputable def vec55SplitEquiv :
    (Fin 10 → ℝ) ≃ₗ[ℝ] InfoGeometry.CliffordTower.SplitSpace 5 :=
  { toFun := fun v =>
      ((v 0, v 5),
        ((v 1, v 6),
          ((v 2, v 7),
            ((v 3, v 8),
            ((v 4, v 9), (0 : InfoGeometry.CliffordTower.SplitSpace 0))))))
    invFun := fun x =>
      ![x.1.1, x.2.1.1, x.2.2.1.1, x.2.2.2.1.1, x.2.2.2.2.1.1,
        x.1.2, x.2.1.2, x.2.2.1.2, x.2.2.2.1.2, x.2.2.2.2.1.2]
    left_inv := by
      intro v
      funext i
      fin_cases i <;> rfl
    right_inv := by
      intro x
      rcases x with ⟨x0, x1, x2, x3, ⟨x4, x5⟩⟩
      have hx5 : x5 = 0 := Subsingleton.elim _ _
      subst x5
      rfl
    map_add' := by
      intro v w
      simp [Pi.add_apply]
    map_smul' := by
      intro c v
      simp [Pi.smul_apply] }

theorem splitQ_vec55SplitEquiv (v : Fin 10 → ℝ) :
    Qsplit 5 (vec55SplitEquiv v) = q55Real v := by
  simp [vec55SplitEquiv, Qsplit, q55Real, CliffordTower.Q11_apply]
  ring

def castVec55 (v : Fin 10 → ℚ) : Fin 10 → ℝ :=
  fun i => (v i : ℝ)

theorem q55Real_castVec55 (v : Fin 10 → ℚ) :
    q55Real (castVec55 v) =
      (InfoGeometry.Physics.Pin55Formal.q55 v : ℝ) := by
  simp [q55Real, castVec55, InfoGeometry.Physics.Pin55Formal.q55,
    QuadraticMap.proj]
  ring

noncomputable def gamma55 (v : Fin 10 → ℝ) : SpinorMatrix 5 :=
  recursiveGamma 5 (vec55SplitEquiv v)

theorem gamma55_sq (v : Fin 10 → ℝ) :
    gamma55 v * gamma55 v =
      algebraMap ℝ (SpinorMatrix 5) (q55Real v) := by
  rw [gamma55, recursiveGamma_sq, splitQ_vec55SplitEquiv]

theorem gamma55_anticomm (v w : Fin 10 → ℝ) :
    gamma55 v * gamma55 w + gamma55 w * gamma55 v =
      algebraMap ℝ (SpinorMatrix 5)
        (QuadraticMap.polar (SplitQuad 5)
          (vec55SplitEquiv v) (vec55SplitEquiv w)) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := SplitQuad 5) (vec55SplitEquiv v) (vec55SplitEquiv w)
  have hm := congrArg (spinorRepresentation 5) h
  rw [map_add, map_mul, map_mul] at hm
  rw [(spinorRepresentation 5).commutes] at hm
  rw [spinorRepresentation_ι] at hm
  rw [spinorRepresentation_ι] at hm
  simpa [gamma55] using hm

noncomputable def hermitianGamma
    (X : Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ) : SpinorMatrix 5 :=
  gamma55 (castVec55 (toVec55Q X))

theorem hermitianGamma_sq
    (X : Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ) :
    hermitianGamma X * hermitianGamma X =
      algebraMap ℝ (SpinorMatrix 5) (X.det : ℝ) := by
  rw [hermitianGamma, gamma55_sq, q55Real_castVec55]
  have hdet := congrArg (fun z : ℚ => (z : ℝ))
    (det_eq_q55_toVec55Q X)
  exact congrArg (algebraMap ℝ (SpinorMatrix 5)) hdet.symm

def vec55Basis (i : Fin 10) : Fin 10 → ℝ :=
  Pi.single i 1

noncomputable def gammaBasis55 (i : Fin 10) : SpinorMatrix 5 :=
  gamma55 (vec55Basis i)

/-! The split gamma generators are the recursive Wigner-Jordan tensor products
of the local `Cl(1,1)` atoms. -/
theorem gammaBasis55_eq_recursiveGammaTensor (i : Fin 10) :
    gammaBasis55 i =
      (tensorMatrixEquivFinPowTwo 5)
        (recursiveGammaTensor 5 (vec55SplitEquiv (vec55Basis i))) := by
  rfl

theorem vec55SplitEquiv_basis0 :
    vec55SplitEquiv (vec55Basis 0) = headPair 4 ((1 : ℝ), 0) := by
  simp [vec55SplitEquiv, vec55Basis, headPair]

theorem vec55SplitEquiv_basis5 :
    vec55SplitEquiv (vec55Basis 5) = headPair 4 ((0 : ℝ), 1) := by
  simp [vec55SplitEquiv, vec55Basis, headPair]

theorem vec55SplitEquiv_basis1 :
    vec55SplitEquiv (vec55Basis 1) =
      tailLift 4 (headPair 3 ((1 : ℝ), 0)) := by
  simp [vec55SplitEquiv, vec55Basis, tailLift, headPair]

theorem vec55SplitEquiv_basis6 :
    vec55SplitEquiv (vec55Basis 6) =
      tailLift 4 (headPair 3 ((0 : ℝ), 1)) := by
  simp [vec55SplitEquiv, vec55Basis, tailLift, headPair]

theorem gammaBasis55_pair05 :
    recursiveGammaTensor 5 (vec55SplitEquiv (vec55Basis 0)) *
        recursiveGammaTensor 5 (vec55SplitEquiv (vec55Basis 5)) =
      appendAtom 1 gradingAtom := by
  rw [vec55SplitEquiv_basis0, vec55SplitEquiv_basis5]
  rw [recursiveGammaTensor_headPair, recursiveGammaTensor_headPair]
  rw [appendAtom_mul]
  simpa [gradingAtom, InfoGeometry.Clifford.GammaMatrices.gamma12_eq]

theorem recursiveGammaTensor_basis1 :
    recursiveGammaTensor 5 (vec55SplitEquiv (vec55Basis 1)) =
      appendAtom (appendAtom 1 gammaPlusAtom) gradingAtom := by
  rw [vec55SplitEquiv_basis1]
  rw [recursiveGammaTensor_tailLift, recursiveGammaTensor_headPair]
  simp [gammaPlusAtom, gammaMinusAtom, gradingAtom,
    InfoGeometry.Clifford.GammaMatrices.gamma12_eq]

theorem recursiveGammaTensor_basis6 :
    recursiveGammaTensor 5 (vec55SplitEquiv (vec55Basis 6)) =
      appendAtom (appendAtom 1 gammaMinusAtom) gradingAtom := by
  rw [vec55SplitEquiv_basis6]
  rw [recursiveGammaTensor_tailLift, recursiveGammaTensor_headPair]
  simp [gammaPlusAtom, gammaMinusAtom, gradingAtom,
    InfoGeometry.Clifford.GammaMatrices.gamma12_eq]

theorem gammaBasis55_pair16 :
    recursiveGammaTensor 5 (vec55SplitEquiv (vec55Basis 1)) *
        recursiveGammaTensor 5 (vec55SplitEquiv (vec55Basis 6)) =
      appendAtom (appendAtom 1 gradingAtom) 1 := by
  rw [recursiveGammaTensor_basis1, recursiveGammaTensor_basis6]
  rw [appendAtom_mul, gradingAtom_sq]
  rw [appendAtom_mul]
  simp [gradingAtom, InfoGeometry.Clifford.GammaMatrices.gamma12_eq]

theorem vec55SplitEquiv_basis2 :
    vec55SplitEquiv (vec55Basis 2) =
      tailLift 4 (tailLift 3 (headPair 2 ((1 : ℝ), 0))) := by
  simp [vec55SplitEquiv, vec55Basis, tailLift, headPair]

theorem vec55SplitEquiv_basis7 :
    vec55SplitEquiv (vec55Basis 7) =
      tailLift 4 (tailLift 3 (headPair 2 ((0 : ℝ), 1))) := by
  simp [vec55SplitEquiv, vec55Basis, tailLift, headPair]

theorem vec55SplitEquiv_basis3 :
    vec55SplitEquiv (vec55Basis 3) =
      tailLift 4 (tailLift 3 (tailLift 2 (headPair 1 ((1 : ℝ), 0)))) := by
  simp [vec55SplitEquiv, vec55Basis, tailLift, headPair]

theorem vec55SplitEquiv_basis8 :
    vec55SplitEquiv (vec55Basis 8) =
      tailLift 4 (tailLift 3 (tailLift 2 (headPair 1 ((0 : ℝ), 1)))) := by
  simp [vec55SplitEquiv, vec55Basis, tailLift, headPair]

theorem vec55SplitEquiv_basis4 :
    vec55SplitEquiv (vec55Basis 4) =
      tailLift 4 (tailLift 3 (tailLift 2 (tailLift 1 (headPair 0 ((1 : ℝ), 0))))) := by
  simp [vec55SplitEquiv, vec55Basis, tailLift, headPair]

theorem vec55SplitEquiv_basis9 :
    vec55SplitEquiv (vec55Basis 9) =
      tailLift 4 (tailLift 3 (tailLift 2 (tailLift 1 (headPair 0 ((0 : ℝ), 1))))) := by
  simp [vec55SplitEquiv, vec55Basis, tailLift, headPair]

/-- The recursive `Cl(1,1)` pairing order is an even permutation of the
ordered basis `0,1,2,3,4,5,6,7,8,9`.

This is the finite combinatorial orientation datum behind the ordered-volume
comparison with `chiralityMatrix`. -/
def split55RecursiveOrderPerm : Equiv.Perm (Fin 10) :=
  { toFun := fun i =>
      match i with
      | ⟨0, _⟩ => 0
      | ⟨1, _⟩ => 5
      | ⟨2, _⟩ => 1
      | ⟨3, _⟩ => 6
      | ⟨4, _⟩ => 2
      | ⟨5, _⟩ => 7
      | ⟨6, _⟩ => 3
      | ⟨7, _⟩ => 8
      | ⟨8, _⟩ => 4
      | ⟨9, _⟩ => 9
    invFun := fun i =>
      match i with
      | ⟨0, _⟩ => 0
      | ⟨1, _⟩ => 2
      | ⟨2, _⟩ => 4
      | ⟨3, _⟩ => 6
      | ⟨4, _⟩ => 8
      | ⟨5, _⟩ => 1
      | ⟨6, _⟩ => 3
      | ⟨7, _⟩ => 5
      | ⟨8, _⟩ => 7
      | ⟨9, _⟩ => 9
    left_inv := by
      decide
    right_inv := by
      decide }

theorem split55RecursiveOrderPerm_sign :
    Equiv.Perm.sign split55RecursiveOrderPerm = 1 := by
  native_decide

theorem gammaBasis55_sq (i : Fin 10) :
    gammaBasis55 i * gammaBasis55 i =
      (if i.val < 5 then (1 : ℝ) else -1) •
        (1 : SpinorMatrix 5) := by
  rw [gammaBasis55, gamma55_sq]
  fin_cases i <;> simp [vec55Basis, q55Real]


private lemma listProd_mul_of_anticommutes
    (x : SpinorMatrix 5)
    (L : List (SpinorMatrix 5))
    (hanti : ∀ y ∈ L, y * x = -(x * y)) :
    L.prod * x =
      ((-1 : ℝ) ^ L.length) • (x * L.prod) := by
  induction L with
  | nil => simp
  | cons y ys ih =>
      have hy : y * x = -(x * y) := hanti y (by simp)
      have hys : ∀ z ∈ ys, z * x = -(x * z) := by
        intro z hz
        exact hanti z (by simp [hz])
      rw [List.prod_cons, mul_assoc, ih hys]
      rw [Algebra.mul_smul_comm]
      rw [← mul_assoc, hy]
      simp [pow_succ, mul_assoc]

noncomputable def gradingTensor : (n : ℕ) → SplitGammaMatrix n
  | 0 => 1
  | n + 1 => appendAtom (gradingTensor n) gradingAtom

@[simp] theorem gradingTensor_sq (n : ℕ) :
    gradingTensor n * gradingTensor n = (1 : SplitGammaMatrix n) := by
  induction n with
  | zero => simp [gradingTensor]
  | succ n ih =>
      rw [gradingTensor, appendAtom_square, ih, gradingAtom_sq]
      ext i j
      rcases i with ⟨i, a⟩
      rcases j with ⟨j, b⟩
      simp only [appendAtom_apply, Matrix.one_apply]
      by_cases hij : i = j <;> by_cases hab : a = b <;>
        simp [hij, hab]

noncomputable def chiralityMatrix : SpinorMatrix 5 :=
  (tensorMatrixEquivFinPowTwo 5) (gradingTensor 5)

@[simp] theorem chiralityMatrix_sq :
    chiralityMatrix * chiralityMatrix = (1 : SpinorMatrix 5) := by
  rw [chiralityMatrix, ← map_mul, gradingTensor_sq, map_one]

/-! The native ordered volume is formed in the Clifford algebra first. -/

noncomputable def gammaBasisClifford55 (i : Fin 10) : Cl_split 5 :=
  CliffordAlgebra.ι (SplitQuad 5)
    (vec55SplitEquiv (vec55Basis i))

theorem clifford_ι_swap_of_polar_eq_zero
    {v w : Fin 10 → ℝ}
    (hpolar : QuadraticMap.polar (SplitQuad 5)
      (vec55SplitEquiv v) (vec55SplitEquiv w) = 0) :
    CliffordAlgebra.ι (SplitQuad 5) (vec55SplitEquiv v) *
        CliffordAlgebra.ι (SplitQuad 5) (vec55SplitEquiv w) =
      - (CliffordAlgebra.ι (SplitQuad 5) (vec55SplitEquiv w) *
        CliffordAlgebra.ι (SplitQuad 5) (vec55SplitEquiv v)) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := SplitQuad 5) (vec55SplitEquiv v) (vec55SplitEquiv w)
  rw [hpolar, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem listProd_adjacent_swap
    (L R : List (SpinorMatrix 5))
    (x y : SpinorMatrix 5)
    (hxy : x * y = -(y * x)) :
    (L ++ x :: y :: R).prod =
      - (L ++ y :: x :: R).prod := by
  rw [List.prod_append, List.prod_cons, List.prod_cons,
    List.prod_append, List.prod_cons, List.prod_cons]
  calc
    L.prod * (x * (y * R.prod)) = L.prod * ((x * y) * R.prod) := by
      simp [mul_assoc]
    _ = L.prod * (-(y * x) * R.prod) := by rw [hxy]
    _ = -(L.prod * (y * (x * R.prod))) := by
      simp [mul_assoc]

def splitHeadPlus (n : ℕ) : InfoGeometry.Clifford.SpinorRep.SplitSpace (n + 1) := ((1, 0), 0)

def splitHeadMinus (n : ℕ) : InfoGeometry.Clifford.SpinorRep.SplitSpace (n + 1) := ((0, 1), 0)

def splitTailLift {n : ℕ} (v : InfoGeometry.Clifford.SpinorRep.SplitSpace n) :
    InfoGeometry.Clifford.SpinorRep.SplitSpace (n + 1) := ((0, 0), v)

theorem recursiveGammaTensor_splitHeadPlus (n : ℕ) :
    recursiveGammaTensor (n + 1) (splitHeadPlus n) =
      appendAtom (1 : SplitGammaMatrix n) gammaPlusAtom := by
  change
    appendAtom (recursiveGammaTensor n
      (0 : InfoGeometry.Clifford.SpinorRep.SplitSpace n)) gradingAtom +
        appendAtom (1 : SplitGammaMatrix n)
          ((1 : ℝ) • gammaPlusAtom + (0 : ℝ) • gammaMinusAtom) = _
  rw [map_zero, appendAtom_zero_left, zero_add, zero_smul, add_zero,
    one_smul]

theorem recursiveGammaTensor_splitHeadMinus (n : ℕ) :
    recursiveGammaTensor (n + 1) (splitHeadMinus n) =
      appendAtom (1 : SplitGammaMatrix n) gammaMinusAtom := by
  change
    appendAtom (recursiveGammaTensor n
      (0 : InfoGeometry.Clifford.SpinorRep.SplitSpace n)) gradingAtom +
        appendAtom (1 : SplitGammaMatrix n)
          ((0 : ℝ) • gammaPlusAtom + (1 : ℝ) • gammaMinusAtom) = _
  rw [map_zero, appendAtom_zero_left, zero_add, zero_smul, zero_add,
    one_smul]

theorem recursiveGammaTensor_splitTailLift
    {n : ℕ} (v : InfoGeometry.Clifford.SpinorRep.SplitSpace n) :
    recursiveGammaTensor (n + 1) ((0, 0), v) =
      appendAtom (recursiveGammaTensor n v) gradingAtom := by
  change
    appendAtom (recursiveGammaTensor n v) gradingAtom +
        appendAtom (1 : SplitGammaMatrix n)
          ((0 : ℝ) • gammaPlusAtom + (0 : ℝ) • gammaMinusAtom) = _
  simp only [zero_smul, add_zero, appendAtom_zero_right]

def pairedSplitVectors : (n : ℕ) → List (InfoGeometry.Clifford.SpinorRep.SplitSpace n)
  | 0 => []
  | n + 1 =>
      splitHeadPlus n :: splitHeadMinus n ::
        (pairedSplitVectors n).map (fun v => ((0, 0), v))

noncomputable def pairedGammaProduct : (n : ℕ) → SplitGammaMatrix n
  | 0 => 1
  | n + 1 =>
      ((pairedSplitVectors (n + 1)).map (recursiveGammaTensor (n + 1))).foldl
        (· * ·) 1

theorem pairedGammaProduct_zero :
    pairedGammaProduct 0 = (1 : SplitGammaMatrix 0) := rfl

theorem pairedGammaProduct_one :
    pairedGammaProduct 1 = gradingTensor 1 := by
  simp only [pairedGammaProduct, pairedSplitVectors, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil, one_mul]
  rw [recursiveGammaTensor_splitHeadPlus,
    recursiveGammaTensor_splitHeadMinus, appendAtom_mul]
  rw [one_mul, ← gamma12_eq, gradingTensor]
  rfl

theorem pairedGammaProduct_two :
    pairedGammaProduct 2 = gradingTensor 2 := by
  simp only [pairedGammaProduct, pairedSplitVectors, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil, one_mul]
  rw [recursiveGammaTensor_splitHeadPlus,
    recursiveGammaTensor_splitHeadMinus, appendAtom_mul]
  rw [recursiveGammaTensor_splitTailLift,
    recursiveGammaTensor_splitTailLift]
  rw [InfoGeometry.Clifford.SpinorRep.appendAtom_mul_assoc_left]
  rw [recursiveGammaTensor_splitHeadPlus,
    recursiveGammaTensor_splitHeadMinus]
  simp [gradingTensor, gamma12_sq, mul_assoc]
  rw [appendAtom_mul, ← gamma12_eq]
  simp [gradingAtom]

noncomputable def pairedGammaTailFold (n : ℕ)
    (A : SplitGammaMatrix (n + 1)) : SplitGammaMatrix (n + 1) :=
  ((pairedSplitVectors n).map (fun v =>
      recursiveGammaTensor (n + 1) ((0, 0), v))).foldl (· * ·) A

theorem pairedGammaProduct_succ_fold (n : ℕ) :
    pairedGammaProduct (n + 1) =
      pairedGammaTailFold n
        ((appendAtom (1 : SplitGammaMatrix n) gammaPlusAtom *
          appendAtom (1 : SplitGammaMatrix n) gammaMinusAtom)) := by
  simp [pairedGammaProduct, pairedSplitVectors, pairedGammaTailFold]
  rw [recursiveGammaTensor_splitHeadPlus,
    recursiveGammaTensor_splitHeadMinus]
  congr 1

theorem liftedFold_appendAtom
    {n : ℕ} (xs : List (InfoGeometry.Clifford.SpinorRep.SplitSpace n))
    (A : SplitGammaMatrix n)
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    ((xs.map (fun v =>
      recursiveGammaTensor (n + 1) ((0, 0), v))).foldl (· * ·)
        (appendAtom A B)) =
      appendAtom
        ((xs.map (recursiveGammaTensor n)).foldl (· * ·) A)
        (B * gradingAtom ^ xs.length) := by
  induction xs generalizing A B with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [recursiveGammaTensor_splitTailLift, appendAtom_mul]
      rw [ih (A := A * recursiveGammaTensor n v)
        (B := B * gradingAtom)]
      rw [List.length_cons, pow_succ]
      simp [mul_assoc, ← pow_succ']
      rw [pow_succ]

theorem pairedGammaProduct_fold (n : ℕ) :
    pairedGammaProduct n =
      ((pairedSplitVectors n).map (recursiveGammaTensor n)).foldl (· * ·) 1 := by
  cases n <;> rfl

theorem pairedGammaTailFold_lifted (n : ℕ) :
    pairedGammaTailFold n
        (appendAtom (1 : SplitGammaMatrix n) gradingAtom) =
      appendAtom (pairedGammaProduct n)
        (gradingAtom * gradingAtom ^ (pairedSplitVectors n).length) := by
  rw [pairedGammaTailFold, liftedFold_appendAtom, pairedGammaProduct_fold]

theorem pairedSplitVectors_length_even (n : ℕ) :
    (pairedSplitVectors n).length = 2 * n := by
  induction n with
  | zero =>
      simp [pairedSplitVectors]
  | succ n ih =>
      simp [pairedSplitVectors, ih]
      omega

theorem pairedGammaProduct_succ (n : ℕ) :
    pairedGammaProduct (n + 1) =
      appendAtom (pairedGammaProduct n) gradingAtom := by
  rw [pairedGammaProduct_succ_fold]
  have hpm :
      appendAtom (1 : SplitGammaMatrix n) gammaPlusAtom *
        appendAtom (1 : SplitGammaMatrix n) gammaMinusAtom =
      appendAtom (1 : SplitGammaMatrix n) gradingAtom := by
    rw [appendAtom_mul]
    simpa [gradingAtom, gamma12_eq]
  rw [hpm]
  rw [pairedGammaTailFold_lifted]
  have hpow :
      gradingAtom * gradingAtom ^ (pairedSplitVectors n).length = gradingAtom := by
    rw [pairedSplitVectors_length_even]
    have hsq : gradingAtom ^ 2 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      simpa [pow_two] using gradingAtom_sq
    rw [pow_mul]
    simp [hsq]
  rw [hpow]

theorem pairedGammaProduct_eq_gradingTensor :
    ∀ n, pairedGammaProduct n = gradingTensor n
  | 0 => by
      rfl
  | n + 1 => by
      rw [pairedGammaProduct_succ, pairedGammaProduct_eq_gradingTensor n]
      rfl

theorem pairedGammaProduct_five :
    pairedGammaProduct 5 = gradingTensor 5 := by
  simpa using pairedGammaProduct_eq_gradingTensor 5

noncomputable def orderedCliffordVolume55 : Cl_split 5 :=
  (List.ofFn gammaBasisClifford55).foldl (· * ·) 1

noncomputable def orderedGammaVolume55 : SpinorMatrix 5 :=
  spinorRepresentation 5 orderedCliffordVolume55

/-! Concrete matrix multiplication is retained only as a readback target. -/
noncomputable def orderedGammaVolume55_matrix : SpinorMatrix 5 :=
  (List.ofFn gammaBasis55).foldl (· * ·) 1

private lemma algHom_map_foldl_mul
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (L : List A) (a : A) :
    f (L.foldl (· * ·) a) =
      (L.map f).foldl (· * ·) (f a) := by
  induction L generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih]
      rw [map_mul]

theorem orderedGammaVolume55_eq_matrix :
    orderedGammaVolume55 = orderedGammaVolume55_matrix := by
  have h1 : (spinorRepresentation 5) 1 = 1 := by
    simp
  rw [orderedGammaVolume55, orderedCliffordVolume55,
    algHom_map_foldl_mul, List.map_ofFn, h1]
  have hcomp : (⇑(spinorRepresentation 5) ∘ gammaBasisClifford55) =
      gammaBasis55 := by
    funext i
    exact spinorRepresentation_ι 5 (vec55SplitEquiv (vec55Basis i))
  rw [hcomp]
  rfl

private theorem gamma55_anticomm_of_polar_zero
    {v w : Fin 10 → ℝ}
    (hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv v) (vec55SplitEquiv w) = 0) :
    gamma55 v * gamma55 w = -(gamma55 w * gamma55 v) := by
  have h := gamma55_anticomm v w
  rw [hpolar, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem gammaBasis55_anticomm_45 :
    gammaBasis55 4 * gammaBasis55 5 = -(gammaBasis55 5 * gammaBasis55 4) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 4)) (vec55SplitEquiv (vec55Basis 5)) = 0 := by
    rw [vec55SplitEquiv_basis4, vec55SplitEquiv_basis5]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 4 + vec55Basis 5)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 4)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 5)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 4) (w := vec55Basis 5) hpolar)

private theorem gammaBasis55_anticomm_35 :
    gammaBasis55 3 * gammaBasis55 5 = -(gammaBasis55 5 * gammaBasis55 3) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 3)) (vec55SplitEquiv (vec55Basis 5)) = 0 := by
    rw [vec55SplitEquiv_basis3, vec55SplitEquiv_basis5]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 3 + vec55Basis 5)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 3)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 5)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 3) (w := vec55Basis 5) hpolar)

private theorem gammaBasis55_anticomm_25 :
    gammaBasis55 2 * gammaBasis55 5 = -(gammaBasis55 5 * gammaBasis55 2) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 2)) (vec55SplitEquiv (vec55Basis 5)) = 0 := by
    rw [vec55SplitEquiv_basis2, vec55SplitEquiv_basis5]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 2 + vec55Basis 5)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 2)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 5)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 2) (w := vec55Basis 5) hpolar)

private theorem gammaBasis55_anticomm_15 :
    gammaBasis55 1 * gammaBasis55 5 = -(gammaBasis55 5 * gammaBasis55 1) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 1)) (vec55SplitEquiv (vec55Basis 5)) = 0 := by
    rw [vec55SplitEquiv_basis1, vec55SplitEquiv_basis5]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 1 + vec55Basis 5)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 1)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 5)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 1) (w := vec55Basis 5) hpolar)

private theorem gammaBasis55_anticomm_46 :
    gammaBasis55 4 * gammaBasis55 6 = -(gammaBasis55 6 * gammaBasis55 4) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 4)) (vec55SplitEquiv (vec55Basis 6)) = 0 := by
    rw [vec55SplitEquiv_basis4, vec55SplitEquiv_basis6]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 4 + vec55Basis 6)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 4)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 6)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 4) (w := vec55Basis 6) hpolar)

private theorem gammaBasis55_anticomm_36 :
    gammaBasis55 3 * gammaBasis55 6 = -(gammaBasis55 6 * gammaBasis55 3) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 3)) (vec55SplitEquiv (vec55Basis 6)) = 0 := by
    rw [vec55SplitEquiv_basis3, vec55SplitEquiv_basis6]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 3 + vec55Basis 6)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 3)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 6)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 3) (w := vec55Basis 6) hpolar)

private theorem gammaBasis55_anticomm_26 :
    gammaBasis55 2 * gammaBasis55 6 = -(gammaBasis55 6 * gammaBasis55 2) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 2)) (vec55SplitEquiv (vec55Basis 6)) = 0 := by
    rw [vec55SplitEquiv_basis2, vec55SplitEquiv_basis6]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 2 + vec55Basis 6)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 2)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 6)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 2) (w := vec55Basis 6) hpolar)

private theorem gammaBasis55_anticomm_47 :
    gammaBasis55 4 * gammaBasis55 7 = -(gammaBasis55 7 * gammaBasis55 4) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 4)) (vec55SplitEquiv (vec55Basis 7)) = 0 := by
    rw [vec55SplitEquiv_basis4, vec55SplitEquiv_basis7]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 4 + vec55Basis 7)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 4)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 7)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 4) (w := vec55Basis 7) hpolar)

private theorem gammaBasis55_anticomm_37 :
    gammaBasis55 3 * gammaBasis55 7 = -(gammaBasis55 7 * gammaBasis55 3) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 3)) (vec55SplitEquiv (vec55Basis 7)) = 0 := by
    rw [vec55SplitEquiv_basis3, vec55SplitEquiv_basis7]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 3 + vec55Basis 7)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 3)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 7)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 3) (w := vec55Basis 7) hpolar)

private theorem gammaBasis55_anticomm_48 :
    gammaBasis55 4 * gammaBasis55 8 = -(gammaBasis55 8 * gammaBasis55 4) := by
  have hpolar : QuadraticMap.polar (Qsplit 5)
      (vec55SplitEquiv (vec55Basis 4)) (vec55SplitEquiv (vec55Basis 8)) = 0 := by
    rw [vec55SplitEquiv_basis4, vec55SplitEquiv_basis8]
    rw [QuadraticMap.polar]
    change (Qsplit 5) (vec55SplitEquiv (vec55Basis 4 + vec55Basis 8)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 4)) -
      (Qsplit 5) (vec55SplitEquiv (vec55Basis 8)) = 0
    rw [splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv, splitQ_vec55SplitEquiv]
    simp [vec55Basis, q55Real]
  simpa [gammaBasis55] using
    (gamma55_anticomm_of_polar_zero (v := vec55Basis 4) (w := vec55Basis 8) hpolar)

set_option maxHeartbeats 1000000 in
theorem orderedGammaVolume55_eq_chiralityMatrix :
    orderedGammaVolume55 = chiralityMatrix := by
  have hswap1 :
      ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 3,
        gammaBasis55 4, gammaBasis55 5, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 3,
          gammaBasis55 5, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    exact listProd_adjacent_swap
      (L := [gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 3])
      (R := [gammaBasis55 6, gammaBasis55 7, gammaBasis55 8, gammaBasis55 9])
      (x := gammaBasis55 4) (y := gammaBasis55 5) gammaBasis55_anticomm_45
  have hswap2 :
      ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 3,
        gammaBasis55 5, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 5,
          gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    let L : List (SpinorMatrix 5) := [gammaBasis55 0, gammaBasis55 1, gammaBasis55 2]
    let R : List (SpinorMatrix 5) := [gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
      gammaBasis55 8, gammaBasis55 9]
    have h := listProd_adjacent_swap
      (L := L) (R := R) (x := gammaBasis55 3) (y := gammaBasis55 5)
      gammaBasis55_anticomm_35
    simpa [L, R] using h
  have hswap3 :
      ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 5,
        gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 5, gammaBasis55 2,
          gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    exact listProd_adjacent_swap
      (L := [gammaBasis55 0, gammaBasis55 1])
      (R := [gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9])
      (x := gammaBasis55 2) (y := gammaBasis55 5) gammaBasis55_anticomm_25
  have hswap4 :
      ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 5, gammaBasis55 2,
        gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
          gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    let L : List (SpinorMatrix 5) := [gammaBasis55 0]
    let R : List (SpinorMatrix 5) := [gammaBasis55 2, gammaBasis55 3, gammaBasis55 4,
      gammaBasis55 6, gammaBasis55 7, gammaBasis55 8, gammaBasis55 9]
    have h := listProd_adjacent_swap
      (L := L) (R := R) (x := gammaBasis55 1) (y := gammaBasis55 5)
      gammaBasis55_anticomm_15
    simpa [L, R] using h
  have hswap5 :
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
        gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
          gammaBasis55 3, gammaBasis55 6, gammaBasis55 4, gammaBasis55 7,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    let L : List (SpinorMatrix 5) := [gammaBasis55 0, gammaBasis55 5, gammaBasis55 1,
      gammaBasis55 2, gammaBasis55 3]
    let R : List (SpinorMatrix 5) := [gammaBasis55 7, gammaBasis55 8, gammaBasis55 9]
    have h := listProd_adjacent_swap
      (L := L) (R := R) (x := gammaBasis55 4) (y := gammaBasis55 6)
      gammaBasis55_anticomm_46
    simpa [L, R] using h
  have hswap6 :
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
        gammaBasis55 3, gammaBasis55 6, gammaBasis55 4, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
          gammaBasis55 6, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    simpa using (listProd_adjacent_swap
      (L := [gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2])
      (R := [gammaBasis55 4, gammaBasis55 7, gammaBasis55 8, gammaBasis55 9])
      (x := gammaBasis55 3) (y := gammaBasis55 6) gammaBasis55_anticomm_36)
  have hswap7 :
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
        gammaBasis55 6, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
          gammaBasis55 2, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    exact listProd_adjacent_swap
      (L := [gammaBasis55 0, gammaBasis55 5, gammaBasis55 1])
      (R := [gammaBasis55 3, gammaBasis55 4, gammaBasis55 7, gammaBasis55 8,
        gammaBasis55 9])
      (x := gammaBasis55 2) (y := gammaBasis55 6) gammaBasis55_anticomm_26
  have hswap8 :
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
        gammaBasis55 2, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
          gammaBasis55 2, gammaBasis55 3, gammaBasis55 7, gammaBasis55 4,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    exact listProd_adjacent_swap
      (L := [gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
        gammaBasis55 2, gammaBasis55 3])
      (R := [gammaBasis55 8, gammaBasis55 9])
      (x := gammaBasis55 4) (y := gammaBasis55 7) gammaBasis55_anticomm_47
  have hswap9 :
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
        gammaBasis55 2, gammaBasis55 3, gammaBasis55 7, gammaBasis55 4,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
          gammaBasis55 2, gammaBasis55 7, gammaBasis55 3, gammaBasis55 4,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    exact listProd_adjacent_swap
      (L := [gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
        gammaBasis55 2])
      (R := [gammaBasis55 4, gammaBasis55 8, gammaBasis55 9])
      (x := gammaBasis55 3) (y := gammaBasis55 7) gammaBasis55_anticomm_37
  have hswap10 :
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
        gammaBasis55 2, gammaBasis55 7, gammaBasis55 3, gammaBasis55 4,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
          gammaBasis55 2, gammaBasis55 7, gammaBasis55 3, gammaBasis55 8,
          gammaBasis55 4, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    exact listProd_adjacent_swap
      (L := [gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
        gammaBasis55 2, gammaBasis55 7, gammaBasis55 3])
      (R := [gammaBasis55 9])
      (x := gammaBasis55 4) (y := gammaBasis55 8) gammaBasis55_anticomm_48
  have h0246 :
      ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 3,
        gammaBasis55 4, gammaBasis55 5, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 5,
        gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    rw [hswap1, hswap2]
    simp
  have h2468 :
      ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 5,
        gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
        gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    rw [hswap3, hswap4]
    simp
  have h46810 :
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
        gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
        gammaBasis55 6, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    rw [hswap5, hswap6]
    simp
  have h6108 :
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
        gammaBasis55 6, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
        gammaBasis55 2, gammaBasis55 3, gammaBasis55 7, gammaBasis55 4,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    have h8neg :
        - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
            gammaBasis55 2, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
            gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
        ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
            gammaBasis55 2, gammaBasis55 3, gammaBasis55 7, gammaBasis55 4,
            gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
      simpa using congrArg (fun z : SpinorMatrix 5 => -z) hswap8
    calc
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
          gammaBasis55 6, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod
          = - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
              gammaBasis55 2, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
              gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := hswap7
      _ = ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
              gammaBasis55 2, gammaBasis55 3, gammaBasis55 7, gammaBasis55 4,
              gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
        simpa using h8neg
  have h8final :
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
        gammaBasis55 2, gammaBasis55 3, gammaBasis55 7, gammaBasis55 4,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
        gammaBasis55 2, gammaBasis55 7, gammaBasis55 3, gammaBasis55 8,
        gammaBasis55 4, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
    have h10neg :
        - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
            gammaBasis55 2, gammaBasis55 7, gammaBasis55 3, gammaBasis55 4,
            gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
        ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
            gammaBasis55 2, gammaBasis55 7, gammaBasis55 3, gammaBasis55 8,
            gammaBasis55 4, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
      simpa using congrArg (fun z : SpinorMatrix 5 => -z) hswap10
    calc
      ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
          gammaBasis55 2, gammaBasis55 3, gammaBasis55 7, gammaBasis55 4,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod
          = - ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
              gammaBasis55 2, gammaBasis55 7, gammaBasis55 3, gammaBasis55 4,
              gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := hswap9
      _ = ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
              gammaBasis55 2, gammaBasis55 7, gammaBasis55 3, gammaBasis55 8,
              gammaBasis55 4, gammaBasis55 9] : List (SpinorMatrix 5)).prod := by
        simpa using h10neg
  have hpaired :
      ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 3,
        gammaBasis55 4, gammaBasis55 5, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod =
      (((pairedSplitVectors 5).map (recursiveGammaTensor 5)).map
        (tensorMatrixEquivFinPowTwo 5)).foldl (· * ·) 1 := by
    calc
      ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 3,
          gammaBasis55 4, gammaBasis55 5, gammaBasis55 6, gammaBasis55 7,
          gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod
          = ([gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 5,
              gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
              gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := h0246
      _ = ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
              gammaBasis55 3, gammaBasis55 4, gammaBasis55 6, gammaBasis55 7,
              gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := h2468
      _ = ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 2,
              gammaBasis55 6, gammaBasis55 3, gammaBasis55 4, gammaBasis55 7,
              gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := h46810
      _ = ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
              gammaBasis55 2, gammaBasis55 3, gammaBasis55 7, gammaBasis55 4,
              gammaBasis55 8, gammaBasis55 9] : List (SpinorMatrix 5)).prod := h6108
      _ = ([gammaBasis55 0, gammaBasis55 5, gammaBasis55 1, gammaBasis55 6,
              gammaBasis55 2, gammaBasis55 7, gammaBasis55 3, gammaBasis55 8,
              gammaBasis55 4, gammaBasis55 9] : List (SpinorMatrix 5)).prod := h8final
      _ = (((pairedSplitVectors 5).map (recursiveGammaTensor 5)).map
          (tensorMatrixEquivFinPowTwo 5)).foldl (· * ·) 1 := by
        rw [← List.prod_eq_foldl]
        congr 1
  have hchir :
      (((pairedSplitVectors 5).map (recursiveGammaTensor 5)).map
        (tensorMatrixEquivFinPowTwo 5)).foldl (· * ·) 1 = chiralityMatrix := by
    have hone : (tensorMatrixEquivFinPowTwo 5) (1 : SplitGammaMatrix 5) =
        (1 : SpinorMatrix 5) := map_one (tensorMatrixEquivFinPowTwo 5)
    rw [← hone]
    have hmap := algHom_map_foldl_mul
      (f := (tensorMatrixEquivFinPowTwo 5).toAlgHom)
      ((pairedSplitVectors 5).map (recursiveGammaTensor 5))
      (1 : SplitGammaMatrix 5)
    change ((((pairedSplitVectors 5).map (recursiveGammaTensor 5)).map
      (tensorMatrixEquivFinPowTwo 5).toAlgHom).foldl (· * ·)
        ((tensorMatrixEquivFinPowTwo 5).toAlgHom (1 : SplitGammaMatrix 5))) =
      chiralityMatrix
    rw [← hmap]
    rw [← pairedGammaProduct_fold, pairedGammaProduct_five]
    rfl
  have hindices : List.ofFn (fun i : Fin 10 => i) =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
    native_decide
  have hlist : List.ofFn gammaBasis55 =
      [gammaBasis55 0, gammaBasis55 1, gammaBasis55 2, gammaBasis55 3,
        gammaBasis55 4, gammaBasis55 5, gammaBasis55 6, gammaBasis55 7,
        gammaBasis55 8, gammaBasis55 9] := by
    simpa only [List.map_ofFn, Function.comp_id, List.map_cons, List.map_nil] using
      congrArg (List.map gammaBasis55) hindices
  rw [orderedGammaVolume55_eq_matrix, orderedGammaVolume55_matrix,
    ← List.prod_eq_foldl, hlist]
  exact hpaired.trans hchir

/-- Canonical concrete `Cl(5,5)` chirality owner on the recursive spinor
matrix carrier. -/
noncomputable def chirality55 : SpinorMatrix 5 :=
  chiralityMatrix

theorem chirality55_eq_canonical :
    chirality55 = chiralityMatrix := rfl

theorem chirality55_sq :
    chirality55 * chirality55 = (1 : SpinorMatrix 5) := by
  exact chiralityMatrix_sq

noncomputable def chiralPlusProjector : SpinorMatrix 5 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix 5) + chirality55)

noncomputable def chiralMinusProjector : SpinorMatrix 5 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix 5) - chirality55)

theorem chiralPlusProjector_idempotent :
    chiralPlusProjector * chiralPlusProjector = chiralPlusProjector := by
  rw [chiralPlusProjector, smul_mul_assoc, Algebra.mul_smul_comm]
  simp only [add_mul, mul_add, one_mul, mul_one, chirality55_sq]
  module

theorem chiralMinusProjector_idempotent :
    chiralMinusProjector * chiralMinusProjector = chiralMinusProjector := by
  rw [chiralMinusProjector, smul_mul_assoc, Algebra.mul_smul_comm]
  simp only [sub_mul, mul_sub, one_mul, mul_one, chirality55_sq]
  module

theorem chirality55_mul_chiralPlusProjector :
    chirality55 * chiralPlusProjector = chiralPlusProjector := by
  rw [chiralPlusProjector, Algebra.mul_smul_comm]
  simp only [mul_add, mul_one, chirality55_sq]
  module

theorem chirality55_mul_chiralMinusProjector :
    chirality55 * chiralMinusProjector = -chiralMinusProjector := by
  rw [chiralMinusProjector, Algebra.mul_smul_comm]
  simp only [mul_sub, mul_one, chirality55_sq]
  module

theorem chiralProjectors_complementary :
    chiralPlusProjector + chiralMinusProjector =
      (1 : SpinorMatrix 5) := by
  rw [chiralPlusProjector, chiralMinusProjector]
  module

theorem chiralProjectors_orthogonal :
    chiralPlusProjector * chiralMinusProjector = 0 := by
  rw [chiralPlusProjector, chiralMinusProjector, smul_mul_assoc,
    Algebra.mul_smul_comm]
  simp only [add_mul, mul_sub, one_mul, mul_one, chirality55_sq]
  module

theorem chiralProjectors_orthogonal_rev :
    chiralMinusProjector * chiralPlusProjector = 0 := by
  rw [chiralPlusProjector, chiralMinusProjector, smul_mul_assoc,
    Algebra.mul_smul_comm]
  simp only [sub_mul, mul_add, one_mul, mul_one, chirality55_sq]
  module

noncomputable def jordanNullPlus :
    Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ :=
  { xp := 1, xm := 0, z := 0 }

noncomputable def jordanNullMinus :
    Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ :=
  { xp := 0, xm := 1, z := 0 }

theorem toVec55Q_jordanNullPlus :
    toVec55Q jordanNullPlus =
      fun i => if i = 0 then 1 / 2 else if i = 5 then 1 / 2 else 0 := by
  funext i
  fin_cases i <;> simp [jordanNullPlus, toVec55Q, Algebra.SplitOctonionQ.SplitO.zero]

theorem toVec55Q_jordanNullMinus :
    toVec55Q jordanNullMinus =
      fun i => if i = 0 then 1 / 2 else if i = 5 then -(1 / 2) else 0 := by
  funext i
  fin_cases i <;> simp [jordanNullMinus, toVec55Q, Algebra.SplitOctonionQ.SplitO.zero] <;> ring

noncomputable def gammaJordanNullPlus : SpinorMatrix 5 :=
  hermitianGamma jordanNullPlus

noncomputable def gammaJordanNullMinus : SpinorMatrix 5 :=
  hermitianGamma jordanNullMinus

theorem vec55Split_jordanNullPlus :
    vec55SplitEquiv (castVec55 (toVec55Q jordanNullPlus)) =
      headNullMinus 4 := by
  ext <;> simp [vec55SplitEquiv, castVec55, toVec55Q, jordanNullPlus,
    headNullMinus, headPair, Algebra.SplitOctonionQ.SplitO.zero] <;>
    try norm_num
  all_goals exfalso
  all_goals exact Fin.elim0 (by assumption)

theorem vec55Split_jordanNullMinus :
    vec55SplitEquiv (castVec55 (toVec55Q jordanNullMinus)) =
      headNullPlus 4 := by
  ext <;> simp [vec55SplitEquiv, castVec55, toVec55Q, jordanNullMinus,
    headNullPlus, headPair, Algebra.SplitOctonionQ.SplitO.zero] <;>
    try norm_num
  all_goals exfalso
  all_goals exact Fin.elim0 (by assumption)

theorem gammaJordanNullPlus_eq_u5 :
    gammaJordanNullPlus =
      spinorRepresentation 5
        InfoGeometry.Clifford.ConformalLieAlgebra55.u5 := by
  rw [gammaJordanNullPlus, hermitianGamma, gamma55,
    vec55Split_jordanNullPlus]
  simpa [InfoGeometry.Clifford.ConformalLieAlgebra55.u5] using
    (spinorRepresentation_ι 5 (headNullMinus 4)).symm

theorem gammaJordanNullMinus_eq_v5 :
    gammaJordanNullMinus =
      spinorRepresentation 5
        InfoGeometry.Clifford.ConformalLieAlgebra55.v5 := by
  rw [gammaJordanNullMinus, hermitianGamma, gamma55,
    vec55Split_jordanNullMinus]
  simpa [InfoGeometry.Clifford.ConformalLieAlgebra55.v5] using
    (spinorRepresentation_ι 5 (headNullPlus 4)).symm

theorem spinorRepresentation_J5 :
    spinorRepresentation 5 InfoGeometry.Clifford.ConformalLieAlgebra55.J5 =
      gammaJordanNullPlus - gammaJordanNullMinus := by
  rw [InfoGeometry.Clifford.ConformalLieAlgebra55.J5, map_sub,
    ← gammaJordanNullPlus_eq_u5, ← gammaJordanNullMinus_eq_v5]

noncomputable def gammaTailNullMinus : SpinorMatrix 5 :=
  (tensorMatrixEquivFinPowTwo 5)
    (appendAtom (recursiveGammaTensor 4 (headNullMinus 3)) gradingAtom)

noncomputable def gammaTailNullPlus : SpinorMatrix 5 :=
  (tensorMatrixEquivFinPowTwo 5)
    (appendAtom (recursiveGammaTensor 4 (headNullPlus 3)) gradingAtom)

theorem gammaTailNullMinus_eq_u4 :
    gammaTailNullMinus =
      spinorRepresentation 5 InfoGeometry.Clifford.ConformalLieAlgebra55.u4 := by
  rw [gammaTailNullMinus]
  simpa [InfoGeometry.Clifford.ConformalLieAlgebra55.u4,
    InfoGeometry.Clifford.ClNN.gammaTail] using
    (spinorRepresentation_tailFactor_ι 4 (headNullMinus 3)).symm

theorem gammaTailNullPlus_eq_v4 :
    gammaTailNullPlus =
      spinorRepresentation 5 InfoGeometry.Clifford.ConformalLieAlgebra55.v4 := by
  rw [gammaTailNullPlus]
  simpa [InfoGeometry.Clifford.ConformalLieAlgebra55.v4,
    InfoGeometry.Clifford.ClNN.gammaTail] using
    (spinorRepresentation_tailFactor_ι 4 (headNullPlus 3)).symm

theorem spinorRepresentation_J4 :
    spinorRepresentation 5 InfoGeometry.Clifford.ConformalLieAlgebra55.J4 =
      gammaTailNullMinus - gammaTailNullPlus := by
  rw [InfoGeometry.Clifford.ConformalLieAlgebra55.J4, map_sub,
    ← gammaTailNullMinus_eq_u4, ← gammaTailNullPlus_eq_v4]

theorem spinorRepresentation_J :
    spinorRepresentation 5 InfoGeometry.Clifford.ConformalLieAlgebra55.J =
      (gammaJordanNullPlus - gammaJordanNullMinus) *
        (gammaTailNullMinus - gammaTailNullPlus) := by
  rw [InfoGeometry.Clifford.ConformalLieAlgebra55.J, map_mul,
    spinorRepresentation_J5, spinorRepresentation_J4]

noncomputable def cl55R0Vec : InfoGeometry.Clifford.ClNN.Carrier 5 :=
  headPair 4 ((1 : ℝ), 0)

noncomputable def cl55R5Vec : InfoGeometry.Clifford.ClNN.Carrier 5 :=
  headPair 4 ((0 : ℝ), 1)

noncomputable def cl55R0 : SpinorMatrix 5 :=
  recursiveGamma 5 cl55R0Vec

noncomputable def cl55R5 : SpinorMatrix 5 :=
  recursiveGamma 5 cl55R5Vec

noncomputable def cl55Atom : Cl11Atom (SpinorMatrix 5) where
  r0 := cl55R0
  r5 := cl55R5
  r0_sq := by
    have hq : SplitQuad 5 cl55R0Vec = 1 := by
      norm_num [cl55R0Vec, headPair, SplitQuad, Qsplit,
        CliffordTower.Q11]
    simpa [cl55R0] using (recursiveGamma_sq 5 cl55R0Vec).trans
      (by rw [hq]; simp)
  r5_sq := by
    have hq : SplitQuad 5 cl55R5Vec = -1 := by
      norm_num [cl55R5Vec, headPair, SplitQuad, Qsplit,
        CliffordTower.Q11]
    simpa [cl55R5] using (recursiveGamma_sq 5 cl55R5Vec).trans
      (by rw [hq]; simp)
  anticommute := by
    have h := gammaGenerator_anticomm 5 cl55R0Vec cl55R5Vec
    have hm := congrArg (spinorRepresentation 5) h
    have hp : QuadraticMap.polar (SplitQuad 5) cl55R0Vec cl55R5Vec = 0 := by
      simpa [cl55R0Vec, cl55R5Vec, headPair, SplitQuad, Qsplit,
        QuadraticMap.polar, InfoGeometry.Clifford.splitB11_apply,
        CliffordTower.Q11]
    rw [map_add, map_mul, map_mul] at hm
    rw [spinorRepresentation_ι, spinorRepresentation_ι] at hm
    rw [hp, map_zero] at hm
    have hm0 : cl55R0 * cl55R5 + cl55R5 * cl55R0 = 0 := by
      simpa [cl55R0, cl55R5] using hm
    exact eq_neg_of_add_eq_zero_left hm0

noncomputable def cl55ChiralityOperator : ChiralityOperator cl55Atom :=
  eulerAsChirality cl55Atom

theorem cl55ChiralityOperator_sq :
    cl55ChiralityOperator.rho * cl55ChiralityOperator.rho =
      (1 : SpinorMatrix 5) :=
  cl55ChiralityOperator.rho_sq_one

theorem cl55ChiralityOperator_anticomm_r0 :
    cl55ChiralityOperator.rho * cl55Atom.r0 =
      -(cl55Atom.r0 * cl55ChiralityOperator.rho) :=
  cl55ChiralityOperator.anticomm_r0

theorem cl55ChiralityOperator_anticomm_r5 :
    cl55ChiralityOperator.rho * cl55Atom.r5 =
      -(cl55Atom.r5 * cl55ChiralityOperator.rho) :=
  cl55ChiralityOperator.anticomm_r5

noncomputable def cl55ChiralProjectorPlus : SpinorMatrix 5 :=
  chiralProjectorPlus cl55Atom

noncomputable def cl55ChiralProjectorMinus : SpinorMatrix 5 :=
  chiralProjectorMinus cl55Atom

theorem cl55ChiralProjectors_orthogonal :
    cl55ChiralProjectorPlus * cl55ChiralProjectorMinus = 0 :=
  chiral_sheets_orthogonal cl55Atom

theorem cl55ChiralProjectors_partition :
    cl55ChiralProjectorPlus + cl55ChiralProjectorMinus =
      (1 : SpinorMatrix 5) :=
  chiral_sheets_partition_unity cl55Atom

theorem cl55ChiralProjectorPlus_idempotent :
    cl55ChiralProjectorPlus * cl55ChiralProjectorPlus =
      cl55ChiralProjectorPlus :=
  chiral_plus_idempotent cl55Atom

theorem cl55ChiralProjectorMinus_idempotent :
    cl55ChiralProjectorMinus * cl55ChiralProjectorMinus =
      cl55ChiralProjectorMinus :=
  chiral_minus_idempotent cl55Atom

theorem cl55Euler_flips_chiral_sheets :
    cl55ChiralProjectorPlus * cl55ChiralityOperator.rho =
      cl55ChiralityOperator.rho * cl55ChiralProjectorMinus :=
  euler_operator_reverses_chiral_sheets cl55Atom

/-- Matrix action on the real spinor carrier. -/
def matrixApply (A : SpinorMatrix 5) (ψ : SpinorSpace 5) : SpinorSpace 5 :=
  fun i => ∑ j, A i j * ψ j

theorem matrixApply_eq_mulVec (A : SpinorMatrix 5) (ψ : SpinorSpace 5) :
    matrixApply A ψ = A.mulVec ψ := by
  rfl

theorem matrixApply_one (ψ : SpinorSpace 5) :
    matrixApply (1 : SpinorMatrix 5) ψ = ψ := by
  rw [matrixApply_eq_mulVec]
  exact Matrix.one_mulVec ψ

theorem matrixApply_mul (A B : SpinorMatrix 5) (ψ : SpinorSpace 5) :
    matrixApply (A * B) ψ = matrixApply A (matrixApply B ψ) := by
  rw [matrixApply_eq_mulVec, matrixApply_eq_mulVec, matrixApply_eq_mulVec]
  exact (Matrix.mulVec_mulVec ψ A B).symm

theorem matrixApply_add (A B : SpinorMatrix 5) (ψ : SpinorSpace 5) :
    matrixApply (A + B) ψ = matrixApply A ψ + matrixApply B ψ := by
  rw [matrixApply_eq_mulVec, matrixApply_eq_mulVec, matrixApply_eq_mulVec]
  exact Matrix.add_mulVec A B ψ

theorem matrixApply_vector_add (A : SpinorMatrix 5)
    (ψ φ : SpinorSpace 5) :
    matrixApply A (ψ + φ) = matrixApply A ψ + matrixApply A φ := by
  rw [matrixApply_eq_mulVec, matrixApply_eq_mulVec, matrixApply_eq_mulVec]
  exact Matrix.mulVec_add A ψ φ

theorem matrixApply_smul (r : ℝ) (A : SpinorMatrix 5) (ψ : SpinorSpace 5) :
    matrixApply (r • A) ψ = r • matrixApply A ψ := by
  rw [matrixApply_eq_mulVec, matrixApply_eq_mulVec]
  exact Matrix.smul_mulVec r A ψ

theorem matrixApply_sub (A B : SpinorMatrix 5) (ψ : SpinorSpace 5) :
    matrixApply (A - B) ψ = matrixApply A ψ - matrixApply B ψ := by
  rw [matrixApply_eq_mulVec, matrixApply_eq_mulVec, matrixApply_eq_mulVec]
  exact Matrix.sub_mulVec A B ψ

theorem matrixApply_neg (A : SpinorMatrix 5) (ψ : SpinorSpace 5) :
    matrixApply (-A) ψ = -matrixApply A ψ := by
  have h : -A = (-1 : ℝ) • A := by module
  rw [h, matrixApply_smul]
  simp

/-- The `+1` chirality eigenspace. -/
def chiralPlus (ψ : SpinorSpace 5) : Prop :=
  matrixApply chiralityMatrix ψ = ψ

/-- The `-1` chirality eigenspace. -/
def chiralMinus (ψ : SpinorSpace 5) : Prop :=
  matrixApply chiralityMatrix ψ = -ψ

theorem chiralPlusProjector_apply_of_chiralPlus
    (ψ : SpinorSpace 5) (hψ : chiralPlus ψ) :
    matrixApply chiralPlusProjector ψ = ψ := by
  rw [chiralPlusProjector, matrixApply_smul, matrixApply_add,
    matrixApply_one]
  rw [chirality55_eq_canonical]
  rw [hψ]
  module

theorem chiralMinusProjector_apply_of_chiralMinus
    (ψ : SpinorSpace 5) (hψ : chiralMinus ψ) :
    matrixApply chiralMinusProjector ψ = ψ := by
  rw [chiralMinusProjector, matrixApply_smul, matrixApply_sub,
    matrixApply_one]
  rw [chirality55_eq_canonical]
  rw [hψ]
  module

theorem chiralMinusProjector_apply_of_chiralPlus
    (ψ : SpinorSpace 5) (hψ : chiralPlus ψ) :
    matrixApply chiralMinusProjector ψ = 0 := by
  rw [chiralMinusProjector, matrixApply_smul, matrixApply_sub,
    matrixApply_one]
  rw [chirality55_eq_canonical]
  rw [hψ]
  module

theorem chiralPlusProjector_apply_of_chiralMinus
    (ψ : SpinorSpace 5) (hψ : chiralMinus ψ) :
    matrixApply chiralPlusProjector ψ = 0 := by
  rw [chiralPlusProjector, matrixApply_smul, matrixApply_add,
    matrixApply_one]
  rw [chirality55_eq_canonical]
  rw [hψ]
  module

theorem chiralPlus_of_chiralPlusProjector (ψ : SpinorSpace 5) :
    chiralPlus (matrixApply chiralPlusProjector ψ) := by
  rw [chiralPlus]
  rw [← chirality55_eq_canonical]
  rw [← matrixApply_mul, chirality55_mul_chiralPlusProjector]

theorem chiralMinus_of_chiralMinusProjector (ψ : SpinorSpace 5) :
    chiralMinus (matrixApply chiralMinusProjector ψ) := by
  rw [chiralMinus]
  rw [← chirality55_eq_canonical]
  rw [← matrixApply_mul, chirality55_mul_chiralMinusProjector]
  exact matrixApply_neg chiralMinusProjector ψ

theorem chiral_decomposition (ψ : SpinorSpace 5) :
    ψ = matrixApply chiralPlusProjector ψ +
      matrixApply chiralMinusProjector ψ := by
  calc
    ψ = matrixApply (1 : SpinorMatrix 5) ψ :=
      (matrixApply_one ψ).symm
    _ = matrixApply (chiralPlusProjector + chiralMinusProjector) ψ := by
      rw [chiralProjectors_complementary]
    _ = matrixApply chiralPlusProjector ψ +
        matrixApply chiralMinusProjector ψ :=
      matrixApply_add chiralPlusProjector chiralMinusProjector ψ

theorem chiralPlus_after_chiralMinus (ψ : SpinorSpace 5) :
    matrixApply chiralPlusProjector (matrixApply chiralMinusProjector ψ) = 0 := by
  rw [← matrixApply_mul, chiralProjectors_orthogonal]
  rw [matrixApply_eq_mulVec]
  simp

theorem chiralMinus_after_chiralPlus (ψ : SpinorSpace 5) :
    matrixApply chiralMinusProjector (matrixApply chiralPlusProjector ψ) = 0 := by
  rw [← matrixApply_mul, chiralProjectors_orthogonal_rev]
  rw [matrixApply_eq_mulVec]
  simp

theorem chiralPlus_iff_projector_fixed (ψ : SpinorSpace 5) :
    chiralPlus ψ ↔ matrixApply chiralPlusProjector ψ = ψ := by
  constructor
  · exact chiralPlusProjector_apply_of_chiralPlus ψ
  · intro hψ
    rw [chiralPlus, ← hψ, ← chirality55_eq_canonical]
    rw [← matrixApply_mul, chirality55_mul_chiralPlusProjector]

theorem chiralMinus_iff_projector_fixed (ψ : SpinorSpace 5) :
    chiralMinus ψ ↔ matrixApply chiralMinusProjector ψ = ψ := by
  constructor
  · exact chiralMinusProjector_apply_of_chiralMinus ψ
  · intro hψ
    rw [chiralMinus, ← hψ, ← chirality55_eq_canonical]
    rw [← matrixApply_mul, chirality55_mul_chiralMinusProjector]
    exact matrixApply_neg chiralMinusProjector ψ

theorem chiralPlus_iff_opposite_projector_zero (ψ : SpinorSpace 5) :
    chiralPlus ψ ↔ matrixApply chiralMinusProjector ψ = 0 := by
  constructor
  · exact chiralMinusProjector_apply_of_chiralPlus ψ
  · intro hψ
    apply (chiralPlus_iff_projector_fixed ψ).2
    have hdecomp := chiral_decomposition ψ
    rw [hψ, add_zero] at hdecomp
    exact hdecomp.symm

theorem chiralMinus_iff_opposite_projector_zero (ψ : SpinorSpace 5) :
    chiralMinus ψ ↔ matrixApply chiralPlusProjector ψ = 0 := by
  constructor
  · exact chiralPlusProjector_apply_of_chiralMinus ψ
  · intro hψ
    apply (chiralMinus_iff_projector_fixed ψ).2
    have hdecomp := chiral_decomposition ψ
    rw [hψ, zero_add] at hdecomp
    exact hdecomp.symm

theorem chiral_decomposition_unique
    (ψ ψPlus ψMinus : SpinorSpace 5)
    (hdecomp : ψ = ψPlus + ψMinus)
    (hPlus : chiralPlus ψPlus)
    (hMinus : chiralMinus ψMinus) :
    ψPlus = matrixApply chiralPlusProjector ψ ∧
      ψMinus = matrixApply chiralMinusProjector ψ := by
  constructor
  · calc
      ψPlus = matrixApply chiralPlusProjector ψPlus :=
        (chiralPlusProjector_apply_of_chiralPlus ψPlus hPlus).symm
      _ = matrixApply chiralPlusProjector (ψPlus + ψMinus) := by
        rw [matrixApply_vector_add,
          chiralPlusProjector_apply_of_chiralPlus ψPlus hPlus,
          chiralPlusProjector_apply_of_chiralMinus ψMinus hMinus,
          add_zero]
      _ = matrixApply chiralPlusProjector ψ := by rw [← hdecomp]
  · calc
      ψMinus = matrixApply chiralMinusProjector ψMinus :=
        (chiralMinusProjector_apply_of_chiralMinus ψMinus hMinus).symm
      _ = matrixApply chiralMinusProjector (ψPlus + ψMinus) := by
        rw [matrixApply_vector_add,
          chiralMinusProjector_apply_of_chiralPlus ψPlus hPlus,
          chiralMinusProjector_apply_of_chiralMinus ψMinus hMinus,
          zero_add]
      _ = matrixApply chiralMinusProjector ψ := by rw [← hdecomp]

end InfoGeometry.Clifford.Cl55SpinorChirality
