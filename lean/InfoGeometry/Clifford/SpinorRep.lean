import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.CliffordInclusionInjective
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.GammaMatrices
import InfoGeometry.Canonical.SplitCliffordDirectLimit

noncomputable section

namespace InfoGeometry.Clifford.SpinorRep

open Matrix
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.GammaMatrices
open InfoGeometry.Canonical.SplitCliffordDirectLimit

abbrev SplitSpace (n : ℕ) := InfoGeometry.CliffordTower.SplitSpace n
abbrev SplitQuad (n : ℕ) : QuadraticForm ℝ (SplitSpace n) := Qsplit n
abbrev Cl_split (n : ℕ) := InfoGeometry.Clifford.Cl_split n
abbrev SpinorSpace (n : ℕ) := Fin (2 ^ n) → ℝ
abbrev SpinorMatrix (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ

/-- Positive split `Cl(1,1)` matrix atom. -/
abbrev gammaPlusAtom : Matrix (Fin 2) (Fin 2) ℝ := gammaPlus

/-- Negative split `Cl(1,1)` matrix atom. -/
abbrev gammaMinusAtom : Matrix (Fin 2) (Fin 2) ℝ := gammaMinus

/-- Local grading atom anticommutes with both split generators. -/
abbrev gradingAtom : Matrix (Fin 2) (Fin 2) ℝ := gamma12

/-- Ordinary matrix anticommutator. -/
def anticommutator {n : ℕ} (A B : SplitGammaMatrix n) : SplitGammaMatrix n :=
  A * B + B * A

/-- Append one two-dimensional atom to the right of a tensor-stage matrix. -/
def appendAtom {n : ℕ}
    (A : SplitGammaMatrix n) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    SplitGammaMatrix (n + 1) :=
  Matrix.kronecker A B

@[simp] theorem appendAtom_apply {n : ℕ}
    (A : SplitGammaMatrix n) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (i j : TensorIndex n) (a b : Fin 2) :
    appendAtom A B (i, a) (j, b) = A i j * B a b := by
  exact Matrix.kronecker_apply A B i a j b

theorem appendAtom_square {n : ℕ}
    (A : SplitGammaMatrix n) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    appendAtom A B * appendAtom A B = appendAtom (A * A) (B * B) := by
  exact (Matrix.mul_kronecker_mul A A B B).symm

theorem appendAtom_mul {n : ℕ}
    (A C : SplitGammaMatrix n) (B D : Matrix (Fin 2) (Fin 2) ℝ) :
    appendAtom A B * appendAtom C D = appendAtom (A * C) (B * D) := by
  change Matrix.kronecker A B * Matrix.kronecker C D =
    Matrix.kronecker (A * C) (B * D)
  exact (Matrix.mul_kronecker_mul A C B D).symm

theorem appendAtom_mul_assoc {n : ℕ}
    (A C E : SplitGammaMatrix n)
    (B D F : Matrix (Fin 2) (Fin 2) ℝ) :
    appendAtom A B * (appendAtom C D * appendAtom E F) =
      appendAtom (A * (C * E)) (B * (D * F)) := by
  rw [appendAtom_mul (A := C) (C := E) (B := D) (D := F)]
  rw [appendAtom_mul (A := A) (C := C * E) (B := B) (D := D * F)]

theorem appendAtom_mul_assoc_left {n : ℕ}
    (A C E : SplitGammaMatrix n)
    (B D F : Matrix (Fin 2) (Fin 2) ℝ) :
    (appendAtom A B * appendAtom C D) * appendAtom E F =
      appendAtom ((A * C) * E) ((B * D) * F) := by
  rw [appendAtom_mul, appendAtom_mul]

@[simp] theorem appendAtom_zero_left {n : ℕ}
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    appendAtom (0 : SplitGammaMatrix n) B = 0 := by
  ext i j
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  simp [appendAtom_apply]

@[simp] theorem appendAtom_zero_right {n : ℕ}
    (A : SplitGammaMatrix n) :
    appendAtom A (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  ext i j
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  simp [appendAtom_apply]

theorem splitHeadAtom_sq (x : ℝ × ℝ) :
    (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) *
      (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) =
        (InfoGeometry.CliffordTower.Q11 x) •
          (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gammaPlusAtom, gammaMinusAtom, gammaPlus, gammaMinus,
      InfoGeometry.Clifford.Cl11Matrix.Eplus, InfoGeometry.Clifford.Cl11Matrix.Eminus,
      InfoGeometry.CliffordTower.Q11_apply, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring_nf

theorem gradingAtom_sq :
    gradingAtom * gradingAtom = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simpa [gradingAtom] using gamma12_sq

theorem gradingAtom_splitHeadAtom_anticomm (x : ℝ × ℝ) :
    gradingAtom * (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) +
      (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) * gradingAtom =
        (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gradingAtom, gammaPlusAtom, gammaMinusAtom, gamma12_eq,
      gammaPlus, gammaMinus, InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eplus, InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]


theorem appendAtom_grading_square {n : ℕ} {s : ℝ}
    {A : SplitGammaMatrix n} (hA : A * A = s • (1 : SplitGammaMatrix n)) :
    appendAtom A gradingAtom * appendAtom A gradingAtom =
      s • (1 : SplitGammaMatrix (n + 1)) := by
  rw [appendAtom_square, hA, gradingAtom_sq]
  ext i j
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    simp [appendAtom_apply, Matrix.one_apply, hij, hab]

theorem appendAtom_cross_splitHead_anticommutator {n : ℕ}
    (A : SplitGammaMatrix n) (x : ℝ × ℝ) :
    appendAtom A gradingAtom *
        appendAtom (1 : SplitGammaMatrix n)
          (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) +
      appendAtom (1 : SplitGammaMatrix n)
          (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) *
      appendAtom A gradingAtom =
      (0 : SplitGammaMatrix (n + 1)) := by
  rw [appendAtom_mul, appendAtom_mul]
  ext i j
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  simp [Matrix.one_apply]
  rw [← mul_add]
  have hentry :
      (gradingAtom * (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom)) a b +
        ((x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) * gradingAtom) a b = 0 := by
    simpa [Matrix.add_apply] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b)
        (gradingAtom_splitHeadAtom_anticomm x)
  rw [hentry, mul_zero]

abbrev SpinorSpace₁₁ := SpinorSpace 1
abbrev Mat2 := Cl11Matrix.Mat2

noncomputable abbrev q11 := Cl11Matrix.q11

noncomputable abbrev gamma₁₁ :
    (ℝ × ℝ) →ₗ[ℝ] Mat2 :=
  Cl11Matrix.gen

theorem gamma₁₁_sq (v : ℝ × ℝ) :
    gamma₁₁ v * gamma₁₁ v = (q11 v) • (1 : Mat2) :=
  Cl11Matrix.gen_sq v

noncomputable abbrev cl11ToMat : CliffordAlgebra q11 →ₐ[ℝ] Mat2 :=
  Cl11Matrix.cl11ToMat

theorem cl11ToMat_ι (v : ℝ × ℝ) :
    cl11ToMat (CliffordAlgebra.ι q11 v) = gamma₁₁ v := by
  simp [cl11ToMat, Cl11Matrix.cl11ToMat, gamma₁₁, CliffordAlgebra.lift_ι_apply]

noncomputable abbrev cl11EquivMat : CliffordAlgebra q11 ≃ₐ[ℝ] Mat2 :=
  Cl11Matrix.cl11EquivMat

theorem cl11ToMat_surjective :
    Function.Surjective cl11ToMat :=
  Cl11Matrix.cl11ToMat_surjective

theorem cl11ToMat_injective :
    Function.Injective cl11ToMat :=
  cl11EquivMat.injective

theorem cl11ToMat_bijective :
    Function.Bijective cl11ToMat :=
  ⟨cl11ToMat_injective, cl11ToMat_surjective⟩

noncomputable abbrev incl_Cl_split (n : ℕ) :
    Cl_split n →ₐ[ℝ] Cl_split (n + 1) :=
  InfoGeometry.Clifford.incl_Cl_split n

theorem incl_Cl_split_injective (n : ℕ) :
    Function.Injective (incl_Cl_split n) :=
  InfoGeometry.Clifford.incl_Cl_split_injective n

noncomputable abbrev gammaGenerator (n : ℕ) :
    SplitSpace n →ₗ[ℝ] Cl_split n :=
  CliffordAlgebra.ι (SplitQuad n)

theorem gammaGenerator_sq (n : ℕ) (v : SplitSpace n) :
    gammaGenerator n v * gammaGenerator n v =
      algebraMap ℝ (Cl_split n) (SplitQuad n v) := by
  exact CliffordAlgebra.ι_sq_scalar (Q := SplitQuad n) v

theorem gammaGenerator_anticomm (n : ℕ) (v w : SplitSpace n) :
    gammaGenerator n v * gammaGenerator n w
      + gammaGenerator n w * gammaGenerator n v =
        algebraMap ℝ (Cl_split n) (QuadraticMap.polar (SplitQuad n) v w) := by
  exact CliffordAlgebra.ι_mul_ι_add_swap (Q := SplitQuad n) v w

noncomputable def recursiveGammaTensor : (n : ℕ) →
    SplitSpace n →ₗ[ℝ] SplitGammaMatrix n
  | 0 => 0
  | n + 1 =>
      let tail : SplitSpace n →ₗ[ℝ] SplitGammaMatrix n := recursiveGammaTensor n
      {
        toFun := fun v =>
          appendAtom (tail v.2) gradingAtom +
            appendAtom (1 : SplitGammaMatrix n)
              (v.1.1 • gammaPlusAtom + v.1.2 • gammaMinusAtom)
        map_add' := by
          intro v w
          rcases v with ⟨⟨vp, vm⟩, vs⟩
          rcases w with ⟨⟨wp, wm⟩, ws⟩
          have hadd :
              (((vp, vm), vs) + ((wp, wm), ws) : SplitSpace (n + 1)) =
                ((vp + wp, vm + wm), vs + ws) := by
            ext <;> simp
          ext i j
          rcases i with ⟨i, a⟩
          rcases j with ⟨j, b⟩
          rw [hadd]
          simp [appendAtom_apply, add_assoc, add_left_comm, add_comm]
          ring_nf
        map_smul' := by
          intro r v
          rcases v with ⟨⟨vp, vm⟩, vs⟩
          have hsmul :
              (r • ((vp, vm), vs) : SplitSpace (n + 1)) =
                ((r * vp, r * vm), r • vs) := by
            ext <;> simp [smul_eq_mul]
          ext i j
          rcases i with ⟨i, a⟩
          rcases j with ⟨j, b⟩
          rw [hsmul]
          simp [appendAtom_apply, smul_eq_mul]
          ring_nf
      }

theorem recursiveGammaTensor_sq (n : ℕ) (v : SplitSpace n) :
    recursiveGammaTensor n v * recursiveGammaTensor n v =
      (SplitQuad n v) • (1 : SplitGammaMatrix n) := by
  induction n with
  | zero =>
      simp [recursiveGammaTensor, SplitQuad, Qsplit]
  | succ n ih =>
      rcases v with ⟨x, xs⟩
      let A : SplitGammaMatrix (n + 1) :=
        appendAtom (recursiveGammaTensor n xs) gradingAtom
      let B : SplitGammaMatrix (n + 1) :=
        appendAtom (1 : SplitGammaMatrix n)
          (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom)
      have hA : A * A = (SplitQuad n xs) • (1 : SplitGammaMatrix (n + 1)) := by
        simpa [A, SplitQuad] using
          appendAtom_grading_square (n := n) (s := SplitQuad n xs) (ih xs)
      have hB : B * B = (InfoGeometry.CliffordTower.Q11 x) •
          (1 : SplitGammaMatrix (n + 1)) := by
        change
          appendAtom (1 : SplitGammaMatrix n)
              (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) *
            appendAtom (1 : SplitGammaMatrix n)
              (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) =
            (InfoGeometry.CliffordTower.Q11 x) • (1 : SplitGammaMatrix (n + 1))
        rw [appendAtom_square, one_mul, splitHeadAtom_sq]
        ext i j
        rcases i with ⟨i, a⟩
        rcases j with ⟨j, b⟩
        simp [appendAtom_apply, smul_eq_mul, Matrix.one_apply]
        by_cases hij : i = j <;> by_cases hab : a = b <;>
          simp [hij, hab]
      have hcross : A * B + B * A = (0 : SplitGammaMatrix (n + 1)) := by
        simpa [A, B, anticommutator] using
          appendAtom_cross_splitHead_anticommutator
            (n := n) (recursiveGammaTensor n xs) x
      calc
        recursiveGammaTensor (n + 1) (x, xs) *
            recursiveGammaTensor (n + 1) (x, xs)
            = (A + B) * (A + B) := by rfl
        _ = A * A + (A * B + B * A) + B * B := by
          noncomm_ring
        _ = (SplitQuad n xs) • (1 : SplitGammaMatrix (n + 1)) +
              (0 : SplitGammaMatrix (n + 1)) +
              (InfoGeometry.CliffordTower.Q11 x) • (1 : SplitGammaMatrix (n + 1)) := by
          rw [hA, hB, hcross]
        _ = (SplitQuad (n + 1) (x, xs)) • (1 : SplitGammaMatrix (n + 1)) := by
          simp [SplitQuad, Qsplit_succ_apply, add_smul, add_comm]

theorem tensorIndex_card_pow_two (n : ℕ) :
    Fintype.card (TensorIndex n) = 2 ^ n := by
  induction n with
  | zero =>
      simp [TensorIndex]
  | succ n ih =>
      simp [TensorIndex, Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

def tensorIndexEquivFinPowTwo : (n : ℕ) → TensorIndex n ≃ Fin (2 ^ n)
  | 0 =>
    { toFun := fun _ => 0
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun x => by
        fin_cases x
        rfl }
  | n + 1 =>
    (tensorIndexEquivFinPowTwo n).prodCongr (Equiv.refl (Fin 2)) |>.trans finProdFinEquiv

noncomputable def tensorMatrixEquivFinPowTwo (n : ℕ) :
    SplitGammaMatrix n ≃ₐ[ℝ] SpinorMatrix n :=
  Matrix.reindexAlgEquiv ℝ ℝ (tensorIndexEquivFinPowTwo n)

noncomputable def recursiveGamma (n : ℕ) :
    SplitSpace n →ₗ[ℝ] SpinorMatrix n :=
  (tensorMatrixEquivFinPowTwo n).toLinearMap.comp (recursiveGammaTensor n)

theorem recursiveGamma_sq (n : ℕ) (v : SplitSpace n) :
    recursiveGamma n v * recursiveGamma n v =
      algebraMap ℝ (SpinorMatrix n) (SplitQuad n v) := by
  let e := tensorMatrixEquivFinPowTwo n
  calc
    recursiveGamma n v * recursiveGamma n v
        = e (recursiveGammaTensor n v) * e (recursiveGammaTensor n v) := by
            rfl
    _ = e (recursiveGammaTensor n v * recursiveGammaTensor n v) := by
            rw [map_mul]
    _ = e ((SplitQuad n v) • (1 : SplitGammaMatrix n)) := by
            rw [recursiveGammaTensor_sq]
    _ = algebraMap ℝ (SpinorMatrix n) (SplitQuad n v) := by
            rw [Algebra.algebraMap_eq_smul_one]
            simp [e]

noncomputable def spinorRepresentation (n : ℕ) :
    Cl_split n →ₐ[ℝ] SpinorMatrix n := by
  exact
    CliffordAlgebra.lift (SplitQuad n)
      ⟨recursiveGamma n, fun v => by
        exact recursiveGamma_sq n v⟩

theorem spinorRepresentation_ι (n : ℕ) (v : SplitSpace n) :
    spinorRepresentation n (CliffordAlgebra.ι (SplitQuad n) v) =
      recursiveGamma n v := by
  rw [spinorRepresentation, CliffordAlgebra.lift_ι_apply]

/-- The image of the spinor representation is exactly the algebra generated by
the recursive split gamma matrices.  This is the native universal-property
statement supplied by `CliffordAlgebra.range_lift`; bijectivity is a stronger
finite-dimensional representation theorem and is not asserted here. -/
theorem spinorRepresentation_range (n : ℕ) :
    (spinorRepresentation n).range =
      Algebra.adjoin ℝ (Set.range (recursiveGamma n)) := by
  simpa [spinorRepresentation] using
    (CliffordAlgebra.range_lift
      (Q := SplitQuad n) (f := recursiveGamma n)
      (cond := fun v => recursiveGamma_sq n v))

theorem spinorRepresentation_surjective_iff_gamma_generate (n : ℕ) :
    Function.Surjective (spinorRepresentation n) ↔
      Algebra.adjoin ℝ (Set.range (recursiveGamma n)) = ⊤ := by
  rw [← AlgHom.range_eq_top, spinorRepresentation_range]

noncomputable def spinorMatrixBottStep (n : ℕ) :
    SpinorMatrix n →ₐ[ℝ] SpinorMatrix (n + 1) :=
  (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo (n + 1)).toAlgHom.comp
    ((InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n).comp
      (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n).symm.toAlgHom)

theorem spinorMatrixBottStep_injective (n : ℕ) :
    Function.Injective (spinorMatrixBottStep n) := by
  intro A B h
  apply (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n).symm.injective
  apply InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_injective n
  apply (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo (n + 1)).injective
  exact h

theorem recursiveGammaTensor_headPair (n : ℕ) (x : ℝ × ℝ) :
    recursiveGammaTensor (n + 1) (headPair n x) =
      appendAtom (1 : SplitGammaMatrix n)
        (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom) := by
  ext i j
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  simp [recursiveGammaTensor, headPair, appendAtom_apply]

theorem recursiveGammaTensor_tailLift (n : ℕ) (xs : SplitSpace n) :
    recursiveGammaTensor (n + 1) (tailLift n xs) =
      appendAtom (recursiveGammaTensor n xs) gradingAtom := by
  ext i j
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  simp [recursiveGammaTensor, tailLift, appendAtom_apply]

theorem spinorRepresentation_headFactor_ι (n : ℕ) (x : ℝ × ℝ) :
    spinorRepresentation (n + 1)
        (CliffordAlgebra.ι (SplitQuad (n + 1)) (headPair n x)) =
      (tensorMatrixEquivFinPowTwo (n + 1))
        (appendAtom (1 : SplitGammaMatrix n)
          (x.1 • gammaPlusAtom + x.2 • gammaMinusAtom)) := by
  rw [spinorRepresentation_ι, recursiveGamma, LinearMap.comp_apply,
    recursiveGammaTensor_headPair]
  rfl

theorem spinorRepresentation_tailFactor_ι (n : ℕ) (xs : SplitSpace n) :
    spinorRepresentation (n + 1)
        (CliffordAlgebra.ι (SplitQuad (n + 1)) (tailLift n xs)) =
      (tensorMatrixEquivFinPowTwo (n + 1))
        (appendAtom (recursiveGammaTensor n xs) gradingAtom) := by
  rw [spinorRepresentation_ι, recursiveGamma, LinearMap.comp_apply,
    recursiveGammaTensor_tailLift]
  rfl

/-- The canonical split-Clifford successor map sends a generator to the
tail-lifted generator at the next finite stage. -/
theorem incl_Cl_split_ι (n : ℕ) (xs : SplitSpace n) :
    incl_Cl_split n (CliffordAlgebra.ι (SplitQuad n) xs) =
      CliffordAlgebra.ι (SplitQuad (n + 1)) (tailLift n xs) := by
  simp [incl_Cl_split, InfoGeometry.Clifford.incl_Cl_split,
    InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordStep,
    InfoGeometry.Canonical.SplitCliffordTensorBridge.splitCliffordTensorStepEquiv,
    tailLift]
  rfl

/-- Generator-level compatibility of the canonical tower inclusion with the
recursive spinor representation. The successor action is the old gamma
operator tensored with `gradingAtom`, as prescribed by the Clifford recursion. -/
theorem spinorRepresentation_incl_ι (n : ℕ) (xs : SplitSpace n) :
    spinorRepresentation (n + 1)
        (incl_Cl_split n (CliffordAlgebra.ι (SplitQuad n) xs)) =
      (tensorMatrixEquivFinPowTwo (n + 1))
        (appendAtom (recursiveGammaTensor n xs) gradingAtom) := by
  rw [incl_Cl_split_ι]
  exact spinorRepresentation_tailFactor_ι n xs

abbrev InfiniteSplitClifford := SplitCliffordInfinity

theorem infiniteSplitClifford_has_finite_stage_representatives
    (z : InfiniteSplitClifford) :
    ∀ N : ℕ, ∃ n ≥ N, ∃ x : Cl_split n,
      DirectLimit.Module.of ℝ ℕ Cl_split
        (fun m n h => splitCliffordMap m n h) n x = z :=
  splitCliffordInfinity_unbounded_representatives z



end SpinorRep
