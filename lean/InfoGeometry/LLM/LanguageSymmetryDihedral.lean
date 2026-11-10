/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.LanguageSymmetryFourier
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Clifford.OperatorValuedJones
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RepresentationTheory.Irreducible

/-!
# Paired-character representations of the dihedral group

The native group `DihedralGroup N` acts on a genuine two-dimensional matrix
block. Its rotation eigenvalues are the opposite characters `χ x` and `χ (-x)`;
reflection exchanges these eigenspaces. Irreducibility requires an element at
which these values differ. The trivial and order-two characters are therefore
not silently included among irreducible blocks.

The finite Fourier block uses the convention `∑ g, f g • ρ (g⁻¹)`. Its entries
are related to the existing cyclic `kernelEigenvalue`. This constructs individual
blocks, not a classification or a Peter--Weyl/Plancherel theorem for all blocks.

The independent Peirce identities below retain the repository's operator-valued
square `J² = -V`; they do not assume every off-diagonal corner normalizes to `V=1`.
-/

noncomputable section

namespace InfoGeometry.LLM.LanguageSymmetry

open Matrix
open scoped BigOperators

section MatrixRepresentation

variable {N : ℕ} {R : Type*} [CommRing R]

/-- Opposite additive characters are the two rotation eigenvalues. -/
def pairedRotation (χ : AddChar (ZMod N) R) (x : ZMod N) : Matrix (Fin 2) (Fin 2) R :=
  !![χ x, 0; 0, χ (-x)]

@[simp] theorem pairedRotation_zero (χ : AddChar (ZMod N) R) :
    pairedRotation χ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairedRotation]

/-- The paired rotation matrices respect addition of the cyclic coordinate. -/
theorem pairedRotation_add (χ : AddChar (ZMod N) R) (x y : ZMod N) :
    pairedRotation χ (x + y) = pairedRotation χ x * pairedRotation χ y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedRotation, Matrix.mul_apply, Fin.sum_univ_two, χ.map_add_eq_mul,
      mul_comm]

/-- Reflection reverses the rotation parameter. -/
theorem pairedReflection_conjugates (χ : AddChar (ZMod N) R) (x : ZMod N) :
    InfoGeometry.Clifford.J_mat * pairedRotation χ x * InfoGeometry.Clifford.J_mat = pairedRotation χ (-x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedRotation, InfoGeometry.Clifford.J_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- A native matrix-valued representation of `DihedralGroup N`.
Mathlib's `sr x` convention is reflection followed by rotation. -/
def dihedralCharacterMatrix (χ : AddChar (ZMod N) R) :
    DihedralGroup N →* Matrix (Fin 2) (Fin 2) R where
  toFun
    | .r x => pairedRotation χ x
    | .sr x => InfoGeometry.Clifford.J_mat * pairedRotation χ x
  map_one' := pairedRotation_zero χ
  map_mul' := by
    intro g h
    cases g <;> cases h <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pairedRotation, InfoGeometry.Clifford.J_mat, Matrix.mul_apply, Fin.sum_univ_two,
        χ.map_add_eq_mul, sub_eq_add_neg, mul_comm]

@[simp] theorem dihedralCharacterMatrix_r (χ : AddChar (ZMod N) R) (x : ZMod N) :
    dihedralCharacterMatrix χ (.r x) = pairedRotation χ x := rfl

@[simp] theorem dihedralCharacterMatrix_sr (χ : AddChar (ZMod N) R) (x : ZMod N) :
    dihedralCharacterMatrix χ (.sr x) = InfoGeometry.Clifford.J_mat * pairedRotation χ x := rfl

/-- Opposite characters give conjugate full dihedral actions, not two unrelated blocks. -/
theorem dihedral_opposite_character_conjugates
    (χ : AddChar (ZMod N) R) (g : DihedralGroup N) :
    InfoGeometry.Clifford.J_mat * dihedralCharacterMatrix χ g * InfoGeometry.Clifford.J_mat =
      dihedralCharacterMatrix (-χ) g := by
  cases g <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [dihedralCharacterMatrix, pairedRotation, InfoGeometry.Clifford.J_mat,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The group rotation relation is preserved by the constructed homomorphism. -/
theorem dihedralCharacterMatrix_rotation_pow (χ : AddChar (ZMod N) R) :
    dihedralCharacterMatrix χ (.r 1) ^ N = 1 := by
  rw [← map_pow, DihedralGroup.r_one_pow_n, map_one]

/-- Every reflected rotation is an involution in the actual matrix action. -/
theorem dihedralCharacterMatrix_reflection_sq (χ : AddChar (ZMod N) R) (x : ZMod N) :
    dihedralCharacterMatrix χ (.sr x) * dihedralCharacterMatrix χ (.sr x) = 1 := by
  rw [← map_mul, DihedralGroup.sr_mul_self, map_one]

/-- The two-reflection product has the native dihedral subtraction order. -/
theorem dihedralCharacterMatrix_two_reflections
    (χ : AddChar (ZMod N) R) (x y : ZMod N) :
    dihedralCharacterMatrix χ (.sr x) * dihedralCharacterMatrix χ (.sr y) =
      pairedRotation χ (y - x) := by
  rw [← map_mul, DihedralGroup.sr_mul_sr, dihedralCharacterMatrix_r]

/-- Noncommutativity of reflection with a rotation has an exact spectral condition. -/
theorem pairedReflection_mul_ne_iff (χ : AddChar (ZMod N) R) (x : ZMod N) :
    InfoGeometry.Clifford.J_mat * pairedRotation χ x ≠
      pairedRotation χ x * InfoGeometry.Clifford.J_mat ↔
      χ x ≠ χ (-x) := by
  constructor
  · intro h hχ
    apply h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairedRotation, InfoGeometry.Clifford.J_mat, Matrix.mul_apply, Fin.sum_univ_two, hχ]
  · intro h hM
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0) hM
    exact h (by simpa [pairedRotation, InfoGeometry.Clifford.J_mat, Matrix.mul_apply,
      Fin.sum_univ_two] using he)

end MatrixRepresentation

section LinearRepresentation

variable {N : ℕ} {R : Type*} [Field R]

/-- The same matrices acting on column vectors as a native `Representation`. -/
def dihedralCharacterRepresentation (χ : AddChar (ZMod N) R) :
    Representation R (DihedralGroup N) (Fin 2 → R) where
  toFun g := (dihedralCharacterMatrix χ g).mulVecLin
  map_one' := by rw [map_one]; exact Matrix.mulVecLin_one
  map_mul' g h := by
    rw [map_mul, Matrix.mulVecLin_mul]
    rfl

@[simp] theorem dihedralCharacterRepresentation_rotation_apply
    (χ : AddChar (ZMod N) R) (x : ZMod N) (v : Fin 2 → R) :
    dihedralCharacterRepresentation χ (.r x) v = ![χ x * v 0, χ (-x) * v 1] := by
  ext i
  fin_cases i <;>
    simp [dihedralCharacterRepresentation, pairedRotation, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

@[simp] theorem dihedralCharacterRepresentation_reflection_apply
    (χ : AddChar (ZMod N) R) (v : Fin 2 → R) :
    dihedralCharacterRepresentation χ (.sr 0) v = ![v 1, v 0] := by
  ext i
  fin_cases i <;>
    simp [dihedralCharacterRepresentation, InfoGeometry.Clifford.J_mat, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

@[simp] theorem dihedralCharacterRepresentation_reflected_apply
    (χ : AddChar (ZMod N) R) (x : ZMod N) (v : Fin 2 → R) :
    dihedralCharacterRepresentation χ (.sr x) v = ![χ (-x) * v 1, χ x * v 0] := by
  ext i
  fin_cases i <;>
    simp [dihedralCharacterRepresentation, pairedRotation, InfoGeometry.Clifford.J_mat,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Distinct opposite characters make the two-dimensional representation
irreducible. The proof constructs both coordinate vectors in every nonzero
invariant subspace. -/
theorem dihedralCharacterRepresentation_irreducible
    (χ : AddChar (ZMod N) R) (hχ : ∃ x, χ x ≠ χ (-x)) :
    Representation.IsIrreducible (dihedralCharacterRepresentation χ) := by
  obtain ⟨x, hx⟩ := hχ
  let : Nontrivial (Subrepresentation (dihedralCharacterRepresentation χ)) :=
    ⟨⟨⊥, ⊤, fun h =>
      (bot_ne_top : (⊥ : Submodule R (Fin 2 → R)) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro U hU
  have hU' : U.toSubmodule ≠ ⊥ := by
    intro h
    exact hU (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hvne⟩ := U.toSubmodule.ne_bot_iff.mp hU'
  have e0_of_ne_zero (w : Fin 2 → R) (hw : w ∈ U.toSubmodule) (hw0 : w 0 ≠ 0) :
      ![1, 0] ∈ U.toSubmodule := by
    have hz : dihedralCharacterRepresentation χ (.r x) w - χ (-x) • w ∈ U.toSubmodule :=
      U.toSubmodule.sub_mem (U.apply_mem_toSubmodule (.r x) hw)
        (U.toSubmodule.smul_mem _ hw)
    have hd : χ x - χ (-x) ≠ 0 := sub_ne_zero.mpr hx
    have heq : ((χ x - χ (-x)) * w 0)⁻¹ •
        (dihedralCharacterRepresentation χ (.r x) w - χ (-x) • w) = ![1, 0] := by
      rw [dihedralCharacterRepresentation_rotation_apply]
      ext i
      fin_cases i
      · change ((χ x - χ (-x)) * w 0)⁻¹ *
          (χ x * w 0 - χ (-x) * w 0) = 1
        rw [← sub_mul, inv_mul_cancel₀ (mul_ne_zero hd hw0)]
      · change ((χ x - χ (-x)) * w 0)⁻¹ *
          (χ (-x) * w 1 - χ (-x) * w 1) = 0
        simp
    rw [← heq]
    exact U.toSubmodule.smul_mem _ hz
  have he0 : ![1, 0] ∈ U.toSubmodule := by
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro h
        apply hvne
        ext i
        fin_cases i <;> simp [hv0, h]
      have hf := U.apply_mem_toSubmodule (.sr 0) hv
      rw [dihedralCharacterRepresentation_reflection_apply] at hf
      exact e0_of_ne_zero ![v 1, v 0] hf (by simpa using hv1)
    · exact e0_of_ne_zero v hv hv0
  have he1 : ![0, 1] ∈ U.toSubmodule := by
    simpa using U.apply_mem_toSubmodule (.sr 0) he0
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro w _
  have hsum := U.toSubmodule.add_mem (U.toSubmodule.smul_mem (w 0) he0)
    (U.toSubmodule.smul_mem (w 1) he1)
  have hw : w 0 • ![1, 0] + w 1 • ![0, 1] = w := by
    ext i
    fin_cases i <;> simp
  rwa [hw] at hsum

/-- Self-inverse characters have an explicit proper invariant diagonal line. -/
theorem dihedralCharacterRepresentation_not_irreducible
    (χ : AddChar (ZMod N) R) (hχ : ∀ x, χ x = χ (-x)) :
    ¬ Representation.IsIrreducible (dihedralCharacterRepresentation χ) := by
  intro hirr
  let U : Subrepresentation (dihedralCharacterRepresentation χ) :=
    { toSubmodule :=
        { carrier := {v | v 0 = v 1}
          zero_mem' := rfl
          add_mem' := by
            intro v w hv hw
            change v 0 + w 0 = v 1 + w 1
            rw [hv, hw]
          smul_mem' := by
            intro c v hv
            change c * v 0 = c * v 1
            rw [hv] }
      apply_mem_toSubmodule := by
        intro g v hv
        change v 0 = v 1 at hv
        change dihedralCharacterRepresentation χ g v 0 =
          dihedralCharacterRepresentation χ g v 1
        cases g with
        | r x => simp only [dihedralCharacterRepresentation_rotation_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, hχ x, hv]
        | sr x => simp only [dihedralCharacterRepresentation_reflected_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, hχ x, hv] }
  let : Representation.IsIrreducible (dihedralCharacterRepresentation χ) := hirr
  rcases eq_bot_or_eq_top U with hU | hU
  · have hv : (![1, 1] : Fin 2 → R) ∈ U := rfl
    rw [hU] at hv
    have hz : (![1, 1] : Fin 2 → R) = 0 := (Submodule.mem_bot R).mp hv
    have hc := congrFun hz 0
    simp at hc
  · have hv : (![1, 0] : Fin 2 → R) ∈ U := by rw [hU]; trivial
    exact one_ne_zero hv

/-- The exact reducibility boundary is equality of the two opposite characters. -/
theorem dihedralCharacterRepresentation_irreducible_iff
    (χ : AddChar (ZMod N) R) :
    Representation.IsIrreducible (dihedralCharacterRepresentation χ) ↔
      ∃ x, χ x ≠ χ (-x) := by
  constructor
  · intro hirr
    by_contra! hχ
    exact dihedralCharacterRepresentation_not_irreducible χ hχ hirr
  · exact dihedralCharacterRepresentation_irreducible χ

end LinearRepresentation

section CyclicFrequencies

variable {N : ℕ} [NeZero N]

/-- For the native frequency indexing, exactly the non-self-opposite frequencies
give irreducible two-dimensional blocks. -/
theorem dihedral_frequency_irreducible_iff (k : ZMod N) :
    Representation.IsIrreducible
      (dihedralCharacterRepresentation (AddChar.zmodAddEquiv k)) ↔ k ≠ -k := by
  rw [dihedralCharacterRepresentation_irreducible_iff]
  constructor
  · rintro ⟨x, hx⟩ hk
    apply hx
    have hchar : AddChar.zmodAddEquiv k = -(AddChar.zmodAddEquiv k) := by
      rw [← map_neg, ← hk]
    simpa only [AddChar.neg_apply] using DFunLike.congr_fun hchar x
  · intro hk
    by_contra! heq
    apply hk
    apply AddChar.zmodAddEquiv.injective
    rw [map_neg]
    ext x
    exact heq x

/-- The fundamental block of the order-six dihedral group is a concrete
irreducible example; no identification with a permutation group is assumed. -/
theorem dihedral_three_fundamental_irreducible :
    Representation.IsIrreducible
      (dihedralCharacterRepresentation (AddChar.zmodAddEquiv (1 : ZMod 3))) :=
  (dihedral_frequency_irreducible_iff (1 : ZMod 3)).mpr (by decide)

/-- The same concrete block contains noncommuting rotation/reflection matrices. -/
theorem dihedral_three_fundamental_noncommuting :
    ∃ x : ZMod 3,
      InfoGeometry.Clifford.J_mat * pairedRotation (AddChar.zmodAddEquiv (1 : ZMod 3)) x ≠
        pairedRotation (AddChar.zmodAddEquiv (1 : ZMod 3)) x * InfoGeometry.Clifford.J_mat := by
  obtain ⟨x, hx⟩ := (dihedralCharacterRepresentation_irreducible_iff _).mp
    dihedral_three_fundamental_irreducible
  exact ⟨x, (pairedReflection_mul_ne_iff _ _).mpr hx⟩

end CyclicFrequencies

section VertexPermutation

/-- The native dihedral group permutes its cyclic vertex set. -/
def dihedralVertexPermutation (N : ℕ) : DihedralGroup N →* Equiv.Perm (ZMod N) where
  toFun
    | .r x => Equiv.addRight x
    | .sr x => (Equiv.addRight x).trans (Equiv.neg (ZMod N))
  map_one' := by
    ext t
    change t + (0 : ZMod N) = t
    exact add_zero t
  map_mul' := by
    intro g h
    cases g with
    | r x =>
      cases h with
      | r y =>
        ext t
        change t + (x + y) = (t + y) + x
        abel
      | sr y =>
        ext t
        change -(t + (y - x)) = -(t + y) + x
        abel
    | sr x =>
      cases h with
      | r y =>
        ext t
        change -(t + (x + y)) = -((t + y) + x)
        abel
      | sr y =>
        ext t
        change t + (y - x) = -(-(t + y) + x)
        abel

private theorem dihedralThree_rotation_ne_reflection (x y : ZMod 3) :
    dihedralVertexPermutation 3 (.r x) ≠ dihedralVertexPermutation 3 (.sr y) := by
  intro h
  have h0 := congrArg (fun e : Equiv.Perm (ZMod 3) => e 0) h
  have h1 := congrArg (fun e : Equiv.Perm (ZMod 3) => e 1) h
  change (0 : ZMod 3) + x = -((0 : ZMod 3) + y) at h0
  change (1 : ZMod 3) + x = -((1 : ZMod 3) + y) at h1
  simp only [zero_add] at h0
  have hshift : (1 : ZMod 3) + x = -1 + x := by
    calc
      1 + x = -(1 + y) := h1
      _ = -1 + (-y) := by abel
      _ = -1 + x := by rw [← h0]
  have hbad : (1 : ZMod 3) = -1 := add_right_cancel hshift
  exact (by decide : (1 : ZMod 3) ≠ -1) hbad

/-- The six dihedral elements act as six distinct permutations of three vertices. -/
theorem dihedralVertexPermutation_three_injective :
    Function.Injective (dihedralVertexPermutation 3) := by
  intro g h heq
  have h0 := congrArg (fun e : Equiv.Perm (ZMod 3) => e 0) heq
  cases g with
  | r x =>
    cases h with
    | r y =>
      change (0 : ZMod 3) + x = (0 : ZMod 3) + y at h0
      exact congrArg DihedralGroup.r (add_left_cancel h0)
    | sr y => exact (dihedralThree_rotation_ne_reflection x y heq).elim
  | sr x =>
    cases h with
    | r y => exact (dihedralThree_rotation_ne_reflection y x heq.symm).elim
    | sr y =>
      change -((0 : ZMod 3) + x) = -((0 : ZMod 3) + y) at h0
      exact congrArg DihedralGroup.sr (add_left_cancel (neg_injective h0))

/-- An actual group equivalence identifies `D₃` with the symmetric group of a
three-element set. -/
noncomputable def dihedralThreeEquivPerm : DihedralGroup 3 ≃* Equiv.Perm (ZMod 3) :=
  MulEquiv.ofBijective (dihedralVertexPermutation 3)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨dihedralVertexPermutation_three_injective, by
        norm_num [DihedralGroup.card, Fintype.card_perm, ZMod.card]⟩)


end VertexPermutation

section RealForm

open InfoGeometry.Clifford

variable {N : ℕ}

/-- The real form uses the repository's existing negative-square generator. -/
def realCharacterRotation (χ : AddChar (ZMod N) ℂ) (x : ZMod N) : Matrix (Fin 2) (Fin 2) ℝ :=
  (χ x).re • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (χ x).im • K_mat

theorem realCharacterRotation_entries (χ : AddChar (ZMod N) ℂ) (x : ZMod N) :
    realCharacterRotation χ x = !![(χ x).re, (χ x).im; -(χ x).im, (χ x).re] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realCharacterRotation, K_mat]

/-- In real coordinates the exact noncommutativity condition is a nonzero sine coefficient. -/
theorem realReflection_mul_ne_iff (χ : AddChar (ZMod N) ℂ) (x : ZMod N) :
    Gamma_mat * realCharacterRotation χ x ≠ realCharacterRotation χ x * Gamma_mat ↔
      (χ x).im ≠ 0 := by
  constructor
  · intro h him
    apply h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realCharacterRotation, K_mat, Gamma_mat, Matrix.mul_apply,
        Fin.sum_univ_two, him]
  · intro him hM
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hM
    simp [realCharacterRotation, K_mat, Gamma_mat, Matrix.mul_apply, Fin.sum_univ_two] at he
    exact him (by linarith)

variable [NeZero N]

/-- A concrete noncommuting block also exists over the real matrix carrier. -/
theorem dihedral_three_real_noncommuting :
    ∃ x : ZMod 3,
      Gamma_mat * realCharacterRotation (AddChar.zmodAddEquiv (1 : ZMod 3)) x ≠
        realCharacterRotation (AddChar.zmodAddEquiv (1 : ZMod 3)) x * Gamma_mat := by
  obtain ⟨x, hx⟩ := (dihedralCharacterRepresentation_irreducible_iff _).mp
    dihedral_three_fundamental_irreducible
  refine ⟨x, (realReflection_mul_ne_iff _ _).mpr ?_⟩
  intro him
  apply hx
  rw [AddChar.map_neg_eq_conj]
  apply Complex.ext
  · simp only [Complex.conj_re]
  · simp only [Complex.conj_im, him, neg_zero]

/-- A native real dihedral representation using the existing `Cl(1,1)` matrices. -/
def dihedralRealCharacterMatrix (χ : AddChar (ZMod N) ℂ) :
    DihedralGroup N →* Matrix (Fin 2) (Fin 2) ℝ where
  toFun
    | .r x => realCharacterRotation χ x
    | .sr x => Gamma_mat * realCharacterRotation χ x
  map_one' := by
    change realCharacterRotation χ 0 = 1
    simp [realCharacterRotation]
  map_mul' := by
    intro g h
    cases g <;> cases h <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [realCharacterRotation_entries, Gamma_mat, Matrix.mul_apply, Fin.sum_univ_two,
        χ.map_add_eq_mul, sub_eq_add_neg, χ.map_neg_eq_conj,
        Complex.mul_re, Complex.mul_im] <;> ring

/-- Columns are the two eigenvectors `(1,i)` and `(1,-i)` of `K_mat`. -/
def pairedToReal : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; Complex.I, -Complex.I]

/-- Explicit inverse of the change from paired characters to real coordinates. -/
def realToPaired : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, -Complex.I / 2; 1 / 2, Complex.I / 2]

theorem pairedToReal_mul_realToPaired : pairedToReal * realToPaired = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairedToReal, realToPaired, Matrix.mul_apply, Fin.sum_univ_two,
      div_eq_mul_inv]
  ring_nf
  norm_num [Complex.I_sq]

theorem realToPaired_mul_pairedToReal : realToPaired * pairedToReal = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairedToReal, realToPaired, Matrix.mul_apply, Fin.sum_univ_two,
      div_eq_mul_inv] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- An explicit invertible intertwiner identifies the paired complex block
with the complexification of the real `Cl(1,1)` matrix action. -/
theorem pairedToReal_intertwines (χ : AddChar (ZMod N) ℂ) (g : DihedralGroup N) :
    pairedToReal * dihedralCharacterMatrix χ g =
      (dihedralRealCharacterMatrix χ g).map Complex.ofReal * pairedToReal := by
  cases g <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [pairedToReal, dihedralCharacterMatrix, pairedRotation, InfoGeometry.Clifford.J_mat,
      dihedralRealCharacterMatrix, realCharacterRotation_entries, Gamma_mat,
      Matrix.mul_apply, Fin.sum_univ_two, χ.map_neg_eq_conj,
      Complex.mul_re, Complex.mul_im]

/-- The real action is obtained by a genuine similarity transformation. -/
theorem pairedToReal_conjugates (χ : AddChar (ZMod N) ℂ) (g : DihedralGroup N) :
    pairedToReal * dihedralCharacterMatrix χ g * realToPaired =
      (dihedralRealCharacterMatrix χ g).map Complex.ofReal := by
  rw [pairedToReal_intertwines, Matrix.mul_assoc, pairedToReal_mul_realToPaired,
    Matrix.mul_one]

/-- The real Fourier coefficient in the same inverse-argument convention. -/
def dihedralRealFourierBlock (χ : AddChar (ZMod N) ℂ) (f : DihedralGroup N → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ g, f g • dihedralRealCharacterMatrix χ g⁻¹

/-- The four Clifford channels are the even/odd coefficients of the rotation
and reflection restrictions. These are not the four literal Peirce corners. -/
theorem dihedralRealFourierBlock_channels
    (χ : AddChar (ZMod N) ℂ) (f : DihedralGroup N → ℝ) :
    dihedralRealFourierBlock χ f =
      reconstruct_jones
        (∑ x, f (.r x) * (χ x).re)
        (∑ x, f (.sr x) * (χ x).re)
        (∑ x, f (.sr x) * (χ x).im)
        (-(∑ x, f (.r x) * (χ x).im)) := by
  classical
  rw [jones_decomposition_eq]
  unfold dihedralRealFourierBlock
  rw [← Equiv.sum_comp DihedralGroup.equivSum.symm, Fintype.sum_sum_type]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [DihedralGroup.equivSum, dihedralRealCharacterMatrix,
      realCharacterRotation_entries, Gamma_mat, Matrix.sum_apply,
      χ.map_neg_eq_conj, Finset.sum_neg_distrib] <;> abel

end RealForm

section FourierBlock

variable {N : ℕ} [NeZero N]

/-- A finite matrix Fourier coefficient, using inverse group arguments. -/
def dihedralFourierBlock (χ : AddChar (ZMod N) ℂ) (f : DihedralGroup N → ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ g, f g • dihedralCharacterMatrix χ g⁻¹

/-- Matrix entries are the two opposite cyclic Fourier coefficients of the
rotation and reflection restrictions of `f`. -/
theorem dihedralFourierBlock_entries (χ : AddChar (ZMod N) ℂ) (f : DihedralGroup N → ℂ) :
    dihedralFourierBlock χ f =
      !![kernelEigenvalue (fun x => f (.r x)) χ,
         kernelEigenvalue (fun x => f (.sr x)) χ;
         kernelEigenvalue (fun x => f (.sr x)) (-χ),
         kernelEigenvalue (fun x => f (.r x)) (-χ)] := by
  classical
  unfold dihedralFourierBlock
  rw [← Equiv.sum_comp DihedralGroup.equivSum.symm, Fintype.sum_sum_type]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [DihedralGroup.equivSum, kernelEigenvalue, pairedRotation,
      InfoGeometry.Clifford.J_mat, Matrix.sum_apply, AddChar.neg_apply]

end FourierBlock

section PeirceRotor

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- The concrete matrix generators are the existing Peirce frame at the first
coordinate projector; its round-trip operator is genuinely normalized to one. -/
theorem matrix_dihedral_peirce_frame {R : Type*} [Ring R] :
    let P : Matrix (Fin 2) (Fin 2) R := Matrix.single 0 0 1
    P * P = P ∧
      invS P = InfoGeometry.Clifford.Gamma_mat ∧
      genPhi P InfoGeometry.Clifford.J_mat InfoGeometry.Clifford.J_mat =
        InfoGeometry.Clifford.J_mat ∧
      genJ P InfoGeometry.Clifford.J_mat InfoGeometry.Clifford.J_mat =
        InfoGeometry.Clifford.K_mat ∧
      genV P InfoGeometry.Clifford.J_mat InfoGeometry.Clifford.J_mat = 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [invS, genPhi, genJ, genV, anticomm, conePlus, coneMinus,
      InfoGeometry.Clifford.Gamma_mat, InfoGeometry.Clifford.J_mat,
      InfoGeometry.Clifford.K_mat, Matrix.single, Matrix.mul_apply, Fin.sum_univ_two]

variable {A R : Type*} [Ring A] [CommRing R] [Algebra R A]

/-- A central-coefficient rotor changes its odd sign under the existing Peirce grading. -/
theorem peirce_rotor_reflection (P X Y : A) (hP : P * P = P) (c s : R) :
    invS P * (c • (1 : A) + s • genJ P X Y) * invS P =
      c • (1 : A) - s • genJ P X Y := by
  peirce_nf hP

/-- The reflection--rotor commutator is an actual off-diagonal operator. -/
theorem peirce_rotor_commutator (P X Y : A) (hP : P * P = P) (c s : R) :
    comm (invS P) (c • (1 : A) + s • genJ P X Y) = (s + s) • genPhi P X Y := by
  simp only [add_smul]
  peirce_nf hP

/-- The square of a reflected rotor retains the operator-valued `V` factor. -/
theorem peirce_reflected_rotor_square (P X Y : A) (hP : P * P = P) (c s : R) :
    ((c • (1 : A) + s • genJ P X Y) * invS P) *
        ((c • (1 : A) + s • genJ P X Y) * invS P) =
      (c * c) • (1 : A) + (s * s) • genV P X Y := by
  have hJ := (archetype_A3_nilpotent_cones_and_tetraktys_table hP X Y).2.2.2.1
  calc
    _ = (c • (1 : A) + s • genJ P X Y) *
        (invS P * (c • (1 : A) + s • genJ P X Y) * invS P) := by
      simp only [mul_assoc]
    _ = (c • (1 : A) + s • genJ P X Y) *
        (c • (1 : A) - s • genJ P X Y) := by rw [peirce_rotor_reflection P X Y hP]
    _ = (c * c) • (1 : A) + (s * s) • genV P X Y := by
      simp only [add_mul, mul_sub, smul_mul_smul, one_mul, mul_one,
        hJ, smul_neg, mul_comm s c]
      abel

end PeirceRotor

end InfoGeometry.LLM.LanguageSymmetry
