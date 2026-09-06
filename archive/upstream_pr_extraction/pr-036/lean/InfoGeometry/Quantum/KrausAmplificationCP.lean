import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
import InfoGeometry.Modular.Choi

noncomputable section

namespace InfoGeometry.Quantum.KrausAmplification

open Matrix
open scoped ComplexOrder

variable {n r : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]

local notation "Mat" => Matrix n n ℂ
local notation "AmpMat" => Matrix (r × n) (r × n) ℂ

def blockK (V : Mat) : AmpMat :=
  fun a b => if a.1 = b.1 then V a.2 b.2 else 0

@[simp] theorem blockK_apply (V : Mat) (a b : r × n) :
    blockK (r := r) V a b = if a.1 = b.1 then V a.2 b.2 else 0 := rfl

def block (X : AmpMat) (p q : r) : Mat :=
  fun i j => X (p, i) (q, j)

@[simp] theorem block_apply (X : AmpMat) (p q : r) (i j : n) :
    block X p q i j = X (p, i) (q, j) := rfl

def amplification (E : Mat →ₗ[ℂ] Mat) : AmpMat →ₗ[ℂ] AmpMat where
  toFun X := fun a b => E (block X a.1 b.1) a.2 b.2
  map_add' X Y := by
    ext a b
    rw [show block (X + Y) a.1 b.1 = block X a.1 b.1 + block Y a.1 b.1 by ext i j; rfl, E.map_add]
    rfl
  map_smul' c X := by
    ext a b
    rw [show block (c • X) a.1 b.1 = c • block X a.1 b.1 by ext i j; rfl, E.map_smul]
    rfl

@[simp] theorem amplification_apply (E : Mat →ₗ[ℂ] Mat)
    (X : AmpMat) (a b : r × n) :
    amplification (r := r) E X a b = E (block X a.1 b.1) a.2 b.2 := rfl

def amplifiedKraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) (X : AmpMat) : AmpMat :=
  ∑ k, blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ

lemma sum_prod_collapse {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℂ) :
    (∑ z : α × β, f z) = ∑ a : α, ∑ b : β, f (a, b) :=
  Fintype.sum_prod_type f

theorem hblock (W : Mat) (X : AmpMat) (p q : r) (i j : n) :
    (blockK (r := r) W * X * (blockK (r := r) W)ᴴ) (p, i) (q, j) =
      (W * block X p q * star W) i j := by
  dsimp [Matrix.mul_apply, Matrix.conjTranspose_apply, blockK, block, Matrix.star_apply]
  simp_rw [sum_prod_collapse]
  have h_inner (a : r) (x : n) :
      (∑ b : r, ∑ y : n, (if p = b then W i y else 0) * X (b, y) (a, x)) =
      ∑ y : n, W i y * X (p, y) (a, x) := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hp; exact (hp (Finset.mem_univ p)).elim
  simp_rw [h_inner]
  have h_outer :
      (∑ a : r, ∑ x : n, (∑ y : n, W i y * X (p, y) (a, x)) * star (if q = a then W j x else 0)) =
      ∑ x : n, (∑ y : n, W i y * X (p, y) (q, x)) * star (W j x) := by
    rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      have hqb : q ≠ b := Ne.symm hb
      have : ∀ x : n, star (if q = b then W j x else 0) = 0 := by intro x; simp [hqb]
      simp_rw [this, mul_zero, Finset.sum_const_zero]
    · intro hq; exact (hq (Finset.mem_univ q)).elim
  exact h_outer

theorem amplification_krausChannel_eq_amplifiedKraus
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) (X : AmpMat) :
    amplification (r := r)
        (InfoGeometry.Modular.Choi.krausChannel V) X =
      amplifiedKraus (r := r) V X := by
  ext ⟨p, i⟩ ⟨q, j⟩
  have h_lhs : amplification (r := r) (InfoGeometry.Modular.Choi.krausChannel V) X (p, i) (q, j) =
      ∑ k : ι, (V k * block X p q * star (V k)) i j := by
    have h1a : (∑ k : ι, V k * block X p q * star (V k)) i =
        ∑ k : ι, (V k * block X p q * star (V k)) i := Finset.sum_apply i Finset.univ (fun (k : ι) => (V k * block X p q * star (V k)))
    have h1b : (∑ k : ι, (V k * block X p q * star (V k)) i) j =
        ∑ k : ι, (V k * block X p q * star (V k)) i j := Finset.sum_apply j Finset.univ (fun (k : ι) => (V k * block X p q * star (V k)) i)
    exact Eq.trans (congr_fun h1a j) h1b
  have h2 : (∑ k : ι, blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ) (p, i) (q, j) =
      ∑ k : ι, (blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ) (p, i) (q, j) := by
    have h2a : (∑ k : ι, blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ) (p, i) =
        ∑ k : ι, (blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ) (p, i) := Finset.sum_apply (p, i) Finset.univ (fun (k : ι) => (blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ))
    have h2b : (∑ k : ι, (blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ) (p, i)) (q, j) =
        ∑ k : ι, (blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ) (p, i) (q, j) := Finset.sum_apply (q, j) Finset.univ (fun (k : ι) => (blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ) (p, i))
    exact Eq.trans (congr_fun h2a (q, j)) h2b
  rw [h_lhs]
  change (∑ k : ι, (V k * block X p q * star (V k)) i j) =
    (∑ k : ι, blockK (r := r) (V k) * X *
      (blockK (r := r) (V k))ᴴ) (p, i) (q, j)
  rw [h2]
  apply Finset.sum_congr rfl
  intro k _
  exact (hblock (V k) X p q i j).symm

theorem amplifiedKraus_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) (X : AmpMat) (hX : X.PosSemidef) :
    (amplifiedKraus (r := r) V X).PosSemidef := by
  unfold amplifiedKraus
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using (Matrix.PosSemidef.zero : (0 : AmpMat).PosSemidef)
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact Matrix.PosSemidef.add
        (Matrix.PosSemidef.mul_mul_conjTranspose_same hX _) ih

/-! The preceding identity transports positivity to every finite matrix
amplification of a Kraus map.  Together with the Choi certificate in the
`Choi` owner, this is the concrete finite-dimensional CP direction. -/

theorem amplification_krausChannel_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) (X : AmpMat) (hX : X.PosSemidef) :
    (amplification (r := r)
      (InfoGeometry.Modular.Choi.krausChannel V) X).PosSemidef := by
  rw [amplification_krausChannel_eq_amplifiedKraus V X]
  exact amplifiedKraus_posSemidef V X hX

theorem krausChannel_choi_and_amplification
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) (X : AmpMat) (hX : X.PosSemidef) :
    (InfoGeometry.Modular.Choi.choiMatrix
      (InfoGeometry.Modular.Choi.krausChannel V)).PosSemidef ∧
      (amplification (r := r)
        (InfoGeometry.Modular.Choi.krausChannel V) X).PosSemidef := by
  constructor
  · exact InfoGeometry.Modular.Choi.krausChannel_choi_posSemidef V
  · exact amplification_krausChannel_posSemidef V X hX

end InfoGeometry.Quantum.KrausAmplification

end noncomputable section
