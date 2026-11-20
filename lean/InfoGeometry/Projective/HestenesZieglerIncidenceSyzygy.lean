/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Hestenes–Ziegler §5.1: the four-space incidence syzygy

Source: D. Hestenes and R. Ziegler, *Projective Geometry with Clifford Algebra*,
Acta Appl. Math. 23 (1991) 25–63, §5.1, Eq. (5.4).

The bracket `[·]` is the repository's volume coordinate `volCoord b` applied to
an ordered exterior 4-frame, which equals the ordered determinant `b.det`.
With this convention the kernel-checked identity is

  `[abcp] q − [abcq] p + ([pqbc] a + [pqca] b + [pqab] c) = 0`.

The printed Eq. (5.4) states `[abcp] q − [abcq] p = [pqab] c + [pqca] b + [pqbc] a`
with a plus sign on the right.  Under the ordered-determinant bracket convention
that printed sign is inconsistent: a concrete counterexample in `ℝ⁴` is included
below.  This is a convention audit of the printed equation, not a claim about
every bracket convention in the paper.

The proof is the Laplace expansion of a `5 × 5` determinant with a repeated
coordinate row; no metric, duality witness, or regressive-product assumption is
used.
-/

noncomputable section

namespace InfoGeometry.Projective.HestenesZieglerIncidenceSyzygy

open InfoGeometry.Projective.ExteriorRegressive
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The five-term Grassmann syzygy in a four-dimensional space: for any five
vectors, the alternating sum of (4-bracket of the complementary frame) times
the omitted vector vanishes.  Proved by Laplace expansion along a duplicated
coordinate row of a `5 × 5` matrix. -/
theorem det_syzygy (b : Module.Basis (Fin 4) K V) (v : Fin 5 → V) :
    ∑ k : Fin 5, ((-1 : K) ^ (k : ℕ) * b.det (v ∘ Fin.succAbove k)) • v k = 0 := by
  apply b.ext_elem
  intro j
  have hcoord : b.repr (∑ k : Fin 5,
      ((-1 : K) ^ (k : ℕ) * b.det (v ∘ Fin.succAbove k)) • v k) j
      = ∑ k : Fin 5, ((-1 : K) ^ (k : ℕ) * b.det (v ∘ Fin.succAbove k)) * b.repr (v k) j := by
    simp [map_sum, map_smul]
  rw [hcoord, map_zero, Finsupp.zero_apply]
  -- The 5×5 matrix whose row 0 duplicates coordinate row j.
  let M : Matrix (Fin 5) (Fin 5) K :=
    Matrix.of (Fin.cons (fun k => b.repr (v k) j) (fun i k => b.repr (v k) i))
  have hM0 : ∀ k, M 0 k = b.repr (v k) j := fun _ => rfl
  have hMsucc : ∀ (i : Fin 4) (k), M i.succ k = b.repr (v k) i := fun _ _ => rfl
  have hdet0 : M.det = 0 := by
    exact Matrix.det_zero_of_row_eq (Fin.succ_ne_zero j) rfl
  have hminor : ∀ k : Fin 5,
      (M.submatrix Fin.succ (Fin.succAbove k)).det = b.det (v ∘ Fin.succAbove k) := by
    intro k
    rw [Module.Basis.det_apply]
    apply congrArg Matrix.det
    ext i l
    rw [Matrix.submatrix_apply, hMsucc, Module.Basis.toMatrix_apply]
    rfl
  rw [Matrix.det_succ_row_zero] at hdet0
  simp only [hM0, hminor] at hdet0
  rw [← hdet0]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The volume-coordinate bracket of an ordered 4-frame is its ordered
determinant in the basis `b`. -/
theorem volCoord_ιMulti_four (b : Module.Basis (Fin 4) K V) (w : Fin 4 → V) :
    volCoord b (ExteriorAlgebra.ιMulti K 4 w) = b.det w := by
  rw [ιMulti_eq_det_smul_volume b w, map_smul,
    show b.ExteriorAlgebra Finset.univ = volume b from rfl,
    volCoord_volume, smul_eq_mul, mul_one]

/-- The double transposition `(2,3,0,1)` of `Fin 4`, an even permutation. -/
def σPlus : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- The odd permutation `(3,2,0,1)` of `Fin 4`. -/
def σMinus : Equiv.Perm (Fin 4) := σPlus * Equiv.swap 0 1

theorem σPlus_sign : σPlus.sign = 1 := by
  simp [σPlus, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 2 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 4) ≠ 3 by decide)]

theorem σMinus_sign : σMinus.sign = -1 := by
  simp [σMinus, σPlus_sign, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 1 by decide)]

/-- **Hestenes–Ziegler §5.1, Eq. (5.4), corrected sign.**  With the bracket
`[wxyz] = volCoord b (ι w ∧ ι x ∧ ι y ∧ ι z)` (the ordered determinant), the
point–line/line–plane incidence expansions satisfy

  `[abcp] q − [abcq] p + ([pqbc] a + [pqca] b + [pqab] c) = 0`.

Equivalently `[abcp] q − [abcq] p = −([pqab] c + [pqca] b + [pqbc] a)`.  The
printed equation carries the opposite sign on the right-hand side under this
bracket convention; see the counterexample below. -/
theorem hz_5_4_incidence_syzygy (b : Module.Basis (Fin 4) K V) (a b₁ c p q : V) :
    volCoord b (ExteriorAlgebra.ιMulti K 4 ![a, b₁, c, p]) • q
      - volCoord b (ExteriorAlgebra.ιMulti K 4 ![a, b₁, c, q]) • p
      + (volCoord b (ExteriorAlgebra.ιMulti K 4 ![p, q, b₁, c]) • a
        + volCoord b (ExteriorAlgebra.ιMulti K 4 ![p, q, c, a]) • b₁
        + volCoord b (ExteriorAlgebra.ιMulti K 4 ![p, q, a, b₁]) • c) = 0 := by
  simp only [volCoord_ιMulti_four]
  -- Frame reindexings for the complementary minors.
  have e0 : (![a, b₁, c, p, q] : Fin 5 → V) ∘ Fin.succAbove 0 = ![b₁, c, p, q] := by
    funext i; fin_cases i <;> rfl
  have e1 : (![a, b₁, c, p, q] : Fin 5 → V) ∘ Fin.succAbove 1 = ![a, c, p, q] := by
    funext i; fin_cases i <;> rfl
  have e2 : (![a, b₁, c, p, q] : Fin 5 → V) ∘ Fin.succAbove 2 = ![a, b₁, p, q] := by
    funext i; fin_cases i <;> rfl
  have e3 : (![a, b₁, c, p, q] : Fin 5 → V) ∘ Fin.succAbove 3 = ![a, b₁, c, q] := by
    funext i; fin_cases i <;> rfl
  have e4 : (![a, b₁, c, p, q] : Fin 5 → V) ∘ Fin.succAbove 4 = ![a, b₁, c, p] := by
    funext i; fin_cases i <;> rfl
  -- Even/odd reorderings into the paper's `pq`-first order.
  have r0 : b.det ![b₁, c, p, q] = b.det ![p, q, b₁, c] := by
    have hf : (![b₁, c, p, q] : Fin 4 → V) = ![p, q, b₁, c] ∘ σPlus := by
      funext i; fin_cases i <;> rfl
    rw [hf, AlternatingMap.map_perm, σPlus_sign, one_smul]
  have r1 : b.det ![a, c, p, q] = -b.det ![p, q, c, a] := by
    have hf : (![a, c, p, q] : Fin 4 → V) = ![p, q, c, a] ∘ σMinus := by
      funext i; fin_cases i <;> rfl
    rw [hf, AlternatingMap.map_perm, σMinus_sign]
    simp
  have r2 : b.det ![a, b₁, p, q] = b.det ![p, q, a, b₁] := by
    have hf : (![a, b₁, p, q] : Fin 4 → V) = ![p, q, a, b₁] ∘ σPlus := by
      funext i; fin_cases i <;> rfl
    rw [hf, AlternatingMap.map_perm, σPlus_sign, one_smul]
  have hsyz := det_syzygy b ![a, b₁, c, p, q]
  rw [Fin.sum_univ_five, e0, e1, e2, e3, e4, r0, r1, r2] at hsyz
  norm_num at hsyz
  -- `hsyz` is now the target identity up to additive rearrangement.
  have hgoal : b.det ![a, b₁, c, p] • q - b.det ![a, b₁, c, q] • p
      + (b.det ![p, q, b₁, c] • a + b.det ![p, q, c, a] • b₁
        + b.det ![p, q, a, b₁] • c)
      = ∑ k : Fin 5, ((-1 : K) ^ (k : ℕ) * b.det (![a, b₁, c, p, q] ∘ Fin.succAbove k)) •
          (![a, b₁, c, p, q] k) := by
    rw [Fin.sum_univ_five, e0, e1, e2, e3, e4, r0, r1, r2]
    norm_num
    module
  rw [hgoal, det_syzygy]

/-- **Counterexample to the printed sign of Eq. (5.4).**  In `ℝ⁴` with the
standard basis and `a = e₀, b = e₁, c = e₂, p = e₃, q = e₁`, the left side
`[abcp] q − [abcq] p` is `e₁` while the printed right side
`[pqab] c + [pqca] b + [pqbc] a` is `−e₁`. -/
theorem hz_5_4_printed_sign_counterexample :
    let b := Pi.basisFun ℝ (Fin 4)
    let a : Fin 4 → ℝ := ![1, 0, 0, 0]
    let b₁ : Fin 4 → ℝ := ![0, 1, 0, 0]
    let c : Fin 4 → ℝ := ![0, 0, 1, 0]
    let p : Fin 4 → ℝ := ![0, 0, 0, 1]
    let q : Fin 4 → ℝ := ![0, 1, 0, 0]
    b.det ![a, b₁, c, p] • q - b.det ![a, b₁, c, q] • p ≠
      b.det ![p, q, a, b₁] • c + b.det ![p, q, c, a] • b₁ + b.det ![p, q, b₁, c] • a := by
  intro b a b₁ c p q h
  have hb : ∀ i : Fin 4, b i = (![a, b₁, c, p] : Fin 4 → Fin 4 → ℝ) i := by
    intro i
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [b, a, b₁, c, p, Pi.basisFun_apply]
  have hd1 : b.det ![a, b₁, c, p] = 1 := by
    have hf : (![a, b₁, c, p] : Fin 4 → Fin 4 → ℝ) = fun i => b i := funext (fun i => (hb i).symm)
    rw [hf, Module.Basis.det_self]
  have hd2 : b.det ![a, b₁, c, q] = 0 :=
    (b.det).map_eq_zero_of_eq _ (i := 1) (j := 3) rfl (by decide)
  have hd3 : b.det ![p, q, a, b₁] = 0 :=
    (b.det).map_eq_zero_of_eq _ (i := 1) (j := 3) rfl (by decide)
  have hd4 : b.det ![p, q, b₁, c] = 0 :=
    (b.det).map_eq_zero_of_eq _ (i := 1) (j := 2) rfl (by decide)
  have hd5 : b.det ![p, q, c, a] = -1 := by
    have hf : (![p, q, c, a] : Fin 4 → Fin 4 → ℝ)
        = (fun i => b i) ∘ Equiv.swap (0 : Fin 4) 3 := by
      funext i
      fin_cases i <;> ext j <;> fin_cases j <;>
        simp (config := {decide := true}) [b, a, c, p, q, Pi.basisFun_apply,
          Equiv.swap_apply_def]
    rw [hf, AlternatingMap.map_perm,
      Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 3 by decide)]
    simp [Module.Basis.det_self]
  have h1 := congrFun h 1
  simp only [hd1, hd2, hd3, hd4, hd5, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul, q, b₁, p, Matrix.cons_val_one] at h1
  norm_num at h1

end InfoGeometry.Projective.HestenesZieglerIncidenceSyzygy
