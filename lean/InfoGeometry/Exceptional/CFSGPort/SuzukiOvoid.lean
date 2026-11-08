/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
module

import InfoGeometry.Algebra.FiniteMatrixNoncommutativity
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.IsPerfect
public import InfoGeometry.Exceptional.CFSGPort.ExceptionalCatalog

public noncomputable section

open scoped LinearAlgebra.Projectivization
open scoped Pointwise
open scoped commutatorElement

namespace InfoGeometry.Exceptional.CFSGPort.Suzuki

open InfoGeometry.Exceptional.CFSGPort.Chevalley

variable {K : Type} [Field K]

/-- The distinguished point at infinity in the Suzuki projective ovoid. -/
@[expose] def ovoidInfinity : ℙ K (Fin 4 → K) :=
  Projectivization.mk K ![1, 0, 0, 0] (by simp)

/-- The normalized finite-point chart of the Suzuki projective ovoid. -/
@[expose] def ovoidPoint (pi : K ≃+* K) (x y : K) : ℙ K (Fin 4 → K) :=
  Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)

/-- The finite ovoid chart's first coordinate is the Suzuki norm coordinate
from the external lower-root presentation, with the same two field
parameters. This is the coordinate identity needed to transport its ovoid
kernel equations through the local projective chart. -/
theorem ovoidPoint_vector_eq_suzukiN (a : ℕ) (pi : K ≃+* K)
    (hpi : ∀ z : K, pi z = z ^ (2 ^ (a + 1))) (x y : K) :
    (![x * y + pi x * x ^ 2 + pi y, y, x, 1] : Fin 4 → K) =
      ![suzukiN a x y, y, x, 1] := by
  have hpow (z : K) : z ^ (2 ^ (a + 1) + 2) = pi z * z ^ 2 := by
    rw [pow_add, hpi]
  funext i
  fin_cases i <;> simp [suzukiN, hpow, hpi] <;> ring

/-- The Suzuki ovoid carrier in projective three-space. -/
@[expose] def ovoid (pi : K ≃+* K) : Set (ℙ K (Fin 4 → K)) :=
  {ovoidInfinity} ∪ Set.range fun z : K × K => ovoidPoint pi z.1 z.2

/-- A general-linear operator fixing a projective point represented by a
nonzero vector acts on that vector by a field scalar. This is the local
projectivization step needed to identify the kernel of the Suzuki ovoid
action before using the explicit ovoid coordinates. -/
theorem projective_fixed_vector_is_eigenvector
    (A : Matrix.GeneralLinearGroup (Fin 4) K) (w : Fin 4 → K) (hw : w ≠ 0)
    (hfix : (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv •
      Projectivization.mk K w hw = Projectivization.mk K w hw) :
    ∃ k : K, ∀ i,
      (A : Matrix (Fin 4) (Fin 4) K) i 0 * w 0 +
        (A : Matrix (Fin 4) (Fin 4) K) i 1 * w 1 +
        (A : Matrix (Fin 4) (Fin 4) K) i 2 * w 2 +
        (A : Matrix (Fin 4) (Fin 4) K) i 3 * w 3 = k * w i := by
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hfix
  obtain ⟨k, hk⟩ := hfix
  refine ⟨k, fun i => ?_⟩
  have hi := congrFun hk i
  change (k : K) * w i =
    Matrix.mulVec (A : Matrix (Fin 4) (Fin 4) K) w i at hi
  rw [hi, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- In a Suzuki field of positive rank, the defining Frobenius power is not
the identity map. Otherwise every field element would be `0` or `1`, contrary
to the prescribed field cardinality. -/
theorem existsSuzukiThetaNotFixed [Finite K] (a : ℕ) (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x : K, x ^ 2 ^ (a + 1) ≠ x := by
  obtain ⟨_, _, hθθ⟩ := suzukiFrobData (a := a) hK
  by_contra h
  push Not at h
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := fun x => by
    have hx : x * (x - 1) = 0 := by
      have hsq : x ^ 2 = x := by rw [← hθθ x, h x, h x]
      linear_combination hsq
    rcases mul_eq_zero.mp hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (sub_eq_zero.mp hx)
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
    intro x
    rcases h01 x with rfl | rfl
    · exact ⟨false, by simp⟩
    · exact ⟨true, by simp⟩
  have hcard : Nat.card K ≤ 2 := by
    simpa using Nat.card_le_card_of_surjective _ hsurj
  have h8 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The external Suzuki scalar-kernel elimination uses a nonzero Frobenius
parameter, its difference from one, and its difference from its twisted
power. All three nonvanishing facts follow from the local witness above. -/
theorem existsSuzukiKernelParameter [Finite K] (a : ℕ) (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x : K, x ≠ 0 ∧ x - 1 ≠ 0 ∧ x - x ^ 2 ^ (a + 1) ≠ 0 := by
  obtain ⟨x, hx⟩ := existsSuzukiThetaNotFixed a ha hK
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hx1 : x - 1 ≠ 0 := by
    intro h
    have hxEq : x = 1 := sub_eq_zero.mp h
    subst x
    exact hx (by simp)
  have hxtheta : x - x ^ 2 ^ (a + 1) ≠ 0 := by
    intro h
    exact hx (sub_eq_zero.mp h).symm
  exact ⟨x, hx0, hx1, hxtheta⟩

/-- The Suzuki norm polynomial vanishes only at the zero pair over the
standard finite Suzuki field. This is the local port of the external
`suzuki_norm_nonzero` input used to make the ovoid Weyl action unconditional. -/
theorem suzukiNorm_eq_zero_iff [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) :
    suzukiN a u v = 0 ↔ u = 0 ∧ v = 0 := by
  obtain ⟨hchar, hadd, hθθ⟩ := suzukiFrobData (a := a) hK
  have h2 : (2 : K) = 0 := hchar
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  constructor
  · intro hN
    by_cases hu : u = 0
    · subst hu
      refine ⟨rfl, ?_⟩
      rw [suzukiN, zero_pow (by positivity), zero_mul, zero_add, zero_add] at hN
      exact pow_eq_zero_iff hθ0 |>.1 hN
    · exfalso
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let t := v / u ^ (2 ^ (a + 1) + 1)
      have hu' : u ^ (2 ^ (a + 1) + 1) ≠ 0 := pow_ne_zero _ hu
      have hv : v = u ^ (2 ^ (a + 1) + 1) * t := by
        dsimp [t]
        rw [mul_div_cancel₀ _ hu']
      have huu : u ^ (2 ^ (a + 1) * 2 ^ (a + 1)) = u ^ 2 := by
        rw [pow_mul, hθθ]
      have e1 : (u ^ (2 ^ (a + 1) + 1) * t) ^ 2 ^ (a + 1) =
          u ^ (2 ^ (a + 1) + 2) * t ^ 2 ^ (a + 1) := by
        rw [mul_pow, ← pow_mul, add_mul, one_mul, pow_add, huu]
        ring
      have hkey : suzukiN a u v =
          u ^ (2 ^ (a + 1) + 2) * (1 + t + t ^ 2 ^ (a + 1)) := by
        rw [suzukiN, hv, e1]
        ring
      rw [hkey] at hN
      have h3 : 1 + t + t ^ 2 ^ (a + 1) = 0 :=
        (mul_eq_zero.mp hN).resolve_left (pow_ne_zero _ hu)
      have htθ : t ^ 2 ^ (a + 1) = t + 1 := by
        linear_combination h3 - h2 * (t + 1)
      have htt : t ^ 2 = t := by
        rw [← hθθ t, htθ, hadd, htθ, one_pow]
        linear_combination h2
      have h01 : t = 0 ∨ t = 1 := by
        have hfactor : t * (t - 1) = 0 := by linear_combination htt
        rcases mul_eq_zero.mp hfactor with ht | ht
        · exact Or.inl ht
        · exact Or.inr (sub_eq_zero.mp ht)
      rcases h01 with ht | ht
      · rw [ht, zero_pow hθ0, add_zero, add_zero] at h3
        exact one_ne_zero h3
      · rw [ht, one_pow] at h3
        have hone : (1 : K) = 0 := by linear_combination h3 - h2
        exact one_ne_zero hone
  · rintro ⟨rfl, rfl⟩
    rw [suzukiN, zero_pow (by positivity), zero_pow hθ0, mul_zero,
      add_zero, add_zero]

/-- The coordinate norm in the projective ovoid agrees with the Suzuki
parameter polynomial. -/
theorem ovoidNorm_eq_suzukiN (a : ℕ) (pi : K ≃+* K)
    (hpi_formula : ∀ z : K, pi z = z ^ (2 ^ (a + 1))) (u v : K) :
    u * v + pi u * u ^ 2 + pi v = suzukiN a u v := by
  rw [hpi_formula u, hpi_formula v, suzukiN, pow_add]
  ring

/-- The local Suzuki norm-zero hypothesis required by the projective ovoid
action follows from the finite Suzuki field axioms. -/
theorem ovoidNorm_eq_zero_only_at_origin [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (pi : K ≃+* K)
    (hpi_formula : ∀ z : K, pi z = z ^ (2 ^ (a + 1))) :
    ∀ x y : K, x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  have hnorm : suzukiN a x y = 0 := by
    rw [← ovoidNorm_eq_suzukiN a pi hpi_formula x y]
    exact h
  exact (suzukiNorm_eq_zero_iff a hK x y).mp hnorm

/-- The normalized finite-point chart is injective: the last projective
coordinate fixes its scalar, and the next two coordinates recover the pair. -/
theorem ovoidPoint_injective (pi : K ≃+* K) :
    Function.Injective (fun z : K × K => ovoidPoint pi z.1 z.2) := by
  intro z w hzw
  change Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1] _ =
    Projectivization.mk K
      ![w.1 * w.2 + pi w.1 * w.1 ^ 2 + pi w.2, w.2, w.1, 1] _ at hzw
  rw [Projectivization.mk_eq_mk_iff] at hzw
  rcases hzw with ⟨c, hc⟩
  have hc_one : (c : K) = 1 := by
    have hc3 := congrFun hc (3 : Fin 4)
    simpa [Units.smul_def] using hc3
  apply Prod.ext
  · have hc2 := congrFun hc (2 : Fin 4)
    simpa [Units.smul_def, hc_one] using hc2.symm
  · have hc1 := congrFun hc (1 : Fin 4)
    simpa [Units.smul_def, hc_one] using hc1.symm

/-- The distinguished point at infinity is not in the finite-point chart. -/
theorem ovoidInfinity_not_mem_range (pi : K ≃+* K) :
    ovoidInfinity (K := K) ∉ Set.range (fun z : K × K => ovoidPoint pi z.1 z.2) := by
  rintro ⟨z, hz⟩
  change Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1] _ =
    Projectivization.mk K ![1, 0, 0, 0] _ at hz
  rw [Projectivization.mk_eq_mk_iff] at hz
  rcases hz with ⟨c, hc⟩
  have hc_zero : (c : K) = 0 := by
    have hc3 := congrFun hc (3 : Fin 4)
    simp at hc3
  exact c.ne_zero hc_zero

/-- The finite Suzuki ovoid carrier has cardinality `|K|^2 + 1`. -/
theorem ovoid_card (pi : K ≃+* K) [Finite K] :
    Nat.card {z // z ∈ ovoid pi} = Nat.card K ^ 2 + 1 := by
  let toO : Option (K × K) → {z // z ∈ ovoid pi}
    | none => ⟨ovoidInfinity (K := K), Or.inl (Set.mem_singleton _)⟩
    | some z => ⟨ovoidPoint pi z.1 z.2, Or.inr ⟨z, rfl⟩⟩
  have htoO_inj : Function.Injective toO := by
    intro u v huv
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some v =>
        exfalso
        exact ovoidInfinity_not_mem_range pi ⟨v, (congrArg Subtype.val huv).symm⟩
    | some u =>
      cases v with
      | none =>
        exfalso
        exact ovoidInfinity_not_mem_range pi ⟨u, congrArg Subtype.val huv⟩
      | some v =>
        exact congrArg Option.some (ovoidPoint_injective pi (congrArg Subtype.val huv))
  have htoO_surj : Function.Surjective toO := by
    intro z
    rcases z with ⟨z, hz⟩
    change z ∈ {ovoidInfinity} ∪ Set.range (fun z : K × K => ovoidPoint pi z.1 z.2) at hz
    rcases hz with hz | ⟨w, hw⟩
    · have hz_eq : z = ovoidInfinity (K := K) := by simpa using hz
      subst z
      exact ⟨none, rfl⟩
    · subst z
      exact ⟨some w, rfl⟩
  let e : Option (K × K) ≃ {z // z ∈ ovoid pi} :=
    Equiv.ofBijective toO ⟨htoO_inj, htoO_surj⟩
  calc
    Nat.card {z // z ∈ ovoid pi} = Nat.card (Option (K × K)) :=
      Nat.card_congr e.symm
    _ = Nat.card (K × K) + 1 := Finite.card_option
    _ = Nat.card K * Nat.card K + 1 := by rw [Nat.card_prod]
    _ = Nat.card K ^ 2 + 1 := by rw [pow_two]

/-- The upper-root Suzuki generator as an invertible linear operator. Its
matrix is the transpose presentation of the locally owned lower-root matrix. -/
@[expose] def upperRootOperator (a : ℕ) (u v : K) : Matrix.GeneralLinearGroup (Fin 4) K :=
  suzukiSGL a u v

/-- The antidiagonal Suzuki Weyl matrix on the four-dimensional carrier. -/
@[expose] def suzukiWeylMatrix : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if i.val + j.val = 3 then 1 else 0

/-- The antidiagonal Weyl generator as an invertible linear operator. -/
@[expose] def suzukiWeylOperator : Matrix.GeneralLinearGroup (Fin 4) K :=
  { val := suzukiWeylMatrix
    inv := suzukiWeylMatrix
    val_inv := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [suzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]
    inv_val := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [suzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] }

/-- Every Suzuki root operator has determinant one. The lower-root
presentation is triangular with unit diagonal, and transposition preserves
the determinant. -/
theorem upperRootOperator_det (a : ℕ) (u v : K) :
    (upperRootOperator a u v).det = 1 := by
  apply Units.ext
  have htri : (Chevalley.suzukiS a u v).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Chevalley.suzukiS, Chevalley.suzukiN]
  change (Chevalley.suzukiS a u v).transpose.det = 1
  rw [Matrix.det_transpose, Matrix.det_of_isLowerTriangular _ htri]
  simp [Chevalley.suzukiS, Fin.prod_univ_four]

/-- The antidiagonal Weyl operator has determinant one in characteristic
two, the field characteristic used by Suzuki groups. -/
theorem suzukiWeylOperator_det :
    (suzukiWeylOperator (K := K)).det = 1 := by
  apply Units.ext
  change (suzukiWeylMatrix (K := K)).det = 1
  let r : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2
  have hr : suzukiWeylMatrix (K := K) = r.permMatrix K := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [suzukiWeylMatrix, r, Equiv.Perm.permMatrix,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  rw [hr, Matrix.det_permutation]
  simp [r]

/-- The torus generator of the full Suzuki operator group, represented on the
same four-dimensional carrier as its root and Weyl generators. -/
@[expose] def suzukiTorusOperator (a : ℕ) (l : Kˣ) : Matrix.GeneralLinearGroup (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD a l) (by
    rw [suzukiD_det]
    exact one_ne_zero)

/-- Matrix readback for the upper-root operator presentation. -/
theorem coe_upperRootOperator (a : ℕ) (u v : K) :
    (upperRootOperator a u v : Matrix (Fin 4) (Fin 4) K) =
      (Chevalley.suzukiS a u v).transpose := rfl

/-- Matrix readback for the Suzuki Weyl operator. -/
theorem coe_suzukiWeylOperator :
    (suzukiWeylOperator (K := K) : Matrix (Fin 4) (Fin 4) K) =
      suzukiWeylMatrix := rfl

/-- Matrix readback for the Suzuki torus operator. -/
theorem coe_suzukiTorusOperator (a : ℕ) (l : Kˣ) :
    (suzukiTorusOperator a l : Matrix (Fin 4) (Fin 4) K) = Chevalley.suzukiD a l := rfl

/-- The antidiagonal Weyl matrix is the matrix model used by the catalog. -/
theorem suzukiWeylMatrix_eq_catalog :
    suzukiWeylMatrix (K := K) = Chevalley.suzukiW K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiWeylMatrix, Chevalley.suzukiW]

/-- The torus generator also has determinant one, by the native determinant
identity for the Suzuki diagonal weights. -/
theorem suzukiTorusOperator_det (a : ℕ) (l : Kˣ) :
    (suzukiTorusOperator a l).det = 1 := by
  apply Units.ext
  change (Chevalley.suzukiD a l).det = 1
  exact Chevalley.suzukiD_det a K l

/-- Every element of the full Suzuki matrix-operator group has determinant
one. The determinant-one condition is checked on the actual transposed root,
torus, and Weyl generators, then passed through subgroup closure. -/
theorem suzukiUpperMatrixGroup_det_eq_one [CharP K 2] (a : ℕ)
    (g : Chevalley.suzukiUpperMatrixGroup a K) :
    (Matrix.GeneralLinearGroup.det
      (g : Matrix.GeneralLinearGroup (Fin 4) K)) = 1 := by
  let detHom := Matrix.GeneralLinearGroup.det
    (n := Fin 4) (R := K)
  have hgens : Chevalley.suzukiUpperMatrixGenerators a K ⊆ detHom.ker := by
    intro A hA
    change ((A : Matrix (Fin 4) (Fin 4) K).transpose) ∈
      {M : Matrix (Fin 4) (Fin 4) K |
        (∃ u v : K, M = Chevalley.suzukiS a u v) ∨
          (∃ l : Kˣ, M = Chevalley.suzukiD a l) ∨ M = Chevalley.suzukiW K} at hA
    have hdetA : detHom A = 1 := by
      apply Units.ext
      change (A : Matrix (Fin 4) (Fin 4) K).det = 1
      rcases hA with ⟨u, v, hroot⟩ | ⟨l, htorus⟩ | hweyl
      · have htri : (Chevalley.suzukiS a u v).IsLowerTriangular := by
          intro i j hij
          change i < j at hij
          fin_cases i <;> fin_cases j <;>
            simp_all [Chevalley.suzukiS, Chevalley.suzukiN]
        rw [← Matrix.det_transpose, hroot,
          Matrix.det_of_isLowerTriangular _ htri]
        simp [Chevalley.suzukiS, Fin.prod_univ_four]
      · rw [← Matrix.det_transpose, htorus, Chevalley.suzukiD_det]
      · rw [← Matrix.det_transpose, hweyl]
        have hw := congrArg (fun x : Kˣ => (x : K))
          (suzukiWeylOperator_det (K := K))
        simpa [Matrix.GeneralLinearGroup.det, suzukiWeylOperator,
          suzukiWeylMatrix, Chevalley.suzukiW] using hw
    exact MonoidHom.mem_ker.mpr hdetA
  have hclosure : Chevalley.suzukiUpperMatrixGroup a K ≤ detHom.ker := by
    rw [Chevalley.suzukiUpperMatrixGroup, Subgroup.closure_le]
    exact hgens
  exact MonoidHom.mem_ker.mp (hclosure g.2)

/-- A four-dimensional scalar operator with determinant one is trivial over a
field of characteristic two: its scalar satisfies `x^4 = 1`, hence
`(x + 1)^4 = 0` and therefore `x = 1`. -/
theorem scalar_eq_one_of_det_one [CharP K 2] (u : Kˣ)
    (hdet : (Matrix.GeneralLinearGroup.scalar (Fin 4) u).det = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 4) u = 1 := by
  have hu4 : (u : K) ^ 4 = 1 := by
    have h := congrArg (fun x : Kˣ => (x : K)) hdet
    simpa [Matrix.GeneralLinearGroup.det_scalar] using h
  have hfour : ((u : K) + 1) ^ 4 = (u : K) ^ 4 + 1 := by
    have hsq : ((u : K) + 1) ^ 2 = (u : K) ^ 2 + 1 := by
      simpa using (CharTwo.add_sq (u : K) (1 : K))
    calc
      ((u : K) + 1) ^ 4 = (((u : K) + 1) ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = ((u : K) ^ 2 + 1) ^ 2 := congrArg (fun x : K => x ^ 2) hsq
      _ = ((u : K) ^ 2) ^ 2 + 1 := by
        simpa using (CharTwo.add_sq ((u : K) ^ 2) (1 : K))
      _ = (u : K) ^ 4 + 1 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  have hzero : ((u : K) + 1) ^ 4 = 0 := by
    rw [hfour, hu4]
    rw [one_add_one_eq_two]
    exact CharP.cast_eq_zero K 2
  have hu1 : (u : K) = 1 := by
    have hsum : (u : K) + 1 = 0 := eq_zero_of_pow_eq_zero hzero
    exact CharTwo.add_eq_zero.mp hsum
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, hu1]

/-- The local Suzuki operator group has trivial intersection with the scalar
center of `GL₄(K)`. This follows from determinant one and the characteristic-
two scalar rigidity lemma. -/
theorem suzukiUpperMatrixGroup_center_trivial [CharP K 2] (a : ℕ)
    {g : Matrix.GeneralLinearGroup (Fin 4) K}
    (hg : g ∈ Chevalley.suzukiUpperMatrixGroup a K)
    (hc : g ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 4) K)) :
    g = 1 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  rcases hc with ⟨u, hu⟩
  have hdet := suzukiUpperMatrixGroup_det_eq_one (K := K) a ⟨g, hg⟩
  change (Matrix.GeneralLinearGroup.det g) = 1 at hdet
  rw [← hu] at hdet
  calc
    g = Matrix.GeneralLinearGroup.scalar (Fin 4) u := hu.symm
    _ = 1 := scalar_eq_one_of_det_one (K := K) u hdet

/-- The local Suzuki group embeds into `PGL₄(K)`. Its projective kernel is
the intersection with the scalar center, which determinant one and
characteristic-two scalar rigidity show is trivial. -/
theorem suzukiUpperMatrixGroup_toPGL_injective [CharP K 2] (a : ℕ) :
    Function.Injective
      ((Matrix.ProjGenLinGroup.mk :
        Matrix.GeneralLinearGroup (Fin 4) K →*
          Matrix.ProjGenLinGroup (Fin 4) K).comp
        (Chevalley.suzukiUpperMatrixGroup a K).subtype) := by
  intro g h hgh
  change Matrix.ProjGenLinGroup.mk
      (g : Matrix.GeneralLinearGroup (Fin 4) K) =
    Matrix.ProjGenLinGroup.mk
      (h : Matrix.GeneralLinearGroup (Fin 4) K) at hgh
  obtain ⟨u, hmul⟩ :=
    (Matrix.ProjGenLinGroup.mk_eq_mk_iff
      (g₁ := (g : Matrix.GeneralLinearGroup (Fin 4) K))
      (g₂ := (h : Matrix.GeneralLinearGroup (Fin 4) K))).mp hgh
  let z := (g : Matrix.GeneralLinearGroup (Fin 4) K)⁻¹ *
    (h : Matrix.GeneralLinearGroup (Fin 4) K)
  have hz : z = Matrix.GeneralLinearGroup.scalar (Fin 4) u := by
    dsimp [z]
    rw [← hmul]
    group
  have hzmem : z ∈ Chevalley.suzukiUpperMatrixGroup a K := by
    dsimp [z]
    exact (Chevalley.suzukiUpperMatrixGroup a K).mul_mem
      ((Chevalley.suzukiUpperMatrixGroup a K).inv_mem g.property) h.property
  have hzcenter : z ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 4) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, hz.symm⟩
  have hzone := suzukiUpperMatrixGroup_center_trivial (K := K) a hzmem hzcenter
  have hval : (g : Matrix.GeneralLinearGroup (Fin 4) K) =
      (h : Matrix.GeneralLinearGroup (Fin 4) K) := by
    have hmul' := congrArg
      (fun x : Matrix.GeneralLinearGroup (Fin 4) K =>
        (g : Matrix.GeneralLinearGroup (Fin 4) K) * x) hzone
    have hrev : (h : Matrix.GeneralLinearGroup (Fin 4) K) =
        (g : Matrix.GeneralLinearGroup (Fin 4) K) := by
      simpa [z] using hmul'
    exact hrev.symm
  exact Subtype.ext hval

/-- Multiplication of torus operators follows multiplication in `Kˣ`. -/
theorem suzukiTorusOperator_mul (a : ℕ) (l m : Kˣ) :
    suzukiTorusOperator a l * suzukiTorusOperator a m =
      suzukiTorusOperator a (l * m) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul]
  change suzukiD a l * suzukiD a m = suzukiD a (l * m)
  exact suzukiD_mul a l m

/-- The identity parameter gives the identity torus operator. -/
theorem suzukiTorusOperator_one (a : ℕ) :
    suzukiTorusOperator a (1 : Kˣ) = 1 := by
  apply Units.ext
  change suzukiD a (1 : Kˣ) = 1
  exact suzukiD_one a

/-- Inversion of torus operators agrees with inversion of their parameters. -/
theorem suzukiTorusOperator_inv (a : ℕ) (l : Kˣ) :
    (suzukiTorusOperator a l)⁻¹ = suzukiTorusOperator a l⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  rw [suzukiTorusOperator_mul, mul_inv_cancel, suzukiTorusOperator_one]

/-- The antidiagonal Weyl operator conjugates each Suzuki torus operator to
the operator indexed by the inverse unit. -/
theorem suzukiWeylOperator_conj_torus (a : ℕ) (l : Kˣ) :
    suzukiWeylOperator (K := K) * suzukiTorusOperator a l *
        suzukiWeylOperator (K := K) = suzukiTorusOperator a l⁻¹ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiWeylOperator, suzukiWeylMatrix, suzukiTorusOperator,
      suzukiD, Matrix.diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Units.val_inv, zpow_neg]
  all_goals congr 1 <;> ring

set_option maxHeartbeats 1600000
/-- Conjugation by a Suzuki torus operator rescales the two parameters of the
upper-root operator by `l` and `l * pi l`. This is the local operator-carrier
form of the torus/root relation used in the external Huppert proof. -/
theorem suzukiTorusOperator_conj_upperRoot
    (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1)))
    (l : Kˣ) (u v : K) :
    suzukiTorusOperator a l * upperRootOperator a u v *
        (suzukiTorusOperator a l)⁻¹ =
      upperRootOperator a ((l : K) * u) ((l : K) * pi (l : K) * v) := by
  apply Units.ext
  rw [suzukiTorusOperator_inv, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul]
  change suzukiD a l * (suzukiS a u v).transpose * suzukiD a l⁻¹ =
    (suzukiS a ((l : K) * u) ((l : K) * pi (l : K) * v)).transpose
  rw [suzukiD_eq, suzukiD_eq]
  let x : K := l
  have hratio : x ^ (1 + 2 ^ a) * (x ^ (2 ^ a))⁻¹ = x := by
    rw [pow_add, pow_one]
    simp [x, pow_ne_zero _ l.ne_zero]
  have hsigma_sq : x ^ (2 ^ a) * x ^ (2 ^ a) = x ^ (2 ^ (a + 1)) := by
    rw [← pow_two, ← pow_mul, pow_succ]
  have hmiddle : x ^ (2 ^ a) * x ^ (1 + 2 ^ a) =
      x * x ^ (2 ^ (a + 1)) := by
    calc
      x ^ (2 ^ a) * x ^ (1 + 2 ^ a) = x ^ (2 ^ a + (1 + 2 ^ a)) :=
        (pow_add _ _ _).symm
      _ = x ^ (1 + 2 ^ (a + 1)) := by
        congr 1
        rw [pow_succ]
        omega
      _ = x * x ^ (2 ^ (a + 1)) := by rw [pow_add, pow_one]
  have houter_sq : x ^ (1 + 2 ^ a) * x ^ (1 + 2 ^ a) =
      x ^ (2 + 2 ^ (a + 1)) := by
    rw [← pow_two, ← pow_mul]
    congr 1
    rw [pow_succ]
    omega
  have hsigma_inv : x ^ (2 ^ a) * (x⁻¹) ^ (2 ^ a) = 1 := by
    rw [← mul_pow]
    simp [x, l.ne_zero]
  have hpi_iter : (x ^ (2 ^ (a + 1))) ^ (2 ^ (a + 1)) = x ^ 2 := by
    calc
      (x ^ (2 ^ (a + 1))) ^ (2 ^ (a + 1)) = pi (pi x) := by
        rw [hpi_formula, hpi_formula]
      _ = x ^ 2 := hpi_sq x
  have hexp : 2 ^ (a + 1) * 2 ^ (a + 1) = 2 ^ (a * 2) * 4 := by
    calc
      2 ^ (a + 1) * 2 ^ (a + 1) = 2 ^ ((a + 1) + (a + 1)) := by
        rw [← pow_add]
      _ = 2 ^ (a * 2 + 2) := by congr 1 <;> omega
      _ = 2 ^ (a * 2) * 4 := by rw [pow_add]; norm_num
  have hpi_iter' : x ^ 2 = x ^ (2 ^ (a * 2) * 4) := by
    calc
      x ^ 2 = (x ^ (2 ^ (a + 1))) ^ (2 ^ (a + 1)) := hpi_iter.symm
      _ = x ^ (2 ^ (a + 1) * 2 ^ (a + 1)) := by rw [← pow_mul]
      _ = x ^ (2 ^ (a * 2) * 4) := by rw [hexp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiS, suzukiN, Matrix.mul_apply, Matrix.diagonal_apply,
      hpi_formula, hratio, hsigma_sq, hmiddle, houter_sq, hpi_iter,
      hsigma_inv, mul_pow, inv_pow, mul_comm, mul_left_comm] <;> ring_nf
  all_goals
    try simp [mul_comm]
    try rw [hpi_iter']
    try simp [x, mul_comm]
    try ring
set_option maxHeartbeats 1600000

/-- The subgroup generated by the Suzuki torus operators on the actual
four-dimensional operator carrier. It is one component of the ovoid point
stabilizer used in the simplicity argument. -/
def suzukiTorusOperatorGroup (a : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  Subgroup.closure (Set.range (suzukiTorusOperator a))

/-- Every explicit Suzuki torus operator belongs to the generated torus
subgroup. -/
theorem suzukiTorusOperator_mem_torusOperatorGroup (a : ℕ) (l : Kˣ) :
    suzukiTorusOperator a l ∈ suzukiTorusOperatorGroup (K := K) a := by
  rw [suzukiTorusOperatorGroup]
  exact Subgroup.subset_closure (Set.mem_range_self l)

/-- The torus operators commute as endomorphism units, since their matrices
are diagonal in the same operator basis. -/
theorem suzukiTorusOperator_commute (a : ℕ) (l m : Kˣ) :
    Commute (suzukiTorusOperator a l) (suzukiTorusOperator a m) := by
  rw [commute_iff_eq]
  apply Units.ext
  change Matrix.diagonal ![
      ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K),
      ((l ^ (2 ^ a : ℤ) : Kˣ) : K),
      ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K),
      ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)] *
      Matrix.diagonal ![
        ((m ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K),
        ((m ^ (2 ^ a : ℤ) : Kˣ) : K),
        ((m ^ (-(2 ^ a : ℤ)) : Kˣ) : K),
        ((m ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)] =
    Matrix.diagonal ![
      ((m ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K),
      ((m ^ (2 ^ a : ℤ) : Kˣ) : K),
      ((m ^ (-(2 ^ a : ℤ)) : Kˣ) : K),
      ((m ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)] *
      Matrix.diagonal ![
        ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K),
        ((l ^ (2 ^ a : ℤ) : Kˣ) : K),
        ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K),
        ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)]
  exact (Matrix.commute_diagonal _ _).eq

/-- The generated Suzuki torus is an abelian subgroup of the operator group. -/
theorem suzukiTorusOperatorGroup_isMulCommutative (a : ℕ) :
    IsMulCommutative (suzukiTorusOperatorGroup (K := K) a) := by
  apply Subgroup.isMulCommutative_closure
  intro x hx y hy _
  obtain ⟨l, rfl⟩ := Set.mem_range.mp hx
  obtain ⟨m, rfl⟩ := Set.mem_range.mp hy
  exact suzukiTorusOperator_commute a l m

/-- The operator torus is solvable, as an abelian subgroup of the
noncommutative Suzuki operator carrier. -/
theorem suzukiTorusOperatorGroup_isSolvable (a : ℕ) :
    Group.IsSolvable (suzukiTorusOperatorGroup (K := K) a) := by
  letI : IsMulCommutative (suzukiTorusOperatorGroup (K := K) a) :=
    suzukiTorusOperatorGroup_isMulCommutative (K := K) a
  infer_instance

/-- The torus operator is one of the generators of the full Suzuki group. -/
theorem suzukiTorusOperator_mem_suzukiMatrixGroup (a : ℕ) (l : Kˣ) :
    suzukiTorusOperator a l ∈ Chevalley.suzukiMatrixGroup a K := by
  change Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD a l)
      (by rw [suzukiD_det]; exact one_ne_zero) ∈ Chevalley.suzukiMatrixGroup a K
  exact Chevalley.suzukiD_mem_suzukiMatrixGroup a K l

/-- The generated torus subgroup stays inside the full Suzuki operator
group, including after taking subgroup closure. -/
theorem suzukiTorusOperatorGroup_le_suzukiMatrixGroup (a : ℕ) :
    suzukiTorusOperatorGroup (K := K) a ≤ Chevalley.suzukiMatrixGroup a K := by
  apply (Subgroup.closure_le (Chevalley.suzukiMatrixGroup a K)).2
  rintro _ ⟨l, rfl⟩
  exact suzukiTorusOperator_mem_suzukiMatrixGroup a l

/-- The torus generator lies in the full Suzuki group acting on the
four-dimensional endomorphism carrier. -/
theorem suzukiTorusOperator_mem_suzukiGroup (a : ℕ) (l : Kˣ) :
    Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))
      (suzukiTorusOperator a l) ∈ Chevalley.suzukiGroup a K := by
  change Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))
      (suzukiTorusOperator a l) ∈
        (Chevalley.suzukiMatrixGroup a K).map
          (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))).toMonoidHom
  rw [Subgroup.mem_map]
  exact ⟨suzukiTorusOperator a l, suzukiTorusOperator_mem_suzukiMatrixGroup a l, rfl⟩

/-- The torus subgroup also sits in the full group of endomorphism units on
the four-dimensional function module. -/
theorem suzukiTorusOperatorGroup_map_le_suzukiGroup (a : ℕ) :
    (suzukiTorusOperatorGroup (K := K) a).map
        (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))).toMonoidHom ≤
      Chevalley.suzukiGroup a K := by
  rw [Chevalley.suzukiGroup]
  exact Subgroup.map_mono
    (suzukiTorusOperatorGroup_le_suzukiMatrixGroup (K := K) a)

/-- A torus operator rescales the finite Suzuki ovoid chart by `l` and
`l * pi l`, matching the action of the full Suzuki operator group. -/
theorem suzukiTorusOperator_smul_finite
    (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1)))
    (l : Kˣ) (x y : K) :
    (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv •
        ovoidPoint pi x y =
      ovoidPoint pi ((l : K) * x) ((l : K) * pi (l : K) * y) := by
  change (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv •
      Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp) =
    Projectivization.mk K
      ![((l : K) * x) * ((l : K) * pi (l : K) * y) +
          pi ((l : K) * x) * ((l : K) * x) ^ 2 +
          pi ((l : K) * pi (l : K) * y),
        (l : K) * pi (l : K) * y, (l : K) * x, 1] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨((l : K) ^ (1 + 2 ^ a))⁻¹, ?_⟩
  have hu : (l : K) ≠ 0 := l.ne_zero
  let s : K := (l : K) ^ (2 ^ a)
  have hs : (l : K) ^ (2 ^ a) = s := rfl
  have hs_ne : s ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero _ hu
  have huouter : (l : K) ^ (1 + 2 ^ a) ≠ 0 := pow_ne_zero _ hu
  have hpi_l : pi (l : K) = s ^ 2 := by
    calc
      pi (l : K) = ((l : K) ^ (2 ^ a)) ^ 2 := by
        rw [hpi_formula, pow_succ, pow_mul]
      _ = s ^ 2 := by rw [hs]
  have huouter_formula : (l : K) ^ (1 + 2 ^ a) = (l : K) * s := by
    rw [pow_add, pow_one, hs]
  have hexp2 : (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) := by
    norm_cast
  have hs_zpow : (l : K) ^ ((2 : ℤ) ^ a) = s := by
    rw [hexp2, zpow_natCast, hs]
  have huouter_formula_zpow :
      (l : K) ^ (1 + (2 : ℤ) ^ a) = (l : K) * s := by
    have hexp : 1 + (2 : ℤ) ^ a = ((1 + 2 ^ a : ℕ) : ℤ) := by
      rw [hexp2, Nat.cast_add, Nat.cast_one]
    rw [hexp, zpow_natCast, huouter_formula]
  funext i
  fin_cases i <;>
    simp [suzukiTorusOperator, suzukiD, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, map_mul, hpi_sq]
  · rw [hpi_l, huouter_formula]
    have hus_ne : (l : K) * s ≠ 0 := mul_ne_zero hu hs_ne
    have hinner :
        (l : K) * x * ((l : K) * s ^ 2 * y) +
            s ^ 2 * pi x * ((l : K) * x) ^ 2 +
            s ^ 2 * (l : K) ^ 2 * pi y =
          ((l : K) * s) ^ 2 * (x * y + pi x * x ^ 2 + pi y) := by
      ring
    calc
      ((l : K) * s)⁻¹ *
          ((l : K) * x * ((l : K) * s ^ 2 * y) +
            s ^ 2 * pi x * ((l : K) * x) ^ 2 +
            s ^ 2 * (l : K) ^ 2 * pi y) =
          ((l : K) * s)⁻¹ * (((l : K) * s) ^ 2 *
            (x * y + pi x * x ^ 2 + pi y)) := by rw [hinner]
      _ = ((l : K) * s) * (x * y + pi x * x ^ 2 + pi y) := by
        rw [pow_two, mul_assoc]
        exact inv_mul_cancel_left₀ hus_ne _
    rw [← huouter_formula]
    rw [← zpow_natCast]
    congr 1
  · rw [hpi_l, huouter_formula]
    have hus_ne : (l : K) * s ≠ 0 := mul_ne_zero hu hs_ne
    rw [show (l : K) * s ^ 2 * y = ((l : K) * s) * (s * y) by ring]
    field_simp [hus_ne]
    rw [hs_zpow]
    exact mul_comm s y
  · field_simp [hu, hs_ne]
    rw [huouter_formula, ← hs]
    rw [← zpow_natCast, hexp2]
    ac_rfl
  · rw [← zpow_natCast, ← zpow_neg]
    congr 1
    push_cast
    ring

/-- The torus operator fixes the distinguished point at infinity. -/
theorem suzukiTorusOperator_smul_infinity (a : ℕ) (l : Kˣ) :
    (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv •
      ovoidInfinity (K := K) = ovoidInfinity := by
  change (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv •
      Projectivization.mk K ![1, 0, 0, 0] (by simp) =
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K), ?_⟩
  funext i
  fin_cases i <;>
    simp [suzukiTorusOperator, suzukiD, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]

/-- Every element of the generated Suzuki torus fixes the ovoid point at
infinity. -/
theorem suzukiTorusOperatorGroup_smul_infinity (a : ℕ)
    (g : suzukiTorusOperatorGroup (K := K) a) :
    (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ovoidInfinity (K := K) = ovoidInfinity := by
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K))
      (ovoidInfinity (K := K))).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hclosure : suzukiTorusOperatorGroup (K := K) a ≤ S := by
    rw [suzukiTorusOperatorGroup, Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    change Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l) ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))
    rw [MulAction.mem_stabilizer_iff]
    exact suzukiTorusOperator_smul_infinity a l
  have hg : g.1 ∈ S := hclosure g.2
  change Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
    MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K))
      (ovoidInfinity (K := K)) at hg
  exact MulAction.mem_stabilizer_iff.mp hg

/-- Each torus operator preserves the full projective Suzuki ovoid. -/
theorem suzukiTorusOperator_maps_ovoid
    (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1)))
    (l : Kˣ) (z : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) :
    (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv • z ∈
      ovoid pi := by
  change z ∈ {ovoidInfinity} ∪
    Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz
  rcases hz with hz | ⟨w, rfl⟩
  · have hz' : z = ovoidInfinity := by simpa using hz
    subst z
    rw [suzukiTorusOperator_smul_infinity]
    exact Or.inl (by simp)
  · exact Or.inr ⟨((l : K) * w.1, (l : K) * pi (l : K) * w.2),
      (suzukiTorusOperator_smul_finite a pi hpi_sq hpi_formula l w.1 w.2).symm⟩

/-- The upper-root Suzuki operator fixes the distinguished ovoid point at
infinity. -/
theorem upperRootOperator_smul_infinity (a : ℕ) (u v : K) :
    (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv •
      ovoidInfinity (K := K) = ovoidInfinity := by
  change (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv •
      Projectivization.mk K ![1, 0, 0, 0] (by simp) =
        Projectivization.mk K ![1, 0, 0, 0] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;>
    simp [upperRootOperator, suzukiSGL, suzukiS, suzukiN]

/-- The antidiagonal Weyl operator sends infinity to the zero chart point. -/
theorem suzukiWeylOperator_smul_infinity (pi : K ≃+* K) :
    (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      ovoidInfinity (K := K) = ovoidPoint pi 0 0 := by
  have h : (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      Projectivization.mk K (![1, 0, 0, 0] : Fin 4 → K) (by simp) =
    Projectivization.mk K (![0, 0, 0, 1] : Fin 4 → K) (by simp) := by
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four]
  simpa [ovoidInfinity, ovoidPoint] using h

/-- The antidiagonal Weyl operator sends the zero chart point to infinity. -/
theorem suzukiWeylOperator_smul_zero (pi : K ≃+* K) :
    (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      ovoidPoint pi 0 0 = ovoidInfinity := by
  have h : (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      Projectivization.mk K (![0, 0, 0, 1] : Fin 4 → K) (by simp) =
    Projectivization.mk K (![1, 0, 0, 0] : Fin 4 → K) (by simp) := by
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four]
  simpa [ovoidInfinity, ovoidPoint] using h

/-- The reciprocal coordinates of a finite ovoid point have reciprocal norm.
This is the field calculation used by the Weyl operator action. -/
theorem suzukiOvoidNorm_inv [CharP K 2]
    (pi : K ≃+* K) (hpi_sq : ∀ z, pi (pi z) = z ^ 2) (x y : K) :
    let n := x * y + pi x * x ^ 2 + pi y
    n ≠ 0 →
      (n⁻¹ * y) * (n⁻¹ * x) + pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 +
        pi (n⁻¹ * x) = n⁻¹ := by
  dsimp only
  let n : K := x * y + pi x * x ^ 2 + pi y
  change n ≠ 0 →
    (n⁻¹ * y) * (n⁻¹ * x) + pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 +
      pi (n⁻¹ * x) = n⁻¹
  intro hn
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  have hpi_n : pi n = pi x * pi y + x ^ 2 * (pi x) ^ 2 + y ^ 2 := by
    dsimp only [n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  have hcore :
      pi n * (x * y) + pi y * y ^ 2 + pi x * n ^ 2 = pi n * n := by
    rw [hpi_n]
    dsimp only [n]
    linear_combination
      (pi x * pi y * x * y + (pi x) ^ 2 * x ^ 3 * y) * htwo
  simp only [map_mul, map_inv₀]
  have hd : pi n * n ^ 2 ≠ 0 := mul_ne_zero hpin (pow_ne_zero _ hn)
  apply mul_left_cancel₀ hd
  calc
    (pi n * n ^ 2) *
        ((n⁻¹ * y) * (n⁻¹ * x) +
          (pi n)⁻¹ * pi y * (n⁻¹ * y) ^ 2 + (pi n)⁻¹ * pi x) =
        pi n * (x * y) + pi y * y ^ 2 + pi x * n ^ 2 := by
      field_simp [hn, hpin]
    _ = pi n * n := hcore
    _ = (pi n * n ^ 2) * n⁻¹ := by field_simp [hn, hpin]

/-- Away from the zero chart point, the antidiagonal Weyl operator acts on
the finite Suzuki ovoid coordinates by reciprocal norm coordinates. -/
theorem suzukiWeylOperator_smul_finite_of_norm_ne_zero [CharP K 2]
    (pi : K ≃+* K) (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (x y : K) :
    let n := x * y + pi x * x ^ 2 + pi y
    n ≠ 0 →
      (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
        ovoidPoint pi x y = ovoidPoint pi (n⁻¹ * y) (n⁻¹ * x) := by
  dsimp only
  let n : K := x * y + pi x * x ^ 2 + pi y
  change n ≠ 0 →
    (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      ovoidPoint pi x y = ovoidPoint pi (n⁻¹ * y) (n⁻¹ * x)
  intro hn
  have hnorm_inv :
      (n⁻¹ * y) * (n⁻¹ * x) + pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 +
        pi (n⁻¹ * x) = n⁻¹ := by
    exact suzukiOvoidNorm_inv pi hpi_sq x y hn
  change (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp) =
    Projectivization.mk K
      ![(n⁻¹ * y) * (n⁻¹ * x) + pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 +
          pi (n⁻¹ * x), n⁻¹ * x, n⁻¹ * y, 1] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨n, ?_⟩
  have hncancel (z : K) : n * (n⁻¹ * z) = z := by
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  funext i
  fin_cases i
  · rw [hnorm_inv]
    simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    exact mul_inv_cancel₀ hn
  · simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, hncancel]
  · simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, hncancel]
  · simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
      n]

/-- The antidiagonal Weyl operator preserves the Suzuki ovoid when the
Suzuki norm vanishes only at the zero coordinate pair. -/
theorem suzukiWeylOperator_maps_ovoid [CharP K 2]
    (pi : K ≃+* K) (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0)
    (z : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) :
    (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv • z ∈
      ovoid pi := by
  change z ∈ {ovoidInfinity} ∪
    Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz
  rcases hz with hz | ⟨w, rfl⟩
  · have hz' : z = ovoidInfinity := by simpa using hz
    subst z
    rw [suzukiWeylOperator_smul_infinity]
    exact Or.inr ⟨(0, 0), rfl⟩
  · rcases w with ⟨x, y⟩
    let n : K := x * y + pi x * x ^ 2 + pi y
    by_cases hn : n = 0
    · have hxy := hnorm_zero x y (by simpa [n] using hn)
      rcases hxy with ⟨rfl, rfl⟩
      rw [suzukiWeylOperator_smul_zero]
      exact Or.inl (by simp)
    · rw [suzukiWeylOperator_smul_finite_of_norm_ne_zero pi hpi_sq x y hn]
      exact Or.inr ⟨(n⁻¹ * y, n⁻¹ * x), rfl⟩

/-- The upper-root Suzuki operator acts on the normalized finite ovoid chart
by the root-group multiplication formula. -/
theorem upperRootOperator_smul_finite
    [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (u v x y : K) :
    (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv •
      ovoidPoint pi x y =
        ovoidPoint pi (x + u) (y + v + pi u * (x + u)) := by
  change (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv •
      Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp) =
    Projectivization.mk K
      ![(x + u) * (y + v + pi u * (x + u)) +
          pi (x + u) * (x + u) ^ 2 + pi (y + v + pi u * (x + u)),
        y + v + pi u * (x + u), x + u, 1] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  have hpow (z : K) : z ^ (2 ^ (a + 1)) = pi z := (hpi_formula z).symm
  have hpow_one (z : K) : z ^ (1 + 2 ^ (a + 1)) = z * pi z := by
    rw [pow_add, hpow, pow_one]
  have hpow_one' (z : K) : z ^ (2 ^ (a + 1) + 1) = z * pi z := by
    rw [Nat.add_comm (2 ^ (a + 1)) 1, hpow_one]
  have hpow_two (z : K) : z ^ (2 + 2 ^ (a + 1)) = z ^ 2 * pi z := by
    rw [pow_add, hpow]
  have hpow_two' (z : K) : z ^ (2 ^ (a + 1) + 2) = z ^ 2 * pi z := by
    rw [Nat.add_comm (2 ^ (a + 1)) 2, hpow_two]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  funext i
  fin_cases i <;>
    simp [upperRootOperator, suzukiSGL, suzukiS, suzukiN,
      hpow, hpow_one', hpow_two', map_add, map_mul, hpi_sq]
  linear_combination
    (x ^ 2 * pi u + 2 * x * u * pi u + x * u * pi x +
      u ^ 2 * pi u + u ^ 2 * pi x) * htwo
  ring

/-- Every upper-root Suzuki operator preserves the projective ovoid. -/
theorem upperRootOperator_maps_ovoid
    [CharP K 2] (a : ℕ) (pi : K ≃+* K) (u v : K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (z : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) :
    (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv • z ∈
      ovoid pi := by
  change z ∈ {ovoidInfinity} ∪
    Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz
  rcases hz with hz | ⟨w, rfl⟩
  · have hz' : z = ovoidInfinity := by simpa using hz
    subst z
    rw [upperRootOperator_smul_infinity]
    exact Or.inl (by simp)
  · exact Or.inr ⟨(w.1 + u, w.2 + v + pi u * (w.1 + u)),
      (upperRootOperator_smul_finite a pi hpi_sq hpi_formula u v w.1 w.2).symm⟩

/-- The subgroup generated by the actual upper-root Suzuki operators. -/
def upperRootMatrixGroup (a : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  Subgroup.closure {g | ∃ u v : K, g = upperRootOperator a u v}

/-- Under the Suzuki field-cardinality condition, the closure defining the
upper-root group is already the set of its two-parameter operators. The
parameter law, identity, and inverse formulas make that range a subgroup on
the same four-dimensional general-linear carrier. -/
theorem upperRootMatrixGroup_eq_paramRange [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (upperRootMatrixGroup (K := K) a :
      Set (Matrix.GeneralLinearGroup (Fin 4) K)) =
      {g | ∃ u v : K, g = upperRootOperator a u v} := by
  let H : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) := {
    carrier := {g | ∃ u v : K, g = upperRootOperator a u v}
    one_mem' := by
      refine ⟨0, 0, ?_⟩
      simpa [upperRootOperator] using
        (suzukiSGL_zero_zero (a := a) (K := K)).symm
    mul_mem' := by
      rintro g h ⟨u, v, rfl⟩ ⟨c, d, rfl⟩
      exact ⟨u + c, v + d + c ^ 2 ^ (a + 1) * u,
        (suzukiSGL_mul a hK u v c d)⟩
    inv_mem' := by
      rintro g ⟨u, v, rfl⟩
      exact ⟨u, v + u ^ (2 ^ (a + 1) + 1), suzukiSGL_inv a hK u v⟩
  }
  have hEq : upperRootMatrixGroup (K := K) a = H := by
    apply le_antisymm
    · rw [upperRootMatrixGroup, Subgroup.closure_le]
      intro g hg
      exact hg
    · intro g hg
      rcases hg with ⟨u, v, rfl⟩
      exact Subgroup.subset_closure ⟨u, v, rfl⟩
  change (upperRootMatrixGroup (K := K) a :
    Set (Matrix.GeneralLinearGroup (Fin 4) K)) = _
  rw [hEq]
  rfl

/-- The commutator of two upper-root Suzuki operators is a central root
operator. Its central parameter is the alternating part of the twisted
bilinear term in the root multiplication law. This is the local matrix
operator form of the root-commutator identity used by the external
Bender--Suzuki simplicity proof. -/
theorem upperRootOperator_commutator [Finite K] [CharP K 2] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v c d : K) :
    upperRootOperator a u v * upperRootOperator a c d *
        (upperRootOperator a u v)⁻¹ * (upperRootOperator a c d)⁻¹ =
      upperRootOperator a 0
        (c ^ (2 ^ (a + 1)) * u + u ^ (2 ^ (a + 1)) * c) := by
  simp only [upperRootOperator, suzukiSGL_mul a hK, suzukiSGL_inv a hK]
  have hparams :
      (u + c + u + c,
        v + d + c ^ (2 ^ (a + 1)) * u +
          (v + u ^ (2 ^ (a + 1) + 1)) +
          u ^ (2 ^ (a + 1)) * (u + c) +
          (d + c ^ (2 ^ (a + 1) + 1)) +
          c ^ (2 ^ (a + 1)) * (u + c + u)) =
        (0, c ^ (2 ^ (a + 1)) * u + u ^ (2 ^ (a + 1)) * c) := by
    apply Prod.ext
    · have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination (u + c) * htwo
    · have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      rw [pow_succ, pow_succ]
      linear_combination
        (v + d + c ^ (2 ^ (a + 1)) * u +
          u ^ (2 ^ (a + 1)) * u + c ^ (2 ^ (a + 1)) * c) * htwo
  exact congrArg (fun p : K × K => suzukiSGL a p.1 p.2) hparams

/-- For a finite field with a Tits automorphism `pi` satisfying
`pi (pi x) = x ^ 2`, the twisted norm `x ↦ x * pi x` permutes the nonzero
elements. This is the arithmetic input that makes every central Suzuki root
operator a root commutator. -/
theorem suzukiTwistedNorm_surjective [Finite K] (pi : K ≃+* K)
    (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2) :
    ∀ y : Kˣ, ∃ x : Kˣ,
      (x : K) * pi (x : K) = (y : K) := by
  let N : Kˣ →* Kˣ :=
    { toFun := fun x => x * Units.map pi.toMonoidHom x
      map_one' := by simp
      map_mul' x y := by
        apply Units.ext
        simp only [Units.val_mul, Units.coe_map, map_mul]
        ring }
  have hN_val (x : Kˣ) :
      (N x : K) = (x : K) * pi (x : K) := rfl
  have hker : N.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxval : (x : K) * pi (x : K) = 1 := by
      rw [← hN_val]
      exact congrArg Units.val hx
    have hpi_norm := congrArg pi hxval
    simp only [map_mul, map_one, hpi_sq] at hpi_norm
    have hpix_ne : pi (x : K) ≠ 0 := (map_ne_zero pi).2 x.ne_zero
    have hsquare : (x : K) ^ 2 = (x : K) := by
      apply mul_left_cancel₀ hpix_ne
      calc
        pi (x : K) * (x : K) ^ 2 = 1 := hpi_norm
        _ = pi (x : K) * (x : K) := by
          simpa [mul_comm] using hxval.symm
    apply Units.ext
    apply mul_left_cancel₀ x.ne_zero
    simpa [pow_two] using hsquare
  have hinj : Function.Injective N := N.ker_eq_bot_iff.mp hker
  let _ : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hsurj : Function.Surjective N := Finite.injective_iff_surjective.mp hinj
  intro y
  rcases hsurj y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [← hN_val]
  exact congrArg Units.val hx

/-- For positive Suzuki rank, the Tits automorphism cannot be the identity:
the fixed-point equation together with `pi²(x) = x²` would force every
element of the field to be either zero or one. -/
theorem suzukiTits_nontrivial [Finite K] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (pi : K ≃+* K)
    (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2) :
    ∃ x : K, pi x ≠ x := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  have hK_card : Fintype.card K = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hcard_gt : 2 < Fintype.card K := by
    rw [hK_card]
    have hpow_lt := Nat.pow_lt_pow_right (a := 2) (by norm_num)
      (show 1 < 2 * a + 1 by omega)
    simpa using hpow_lt
  have hexists : ∃ x : K, x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    push Not at h
    have huniv : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · simp [h x hx0]
    have hle : Fintype.card K ≤ 2 := by
      rw [← Finset.card_univ]
      calc
        Finset.univ.card ≤ ({0, 1} : Finset K).card := Finset.card_le_card huniv
        _ = 2 := by simp
    omega
  rcases hexists with ⟨x, hx0, hx1⟩
  refine ⟨x, ?_⟩
  intro hpix
  have hsq : x ^ 2 = x := by
    calc
      x ^ 2 = pi (pi x) := (hpi_sq x).symm
      _ = x := by rw [hpix, hpix]
  have hprod : x * (x - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, hsq, sub_self]
  rcases mul_eq_zero.mp hprod with hzero | hone
  · exact hx0 hzero
  · exact hx1 (sub_eq_zero.mp hone)

/-- The torus parameter used in Suzuki's nonzero root/Weyl factorization has
the two diagonal powers required by the local four-dimensional torus action.
This is the field-arithmetic input to the Weyl-image step in perfectness. -/
theorem suzukiBruhatTorusParameter_powers [CharP K 2]
    (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1)))
    (n : K) (hn : n ≠ 0) :
    let uval : K := pi n * n⁻¹ ^ 2
    (uval ^ (2 ^ a) = n * (pi n)⁻¹) ∧
      (uval ^ (1 + 2 ^ a) = n⁻¹) := by
  let uval : K := pi n * n⁻¹ ^ 2
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  have huval : uval ≠ 0 :=
    mul_ne_zero hpin (pow_ne_zero _ (inv_ne_zero hn))
  change (uval ^ (2 ^ a) = n * (pi n)⁻¹) ∧
    (uval ^ (1 + 2 ^ a) = n⁻¹)
  have hpi_uval : pi uval = (n * (pi n)⁻¹) ^ 2 := by
    dsimp only [uval]
    simp only [map_mul, map_pow, map_inv₀, hpi_sq]
    ring
  have hq : uval ^ (2 ^ a) = n * (pi n)⁻¹ := by
    apply CharTwo.sq_injective
    calc
      (uval ^ (2 ^ a)) ^ 2 = uval ^ (2 ^ (a + 1)) := by
        rw [show 2 ^ (a + 1) = 2 ^ a * 2 by rw [pow_succ], pow_mul]
      _ = pi uval := (hpi_formula uval).symm
      _ = (n * (pi n)⁻¹) ^ 2 := hpi_uval
  refine ⟨hq, ?_⟩
  rw [pow_add, pow_one, hq]
  dsimp only [uval]
  calc
    pi n * n⁻¹ ^ 2 * (n * (pi n)⁻¹) =
        (pi n * (pi n)⁻¹) * (n⁻¹ * n) * n⁻¹ := by ring
    _ = n⁻¹ := by
      rw [mul_inv_cancel₀ hpin, inv_mul_cancel₀ hn]
      simp

/-- Assuming one nonfixed Tits parameter, every central upper-root operator
is a commutator of two operators in the actual upper-root subgroup. The
twisted norm surjectivity supplies the parameter; the preceding operator
commutator formula verifies the equality in `GL(4,K)`. -/
theorem upperRootCentralOperator_is_commutator [Finite K] [CharP K 2]
    (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1)))
    (t : K) (ht : pi t + t ≠ 0) (b : K) :
    ∃ x y : upperRootMatrixGroup (K := K) a,
      x * y * x⁻¹ * y⁻¹ =
        (⟨upperRootOperator a 0 b,
          by
            apply Subgroup.subset_closure
            exact ⟨0, b, rfl⟩⟩ : upperRootMatrixGroup (K := K) a) := by
  by_cases hb : b = 0
  · subst b
    refine ⟨1, 1, ?_⟩
    apply Subtype.ext
    simp [upperRootOperator, suzukiSGL_zero_zero]
  · let yNorm : Kˣ := Units.mk0 (b / (pi t + t)) (div_ne_zero hb ht)
    rcases suzukiTwistedNorm_surjective (K := K) pi hpi_sq yNorm with
      ⟨z, hz⟩
    have hz_norm : (z : K) * pi (z : K) = b / (pi t + t) := by
      simpa [yNorm] using hz
    have hcentral :
        (z * t) ^ (2 ^ (a + 1)) * (z : K) +
          (z : K) ^ (2 ^ (a + 1)) * ((z : K) * t) = b := by
      rw [← hpi_formula (z * t), ← hpi_formula (z : K), map_mul]
      calc
        pi (z : K) * pi t * (z : K) +
            pi (z : K) * ((z : K) * t) =
              ((z : K) * pi (z : K)) * (pi t + t) := by ring
        _ = b := by rw [hz_norm, div_mul_cancel₀ b ht]
    let x : upperRootMatrixGroup (K := K) a :=
      ⟨upperRootOperator a (z : K) 0,
        Subgroup.subset_closure ⟨(z : K), 0, rfl⟩⟩
    let y : upperRootMatrixGroup (K := K) a :=
      ⟨upperRootOperator a ((z : K) * t) 0,
        Subgroup.subset_closure ⟨(z : K) * t, 0, rfl⟩⟩
    refine ⟨x, y, ?_⟩
    apply Subtype.ext
    change upperRootOperator a (z : K) 0 *
        upperRootOperator a ((z : K) * t) 0 *
        (upperRootOperator a (z : K) 0)⁻¹ *
        (upperRootOperator a ((z : K) * t) 0)⁻¹ =
      upperRootOperator a 0 b
    rw [upperRootOperator_commutator a hK]
    exact congrArg (upperRootOperator a 0) hcentral

/-- The standard Suzuki field hypotheses produce the nonfixed Tits parameter
needed in `upperRootCentralOperator_is_commutator`. -/
theorem upperRootCentralOperator_is_commutator_of_field [Finite K] [CharP K 2]
    (a : ℕ) (ha : 0 < a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1))) (b : K) :
    ∃ x y : upperRootMatrixGroup (K := K) a,
      x * y * x⁻¹ * y⁻¹ =
        (⟨upperRootOperator a 0 b,
          by
            apply Subgroup.subset_closure
            exact ⟨0, b, rfl⟩⟩ : upperRootMatrixGroup (K := K) a) := by
  obtain ⟨t, ht⟩ := suzukiTits_nontrivial (K := K) a ha hK pi hpi_sq
  have hdelta : pi t + t ≠ 0 := by
    intro hzero
    exact ht (CharTwo.add_eq_zero.mp hzero)
  exact upperRootCentralOperator_is_commutator a hK pi hpi_sq hpi_formula
    t hdelta b

/-- The two field parameters give a bijective coordinate system on the
upper-root subgroup. -/
noncomputable def upperRootParamEquiv [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    K × K ≃ ↥(upperRootMatrixGroup (K := K) a) := by
  let f : K × K → ↥(upperRootMatrixGroup (K := K) a) := fun p =>
    ⟨upperRootOperator a p.1 p.2, by
      exact Subgroup.subset_closure ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      apply suzukiSGL_injective a
      simpa [f, upperRootOperator] using congrArg Subtype.val hpq
    · intro g
      have hg : (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
          ({x | ∃ u v : K, x = upperRootOperator a u v} :
            Set (Matrix.GeneralLinearGroup (Fin 4) K)) := by
        rw [← upperRootMatrixGroup_eq_paramRange (K := K) a hK]
        exact g.property
      rcases hg with ⟨u, v, h⟩
      exact ⟨(u, v), Subtype.ext h.symm⟩
  exact Equiv.ofBijective f hf

/-- The local upper-root Suzuki subgroup has the expected `|K|²` elements,
counted on its actual matrix-operator carrier. -/
theorem upperRootMatrixGroup_card [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (upperRootMatrixGroup (K := K) a) = Nat.card K ^ 2 := by
  calc
    Nat.card (upperRootMatrixGroup (K := K) a) = Nat.card (K × K) :=
      Nat.card_congr (upperRootParamEquiv (K := K) a hK).symm
    _ = Nat.card K * Nat.card K := by rw [Nat.card_prod]
    _ = Nat.card K ^ 2 := by rw [pow_two]

/-- The local upper-root Suzuki subgroup is solvable: its faithful parameter
count makes it a finite 2-group, hence nilpotent and solvable. -/
theorem upperRootMatrixGroup_isSolvable [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Group.IsSolvable (upperRootMatrixGroup (K := K) a) := by
  have hcard : Nat.card (upperRootMatrixGroup (K := K) a) =
      2 ^ (2 * (2 * a + 1)) := by
    rw [upperRootMatrixGroup_card (K := K) a hK, hK, ← pow_mul]
    congr 1
    omega
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (upperRootMatrixGroup (K := K) a) :=
    IsPGroup.of_card hcard
  letI : Group.IsNilpotent (upperRootMatrixGroup (K := K) a) := hp.isNilpotent
  infer_instance

/-- Every upper-root translation fixes the distinguished ovoid point at
infinity, and this fixed-point property passes to the subgroup they generate.
This identifies the translation subgroup as a candidate point stabilizer
component for the Suzuki ovoid action. -/
theorem upperRootMatrixGroup_smul_infinity (a : ℕ)
    (g : upperRootMatrixGroup (K := K) a) :
    (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ovoidInfinity (K := K) = ovoidInfinity := by
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K))
      (ovoidInfinity (K := K))).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hclosure : upperRootMatrixGroup (K := K) a ≤ S := by
    rw [upperRootMatrixGroup, Subgroup.closure_le]
    intro A hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))
    rw [MulAction.mem_stabilizer_iff]
    rcases hA with ⟨u, v, rfl⟩
    exact upperRootOperator_smul_infinity a u v
  have hg : g.1 ∈ S := hclosure g.2
  change Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
    MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K))
      (ovoidInfinity (K := K)) at hg
  exact (MulAction.mem_stabilizer_iff.mp hg)

/-- The local Suzuki point-stabilizer carrier generated by the upper-root
operators and the torus operators. This is the operator analogue of the
root-torus subgroup appearing in the external Suzuki simplicity proof. -/
def suzukiPointStabilizerOperatorGroup (a : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  upperRootMatrixGroup (K := K) a ⊔ suzukiTorusOperatorGroup (K := K) a

/-- The upper-root operator subgroup is contained in the generated local
root–torus point-stabilizer candidate. -/
theorem upperRootMatrixGroup_le_suzukiPointStabilizerOperatorGroup (a : ℕ) :
    upperRootMatrixGroup (K := K) a ≤ suzukiPointStabilizerOperatorGroup (K := K) a :=
  le_sup_left

/-- The torus operator subgroup is contained in the generated local
root–torus point-stabilizer candidate. -/
theorem suzukiTorusOperatorGroup_le_suzukiPointStabilizerOperatorGroup (a : ℕ) :
    suzukiTorusOperatorGroup (K := K) a ≤ suzukiPointStabilizerOperatorGroup (K := K) a :=
  le_sup_right

/-- Each torus operator normalizes the generated upper-root subgroup. The
finite Suzuki field hypothesis identifies that closure with its two-parameter
operator range. -/
theorem suzukiTorusOperator_mem_normalizer_upperRoot [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1))) (l : Kˣ) :
    suzukiTorusOperator a l ∈ Subgroup.normalizer
      (upperRootMatrixGroup (K := K) a : Set (Matrix.GeneralLinearGroup (Fin 4) K)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  have hforward (m : Kˣ) (y : Matrix.GeneralLinearGroup (Fin 4) K)
      (hy : y ∈ upperRootMatrixGroup (K := K) a) :
      suzukiTorusOperator a m * y * (suzukiTorusOperator a m)⁻¹ ∈
        upperRootMatrixGroup (K := K) a := by
    change y ∈ (upperRootMatrixGroup (K := K) a :
      Set (Matrix.GeneralLinearGroup (Fin 4) K)) at hy
    rw [upperRootMatrixGroup_eq_paramRange (K := K) a hK] at hy
    rcases hy with ⟨u, v, rfl⟩
    rw [suzukiTorusOperator_conj_upperRoot a pi hpi_sq hpi_formula m u v]
    exact Subgroup.subset_closure
      ⟨(m : K) * u, (m : K) * pi (m : K) * v, rfl⟩
  constructor
  · intro hx
    exact hforward l x hx
  · intro hx
    have hback := hforward l⁻¹
      (suzukiTorusOperator a l * x * (suzukiTorusOperator a l)⁻¹) hx
    have htorus_inv : suzukiTorusOperator a l⁻¹ =
        (suzukiTorusOperator a l)⁻¹ := (suzukiTorusOperator_inv a l).symm
    simpa [htorus_inv, mul_assoc] using hback

/-- The torus normalizes the generated upper-root subgroup, by closure from
the individual conjugation laws. -/
theorem suzukiTorusOperatorGroup_le_normalizer_upperRoot [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1))) :
    suzukiTorusOperatorGroup (K := K) a ≤
      Subgroup.normalizer
        (upperRootMatrixGroup (K := K) a : Set (Matrix.GeneralLinearGroup (Fin 4) K)) := by
  rw [suzukiTorusOperatorGroup]
  apply (Subgroup.closure_le _).2
  rintro _ ⟨l, rfl⟩
  exact suzukiTorusOperator_mem_normalizer_upperRoot
    (K := K) a hK pi hpi_sq hpi_formula l

/-- The upper-root subgroup is normal in the local root-torus point-stabilizer
candidate. -/
theorem upperRoot_subgroupOf_pointStabilizer_normal [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1))) :
    ((upperRootMatrixGroup (K := K) a).subgroupOf
      (suzukiPointStabilizerOperatorGroup (K := K) a)).Normal := by
  rw [suzukiPointStabilizerOperatorGroup, sup_comm]
  exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
    (H := suzukiTorusOperatorGroup (K := K) a)
    (N := upperRootMatrixGroup (K := K) a)
    (suzukiTorusOperatorGroup_le_normalizer_upperRoot
      (K := K) a hK pi hpi_sq hpi_formula)

/-- The local root-torus subgroup is solvable: its normal upper-root subgroup
is solvable, and the quotient is a surjective image of the abelian torus. -/
theorem suzukiPointStabilizerOperatorGroup_isSolvable [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1))) :
    Group.IsSolvable (suzukiPointStabilizerOperatorGroup (K := K) a) := by
  let T := suzukiTorusOperatorGroup (K := K) a
  let U := upperRootMatrixGroup (K := K) a
  let B := suzukiPointStabilizerOperatorGroup (K := K) a
  letI : IsMulCommutative T := suzukiTorusOperatorGroup_isMulCommutative (K := K) a
  letI : Group.IsSolvable T := inferInstance
  letI : (U.subgroupOf B).Normal := by
    change ((upperRootMatrixGroup (K := K) a).subgroupOf
      (suzukiPointStabilizerOperatorGroup (K := K) a)).Normal
    exact upperRoot_subgroupOf_pointStabilizer_normal
      (K := K) a hK pi hpi_sq hpi_formula
  letI : Group.IsSolvable U := upperRootMatrixGroup_isSolvable (K := K) a hK
  let eU : U.subgroupOf B ≃* U := Subgroup.subgroupOfEquivOfLe le_sup_left
  letI : Group.IsSolvable (U.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := eU.toMonoidHom) eU.injective
  have hjoin : (U.subgroupOf B) ⊔ (T.subgroupOf B) = ⊤ := by
    change (U.subgroupOf (U ⊔ T)) ⊔ (T.subgroupOf (U ⊔ T)) = ⊤
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self (U ⊔ T)
  let f : T →* B ⧸ U.subgroupOf B :=
    (QuotientGroup.mk' (U.subgroupOf B)).comp
      ((T.subgroupOf B).subtype.comp (Subgroup.subgroupOfEquivOfLe le_sup_right).symm.toMonoidHom)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) y
    have hb : b ∈ (U.subgroupOf B) ⊔ (T.subgroupOf B) := by
      rw [hjoin]
      exact Subgroup.mem_top b
    rcases (Subgroup.mem_sup_of_normal_left
      (s := U.subgroupOf B) (t := T.subgroupOf B) (x := b)).mp hb with
      ⟨u, hu, t, ht, hut⟩
    refine ⟨⟨t.1, ht⟩, ?_⟩
    change QuotientGroup.mk' (U.subgroupOf B) t =
      QuotientGroup.mk' (U.subgroupOf B) b
    rw [← hut]
    simp [QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      QuotientGroup.eq_one_iff, hu]
  letI : Group.IsSolvable (B ⧸ U.subgroupOf B) := Group.isSolvable_of_surjective hf
  apply Group.isSolvable_of_ker_le_range (U.subgroupOf B).subtype
    (QuotientGroup.mk' (U.subgroupOf B))
  rw [QuotientGroup.ker_mk']
  rw [Subgroup.range_subtype]

/-- The root-torus operator subgroup fixes infinity, so it is contained in
the point stabilizer of the actual projective-space action. -/
theorem suzukiPointStabilizerOperatorGroup_le_stabilizer (a : ℕ) :
    suzukiPointStabilizerOperatorGroup (K := K) a ≤
      (MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))).comap
          Matrix.GeneralLinearGroup.toLin.toMonoidHom := by
  apply sup_le
  · intro g hg
    change Matrix.GeneralLinearGroup.toLin g ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))
    rw [MulAction.mem_stabilizer_iff]
    exact upperRootMatrixGroup_smul_infinity (K := K) a ⟨g, hg⟩
  · intro g hg
    change Matrix.GeneralLinearGroup.toLin g ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))
    rw [MulAction.mem_stabilizer_iff]
    exact suzukiTorusOperatorGroup_smul_infinity (K := K) a ⟨g, hg⟩

/-- The upper-root operator subgroup acts transitively on the finite chart of
the Suzuki ovoid. In characteristic two, choose the two root parameters to
translate the input coordinates to the desired output coordinates. -/
theorem upperRootMatrixGroup_transitive_on_finite_chart
    [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (x y x' y' : K) :
    ∃ g : upperRootMatrixGroup (K := K) a,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
          ovoidPoint pi x y = ovoidPoint pi x' y' := by
  let u : K := x + x'
  let v : K := y + y' + pi u * x'
  have hzero : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hxx : x + x = 0 := by linear_combination x * hzero
  have hyy : y + y = 0 := by linear_combination y * hzero
  have hcross : pi u * x' + pi u * x' = 0 := by
    linear_combination (pi u * x') * hzero
  have hu : x + u = x' := by
    dsimp [u]
    calc
      x + (x + x') = (x + x) + x' := by ac_rfl
      _ = x' := by rw [hxx, zero_add]
  have hv : y + v + pi u * (x + u) = y' := by
    rw [hu]
    dsimp [v]
    linear_combination hyy + hcross
  refine ⟨⟨upperRootOperator a u v,
    Subgroup.subset_closure ⟨u, v, rfl⟩⟩, ?_⟩
  change (Matrix.GeneralLinearGroup.toLin
    (upperRootOperator a u v)).toLinearEquiv • ovoidPoint pi x y = _
  rw [upperRootOperator_smul_finite a pi hpi_sq hpi_formula]
  exact congrArg₂ (ovoidPoint pi) hu hv

/-- Every element of the upper-root operator subgroup preserves the Suzuki
ovoid. The finite-field hypothesis lets the generator's injective action on
the finite ovoid be upgraded from inclusion to equality, hence to membership
in the set stabilizer. -/
theorem upperRootMatrixGroup_smul_mem_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1))) :
    ∀ g : upperRootMatrixGroup (K := K) a, ∀ z, z ∈ ovoid pi →
      (Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈
        ovoid pi := by
  let O := ovoid pi
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hfinite : O.Finite := Set.toFinite O
  have hgens :
      {g : Matrix.GeneralLinearGroup (Fin 4) K |
        ∃ u v : K, g = upperRootOperator a u v} ⊆ S := by
    intro A hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O
    rw [MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite]
    apply Set.smul_set_subset_iff.2
    rintro z hz
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
    rcases hA with ⟨u, v, rfl⟩
    exact upperRootOperator_maps_ovoid a pi u v hpi_sq hpi_formula z hz
  have hclosure : upperRootMatrixGroup (K := K) a ≤ S := by
    rw [upperRootMatrixGroup, Subgroup.closure_le]
    exact hgens
  intro g z hz
  have hgS : Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O := hclosure g.property
  have hsubset : Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K) • O ⊆ O :=
    (MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite).1 hgS
  have hz' := hsubset (Set.smul_mem_smul_set hz)
  change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ O
  exact hz'

/-- The subgroup generated by upper-root and antidiagonal Weyl operators,
both acting on the same four-dimensional module carrier. -/
def rootWeylOperatorGroup (a : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  Subgroup.closure
    ({g | ∃ u v : K, g = upperRootOperator a u v} ∪
      {suzukiWeylOperator (K := K)})

/-- The upper-root translations form a subgroup of the root-plus-Weyl
operator group. This makes their finite-chart transitivity available inside
the same noncommutative carrier used for the transitive ovoid action. -/
theorem upperRootMatrixGroup_le_rootWeylOperatorGroup (a : ℕ) :
    upperRootMatrixGroup (K := K) a ≤ rootWeylOperatorGroup (K := K) a := by
  rw [upperRootMatrixGroup, rootWeylOperatorGroup, Subgroup.closure_le]
  intro g hg
  exact Subgroup.subset_closure (Or.inl hg)

/-- The local root-plus-Weyl operator subgroup sends every Suzuki ovoid point
to the distinguished point at infinity. An upper-root translation sends a
finite chart point to `(0,0)`, and the Weyl operator sends that point to
infinity. This is an action result, not a simplicity claim. -/
theorem rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (z : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) :
    ∃ g : rootWeylOperatorGroup (K := K) a,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z =
          ovoidInfinity := by
  change z ∈ {ovoidInfinity} ∪
    Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz
  rcases hz with hz | ⟨⟨x, y⟩, rfl⟩
  · have hz' : z = ovoidInfinity := by simpa using hz
    subst z
    exact ⟨1, by simp [ovoidInfinity]⟩
  · let r : rootWeylOperatorGroup (K := K) a :=
      ⟨upperRootOperator a x y,
        Subgroup.subset_closure (Or.inl ⟨x, y, rfl⟩)⟩
    let w : rootWeylOperatorGroup (K := K) a :=
      ⟨suzukiWeylOperator (K := K),
        Subgroup.subset_closure (Or.inr rfl)⟩
    have hxx : x + x = 0 := by
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination x * htwo
    have hyy : y + y = 0 := by
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination y * htwo
    have hroot :
        (Matrix.GeneralLinearGroup.toLin
          (upperRootOperator a x y)).toLinearEquiv • ovoidPoint pi x y =
            ovoidPoint pi 0 0 := by
      simpa [hxx, hyy] using
        upperRootOperator_smul_finite a pi hpi_sq hpi_formula x y x y
    refine ⟨w * r, ?_⟩
    calc
      (Matrix.GeneralLinearGroup.toLin
          ((w * r : rootWeylOperatorGroup (K := K) a) :
            Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
          ovoidPoint pi x y =
        (Matrix.GeneralLinearGroup.toLin
            (w : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin
              (r : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
            ovoidPoint pi x y) := by
          change (Matrix.GeneralLinearGroup.toLin
            ((w : Matrix.GeneralLinearGroup (Fin 4) K) *
              (r : Matrix.GeneralLinearGroup (Fin 4) K))).toLinearEquiv • _ = _
          rw [(Matrix.GeneralLinearGroup.toLin).map_mul,
            LinearMap.GeneralLinearGroup.toLinearEquiv_mul, mul_smul]
      _ = (Matrix.GeneralLinearGroup.toLin
            (suzukiWeylOperator (K := K))).toLinearEquiv •
          ovoidPoint pi 0 0 := by
            rw [hroot]
      _ = ovoidInfinity := suzukiWeylOperator_smul_zero pi

/-- The root-plus-Weyl subgroup acts transitively on the Suzuki ovoid under
the same field and automorphism hypotheses: move each of two points to
infinity, then compose one transporter with the inverse of the other. -/
theorem rootWeylOperatorGroup_transitive_on_ovoid
    [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (z z' : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) (hz' : z' ∈ ovoid pi) :
    ∃ g : rootWeylOperatorGroup (K := K) a,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z = z' := by
  obtain ⟨g, hg⟩ := rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    a pi hpi_sq hpi_formula z hz
  obtain ⟨g', hg'⟩ := rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    a pi hpi_sq hpi_formula z' hz'
  refine ⟨g'⁻¹ * g, ?_⟩
  calc
    (Matrix.GeneralLinearGroup.toLin
        ((g'⁻¹ * g : rootWeylOperatorGroup (K := K) a) :
          Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z =
      (Matrix.GeneralLinearGroup.toLin
          (g'⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin
            (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z) := by
        change (Matrix.GeneralLinearGroup.toLin
          (((g' : rootWeylOperatorGroup (K := K) a) :
            Matrix.GeneralLinearGroup (Fin 4) K)⁻¹ *
            (g : Matrix.GeneralLinearGroup (Fin 4) K))).toLinearEquiv • _ = _
        rw [(Matrix.GeneralLinearGroup.toLin).map_mul,
          LinearMap.GeneralLinearGroup.toLinearEquiv_mul, mul_smul]
    _ = (Matrix.GeneralLinearGroup.toLin
          (g'⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ovoidInfinity := by rw [hg]
    _ = z' := by
      rw [← hg', (Matrix.GeneralLinearGroup.toLin).map_inv,
        LinearMap.GeneralLinearGroup.toLinearEquiv_inv]
      exact inv_smul_smul _ _

/-- Every element in the root-plus-Weyl operator subgroup preserves the
projective ovoid over finite fields, under the explicit Suzuki norm-zero
property. -/
theorem rootWeylOperatorGroup_smul_mem_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0) :
    ∀ g : rootWeylOperatorGroup (K := K) a, ∀ z, z ∈ ovoid pi →
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ ovoid pi := by
  let O := ovoid pi
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hfinite : O.Finite := Set.toFinite O
  have hgens :
      ({g : Matrix.GeneralLinearGroup (Fin 4) K |
        ∃ u v : K, g = upperRootOperator a u v} ∪
        {suzukiWeylOperator (K := K)}) ⊆ S := by
    intro A hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O
    rw [MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite]
    apply Set.smul_set_subset_iff.2
    rintro z hz
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
    rcases hA with ⟨u, v, rfl⟩ | hweyl
    · exact upperRootOperator_maps_ovoid a pi u v hpi_sq hpi_formula z hz
    · have hA' : A = suzukiWeylOperator (K := K) := by simpa using hweyl
      subst A
      exact suzukiWeylOperator_maps_ovoid pi hpi_sq hnorm_zero z hz
  have hclosure : rootWeylOperatorGroup (K := K) a ≤ S := by
    rw [rootWeylOperatorGroup, Subgroup.closure_le]
    exact hgens
  intro g z hz
  have hgS : Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O := hclosure g.property
  have hsubset : Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K) • O ⊆ O :=
    (MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite).1 hgS
  have hz' := hsubset (Set.smul_mem_smul_set hz)
  change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ O
  exact hz'

/-- The root-plus-Weyl operator group acts two-transitively on the Suzuki
ovoid, provided the explicit finite-field norm condition makes the ovoid
stable. The proof uses upper-root transitivity on the finite chart inside
the stabilizer of infinity, together with transitivity of the full group. -/
theorem rootWeylOperatorGroup_two_transitive_on_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0)
    (z₁ z₂ z₃ z₄ : ℙ K (Fin 4 → K))
    (hz₁ : z₁ ∈ ovoid pi) (hz₂ : z₂ ∈ ovoid pi)
    (hz₃ : z₃ ∈ ovoid pi) (hz₄ : z₄ ∈ ovoid pi)
    (hne₁ : z₁ ≠ z₂) (hne₂ : z₃ ≠ z₄) :
    ∃ g : rootWeylOperatorGroup (K := K) a,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₁ = z₃ ∧
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₂ = z₄ := by
  let ρ : rootWeylOperatorGroup (K := K) a →*
      LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    (Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp
      (rootWeylOperatorGroup (K := K) a).subtype
  letI : MulAction (rootWeylOperatorGroup (K := K) a)
      (ℙ K (Fin 4 → K)) := MulAction.compHom _ ρ
  obtain ⟨g, hg₁⟩ := rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    a pi hpi_sq hpi_formula z₁ hz₁
  obtain ⟨g', hg₃⟩ := rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    a pi hpi_sq hpi_formula z₃ hz₃
  have hg₁' : g • z₁ = ovoidInfinity (K := K) := by
    change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₁ = _
    exact hg₁
  have hg₃' : g' • z₃ = ovoidInfinity (K := K) := by
    change (Matrix.GeneralLinearGroup.toLin
      (g' : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₃ = _
    exact hg₃
  have hz₂g : g • z₂ ∈ ovoid pi := by
    change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₂ ∈ ovoid pi
    exact rootWeylOperatorGroup_smul_mem_ovoid a pi hpi_sq hpi_formula
      hnorm_zero g z₂ hz₂
  have hz₄g' : g' • z₄ ∈ ovoid pi := by
    change (Matrix.GeneralLinearGroup.toLin
      (g' : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₄ ∈ ovoid pi
    exact rootWeylOperatorGroup_smul_mem_ovoid a pi hpi_sq hpi_formula
      hnorm_zero g' z₄ hz₄
  have hne₂g : g • z₂ ≠ ovoidInfinity := by
    intro h
    apply hne₁
    have heq : g • z₁ = g • z₂ := hg₁.trans h.symm
    have heq' := congrArg (fun z => g⁻¹ • z) heq
    simpa using heq'
  have hne₄g' : g' • z₄ ≠ ovoidInfinity := by
    intro h
    apply hne₂
    have heq : g' • z₃ = g' • z₄ := hg₃.trans h.symm
    have heq' := congrArg (fun z => g'⁻¹ • z) heq
    simpa using heq'
  have hcoord₂ : ∃ x y : K, g • z₂ = ovoidPoint pi x y := by
    change g • z₂ ∈ {ovoidInfinity} ∪
      Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz₂g
    rcases hz₂g with hi | ⟨⟨x, y⟩, h⟩
    · exact (hne₂g hi).elim
    · exact ⟨x, y, h.symm⟩
  have hcoord₄ : ∃ x y : K, g' • z₄ = ovoidPoint pi x y := by
    change g' • z₄ ∈ {ovoidInfinity} ∪
      Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz₄g'
    rcases hz₄g' with hi | ⟨⟨x, y⟩, h⟩
    · exact (hne₄g' hi).elim
    · exact ⟨x, y, h.symm⟩
  obtain ⟨x, y, hxy⟩ := hcoord₂
  obtain ⟨x', y', hx'y'⟩ := hcoord₄
  obtain ⟨k₀, hk₀⟩ := upperRootMatrixGroup_transitive_on_finite_chart
    a pi hpi_sq hpi_formula x y x' y'
  let k : rootWeylOperatorGroup (K := K) a :=
    ⟨(k₀ : Matrix.GeneralLinearGroup (Fin 4) K),
      upperRootMatrixGroup_le_rootWeylOperatorGroup (K := K) a k₀.property⟩
  have hk : k • (g • z₂) = g' • z₄ := by
    change (Matrix.GeneralLinearGroup.toLin
      (k₀ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        (g • z₂) = g' • z₄
    calc
      _ = (Matrix.GeneralLinearGroup.toLin
          (k₀ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
            ovoidPoint pi x y := congrArg _ hxy
      _ = ovoidPoint pi x' y' := hk₀
      _ = g' • z₄ := hx'y'.symm
  have hkinf : k • ovoidInfinity (K := K) = ovoidInfinity (K := K) := by
    change (Matrix.GeneralLinearGroup.toLin
      (k₀ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ovoidInfinity (K := K) = ovoidInfinity (K := K)
    exact upperRootMatrixGroup_smul_infinity (K := K) a k₀
  refine ⟨g'⁻¹ * k * g, ?_, ?_⟩
  · change (g'⁻¹ * k * g) • z₁ = z₃
    rw [mul_smul, mul_smul, hg₁', hkinf]
    rw [← hg₃']
    exact inv_smul_smul g' z₃
  · change (g'⁻¹ * k * g) • z₂ = z₄
    rw [mul_smul, mul_smul, hk]
    exact inv_smul_smul g' z₄

/-- The root-plus-Weyl subgroup is genuinely noncommutative: the upper-root
operator at `(1,0)` and the antidiagonal Weyl operator differ in their
`(0,0)` matrix entries after multiplication in the two orders. -/
theorem suzukiUpperMatrixGroup_smul_mem_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0) :
    ∀ g : Chevalley.suzukiUpperMatrixGroup a K, ∀ z, z ∈ ovoid pi →
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ ovoid pi := by
  let O := ovoid pi
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hfinite : O.Finite := Set.toFinite O
  have hgens : Chevalley.suzukiUpperMatrixGenerators a K ⊆ S := by
    intro A hA
    change ((A : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).transpose ∈
      {M : Matrix (Fin 4) (Fin 4) K |
        (∃ u v : K, M = suzukiS a u v) ∨
          (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K} at hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O
    rw [MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite]
    apply Set.smul_set_subset_iff.2
    rintro z hz
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
    rcases hA with ⟨u, v, hroot⟩ | ⟨l, htorus⟩ | hw
    · have hAeq : A = upperRootOperator a u v := by
        apply Units.ext
        apply Matrix.transpose_injective
        simpa [upperRootOperator, suzukiSGL] using hroot
      rw [hAeq]
      exact upperRootOperator_maps_ovoid a pi u v hpi_sq hpi_formula z hz
    · have hAeq : A = suzukiTorusOperator a l := by
        have hmat : (A : Matrix (Fin 4) (Fin 4) K) = suzukiD a l := by
          calc
            (A : Matrix (Fin 4) (Fin 4) K) =
                ((A : Matrix (Fin 4) (Fin 4) K).transpose).transpose := by simp
            _ = (suzukiD a l).transpose := congrArg Matrix.transpose htorus
            _ = suzukiD a l := by simp [suzukiD]
        apply Units.ext
        simpa [suzukiTorusOperator] using hmat
      rw [hAeq]
      exact suzukiTorusOperator_maps_ovoid a pi hpi_sq hpi_formula l z hz
    · have hAeq : A = suzukiWeylOperator (K := K) := by
        have hmat : (A : Matrix (Fin 4) (Fin 4) K) = Chevalley.suzukiW K := by
          calc
            (A : Matrix (Fin 4) (Fin 4) K) =
                ((A : Matrix (Fin 4) (Fin 4) K).transpose).transpose := by simp
            _ = (Chevalley.suzukiW K).transpose := congrArg Matrix.transpose hw
            _ = Chevalley.suzukiW K := by
              ext i j
              simp [Chevalley.suzukiW, Nat.add_comm]
        apply Units.ext
        simpa [suzukiWeylOperator, suzukiWeylMatrix, Chevalley.suzukiW] using hmat
      rw [hAeq]
      exact suzukiWeylOperator_maps_ovoid pi hpi_sq hnorm_zero z hz
  have hclosure : Chevalley.suzukiUpperMatrixGroup a K ≤ S := by
    rw [Chevalley.suzukiUpperMatrixGroup, Subgroup.closure_le]
    exact hgens
  intro g z hz
  have hgS : Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O := hclosure g.property
  have hsubset : Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K) • O ⊆ O :=
    (MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite).1 hgS
  have hz' := hsubset (Set.smul_mem_smul_set hz)
  change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ O
  exact hz'

theorem rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (a : ℕ) :
    rootWeylOperatorGroup (K := K) a ≤ Chevalley.suzukiUpperMatrixGroup a K := by
  rw [rootWeylOperatorGroup, Subgroup.closure_le]
  intro A hA
  rcases hA with ⟨u, v, hA⟩ | hA
  · apply Subgroup.subset_closure
    change ((A : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).transpose ∈
      {M : Matrix (Fin 4) (Fin 4) K |
        (∃ u v : K, M = suzukiS a u v) ∨
          (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K}
    subst A
    left
    exact ⟨u, v, by simp [upperRootOperator, suzukiSGL]⟩
  · apply Subgroup.subset_closure
    change ((A : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).transpose ∈
      {M : Matrix (Fin 4) (Fin 4) K |
        (∃ u v : K, M = suzukiS a u v) ∨
          (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K}
    have hAeq : A = suzukiWeylOperator (K := K) := by simpa using hA
    subst A
    right
    right
    ext i j
    simp [suzukiWeylOperator, suzukiWeylMatrix, Chevalley.suzukiW,
      Nat.add_comm]

/-- A diagonal Suzuki torus operator is a generator of the same upper
transpose-presentation operator group as the root and Weyl operators. -/
theorem suzukiTorusOperator_mem_suzukiUpperMatrixGroup (a : ℕ) (l : Kˣ) :
    suzukiTorusOperator a l ∈ Chevalley.suzukiUpperMatrixGroup a K := by
  apply Subgroup.subset_closure
  change ((suzukiTorusOperator a l : Matrix.GeneralLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).transpose ∈
    {M : Matrix (Fin 4) (Fin 4) K |
      (∃ u v : K, M = suzukiS a u v) ∨
        (∃ m : Kˣ, M = suzukiD a m) ∨ M = Chevalley.suzukiW K}
  right
  left
  refine ⟨l, ?_⟩
  change (suzukiD a l).transpose = suzukiD a l
  ext i j
  by_cases hij : i = j
  · subst j
    simp [suzukiD, Matrix.diagonal_apply]
  · have hji : j ≠ i := Ne.symm hij
    simp [suzukiD, Matrix.diagonal_apply, hij, hji]

/-- The local root–torus point-stabilizer subgroup embeds into the actual
upper-orientation Suzuki operator group. -/
theorem suzukiPointStabilizerOperatorGroup_le_suzukiUpperMatrixGroup
    (a : ℕ) :
    suzukiPointStabilizerOperatorGroup (K := K) a ≤
      Chevalley.suzukiUpperMatrixGroup a K := by
  rw [suzukiPointStabilizerOperatorGroup]
  apply sup_le
  · exact (upperRootMatrixGroup_le_rootWeylOperatorGroup (K := K) a).trans
      (rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a)
  · apply (Subgroup.closure_le
      (Chevalley.suzukiUpperMatrixGroup a K)).2
    rintro _ ⟨l, rfl⟩
    exact suzukiTorusOperator_mem_suzukiUpperMatrixGroup (K := K) a l

/-- The antidiagonal Weyl operator belongs to the same transpose-presentation
Suzuki group as the upper-root and torus operators. -/
theorem suzukiWeylOperator_mem_suzukiUpperMatrixGroup (a : ℕ) :
    suzukiWeylOperator (K := K) ∈ Chevalley.suzukiUpperMatrixGroup a K := by
  apply Subgroup.subset_closure
  change ((suzukiWeylOperator (K := K) : Matrix.GeneralLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).transpose ∈
    {M : Matrix (Fin 4) (Fin 4) K |
      (∃ u v : K, M = suzukiS a u v) ∨
        (∃ m : Kˣ, M = suzukiD a m) ∨ M = Chevalley.suzukiW K}
  right
  right
  change suzukiWeylMatrix.transpose = Chevalley.suzukiW K
  ext i j
  simp [suzukiWeylMatrix, Chevalley.suzukiW, Matrix.transpose_apply,
    Nat.add_comm]

/-- The `(0,1)` root/Weyl factorization from the Suzuki Bruhat argument, in
the local transpose presentation. Its torus factor is the identity because
the associated norm parameter is `1`. -/
theorem suzukiWeyl_root_weyl_bruhat_unit [CharP K 2] (a : ℕ) :
    suzukiWeylOperator (K := K) * upperRootOperator a 0 1 *
        suzukiWeylOperator (K := K) =
      upperRootOperator a 1 1 * suzukiWeylOperator (K := K) *
        upperRootOperator a 1 0 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hfour : (4 : K) = 0 := by
    calc
      (4 : K) = (2 : K) + 2 := by norm_num
      _ = 0 := CharTwo.add_self_eq_zero _
  have hsix : (6 : K) = 0 := by
    calc
      (6 : K) = (4 : K) + 2 := by norm_num
      _ = 0 := by rw [hfour, htwo]; simp
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiWeylOperator, suzukiWeylMatrix, upperRootOperator,
      suzukiSGL, suzukiS, suzukiN, Matrix.mul_apply,
      Fin.sum_univ_four]
  all_goals try omega
  all_goals norm_num <;> first
    | exact htwo
    | exact hfour
    | exact hsix
    | exact htwo.symm
    | exact hfour.symm
    | exact hsix.symm

/-- The Weyl class in the abelianization of the local Suzuki operator group
has order dividing two. This is the involution half of the external
Weyl-image argument; identifying that class with a torus class still requires
the root/Weyl Bruhat factorization. -/
theorem suzukiWeylOperator_image_sq_eq_one (a : ℕ)
    (g : Chevalley.suzukiUpperMatrixGroup a K)
    (hg : (g : Matrix.GeneralLinearGroup (Fin 4) K) =
      suzukiWeylOperator (K := K)) :
    Abelianization.of g ^ 2 = 1 := by
  have hw : suzukiWeylOperator (K := K) *
      suzukiWeylOperator (K := K) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mul_apply,
        Fin.sum_univ_four]
  have hsq : g * g = 1 := by
    apply Subtype.ext
    change (g : Matrix.GeneralLinearGroup (Fin 4) K) *
      (g : Matrix.GeneralLinearGroup (Fin 4) K) = 1
    rw [hg, hw]
  rw [pow_two, ← map_mul, hsq, map_one]

/-- The image of a Suzuki torus operator in the full group's abelianization
has exponent dividing the order of the multiplicative field group. -/
theorem suzukiTorusOperator_image_pow_card_units_eq_one [Finite K] (a : ℕ)
    (l : Kˣ) (g : Chevalley.suzukiUpperMatrixGroup a K)
    (hg : (g : Matrix.GeneralLinearGroup (Fin 4) K) =
      suzukiTorusOperator a l) :
    Abelianization.of g ^ Nat.card Kˣ = 1 := by
  let t : Kˣ →* Chevalley.suzukiUpperMatrixGroup a K := {
    toFun := fun u => ⟨suzukiTorusOperator a u,
      suzukiTorusOperator_mem_suzukiUpperMatrixGroup (K := K) a u⟩
    map_one' := by
      apply Subtype.ext
      exact suzukiTorusOperator_one a
    map_mul' := by
      intro u v
      apply Subtype.ext
      change suzukiTorusOperator a (u * v) =
        suzukiTorusOperator a u * suzukiTorusOperator a v
      exact (suzukiTorusOperator_mul a u v).symm
  }
  have hpow : l ^ Nat.card Kˣ = 1 := pow_card_eq_one'
  have htg : t l = g := by
    apply Subtype.ext
    exact hg.symm
  calc
    Abelianization.of g ^ Nat.card Kˣ =
        Abelianization.of (t l) ^ Nat.card Kˣ := by rw [← htg]
    _ = Abelianization.of (t l ^ Nat.card Kˣ) := by rw [map_pow]
    _ = Abelianization.of (t (l ^ Nat.card Kˣ)) := by
      congr 1
      exact (map_pow t l (Nat.card Kˣ)).symm
    _ = 1 := by rw [hpow, map_one, map_one]

/-- If the Weyl class is identified with a torus class in the local Suzuki
operator group's abelianization, the two coprime order bounds force that class
to be trivial. The missing Bruhat theorem must provide `hwt`. -/
theorem suzukiWeylOperator_image_eq_one_of_eq_torus_image [Finite K]
    (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w t : Chevalley.suzukiUpperMatrixGroup a K)
    (hw : (w : Matrix.GeneralLinearGroup (Fin 4) K) =
      suzukiWeylOperator (K := K))
    (l : Kˣ)
    (ht : (t : Matrix.GeneralLinearGroup (Fin 4) K) =
      suzukiTorusOperator a l)
    (hwt : Abelianization.of w = Abelianization.of t) :
    Abelianization.of w = 1 := by
  let q : ℕ := 2 ^ (2 * a + 1)
  have hq_card : Nat.card K = q := by
    dsimp [q]
    exact hK
  have h_units_card : Nat.card Kˣ = q - 1 := by
    rw [Nat.card_units, hq_card]
  have hq_even : Even q := by
    refine ⟨2 ^ (2 * a), ?_⟩
    dsimp only [q]
    rw [show 2 * a + 1 = 1 + 2 * a by omega, pow_add]
    omega
  have hcoprime : Nat.Coprime 2 (q - 1) :=
    (Nat.Even.sub_odd (m := q) (n := 1) (by
      dsimp only [q]
      exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)) hq_even odd_one).coprime_two_left
  have hw_two : Abelianization.of w ^ 2 = 1 :=
    suzukiWeylOperator_image_sq_eq_one a w hw
  have ht_q : Abelianization.of t ^ (q - 1) = 1 := by
    rw [← h_units_card]
    exact suzukiTorusOperator_image_pow_card_units_eq_one
      (K := K) a l t ht
  have hw_q : Abelianization.of w ^ (q - 1) = 1 := by
    rw [hwt]
    exact ht_q
  have horder : orderOf (Abelianization.of w) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime
      (orderOf_dvd_of_pow_eq_one hw_two)
      (orderOf_dvd_of_pow_eq_one hw_q)
  exact orderOf_eq_one_iff.mp horder

/-- Every central upper-root operator has trivial image in the abelianization
of the full Suzuki upper-orientation operator group. The commutator is formed
inside the upper-root subgroup and then transported to the full operator
group. -/
theorem upperRootCentralOperator_trivial_in_upperAbelianization
    [Finite K] [CharP K 2] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 0 < a)
    (pi : K ≃+* K) (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1))) (b : K)
    (g : Chevalley.suzukiUpperMatrixGroup a K)
    (hg : (g : Matrix.GeneralLinearGroup (Fin 4) K) = upperRootOperator a 0 b) :
    Abelianization.of g = 1 := by
  let U := upperRootMatrixGroup (K := K) a
  let S := Chevalley.suzukiUpperMatrixGroup a K
  have hU_le_S : U ≤ S :=
    (upperRootMatrixGroup_le_rootWeylOperatorGroup (K := K) a).trans
      (rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a)
  let inc : U →* S := Subgroup.inclusion hU_le_S
  let phi : ↥S →* Abelianization ↥S := Abelianization.of
  let zU : U := ⟨upperRootOperator a 0 b,
    by
      apply Subgroup.subset_closure
      exact ⟨0, b, rfl⟩⟩
  let zS : S := inc zU
  have hzS : zS = g := by
    apply Subtype.ext
    change upperRootOperator a 0 b = (g : Matrix.GeneralLinearGroup (Fin 4) K)
    exact hg.symm
  obtain ⟨x, y, hxy⟩ := upperRootCentralOperator_is_commutator_of_field
    (K := K) a ha hK pi hpi_sq hpi_formula b
  have hcomm : ⁅x, y⁆ = zU := by
    apply Subtype.ext
    simpa [commutatorElement_def] using congrArg Subtype.val hxy
  have hzcomm : zU ∈ commutator U := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hzker : zU ∈ (phi.comp inc).ker :=
    Abelianization.commutator_subset_ker (phi.comp inc) hzcomm
  rw [← hzS]
  change phi (inc zU) = 1
  exact hzker

set_option maxHeartbeats 5000000 in
/-- Every upper-root generator has trivial image in the abelianization of the
full Suzuki upper-orientation operator group. The diagonal torus rescales the
first root parameter, while the root multiplication law makes its image have
square one; writing `u = x + s*x` then kills that image. -/
theorem upperRootOperator_trivial_in_upperAbelianization
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1)))
    (u v : K) (g : Chevalley.suzukiUpperMatrixGroup a K)
    (hg : (g : Matrix.GeneralLinearGroup (Fin 4) K) = upperRootOperator a u v) :
    Abelianization.of g = 1 := by
  let U := upperRootMatrixGroup (K := K) a
  let S := Chevalley.suzukiUpperMatrixGroup a K
  have hU_le_S : U ≤ S :=
    (upperRootMatrixGroup_le_rootWeylOperatorGroup (K := K) a).trans
      (rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a)
  let inc : U →* S := Subgroup.inclusion hU_le_S
  let phi : ↥S →* Abelianization ↥S := Abelianization.of
  let rU : K → K → U := fun x y =>
    ⟨upperRootOperator a x y, by
      apply Subgroup.subset_closure
      exact ⟨x, y, rfl⟩⟩
  let r : K → K → S := fun x y => inc (rU x y)
  have hr_mul (x y x' y' : K) :
      r x y * r x' y' =
        r (x + x') (y + y' + x' ^ (2 ^ (a + 1)) * x) := by
    apply Subtype.ext
    exact suzukiSGL_mul a hK x y x' y'
  have hcentral (y : K) : phi (r 0 y) = 1 := by
    exact upperRootCentralOperator_trivial_in_upperAbelianization
      (K := K) a hK ha pi hpi_sq hpi_formula y (r 0 y) rfl
  have hforget_second (x y : K) : phi (r x y) = phi (r x 0) := by
    have hmul : r x 0 * r 0 y = r x y := by
      simpa using hr_mul x 0 0 y
    rw [← hmul, map_mul, hcentral, mul_one]
  have hroot_sq (x : K) : phi (r x 0) ^ 2 = 1 := by
    have hsq : r x 0 * r x 0 = r 0 (x ^ (2 ^ (a + 1)) * x) := by
      simpa only [CharTwo.add_self_eq_zero, zero_add] using hr_mul x 0 x 0
    rw [pow_two, ← map_mul, hsq, hcentral]
  obtain ⟨t, ht⟩ := suzukiTits_nontrivial (K := K) a ha hK pi hpi_sq
  have ht0 : t ≠ 0 := by
    intro hzero
    subst t
    exact ht (by simp)
  have ht1 : t ≠ 1 := by
    intro hone
    apply ht
    simpa [hone] using (map_one pi : pi (1 : K) = 1)
  let s : Kˣ := Units.mk0 t ht0
  have hs : s ≠ 1 := by
    intro hone
    apply ht1
    exact congrArg Units.val hone
  have hs_add_one : (s : K) + 1 ≠ 0 := by
    intro hzero
    apply hs
    apply Units.ext
    simpa [CharTwo.neg_eq] using (add_eq_zero_iff_eq_neg.mp hzero)
  let torus : S := ⟨suzukiTorusOperator a s,
    suzukiTorusOperator_mem_suzukiUpperMatrixGroup (K := K) a s⟩
  have hscale (x : K) : phi (r ((s : K) * x) 0) = phi (r x 0) := by
    have hconj : torus * r x 0 * torus⁻¹ = r ((s : K) * x) 0 := by
      apply Subtype.ext
      change suzukiTorusOperator a s * upperRootOperator a x 0 *
        (suzukiTorusOperator a s)⁻¹ = upperRootOperator a ((s : K) * x) 0
      simpa only [mul_zero] using
        suzukiTorusOperator_conj_upperRoot a pi hpi_sq hpi_formula s x 0
    rw [← hconj, map_mul, map_mul, map_inv]
    calc
      phi torus * phi (r x 0) * (phi torus)⁻¹ =
          phi (r x 0) * phi torus * (phi torus)⁻¹ := by
            rw [mul_comm (phi torus) (phi (r x 0))]
      _ = phi (r x 0) := mul_inv_cancel_right _ _
  let x : K := ((s : K) + 1)⁻¹ * u
  have hfirst : x + (s : K) * x = u := by
    dsimp only [x]
    rw [show ((s : K) + 1)⁻¹ * u + (s : K) *
        (((s : K) + 1)⁻¹ * u) =
      (((s : K) + 1)⁻¹ * ((s : K) + 1)) * u by ring]
    rw [inv_mul_cancel₀ hs_add_one, one_mul]
  have hproduct_image : phi (r x 0 * r ((s : K) * x) 0) = 1 := by
    rw [map_mul, hscale, ← pow_two, hroot_sq]
  rw [hr_mul, hfirst, hforget_second] at hproduct_image
  have hroot_image : phi (r u 0) = 1 := hproduct_image
  have htarget : phi (r u v) = 1 := by
    rw [hforget_second]
    exact hroot_image
  have hr_eq : r u v = g := by
    apply Subtype.ext
    change upperRootOperator a u v = (g : Matrix.GeneralLinearGroup (Fin 4) K)
    exact hg.symm
  rw [hr_eq] at htarget
  change phi g = 1
  exact htarget

/-- Under the standard positive-rank Suzuki field hypotheses, the Weyl
operator has trivial image in the full operator group's abelianization. The
local `(0,1)` Bruhat factorization has identity torus factor, and both root
factors vanish in the abelianization. -/
theorem suzukiWeylOperator_trivial_in_upperAbelianization
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1)))
    (w : Chevalley.suzukiUpperMatrixGroup a K)
    (hw : (w : Matrix.GeneralLinearGroup (Fin 4) K) =
      suzukiWeylOperator (K := K)) :
    Abelianization.of w = 1 := by
  let S := Chevalley.suzukiUpperMatrixGroup a K
  let U := upperRootMatrixGroup (K := K) a
  have hU_le_S : U ≤ S :=
    (upperRootMatrixGroup_le_rootWeylOperatorGroup (K := K) a).trans
      (rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a)
  let inc : U →* S := Subgroup.inclusion hU_le_S
  let r : K → K → S := fun x y => inc
    ⟨upperRootOperator a x y,
      by
        apply Subgroup.subset_closure
        exact ⟨x, y, rfl⟩⟩
  let phi : S →* Abelianization S := Abelianization.of
  let w₀ : S := ⟨suzukiWeylOperator (K := K),
    suzukiWeylOperator_mem_suzukiUpperMatrixGroup (K := K) a⟩
  have hw_factor : w₀ * r 0 1 * w₀ = r 1 1 * w₀ * r 1 0 := by
    apply Subtype.ext
    exact suzukiWeyl_root_weyl_bruhat_unit (K := K) a
  have hfactor_image := congrArg phi hw_factor
  have hr_image (x y : K) : phi (r x y) = 1 := by
    exact upperRootOperator_trivial_in_upperAbelianization
      (K := K) a ha hK pi hpi_sq hpi_formula x y (r x y) rfl
  have hw₀_eq : w = w₀ := by
    apply Subtype.ext
    exact hw
  have hmul : phi w₀ * phi w₀ = phi w₀ := by
    simpa only [map_mul, hr_image, one_mul, mul_one] using hfactor_image
  rw [hw₀_eq]
  exact mul_left_cancel (hmul.trans (mul_one _).symm)

/-- Every local Suzuki torus generator also has trivial image in the full
operator group's abelianization. Weyl conjugation identifies its image with
its inverse, while the torus order divides the odd number `|Kˣ|`. -/
theorem suzukiTorusOperator_trivial_in_upperAbelianization
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1)))
    (l : Kˣ) (g : Chevalley.suzukiUpperMatrixGroup a K)
    (hg : (g : Matrix.GeneralLinearGroup (Fin 4) K) =
      suzukiTorusOperator a l) :
    Abelianization.of g = 1 := by
  let S := Chevalley.suzukiUpperMatrixGroup a K
  let phi : S →* Abelianization S := Abelianization.of
  let torus : Kˣ →* S := {
    toFun := fun u => ⟨suzukiTorusOperator a u,
      suzukiTorusOperator_mem_suzukiUpperMatrixGroup (K := K) a u⟩
    map_one' := by
      apply Subtype.ext
      exact suzukiTorusOperator_one a
    map_mul' := by
      intro u v
      apply Subtype.ext
      change suzukiTorusOperator a (u * v) =
        suzukiTorusOperator a u * suzukiTorusOperator a v
      exact (suzukiTorusOperator_mul a u v).symm
  }
  let w : S := ⟨suzukiWeylOperator (K := K),
    suzukiWeylOperator_mem_suzukiUpperMatrixGroup (K := K) a⟩
  have hw : phi w = 1 :=
    suzukiWeylOperator_trivial_in_upperAbelianization
      (K := K) a ha hK pi hpi_sq hpi_formula w rfl
  have hconj : w * torus l * w = torus l⁻¹ := by
    apply Subtype.ext
    exact suzukiWeylOperator_conj_torus (K := K) a l
  have hconj_image := congrArg phi hconj
  have himage_inv : phi (torus l) = (phi (torus l))⁻¹ := by
    calc
      phi (torus l) = phi w * phi (torus l) * phi w := by rw [hw]; simp
      _ = phi (torus l⁻¹) := by
        simpa only [map_mul, hw, one_mul, mul_one] using hconj_image
      _ = (phi (torus l))⁻¹ := by simp [map_inv]
  have hsq : phi (torus l) ^ 2 = 1 := by
    calc
      phi (torus l) ^ 2 = phi (torus l) * phi (torus l) := pow_two _
      _ = phi (torus l) * (phi (torus l))⁻¹ :=
        congrArg (fun z => phi (torus l) * z) himage_inv
      _ = 1 := mul_inv_cancel _
  let q : ℕ := 2 ^ (2 * a + 1)
  have hq_card : Nat.card K = q := by
    dsimp [q]
    exact hK
  have h_units_card : Nat.card Kˣ = q - 1 := by
    rw [Nat.card_units, hq_card]
  have hq_even : Even q := by
    refine ⟨2 ^ (2 * a), ?_⟩
    dsimp only [q]
    rw [show 2 * a + 1 = 1 + 2 * a by omega, pow_add]
    omega
  have hcoprime : Nat.Coprime 2 (q - 1) :=
    (Nat.Even.sub_odd (m := q) (n := 1) (by
      dsimp only [q]
      exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)) hq_even odd_one).coprime_two_left
  have ht_pow : phi (torus l) ^ (q - 1) = 1 := by
    rw [← h_units_card]
    exact suzukiTorusOperator_image_pow_card_units_eq_one
      (K := K) a l (torus l) rfl
  have horder : orderOf (phi (torus l)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime
      (orderOf_dvd_of_pow_eq_one hsq)
      (orderOf_dvd_of_pow_eq_one ht_pow)
  have htorus : phi (torus l) = 1 := orderOf_eq_one_iff.mp horder
  have htg : torus l = g := by
    apply Subtype.ext
    exact hg.symm
  rw [← htg]
  exact htorus

/-- The local Suzuki upper-operator group is perfect under the standard
positive-rank field hypotheses. The proof closes the root, torus, and Weyl
generator cases in the abelianization, then propagates triviality over the
actual closure presentation. -/
theorem suzukiUpperMatrixGroup_isPerfect
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1))) :
    Group.IsPerfect (Chevalley.suzukiUpperMatrixGroup a K) := by
  let S := Chevalley.suzukiUpperMatrixGroup a K
  let phi : S →* Abelianization S := Abelianization.of
  have htrivial (g : S) : phi g = 1 := by
    have hg : (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
        Subgroup.closure (Chevalley.suzukiUpperMatrixGenerators a K) := by
      change (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
        Subgroup.closure (Chevalley.suzukiUpperMatrixGenerators a K)
      exact g.property
    have hclosure : ∃ y : S,
        (y : Matrix.GeneralLinearGroup (Fin 4) K) =
          (g : Matrix.GeneralLinearGroup (Fin 4) K) ∧ phi y = 1 := by
      refine Subgroup.closure_induction
        (k := Chevalley.suzukiUpperMatrixGenerators a K)
        (p := fun x _ => ∃ y : S,
          (y : Matrix.GeneralLinearGroup (Fin 4) K) = x ∧ phi y = 1)
        ?_ ?_ ?_ ?_ hg
      · intro x hx
        let y : S := ⟨x, Subgroup.subset_closure hx⟩
        change ((x : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).transpose ∈
          {M : Matrix (Fin 4) (Fin 4) K |
            (∃ u v : K, M = suzukiS a u v) ∨
              (∃ l : Kˣ, M = suzukiD a l) ∨ M = Chevalley.suzukiW K} at hx
        rcases hx with ⟨u, v, hx⟩ | ⟨l, hx⟩ | hx
        · have hval :
            ((x : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
              (suzukiS a u v).transpose := by
            calc
              _ = (((x : Matrix.GeneralLinearGroup (Fin 4) K) :
                  Matrix (Fin 4) (Fin 4) K).transpose).transpose := by simp
              _ = (suzukiS a u v).transpose := congrArg Matrix.transpose hx
          have hroot : x = upperRootOperator a u v := by
            apply Units.ext
            simpa [upperRootOperator, suzukiSGL] using hval
          refine ⟨y, rfl, ?_⟩
          exact upperRootOperator_trivial_in_upperAbelianization
            (K := K) a ha hK pi hpi_sq hpi_formula u v y (by
              change (y : Matrix.GeneralLinearGroup (Fin 4) K) = _
              exact hroot)
        · have hD : (suzukiD a l).transpose = suzukiD a l := by
            ext i j
            by_cases hij : i = j
            · subst j
              simp [suzukiD, Matrix.diagonal_apply]
            · have hji : j ≠ i := Ne.symm hij
              simp [suzukiD, hij, hji]
          have hval :
              ((x : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
                suzukiD a l := by
            calc
              _ = (((x : Matrix.GeneralLinearGroup (Fin 4) K) :
                  Matrix (Fin 4) (Fin 4) K).transpose).transpose := by simp
              _ = (suzukiD a l).transpose := congrArg Matrix.transpose hx
              _ = suzukiD a l := hD
          have htorus : x = suzukiTorusOperator a l := by
            apply Units.ext
            simpa [suzukiTorusOperator] using hval
          refine ⟨y, rfl, ?_⟩
          exact suzukiTorusOperator_trivial_in_upperAbelianization
            (K := K) a ha hK pi hpi_sq hpi_formula l y (by
              change (y : Matrix.GeneralLinearGroup (Fin 4) K) = _
              exact htorus)
        · have hW : (Chevalley.suzukiW K).transpose = Chevalley.suzukiW K := by
            ext i j
            simp [Chevalley.suzukiW, Matrix.transpose_apply, Nat.add_comm]
          have hval :
              ((x : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
                suzukiWeylMatrix := by
            calc
              _ = (((x : Matrix.GeneralLinearGroup (Fin 4) K) :
                  Matrix (Fin 4) (Fin 4) K).transpose).transpose := by simp
              _ = (Chevalley.suzukiW K).transpose := congrArg Matrix.transpose hx
              _ = Chevalley.suzukiW K := hW
              _ = suzukiWeylMatrix := by
                ext i j
                simp [Chevalley.suzukiW, suzukiWeylMatrix, Nat.add_comm]
          have hw : x = suzukiWeylOperator (K := K) := by
            apply Units.ext
            simpa [suzukiWeylOperator] using hval
          refine ⟨y, rfl, ?_⟩
          exact suzukiWeylOperator_trivial_in_upperAbelianization
            (K := K) a ha hK pi hpi_sq hpi_formula y (by
              change (y : Matrix.GeneralLinearGroup (Fin 4) K) = _
              exact hw)
      · exact ⟨1, rfl, map_one phi⟩
      · intro x z hx hz ⟨y, hy, hφy⟩ ⟨w, hw, hφw⟩
        refine ⟨y * w, ?_, ?_⟩
        · change ((y : Matrix.GeneralLinearGroup (Fin 4) K) *
            (w : Matrix.GeneralLinearGroup (Fin 4) K)) = x * z
          rw [hy, hw]
        · rw [map_mul, hφy, hφw, one_mul]
      · intro x hx ⟨y, hy, hφy⟩
        refine ⟨y⁻¹, ?_, ?_⟩
        · change ((y : Matrix.GeneralLinearGroup (Fin 4) K)⁻¹) = x⁻¹
          rw [hy]
        · rw [map_inv, hφy, inv_one]
    rcases hclosure with ⟨y, hy, hphi⟩
    have hEq : y = g := Subtype.ext hy
    rw [← hEq]
    exact hphi
  have hker : phi.ker = (⊤ : Subgroup S) := by
    ext g
    simp [MonoidHom.mem_ker, htrivial g]
  have hcomm : commutator S = ⊤ := by
    calc
      commutator S = phi.ker := by
        exact (Abelianization.ker_of S).symm
      _ = ⊤ := hker
  exact Group.isPerfect_def.mpr hcomm

/-- Perfectness transfers from the upper-orientation Suzuki presentation to
the full matrix generator group through the proved inverse-transpose
equivalence. -/
theorem suzukiMatrixGroup_isPerfect
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1))) :
    Group.IsPerfect (Chevalley.suzukiMatrixGroup a K) := by
  letI : Group.IsPerfect ↥(Chevalley.suzukiUpperMatrixGroup a K) :=
    suzukiUpperMatrixGroup_isPerfect (K := K) a ha hK pi hpi_sq hpi_formula
  let e : Matrix.GeneralLinearGroup (Fin 4) K ≃*
      Matrix.GeneralLinearGroup (Fin 4) K := Matrix.GeneralLinearGroup.inverseTranspose
  have hp : Group.IsPerfect
      ↥((Chevalley.suzukiUpperMatrixGroup a K).map e.toMonoidHom) :=
    Group.IsPerfect.map e.toMonoidHom
  change Group.IsPerfect
    ↥((Chevalley.suzukiUpperMatrixGroup a K).map
      Matrix.GeneralLinearGroup.inverseTranspose.toMonoidHom) at hp
  rw [Chevalley.suzukiUpperMatrixGroup_inverseTranspose] at hp
  exact hp

/-- Perfectness also transfers to the faithful linear-operator Suzuki group
on the four-dimensional coordinate module. -/
theorem suzukiGroup_isPerfect
    [Finite K] [CharP K 2] (a : ℕ) (ha : 0 < a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K) (hpi_sq : ∀ x : K, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x : K, pi x = x ^ (2 ^ (a + 1))) :
    Group.IsPerfect ↥(Chevalley.suzukiGroup a K) := by
  letI : Group.IsPerfect ↥(Chevalley.suzukiMatrixGroup a K) :=
    suzukiMatrixGroup_isPerfect (K := K) a ha hK pi hpi_sq hpi_formula
  let e := Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))
  have hp : Group.IsPerfect
      ↥((Chevalley.suzukiMatrixGroup a K).map e.toMonoidHom) :=
    Group.IsPerfect.map e.toMonoidHom
  change Group.IsPerfect ↥(Chevalley.suzukiGroup a K) at hp
  exact hp

/-- Two-transitivity transfers from the root-plus-Weyl subgroup to the full
upper-orientation Suzuki operator group, which also contains the torus. -/
theorem suzukiUpperMatrixGroup_two_transitive_on_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0)
    (z₁ z₂ z₃ z₄ : ℙ K (Fin 4 → K))
    (hz₁ : z₁ ∈ ovoid pi) (hz₂ : z₂ ∈ ovoid pi)
    (hz₃ : z₃ ∈ ovoid pi) (hz₄ : z₄ ∈ ovoid pi)
    (hne₁ : z₁ ≠ z₂) (hne₂ : z₃ ≠ z₄) :
    ∃ g : Chevalley.suzukiUpperMatrixGroup a K,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₁ = z₃ ∧
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₂ = z₄ := by
  obtain ⟨g, hg₁, hg₂⟩ := rootWeylOperatorGroup_two_transitive_on_ovoid
    (K := K) a pi hpi_sq hpi_formula hnorm_zero
    z₁ z₂ z₃ z₄ hz₁ hz₂ hz₃ hz₄ hne₁ hne₂
  let g' : Chevalley.suzukiUpperMatrixGroup a K :=
    ⟨g, rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a g.property⟩
  refine ⟨g', ?_, ?_⟩
  · simpa [g'] using hg₁
  · simpa [g'] using hg₂

/-- The finite Suzuki field hypotheses discharge the norm condition in the
two-transitivity theorem for the full upper-orientation operator group. -/
theorem suzukiUpperMatrixGroup_two_transitive_on_ovoid_of_field
    [Finite K] [CharP K 2] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (z₁ z₂ z₃ z₄ : ℙ K (Fin 4 → K))
    (hz₁ : z₁ ∈ ovoid pi) (hz₂ : z₂ ∈ ovoid pi)
    (hz₃ : z₃ ∈ ovoid pi) (hz₄ : z₄ ∈ ovoid pi)
    (hne₁ : z₁ ≠ z₂) (hne₂ : z₃ ≠ z₄) :
    ∃ g : Chevalley.suzukiUpperMatrixGroup a K,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₁ = z₃ ∧
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₂ = z₄ := by
  exact suzukiUpperMatrixGroup_two_transitive_on_ovoid
    (K := K) a pi hpi_sq hpi_formula
    (ovoidNorm_eq_zero_only_at_origin a hK pi hpi_formula)
    z₁ z₂ z₃ z₄ hz₁ hz₂ hz₃ hz₄ hne₁ hne₂

theorem rootWeylOperatorGroup_noncommuting_pair (a : ℕ) :
    ∃ g h : rootWeylOperatorGroup (K := K) a, g * h ≠ h * g := by
  let g : rootWeylOperatorGroup (K := K) a :=
    ⟨upperRootOperator a 1 0,
      Subgroup.subset_closure (Or.inl ⟨1, 0, rfl⟩)⟩
  let h : rootWeylOperatorGroup (K := K) a :=
    ⟨suzukiWeylOperator (K := K), Subgroup.subset_closure (Or.inr rfl)⟩
  refine ⟨g, h, ?_⟩
  intro hcomm
  have hGL : (g : Matrix.GeneralLinearGroup (Fin 4) K) * h =
      (h : Matrix.GeneralLinearGroup (Fin 4) K) * g :=
    congrArg (fun x : rootWeylOperatorGroup (K := K) a =>
      (x : Matrix.GeneralLinearGroup (Fin 4) K)) hcomm
  have hmat :
      ((g : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (((h : rootWeylOperatorGroup (K := K) a) :
          Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((h : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (((g : rootWeylOperatorGroup (K := K) a) :
          Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    congrArg (fun x : Matrix.GeneralLinearGroup (Fin 4) K =>
      (x : Matrix (Fin 4) (Fin 4) K)) hGL
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) hmat
  norm_num [g, h, upperRootOperator, suzukiSGL, suzukiS, suzukiN,
    suzukiWeylOperator, suzukiWeylMatrix, Matrix.mul_apply,
    Fin.sum_univ_four] at h00

/-- The full upper-orientation Suzuki operator group is noncommutative. The
root/Weyl witness embeds into the group that also contains the torus. -/
theorem suzukiUpperMatrixGroup_noncommuting_pair (a : ℕ) :
    ∃ g h : ↥(Chevalley.suzukiUpperMatrixGroup a K), g * h ≠ h * g := by
  obtain ⟨g, h, hgh⟩ := rootWeylOperatorGroup_noncommuting_pair (K := K) a
  let g' : ↥(Chevalley.suzukiUpperMatrixGroup a K) :=
    ⟨g, rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a g.property⟩
  let h' : ↥(Chevalley.suzukiUpperMatrixGroup a K) :=
    ⟨h, rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a h.property⟩
  refine ⟨g', h', ?_⟩
  intro hcomm
  have hGL : (g : Matrix.GeneralLinearGroup (Fin 4) K) * h =
      (h : Matrix.GeneralLinearGroup (Fin 4) K) * g := by
    simpa [g', h'] using congrArg
      (fun x : ↥(Chevalley.suzukiUpperMatrixGroup a K) =>
        (x : Matrix.GeneralLinearGroup (Fin 4) K)) hcomm
  apply hgh
  apply Subtype.ext
  exact hGL

/-- The concrete root and Weyl matrices in the Suzuki operator construction
do not commute, witnessed in their actual four-dimensional matrix carrier. -/
theorem suzukiGeneratorMatrices_noncommute (a : ℕ) :
    ∃ A B : Matrix (Fin 4) (Fin 4) K, A * B ≠ B * A := by
  refine ⟨((upperRootOperator a (1 : K) (0 : K) :
      Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
    ((suzukiWeylOperator (K := K) :
      Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) h
  norm_num [upperRootOperator, suzukiSGL, suzukiS, suzukiN,
    suzukiWeylOperator, suzukiWeylMatrix, Chevalley.suzukiW,
    Matrix.mul_apply, Fin.sum_univ_four] at h00

/-- The upper-root operator subgroup is genuinely noncommutative: the
operators with parameters `(1,0)` and `(c,0)` have different `(0,2)` entries
after multiplication in the two orders whenever `pi c ≠ c`. -/
theorem upperRootMatrixGroup_noncommuting_pair [CharP K 2] (a : ℕ)
    (pi : K ≃+* K) (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (c : K) (hc : pi c ≠ c) :
    ∃ g h : upperRootMatrixGroup (K := K) a, g * h ≠ h * g := by
  let g : upperRootMatrixGroup (K := K) a :=
    ⟨upperRootOperator a 1 0, Subgroup.subset_closure ⟨1, 0, rfl⟩⟩
  let h : upperRootMatrixGroup (K := K) a :=
    ⟨upperRootOperator a c 0, Subgroup.subset_closure ⟨c, 0, rfl⟩⟩
  refine ⟨g, h, ?_⟩
  intro hcomm
  have hGL : (g : Matrix.GeneralLinearGroup (Fin 4) K) * h =
      (h : Matrix.GeneralLinearGroup (Fin 4) K) * g :=
    congrArg (fun x : upperRootMatrixGroup (K := K) a =>
      (x : Matrix.GeneralLinearGroup (Fin 4) K)) hcomm
  have hmat : ((g : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (((h : upperRootMatrixGroup (K := K) a) :
        Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((h : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (((g : upperRootMatrixGroup (K := K) a) :
        Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    exact congrArg (fun x : Matrix.GeneralLinearGroup (Fin 4) K =>
      (x : Matrix (Fin 4) (Fin 4) K)) hGL
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 2) hmat
  have hpi_c_eq_c : pi c = c := by
    simpa [g, h, upperRootOperator, suzukiSGL, suzukiS, suzukiN,
      Matrix.mul_apply, Fin.sum_univ_four, hpi_formula] using h02
  exact hc hpi_c_eq_c

end InfoGeometry.Exceptional.CFSGPort.Suzuki
